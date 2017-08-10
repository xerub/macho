/*
 *  ghetto kext extractor (noarch, mach-o kernel)
 *
 *  Copyright (c) 2016 xerub
 */

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach-o/reloc.h>

#include <sqlite3.h>

typedef unsigned long long addr_t;

#define IS64(image) (*(uint8_t *)(image) & 1)

#define MACHO(p) ((*(unsigned int *)(p) & ~1) == 0xfeedface)

static size_t align = 0xFFF;

static __inline size_t
round_page(size_t size)
{
    return (size + align) & ~align;
}

/* generic stuff *************************************************************/

#define UCHAR_MAX 255

static unsigned char *
boyermoore_horspool_memmem(const unsigned char* haystack, size_t hlen,
                           const unsigned char* needle,   size_t nlen)
{
    size_t last, scan = 0;
    size_t bad_char_skip[UCHAR_MAX + 1]; /* Officially called:
                                          * bad character shift */

    /* Sanity checks on the parameters */
    if (nlen <= 0 || !haystack || !needle)
        return NULL;

    /* ---- Preprocess ---- */
    /* Initialize the table to default value */
    /* When a character is encountered that does not occur
     * in the needle, we can safely skip ahead for the whole
     * length of the needle.
     */
    for (scan = 0; scan <= UCHAR_MAX; scan = scan + 1)
        bad_char_skip[scan] = nlen;

    /* C arrays have the first byte at [0], therefore:
     * [nlen - 1] is the last byte of the array. */
    last = nlen - 1;

    /* Then populate it with the analysis of the needle */
    for (scan = 0; scan < last; scan = scan + 1)
        bad_char_skip[needle[scan]] = last - scan;

    /* ---- Do the matching ---- */

    /* Search the haystack, while the needle can still be within it. */
    while (hlen >= nlen)
    {
        /* scan from the end of the needle */
        for (scan = last; haystack[scan] == needle[scan]; scan = scan - 1)
            if (scan == 0) /* If the first byte matches, we've found it. */
                return (void *)haystack;

        /* otherwise, we need to skip some bytes and start again.
           Note that here we are getting the skip value based on the last byte
           of needle, no matter where we didn't match. So if needle is: "abcd"
           then we are skipping based on 'd' and that value will be 4, and
           for "abcdd" we again skip on 'd' but the value will be only 1.
           The alternative of pretending that the mismatched character was
           the last character is slower in the normal case (E.g. finding
           "abcd" in "...azcd..." gives 4 by using 'd' but only
           4-2==2 using 'z'. */
        hlen     -= bad_char_skip[haystack[last]];
        haystack += bad_char_skip[haystack[last]];
    }

    return NULL;
}

/* generic macho *************************************************************/

static addr_t
get_sect_data(const uint8_t *p, size_t size, const char *segname, const char *sectname, size_t *sz)
{
    unsigned i, j;
    const struct mach_header *hdr = (struct mach_header *)p;
    const uint8_t *q = p + sizeof(struct mach_header);

    (void)size;

    if (sz) *sz = 0;

    if (!MACHO(p)) {
        return 0;
    }
    if (IS64(p)) {
        q += 4;
    }

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, segname)) {
                const struct section *sec = (struct section *)(seg + 1);
                if (sectname == NULL) {
                    if (sz) *sz = seg->filesize;
                    return seg->fileoff;
                }
                for (j = 0; j < seg->nsects; j++) {
                    if (!strcmp(sec[j].sectname, sectname)) {
                        if (sz) *sz = sec[j].size;
                        if (sec[j].flags == S_ZEROFILL) {
                            return seg->fileoff + sec[j].addr - seg->vmaddr;
                        }
                        return sec[j].offset;
                    }
                }
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, segname)) {
                const struct section_64 *sec = (struct section_64 *)(seg + 1);
                if (sectname == NULL) {
                    if (sz) *sz = seg->filesize;
                    return seg->fileoff;
                }
                for (j = 0; j < seg->nsects; j++) {
                    if (!strcmp(sec[j].sectname, sectname)) {
                        if (sz) *sz = sec[j].size;
                        if (sec[j].flags == S_ZEROFILL) {
                            return seg->fileoff + sec[j].addr - seg->vmaddr;
                        }
                        return sec[j].offset;
                    }
                }
            }
        }
        q = q + cmd->cmdsize;
    }

    return 0;
}

static addr_t
get_low_sect(const uint8_t *p, size_t size)
{
    unsigned i, j;
    addr_t low = -1;
    const struct mach_header *hdr = (struct mach_header *)p;
    const uint8_t *q = p + sizeof(struct mach_header);

    (void)size;

    if (!MACHO(p)) {
        return 0;
    }
    if (IS64(p)) {
        q += 4;
    }

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            const struct section *sec = (struct section *)(seg + 1);
            for (j = 0; j < seg->nsects; j++) {
                if (low > sec[j].offset && sec[j].flags != S_ZEROFILL) {
                    low = sec[j].offset;
                }
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            const struct section_64 *sec = (struct section_64 *)(seg + 1);
            for (j = 0; j < seg->nsects; j++) {
                if (low > sec[j].offset && sec[j].flags != S_ZEROFILL) {
                    low = sec[j].offset;
                }
            }
        }
        q = q + cmd->cmdsize;
    }

    return low;
}

/* kernel stuff **************************************************************/

uint8_t *kernel = MAP_FAILED;
size_t kernel_size = 0;
int kernel_fd = -1;

static int
init_kernel(const char *filename)
{
    kernel_fd = open(filename, O_RDONLY);
    if (kernel_fd < 0) {
        return -1;
    }

    kernel_size = lseek(kernel_fd, 0, SEEK_END);

    kernel = mmap(NULL, kernel_size, PROT_READ, MAP_PRIVATE, kernel_fd, 0);
    if (kernel == MAP_FAILED) {
        close(kernel_fd);
        kernel_fd = -1;
        return -1;
    }

    return 0;
}

static void
term_kernel(void)
{
    munmap(kernel, kernel_size);
    close(kernel_fd);
}

/* processor *****************************************************************/

static int
show_syms(size_t offset, int thumbize, int (*callback)(unsigned long long value, const char *symbol, void *opaque), void *opaque)
{
    uint32_t i;
    const uint8_t *p, *q;
    const struct mach_header *hdr;
    size_t eseg, size, next;
    int is64;

again:
    if (offset >= kernel_size - 3) {
        return 0;
    }

    size = 0;
    next = 0;
    p = kernel + offset;
    hdr = (struct mach_header *)p;
    q = p + sizeof(struct mach_header);
    is64 = 0;

    if (!MACHO(p)) {
        return 0;
    }
    if (IS64(p)) {
        is64 = 4;
    }

    q = p + sizeof(struct mach_header) + is64;

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, "__PRELINK_TEXT")) {
                next = seg->fileoff;
            }
            if (!strcmp(seg->segname, "__PAGEZERO")) {
                goto cont;
            }
            if (seg->vmaddr == 0) {
                eseg = round_page(seg->fileoff + seg->vmsize);
                if (offset + eseg < kernel_size - 3 && *(uint32_t *)(kernel + offset + eseg) != *(uint32_t *)kernel) {
                    align = 0x3FFF; /* promote alignment and hope for the best */
                    eseg = round_page(seg->fileoff + seg->vmsize);
                }
            } else {
                assert((seg->fileoff & 0xFFF) == 0 || next);
                eseg = seg->fileoff + round_page(seg->vmsize);
            }
            if (size < eseg) {
                size = eseg;
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__PRELINK_TEXT")) {
                next = seg->fileoff;
            }
            if (!strcmp(seg->segname, "__PAGEZERO")) {
                goto cont;
            }
            if (seg->vmaddr == 0) {
                eseg = round_page(seg->fileoff + seg->vmsize);
                if (offset + eseg < kernel_size - 3 && *(uint32_t *)(kernel + offset + eseg) != *(uint32_t *)kernel) {
                    align = 0x3FFF; /* promote alignment and hope for the best */
                    eseg = round_page(seg->fileoff + seg->vmsize);
                }
            } else {
                assert((seg->fileoff & 0xFFF) == 0 || next);
                eseg = seg->fileoff + round_page(seg->vmsize);
            }
            if (size < eseg) {
                size = eseg;
            }
        }
        if (cmd->cmd == LC_SYMTAB) {
            const struct symtab_command *sym = (struct symtab_command *)q;
            const char *stroff = (const char *)p + sym->stroff;
            if (is64) {
                uint32_t k;
                const struct nlist_64 *s = (struct nlist_64 *)(p + sym->symoff);
                for (k = 0; k < sym->nsyms; k++) {
                    if (s[k].n_type & N_STAB) {
                        continue;
                    }
                    if (s[k].n_value && (s[k].n_type & N_TYPE) != N_INDR) {
                        if (callback(s[k].n_value, stroff + s[k].n_un.n_strx, opaque)) {
                            return -1;
                        }
                    }
                }
            } else {
                uint32_t k;
                const struct nlist *s = (struct nlist *)(p + sym->symoff);
                for (k = 0; k < sym->nsyms; k++) {
                    if (s[k].n_type & N_STAB) {
                        continue;
                    }
                    if (s[k].n_value && (s[k].n_type & N_TYPE) != N_INDR) {
                        int thumb = thumbize && (s[k].n_desc & N_ARM_THUMB_DEF);
                        if (callback(s[k].n_value + thumb, stroff + s[k].n_un.n_strx, opaque)) {
                            return -1;
                        }
                    }
                }
            }
        }
        cont: q = q + cmd->cmdsize;
    }

    if (next) {
        return show_syms(next, thumbize, callback, opaque);
    }
    if (size) {
        offset += size;
        goto again;
    }
    return 0;
}

static int
callback(unsigned long long value, const char *symbol, void *opaque)
{
    int rv;
    sqlite3_stmt *stmt = (sqlite3_stmt *)opaque;
    //printf("INSERT INTO \"Symbols\" VALUES('%s',%llu);\n", symbol, value);
    rv = sqlite3_reset(stmt);
    if (rv) {
        return -1;
    }
    rv = sqlite3_bind_text(stmt, 1, symbol, strlen(symbol), SQLITE_STATIC);
    if (rv) {
        return -1;
    }
    rv = sqlite3_bind_int64(stmt, 2, value);
    if (rv) {
        return -1;
    }
    rv = sqlite3_step(stmt);
    if (rv != SQLITE_DONE) {
        fprintf(stderr, "sqlite error: %d\n", rv);
        return -1;
    }
    return 0;
}

static sqlite3 *
make_core_db(void)
{
    int rv;
    sqlite3 *db;
    sqlite3_stmt *stmt;
    char *str;

    rv = sqlite3_open(":memory:", &db);
    if (rv) {
        fprintf(stderr, "[e] cannot open database\n");
        return NULL;
    }

    //printf("CREATE TABLE Symbols(Symbol varchar(255), Value int);\n");
    rv = sqlite3_exec(db, "CREATE TABLE Symbols(Symbol varchar(255), Value int);", NULL, NULL, &str);
    if (rv) {
        fprintf(stderr, "sqlite error: %s\n", str);
        sqlite3_free(str);
        sqlite3_close(db);
        return NULL;
    }

    str = "INSERT INTO \"Symbols\" VALUES(?1,?2);";
    rv = sqlite3_prepare_v2(db, str, strlen(str) + 1, &stmt, NULL);
    if (rv) {
        sqlite3_close(db);
        fprintf(stderr, "[e] cannot make statement\n");
        return NULL;
    }

    rv = sqlite3_exec(db, "BEGIN TRANSACTION;", NULL, NULL, NULL);

    show_syms(0, 1, callback, stmt);

    sqlite3_finalize(stmt);

    rv = sqlite3_exec(db, "END TRANSACTION;", NULL, NULL, NULL);
    if (rv) {
        sqlite3_close(db);
        fprintf(stderr, "[e] cannot end transaction\n");
        return NULL;
    }

    rv = sqlite3_exec(db, "CREATE INDEX symbol_index on Symbols (Value);", NULL, NULL, &str);
    if (rv) {
        fprintf(stderr, "sqlite error: %s\n", str);
        sqlite3_free(str);
    }

    return db;
}

/* main **********************************************************************/

static char *
kdb_get_addrsym(sqlite3 *db, addr_t addr)
{
    int rv;
    char sql[4096];
    int err = 0;
    int row = 0;

    sqlite3_stmt *stmt;
    char *x = NULL;

    snprintf(sql, sizeof(sql), "SELECT Symbol FROM Symbols WHERE Value IS %lld", addr);
    rv = sqlite3_prepare_v2(db, sql, strlen(sql) + 1, &stmt, NULL);
    if (rv) {
        return NULL;
    }

    while (1) {
        rv = sqlite3_step(stmt);
        if (rv == SQLITE_ROW) {
            if (row) {
                err = 1;
                break;
            }
            free(x);
            x = strdup((char *)sqlite3_column_text(stmt, 0));
            row++;
#if 666 /* a bit faster */
            break;
#endif
        } else if (rv == SQLITE_DONE) {
            break;
        } else {
            err = 2;
            break;
        }
    }

    sqlite3_finalize(stmt);
    if (err || !row) {
        free(x);
        return NULL;
    }
    return x;
}

static size_t
append_str(char **str_data, size_t *str_size, const char *sym)
{
    char *tmp;
    size_t len;
    size_t ret = *str_size;

    assert(sym);

    len = strlen(sym) + 1;

    tmp = realloc(*str_data, ret + len);
    assert(tmp);
    *str_data = tmp;
    *str_size += len;

    memcpy(tmp + ret, sym, len);

    return ret;
}

static int
restore_kext(size_t offset, size_t size, addr_t base, const char *kext, sqlite3 *db)
{
    unsigned i;
    uint8_t *buf;
    struct symtab_command *sym = NULL;
    struct mach_header *hdr;
    const uint8_t *q;
    int is64 = 0;

    FILE *f;

    char *symstr, *tmp;
    char *str_data = NULL;
    size_t str_size = 0;
    void *sym_data = NULL;
    size_t sym_size = 0;
    struct relocation_info *rtmp, *rel_data = NULL;
    size_t rel_size = 0;
    size_t counts = 0;
    size_t countr = 0;
    size_t total;
    unsigned idx;

    size_t sz;
    addr_t comm, bss, imp;

    if (IS64(kernel)) {
        is64 = 4;
    }

    hdr = (struct mach_header *)(kernel + offset);
    q = kernel + offset + sizeof(struct mach_header) + is64;

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SYMTAB) {
            sym = (struct symtab_command *)q;
        }
        q = q + cmd->cmdsize;
    }

    if (sym) {
        str_size = sym->strsize;
        str_data = malloc(str_size);
        assert(str_data);
        memcpy(str_data, kernel + offset + sym->stroff, str_size);
        counts = sym->nsyms;
        sym_size = counts * (is64 ? sizeof(struct nlist_64) : sizeof(struct nlist));
        sym_data = malloc(sym_size);
        assert(sym_data);
        memcpy(sym_data, kernel + offset + sym->symoff, sym_size);
    } else {
        append_str(&str_data, &str_size, "");
    }

    comm = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__common", &sz);
    bss = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__bss", &sz);
    if (comm || bss) {
        if (bss && (!comm || comm > bss)) {
            comm = bss;
        }
    } else {
        comm = get_sect_data(kernel + offset, kernel_size - offset, "__LINKEDIT", NULL, &sz);
    }
    assert(comm);

    imp = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__got", &sz);
    if (!imp) {
        imp = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__nl_symbol_ptr", &sz);
    }
    if (!imp) {
        imp = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", NULL, &sz);
    }
    assert(imp);

    sz = comm - imp; // scan all pointers, up to __common

    imp += offset;

    if (is64) {
        struct nlist_64 *s;
        const uint64_t *ptr = (uint64_t *)(kernel + imp);
        sz /= sizeof(*ptr);
        for (i = 0; i < sz; i++) {
            if (ptr[i] >= base && ptr[i] < base + size) {
                // local symbol // printf("0x%llx: loc_%llx\n", ptr[i], ptr[i]);
                continue;
            }
            symstr = kdb_get_addrsym(db, ptr[i]);
            if (!symstr) {
                // undefined symbol // printf("0x%llx: ext_%llx\n", ptr[i], ptr[i]);
                continue;
            }

            tmp = (char *)boyermoore_horspool_memmem((uint8_t *)str_data, str_size, (const uint8_t *)symstr, strlen(symstr) + 1);
            if (tmp) {
                for (idx = 0; tmp > str_data; tmp--) {
                    if (*tmp == '\0') {
                        idx++;
                    }
                }
            } else {
                idx = counts++;
                s = realloc(sym_data, counts * sizeof(*s));
                assert(s);
                sym_data = s;
                s[idx].n_un.n_strx = append_str(&str_data, &str_size, symstr);
                s[idx].n_type = N_EXT;
                s[idx].n_sect = NO_SECT;
                s[idx].n_desc = REFERENCE_FLAG_UNDEFINED_NON_LAZY | (DYNAMIC_LOOKUP_ORDINAL << 8);
                s[idx].n_value = 0;
            }

            rtmp = realloc(rel_data, (countr + 1) * sizeof(*rel_data));
            assert(rtmp);
            rel_data = rtmp;
            rel_data[countr].r_pcrel = 0;
            rel_data[countr].r_length = 3;
            rel_data[countr].r_extern = 1;
            rel_data[countr].r_type = GENERIC_RELOC_VANILLA;
            rel_data[countr].r_address = (uint8_t *)(ptr + i) - (kernel + offset);
            rel_data[countr].r_symbolnum = idx;
            countr++;

            printf("0x%lx: 0x%llx: %s\n", (uint8_t *)(ptr + i) - (kernel + offset), ptr[i], symstr);
            free(symstr);
        }
        sym_size = counts * sizeof(*s);
    } else {
        struct nlist *s;
        const uint32_t *ptr = (uint32_t *)(kernel + imp);
        sz /= sizeof(*ptr);
        for (i = 0; i < sz; i++) {
            if (ptr[i] >= base && ptr[i] < base + size) {
                // local symbol // printf("0x%x: loc_%x\n", ptr[i], ptr[i]);
                continue;
            }
            symstr = kdb_get_addrsym(db, ptr[i]);
            if (!symstr) {
                // undefined symbol // printf("0x%x: ext_%x\n", ptr[i], ptr[i]);
                continue;
            }

            tmp = (char *)boyermoore_horspool_memmem((uint8_t *)str_data, str_size, (const uint8_t *)symstr, strlen(symstr) + 1);
            if (tmp) {
                for (idx = 0; tmp > str_data; tmp--) {
                    if (*tmp == '\0') {
                        idx++;
                    }
                }
            } else {
                idx = counts++;
                s = realloc(sym_data, counts * sizeof(*s));
                assert(s);
                sym_data = s;
                s[idx].n_un.n_strx = append_str(&str_data, &str_size, symstr);
                s[idx].n_type = N_EXT;
                s[idx].n_sect = NO_SECT;
                s[idx].n_desc = REFERENCE_FLAG_UNDEFINED_NON_LAZY | (DYNAMIC_LOOKUP_ORDINAL << 8);
                s[idx].n_value = 0;
            }

            rtmp = realloc(rel_data, (countr + 1) * sizeof(*rel_data));
            assert(rtmp);
            rel_data = rtmp;
            rel_data[countr].r_pcrel = 0;
            rel_data[countr].r_length = 2;
            rel_data[countr].r_extern = 1;
            rel_data[countr].r_type = GENERIC_RELOC_VANILLA;
            rel_data[countr].r_address = (uint8_t *)(ptr + i) - (kernel + offset);
            rel_data[countr].r_symbolnum = idx;
            countr++;

            printf("0x%lx: 0x%x: %s\n", (uint8_t *)(ptr + i) - (kernel + offset), ptr[i], symstr);
            free(symstr);
        }
        sym_size = counts * sizeof(*s);
    }
    rel_size = countr * sizeof(rel_data);

    total = rel_size + sym_size + str_size;
    buf = malloc(size + total);
    assert(buf);
    memcpy(buf, kernel + offset, size);
    memcpy(buf + size, rel_data, rel_size);
    memcpy(buf + size + rel_size, sym_data, sym_size);
    memcpy(buf + size + rel_size + sym_size, str_data, str_size);

    free(str_data);
    free(sym_data);

    hdr = (struct mach_header *)buf;
    q = buf + sizeof(struct mach_header) + is64;

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, "__LINKEDIT")) {
                assert(seg->filesize == seg->vmsize);
                //seg->filesize += total;
                //seg->vmsize += (total + 0xFFF) & ~0xFFF;
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__LINKEDIT")) {
                assert(seg->filesize == seg->vmsize);
                //seg->filesize += total;
                //seg->vmsize += (total + 0xFFF) & ~0xFFF;
            }
        }
        if (cmd->cmd == LC_SYMTAB) {
            sym = (struct symtab_command *)q;
        }
        if (cmd->cmd == LC_DYSYMTAB) {
            struct dysymtab_command *dys = (struct dysymtab_command *)q;
            dys->extreloff = size;
            dys->nextrel = countr;
        }
        q = q + cmd->cmdsize;
    }
    if (!sym) {
        addr_t text = get_low_sect(kernel + offset, kernel_size - offset);
        assert(text != -1ULL);
        sym = (struct symtab_command *)q;
        assert((uint8_t *)(sym + 1) <= buf + text);
        sym->cmd = LC_SYMTAB;
        sym->cmdsize = sizeof(struct symtab_command);
        hdr->ncmds++;
        hdr->sizeofcmds += sym->cmdsize;
    }
    sym->symoff = size + rel_size;
    sym->nsyms = counts;
    sym->stroff = size + rel_size + sym_size;
    sym->strsize = str_size;

    // for some fucking reason, IDA displays ugly shit, unless we do this
    if (is64) {
        for (i = 0; i < countr; i++) {
            *(uint64_t *)(buf + rel_data[i].r_address) = 0;
        }
    }

    free(rel_data);

    f = fopen(kext, "wb");
    if (f) {
        fwrite(buf, 1, size + total, f);
        fclose(f);
    }

    free(buf);

    return 0;
}

#define OK(c) (isalnum(c) || (c) == '_' || (c) == '.' || (c) == '-')

static int
parse_one(size_t offset, size_t size, addr_t base, const char *kext, sqlite3 *db)
{
    size_t sz;
    addr_t data = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__data", &sz);
    size_t i, j, n = sz / sizeof(uint32_t);
    const uint32_t *ptr = (uint32_t *)(kernel + offset + data);
    const char *id = NULL;

    for (i = 0; i + 2 < n; i++, ptr++) {
        if (ptr[0] == 0 && ptr[1] == 1 && ptr[2] == -1U &&
            (uint8_t *)(ptr + 3) + 64 < kernel + offset + data + sz) {
            id = (char *)(ptr + 3);
            for (j = 0; j < 64 && OK(id[j]); j++) {
            }
            if (j >= 3 && j < 64 && id[j] == '\0') {
                if (!kext) {
                    printf("0x%llx(0x%zx): %s\n", base, offset, id);
                } else if (!strcmp(kext, id)) {
                    return restore_kext(offset, size, base, kext, db);
                }
                return 0;
            }
        }
    }

    assert(0);
    return -1;
}

static int
parse_kexts(size_t offset, const char *kext, sqlite3 *db)
{
    uint32_t i;
    const uint8_t *p, *q;
    const struct mach_header *hdr;
    size_t eseg, size, next;
    addr_t base;
    int is64;

again:
    if (offset >= kernel_size - 3) {
        return 0;
    }

    size = 0;
    next = 0;
    base = 0;
    p = kernel + offset;
    hdr = (struct mach_header *)p;
    q = p + sizeof(struct mach_header);
    is64 = 0;

    if (!MACHO(p)) {
        return 0;
    }
    if (IS64(p)) {
        is64 = 4;
    }

    q = p + sizeof(struct mach_header) + is64;

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, "__PRELINK_TEXT")) {
                next = seg->fileoff;
            }
            if (!strcmp(seg->segname, "__TEXT")) {
                base = seg->vmaddr;
            }
            if (!strcmp(seg->segname, "__PAGEZERO")) {
                goto cont;
            }
            if (seg->vmaddr == 0) {
                eseg = round_page(seg->fileoff + seg->vmsize);
                if (offset + eseg < kernel_size - 3 && *(uint32_t *)(kernel + offset + eseg) != *(uint32_t *)kernel) {
                    align = 0x3FFF; /* promote alignment and hope for the best */
                    eseg = round_page(seg->fileoff + seg->vmsize);
                }
            } else {
                assert((seg->fileoff & 0xFFF) == 0 || next);
                eseg = seg->fileoff + round_page(seg->vmsize);
            }
            if (size < eseg) {
                size = eseg;
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__PRELINK_TEXT")) {
                next = seg->fileoff;
            }
            if (!strcmp(seg->segname, "__TEXT")) {
                base = seg->vmaddr;
            }
            if (!strcmp(seg->segname, "__PAGEZERO")) {
                goto cont;
            }
            if (seg->vmaddr == 0) {
                eseg = round_page(seg->fileoff + seg->vmsize);
                if (offset + eseg < kernel_size - 3 && *(uint32_t *)(kernel + offset + eseg) != *(uint32_t *)kernel) {
                    align = 0x3FFF; /* promote alignment and hope for the best */
                    eseg = round_page(seg->fileoff + seg->vmsize);
                }
            } else {
                assert((seg->fileoff & 0xFFF) == 0 || next);
                eseg = seg->fileoff + round_page(seg->vmsize);
            }
            if (size < eseg) {
                size = eseg;
            }
        }
        cont: q = q + cmd->cmdsize;
    }

    if (offset && base) {
        parse_one(offset, size, base, kext, db);
    }

    if (next) {
        return parse_kexts(next, kext, db);
    }
    if (size) {
        offset += size;
        goto again;
    }
    return 0;
}

int
main(int argc, char **argv)
{
    int rv;
    sqlite3 *db;
    const char *krnl = NULL;
    const char *kext = NULL;

    while (--argc > 0) {
        const char *p = *++argv;
        if (!strcmp(p, "-k")) {
            if (argc < 2) {
                fprintf(stderr, "argument to '%s' is missing\n", p);
                return 1;
            }
            argc--;
            kext = *++argv;
            continue;
        }
        krnl = p;
    }

    if (!krnl) {
        fprintf(stderr, "usage: %s [options] kernel\n", argv[0]);
        fprintf(stderr, "\t-k kext\ta kext identifier\n");
        return 1;
    }

    rv = init_kernel(krnl);
    if (rv) {
        fprintf(stderr, "[e] cannot read kernel\n");
        return -1;
    }

    db = make_core_db();
    if (db) {
        parse_kexts(0, kext, db);
        sqlite3_close(db);
    }

    term_kernel();
    return 0;
}
