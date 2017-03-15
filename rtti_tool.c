/*
 *  ghetto vtable tool (noarch, mach-o exe/dylib, rtti)
 *
 *  Copyright (c) 2016 xerub
 */

/*
 * use case:
 * ./vtool -s symbolicated_macho > sqlite.ini
 * sqlite3 -init sqlite.ini sym.db .quit
 * ./vtool -i -l sym.db stripped_macho > symbolicate.idc
 * NB: you can merge multiple sqlite.ini into the same sym.db
 */

#include <assert.h>
#include <ctype.h>
#include <err.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach-o/reloc.h>

#include <sqlite3.h>

typedef unsigned long long addr_t;

#define IS64(image) (*(uint8_t *)(image) & 1)

static int for_ida = 0;
static int for_sqlite = 0;
static sqlite3_stmt *g_stmt;

/* generic macho *************************************************************/

static addr_t
get_range(uint8_t *buf, size_t size, addr_t *end)
{
    unsigned i;
    const struct mach_header *hdr = (struct mach_header *)buf;
    const uint8_t *q = buf + sizeof(struct mach_header);
    addr_t min = -1;
    addr_t max = 0;

    (void)size;

    *end = 0;

    if ((buf[0] & 0xFE) != 0xCE && buf[1] != 0xFA && buf[2] != 0xED && buf[3] != 0xFE) {
        return -1;
    }
    if (IS64(buf)) {
        q += 4;
    }

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, "__TEXT")) {
                const struct section *sec = (struct section *)(seg + 1);
                if (seg->nsects) {
                    min = sec[0].addr;
                }
            }
            if (!strcmp(seg->segname, "__LINKEDIT")) {
                max = seg->vmaddr;
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__TEXT")) {
                const struct section_64 *sec = (struct section_64 *)(seg + 1);
                if (seg->nsects) {
                    min = sec[0].addr;
                }
            }
            if (!strcmp(seg->segname, "__LINKEDIT")) {
                max = seg->vmaddr;
            }
        }
        q = q + cmd->cmdsize;
    }

    *end = max;
    return min;
}

static addr_t
get_base(uint8_t *buf, size_t size)
{
    unsigned i;
    const struct mach_header *hdr = (struct mach_header *)buf;
    const uint8_t *q = buf + sizeof(struct mach_header);

    (void)size;

    if ((buf[0] & 0xFE) != 0xCE && buf[1] != 0xFA && buf[2] != 0xED && buf[3] != 0xFE) {
        return -1;
    }
    if (IS64(buf)) {
        q += 4;
    }

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, "__TEXT")) {
                return seg->vmaddr;
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__TEXT")) {
                return seg->vmaddr;
            }
        }
        q = q + cmd->cmdsize;
    }

    return -1;
}

static addr_t
get_sect_data(const uint8_t *p, size_t size, const char *segname, const char *sectname, size_t *sz)
{
    unsigned i, j;
    const struct mach_header *hdr = (struct mach_header *)p;
    const uint8_t *q = p + sizeof(struct mach_header);

    (void)size;

    if (sz) *sz = 0;

    if ((p[0] & 0xFE) != 0xCE && p[1] != 0xFA && p[2] != 0xED && p[3] != 0xFE) {
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

/* kernel stuff **************************************************************/

uint8_t *kernel = MAP_FAILED;
size_t kernel_size = 0;
int kernel_fd = -1;
uint64_t kernel_base = 0;

static int
init_kernel(const char *filename)
{
    kernel_fd = open(filename, O_RDONLY);
    if (kernel_fd < 0) {
        return -1;
    }

    kernel_size = lseek(kernel_fd, 0, SEEK_END);

    kernel = mmap(NULL, kernel_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, kernel_fd, 0);
    if (kernel == MAP_FAILED) {
        close(kernel_fd);
        kernel_fd = -1;
        return -1;
    }

    kernel_base = get_base(kernel, kernel_size);
    return 0;
}

static void
term_kernel(void)
{
    munmap(kernel, kernel_size);
    close(kernel_fd);
}

/* trie **********************************************************************/

static int
PRINTEXP(uint64_t value, const char *symbol)
{
    int rv;
    sqlite3_stmt *stmt = g_stmt;
    //printf("INSERT INTO \"Symbols\" VALUES('%s',0x%llx);\n", symbol, value);
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

static uint64_t
read_uleb128(const uint8_t **q, const uint8_t *end)
{
    const uint8_t *p = *q;
    uint64_t result = 0;
    int bit = 0;
    do {
        uint64_t slice;

        if (p == end) {
            errx(1, "malformed uleb128 extends beyond trie");
        }

        slice = *p & 0x7f;

        if (bit >= 64 || slice << bit >> bit != slice) {
            errx(1, "uleb128 too big for 64-bits");
        } else {
            result |= (slice << bit);
            bit += 7;
        }
    } while (*p++ & 0x80);
    *q = p;
    return result;
}

static void
processExportNode(const uint8_t *const start, const uint8_t *p, const uint8_t* const end, char *cummulativeString, int curStrOffset, uint64_t base)
{
    if (p >= end) {
        errx(1, "malformed trie, node past end");
    }
    const uint8_t terminalSize = read_uleb128(&p, end);
    const uint8_t *children = p + terminalSize;
    if (terminalSize != 0) {
        /*uintptr_t nodeOffset = p - start;*/
        const char *name = strdup(cummulativeString);
        uint64_t address;
        uint64_t flags = read_uleb128(&p, end);
        uint64_t other;
        const char *importName;

        if (flags & EXPORT_SYMBOL_FLAGS_REEXPORT) {
            address = 0;
            other = read_uleb128(&p, end);
            importName = (char*)p;
//printf("[%s] -> [%s]%d\n", name, importName, other);
        } else {
            address = read_uleb128(&p, end); 
            if (flags & EXPORT_SYMBOL_FLAGS_STUB_AND_RESOLVER) {
                other = read_uleb128(&p, end);
            } else {
                other = 0;
            }
            importName = NULL;
        }
        PRINTEXP(address + base, name);
        free((char *)name);
    }

    const uint8_t childrenCount = *children++;
    const uint8_t *s = children;
    uint8_t i;
    for (i = 0; i < childrenCount; ++i) {
        int edgeStrLen = 0;
        while (*s != '\0') {
            cummulativeString[curStrOffset + edgeStrLen] = *s++;
            ++edgeStrLen;
        }
        cummulativeString[curStrOffset + edgeStrLen] = *s++;
        uint32_t childNodeOffset = read_uleb128(&s, end);
        if (childNodeOffset == 0) {
            errx(1, "malformed trie, childNodeOffset==0");
        }
        processExportNode(start, start + childNodeOffset, end, cummulativeString, curStrOffset + edgeStrLen, base);
    }
}

static void
do_export(const unsigned char *p, off_t sz, uint32_t export_off, uint32_t export_size, uint64_t base)
{
    const unsigned char *q = p + export_off;
    const unsigned char *end = q + export_size;
    char *cummulativeString;
    if (q == end) {
        return;
    }
    cummulativeString = malloc(end - q);
    if (!cummulativeString) {
        errx(1, "out of memory");
    }
    processExportNode(q, q, end, cummulativeString, 0, base);
    free(cummulativeString);
    (void)sz;
}

static int
show_exports(const uint8_t *buf, size_t size, int thumbize)
{
    uint32_t i;
    const uint8_t *p, *q;
    const struct mach_header *hdr;
    const struct dyld_info_command *kdic = NULL;
    const struct symtab_command *ksym = NULL;
    uint64_t base = 0;
    int is64;

    p = buf;
    hdr = (struct mach_header *)p;
    q = p + sizeof(struct mach_header);
    is64 = 0;

    if ((p[0] & 0xFE) != 0xCE && p[1] != 0xFA && p[2] != 0xED && p[3] != 0xFE) {
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
            if (!strcmp(seg->segname, "__TEXT")) {
                base = seg->vmaddr;
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__TEXT")) {
                base = seg->vmaddr;
            }
        }
        if (cmd->cmd == LC_SYMTAB) {
            const struct symtab_command *sym = (struct symtab_command *)q;
            ksym = sym;
        }
        if (cmd->cmd == LC_DYLD_INFO_ONLY) {
            const struct dyld_info_command *dic = (struct dyld_info_command *)q;
            kdic = dic;
        }
        q = q + cmd->cmdsize;
    }

    if (kdic) {
        do_export(buf, size, kdic->export_off, kdic->export_size, base);
    }

    if (ksym) {
        uint32_t k;
        const char *stroff = (const char *)p + ksym->stroff;
        if (is64) {
            const struct nlist_64 *s = (struct nlist_64 *)(p + ksym->symoff);
            for (k = 0; k < ksym->nsyms; k++) {
                if (s[k].n_type & N_STAB) {
                    continue;
                }
                if (s[k].n_value && (s[k].n_type & N_TYPE) != N_INDR) {
                    PRINTEXP(s[k].n_value, stroff + s[k].n_un.n_strx);
                }
            }
        } else {
            const struct nlist *s = (struct nlist *)(p + ksym->symoff);
            for (k = 0; k < ksym->nsyms; k++) {
                if (s[k].n_type & N_STAB) {
                    continue;
                }
                if (s[k].n_value && (s[k].n_type & N_TYPE) != N_INDR) {
                    uint64_t thumb = thumbize && (s[k].n_desc & N_ARM_THUMB_DEF);
                    PRINTEXP(s[k].n_value + thumb, stroff + s[k].n_un.n_strx);
                }
            }
        }
    }

    return 0;
}

/* bind vm *******************************************************************/

static void
PRINTIMP(uint64_t addr, const char *symbol)
{
    uint64_t special = 0xdeadbea1deadbea1;
    if (!strcmp(symbol, "__ZTVN10__cxxabiv117__class_type_infoE") ||
        !strcmp(symbol, "__ZTVN10__cxxabiv120__si_class_type_infoE") ||
        !strcmp(symbol, "__ZTVN10__cxxabiv121__vmi_class_type_infoE")) {
        special = 0xbea1deadbea1dead;
    }
    if (IS64(kernel)) {
        *(uint64_t *)(kernel + addr - kernel_base) = special;
    } else {
        *(uint32_t *)(kernel + addr - kernel_base) = special;
    }
}

static int
bindAt(void *context, uint64_t addr, uint8_t type, const char* symbolName, uint8_t symbolFlags, int64_t addend, long libraryOrdinal)
{
    (void)(context && addr && type && symbolName && symbolFlags && addend && libraryOrdinal);
    PRINTIMP(addr, symbolName);
    return 0;
}

static int64_t
read_sleb128(const uint8_t **q, const uint8_t *end)
{
    const uint8_t *p = *q;
    int64_t result = 0;
    int bit = 0;
    uint8_t byte;
    do {
        if (p == end) {
            errx(1, "malformed sleb128");
        }
        byte = *p++;
        result |= ((int64_t)(byte & 0x7f)) << bit;
        bit += 7;
    } while (byte & 0x80);
    if (byte & 0x40) {
        result |= (-1LL) << bit;
    }
    *q = p;
    return result;
}

#define segActualLoadAddress(i) segments[(i) * 2]
#define segActualEndAddress(i) segments[(i) * 2 + 1]

static void
do_import(const uint8_t *buf, uint32_t bind_off, uint32_t bind_size, const uint64_t *segments, int n, int sizeof_intptr_t, int lazy)
{
	uint32_t i;
	uint8_t type = lazy;
	int segmentIndex = 0;
	uint64_t address = segActualLoadAddress(0);
	uint64_t segmentEndAddress = segActualEndAddress(0);
	const char* symbolName = NULL;
	uint8_t symboFlags = 0;
	long libraryOrdinal = 0;
	int64_t addend = 0;
	uint64_t count;
	uint64_t skip;
	const uint8_t* const start = buf + bind_off;
	const uint8_t* const end = &start[bind_size];
	const uint8_t* p = start;
	int done = 0;
	while ( !done && (p < end) ) {
		uint8_t immediate = *p & BIND_IMMEDIATE_MASK;
		uint8_t opcode = *p & BIND_OPCODE_MASK;
		++p;
		switch (opcode) {
			case BIND_OPCODE_DONE:
				if (!lazy) done = 1;
				break;
			case BIND_OPCODE_SET_DYLIB_ORDINAL_IMM:
				libraryOrdinal = immediate;
				break;
			case BIND_OPCODE_SET_DYLIB_ORDINAL_ULEB:
				libraryOrdinal = read_uleb128(&p, end);
				break;
			case BIND_OPCODE_SET_DYLIB_SPECIAL_IMM:
				// the special ordinals are negative numbers
				if ( immediate == 0 )
					libraryOrdinal = 0;
				else {
					int8_t signExtended = BIND_OPCODE_MASK | immediate;
					libraryOrdinal = signExtended;
				}
				break;
			case BIND_OPCODE_SET_SYMBOL_TRAILING_FLAGS_IMM:
				symbolName = (char*)p;
				symboFlags = immediate;
				while (*p != '\0')
					++p;
				++p;
				break;
			case BIND_OPCODE_SET_TYPE_IMM:
				type = immediate;
				break;
			case BIND_OPCODE_SET_ADDEND_SLEB:
				addend = read_sleb128(&p, end);
				break;
			case BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB:
				segmentIndex = immediate;
				if ( segmentIndex > n )
					errx(1, "BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB has segment %d which is too large (%d)\n", 
							segmentIndex, n);
				address = segActualLoadAddress(segmentIndex) + read_uleb128(&p, end);
				segmentEndAddress = segActualEndAddress(segmentIndex);
				break;
			case BIND_OPCODE_ADD_ADDR_ULEB:
				address += read_uleb128(&p, end);
				break;
			case BIND_OPCODE_DO_BIND:
				if ( address >= segmentEndAddress ) 
					errx(1, "throwBadBindingAddress(0x%llx, 0x%llx, %d, %p, %p, %p);", address, segmentEndAddress, segmentIndex, start, end, p);
				bindAt(NULL, address, type, symbolName, symboFlags, addend, libraryOrdinal);
				address += sizeof_intptr_t;
				break;
			case BIND_OPCODE_DO_BIND_ADD_ADDR_ULEB:
				if ( address >= segmentEndAddress ) 
					errx(1, "throwBadBindingAddress(0x%llx, 0x%llx, %d, %p, %p, %p);", address, segmentEndAddress, segmentIndex, start, end, p);
				bindAt(NULL, address, type, symbolName, symboFlags, addend, libraryOrdinal);
				address += read_uleb128(&p, end) + sizeof_intptr_t;
				break;
			case BIND_OPCODE_DO_BIND_ADD_ADDR_IMM_SCALED:
				if ( address >= segmentEndAddress ) 
					errx(1, "throwBadBindingAddress(0x%llx, 0x%llx, %d, %p, %p, %p);", address, segmentEndAddress, segmentIndex, start, end, p);
				bindAt(NULL, address, type, symbolName, symboFlags, addend, libraryOrdinal);
				address += immediate*sizeof_intptr_t + sizeof_intptr_t;
				break;
			case BIND_OPCODE_DO_BIND_ULEB_TIMES_SKIPPING_ULEB:
				count = read_uleb128(&p, end);
				skip = read_uleb128(&p, end);
				for (i=0; i < count; ++i) {
					if ( address >= segmentEndAddress ) 
						errx(1, "throwBadBindingAddress(0x%llx, 0x%llx, %d, %p, %p, %p);", address, segmentEndAddress, segmentIndex, start, end, p);
					bindAt(NULL, address, type, symbolName, symboFlags, addend, libraryOrdinal);
					address += skip + sizeof_intptr_t;
				}
				break;
			default:
				errx(1, "bad bind opcode %d in bind info", *p);
		}
	}
}

#undef segActualEndAddress
#undef segActualLoadAddress

static int
show_imports(uint8_t *buf, size_t size)
{
    unsigned i, k;
    const struct mach_header *hdr = (struct mach_header *)buf;
    const uint8_t *q = buf + sizeof(struct mach_header);
    const struct dyld_info_command *kdic = NULL;
    const struct symtab_command *ksym = NULL;
    const struct dysymtab_command *kdys = NULL;
    uint64_t *segments;
    uint64_t base = 0;
    int is64 = 0;
    int n = 0;

    (void)size;

    if ((buf[0] & 0xFE) != 0xCE && buf[1] != 0xFA && buf[2] != 0xED && buf[3] != 0xFE) {
        return -1;
    }

    if (IS64(buf)) {
        is64 = 4;
    }
    q += is64;

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, "__TEXT")) {
                base = seg->vmaddr;
            }
            n++;
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__TEXT")) {
                base = seg->vmaddr;
            }
            n++;
        }
        if (cmd->cmd == LC_DYLD_INFO_ONLY) {
            const struct dyld_info_command *dic = (struct dyld_info_command *)q;
            kdic = dic;
        }
        if (cmd->cmd == LC_SYMTAB) {
            const struct symtab_command *sym = (struct symtab_command *)q;
            ksym = sym;
        }
        if (cmd->cmd == LC_DYSYMTAB) {
            const struct dysymtab_command *dys = (struct dysymtab_command *)q;
            kdys = dys;
        }
        q = q + cmd->cmdsize;
    }

    if (!kdic) {
        if (kdys && kdys->extreloff && ksym->symoff) {
            const struct relocation_info *r = (struct relocation_info *)(buf + kdys->extreloff);
            if (is64) {
                const struct nlist_64 *s = (struct nlist_64 *)(buf + ksym->symoff);
                for (k = 0; k < kdys->nextrel; k++, r++) {
                    assert(!r->r_pcrel && r->r_length == 3 && r->r_extern && r->r_type == GENERIC_RELOC_VANILLA);
                    PRINTIMP(base + r->r_address, (char *)buf + ksym->stroff + s[r->r_symbolnum].n_un.n_strx);
                }
            } else {
                const struct nlist *s = (struct nlist *)(buf + ksym->symoff);
                for (k = 0; k < kdys->nextrel; k++, r++) {
                    assert(!r->r_pcrel && r->r_length == 2 && r->r_extern && r->r_type == GENERIC_RELOC_VANILLA);
                    PRINTIMP(base + r->r_address, (char *)buf + ksym->stroff + s[r->r_symbolnum].n_un.n_strx);
                }
            }
        }
        return 0;
    }

    segments = malloc(2 * sizeof(uint64_t) * n);
    if (!segments) {
        return -1;
    }

    n = 0;
    q = buf + sizeof(struct mach_header) + is64;

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            segments[n * 2 + 0] = seg->vmaddr;
            segments[n * 2 + 1] = seg->vmaddr + seg->vmsize;
            n++;
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            segments[n * 2 + 0] = seg->vmaddr;
            segments[n * 2 + 1] = seg->vmaddr + seg->vmsize;
            n++;
        }
        q = q + cmd->cmdsize;
    }

    do_import(buf, kdic->bind_off, kdic->bind_size, segments, n, is64 ? 8 : 4, 0);
    do_import(buf, kdic->lazy_bind_off, kdic->lazy_bind_size, segments, n, is64 ? 8 : 4, BIND_TYPE_POINTER);

    free(segments);
    return 0;
}

/* processor *****************************************************************/

static sqlite3 *
make_core_db(const char *other)
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

    if (other) {
        char sql[4096];
        snprintf(sql, sizeof(sql), "ATTACH DATABASE '%s' AS other;", other);
        //printf("%s\n", sql);
        rv = sqlite3_exec(db, sql, NULL, NULL, &str);
        if (rv) {
            fprintf(stderr, "sqlite error: %s\n", str);
            sqlite3_free(str);
            sqlite3_close(db);
            return NULL;
        }
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

    g_stmt = stmt;
    show_exports(kernel, kernel_size, 1);
    g_stmt = NULL;

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
kdb_get_addrsym(sqlite3 *db, const char *table, addr_t addr)
{
    int rv;
    char sql[4096];
    int err = 0;
    int row = 0;

    sqlite3_stmt *stmt;
    char *x = NULL;

    snprintf(sql, sizeof(sql), "SELECT Symbol FROM %s WHERE Value IS %lld", table, addr);
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

#define OK(c) (isalnum(c) || (c) == '_' || (c) == '$')

static int
is_typeinfo(addr_t found)
{
    if (IS64(kernel)) {
        return ((uint64_t *)(kernel + found))[-1] == 0xbea1deadbea1dead;
    } else {
        return ((uint32_t *)(kernel + found))[-1] == 0xbea1dead;
    }
}

static addr_t
get_dref(addr_t what, size_t secs[][2], unsigned n, int vtable)
{
    size_t j;
    if (IS64(kernel)) {
        while (n--) {
            size_t ptr = (*secs)[0];
            size_t len = (*secs)[1];
            for (j = 0; j + 7 < len; j += 8) {
                if (what == *(uint64_t *)(kernel + ptr + j) && (!vtable || ((uint64_t *)(kernel + ptr + j))[-1] == 0)) {
                    return ptr + j;
                }
            }
            secs++;
        }
    } else {
        while (n--) {
            size_t ptr = (*secs)[0];
            size_t len = (*secs)[1];
            for (j = 0; j + 3 < len; j += 4) {
                if (what == *(uint32_t *)(kernel + ptr + j) && (!vtable || ((uint32_t *)(kernel + ptr + j))[-1] == 0)) {
                    return ptr + j;
                }
            }
            secs++;
        }
    }
    return 0;
}

static int
parse_macho(sqlite3 *db)
{
    size_t sizeof_tconst;
    addr_t tconst, lo, hi;
    size_t i, last = 0;
    addr_t wsize;

    size_t secs[3][2];

    addr_t base = get_base(kernel, kernel_size);
    assert(base != -1U);

    if (*(uint32_t *)(kernel + 12) != MH_EXECUTE &&
        *(uint32_t *)(kernel + 12) != MH_DYLIB) {
        return -1;
    }

    tconst = get_sect_data(kernel, kernel_size, "__TEXT", "__const", &sizeof_tconst);

    secs[0][0] = get_sect_data(kernel, kernel_size, "__DATA_CONST", "__const", &secs[0][1]);
    secs[1][0] = get_sect_data(kernel, kernel_size, "__DATA",       "__const", &secs[1][1]);
    secs[2][0] = get_sect_data(kernel, kernel_size, "__DATA",       "__data",  &secs[2][1]);

    lo = get_range(kernel, kernel_size, &hi);
    assert(lo < hi);

    if (IS64(kernel)) {
        wsize = sizeof(uint64_t);
    } else {
        wsize = sizeof(uint32_t);
    }

    do {
        for (i = last; i < sizeof_tconst && OK(kernel[tconst + i]); i++) {
        }
        if (i - last >= 3 && kernel[tconst + i] == '\0') {
            addr_t found = get_dref(base + tconst + last, secs, sizeof(secs) / sizeof(secs[0]), 0);
            if (found && is_typeinfo(found)) {
                addr_t vtab;
                found -= wsize;
                if (!for_sqlite) {
                    if (for_ida) {
                        printf("\tMakeName(0x%llx, \"__ZTS%s\");\n", base + tconst + last, kernel + tconst + last);
                        printf("\tMakeName(0x%llx, \"__ZTI%s\");\n", base + found, kernel + tconst + last);
                    } else {
                        printf("0x%llx: __ZTS%s\n", base + tconst + last, kernel + tconst + last);
                        printf("\t0x%llx: __ZTI%s\n", base + found, kernel + tconst + last);
                    }
                }
                vtab = get_dref(base + found, secs, sizeof(secs) / sizeof(secs[0]), 1);
                if (vtab) {
                    size_t j;
                    if (for_sqlite) {
                        printf("CREATE TABLE __ZTV%s(Symbol varchar(4096), Value int);\n", kernel + tconst + last);
                    } else if (for_ida) {
                        printf("\tMakeName(0x%llx, \"__ZTV%s\");\n", base + vtab - wsize, kernel + tconst + last);
                    } else {
                        printf("\t0x%llx: __ZTV%s\n", base + vtab - wsize, kernel + tconst + last);
                    }
                    for (j = vtab + wsize; ; j += wsize) {
                        addr_t ptr;
                        char *sym;
                        if (vtab < found && j == found) {
                            break;
                        }
                        // XXX the stop heuristic sucks. really! I should properly handle multiple inheritance
                        if (IS64(kernel)) {
                            ptr = *(uint64_t *)(kernel + j);
                            if ((ptr & 0xFFFFFFFFFFFF0000) == 0xFFFFFFFFFFFF0000 || ptr == 0xdeadbea1deadbea1) {
                                continue;
                            }
                        } else {
                            ptr = *(uint32_t *)(kernel + j);
                            if ((ptr & 0xFFFF0000) == 0xFFFF0000 || ptr == 0xdeadbea1) {
                                continue;
                            }
                        }
                        if (ptr < lo || ptr >= hi) {
                            break;
                        }
                        // XXX all pointers, except imports and typeinfo must be in code section
                        sym = kdb_get_addrsym(db, "Symbols", ptr);
                        if (!sym) {
                            char tmp[4096];
                            snprintf(tmp, sizeof(tmp), "other.__ZTV%s", kernel + tconst + last);
                            sym = kdb_get_addrsym(db, tmp, (j - vtab) / wsize + 1);
                        }
                        if (!sym) {
                            if (!for_sqlite && !for_ida) {
                                printf("\t\t%llu: sub_%llx\n", (j - vtab) / wsize + 1, ptr);
                            }
                        } else {
                            if (for_sqlite) {
                                printf("INSERT INTO \"__ZTV%s\" VALUES('%s',%llu);\n", kernel + tconst + last, sym, (j - vtab) / wsize + 1);
                            } else if (for_ida) {
                                printf("\tMakeName(0x%llx, \"%s\");\n", ptr, sym);
                            } else {
                                printf("\t\t%llu: %s\n", (j - vtab) / wsize + 1, sym);
                            }
                            free(sym);
                        }
                    }
                    if (for_ida) {
                        printf("\n");
                    }
                }
                last = ((i + 1) + 3) & ~3;
                continue;
            }
        }
        last += 4;
    } while (last < sizeof_tconst);

    return 0;
}

int
main(int argc, char **argv)
{
    int rv;
    sqlite3 *db;
    const char *krnl = NULL;
    const char *other = NULL;

    while (--argc > 0) {
        const char *p = *++argv;
        if (!strcmp(p, "-i")) {
            for_ida = 1;
            continue;
        }
        if (!strcmp(p, "-s")) {
            for_sqlite = 1;
            continue;
        }
        if (!strcmp(p, "-l")) {
            if (argc < 2) {
                fprintf(stderr, "argument to '%s' is missing\n", p);
                return 1;
            }
            argc--;
            other = *++argv;
            continue;
        }
        krnl = p;
    }

    if (!krnl) {
        fprintf(stderr, "usage: %s [options] executable\n", argv[0]);
        fprintf(stderr, "\t-i\toutput ida script\n");
        fprintf(stderr, "\t-s\toutput sqlite ini\n");
        fprintf(stderr, "\t-l db\tuse other database\n");
        return 1;
    }

    rv = init_kernel(krnl);
    if (rv) {
        fprintf(stderr, "[e] cannot read kernel\n");
        return -1;
    }
    show_imports(kernel, kernel_size);

    db = make_core_db(other);
    if (db) {
        if (for_ida) {
            printf("#include <idc.idc>\n");
            printf("\nstatic main(void)\n{\n");
        }
        parse_macho(db);
        if (for_ida) {
            printf("}\n");
        }
        sqlite3_close(db);
    }

    term_kernel();
    return 0;
}
