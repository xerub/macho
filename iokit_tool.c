/*
 *  ghetto iokit dumper (arm, mach-o kernel/kext)
 *
 *  Copyright (c) 2016 xerub
 */

#include <assert.h>
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

#define VPREFIX "vtable_"
#define OPREFIX ""
#define RETTYPE "void *"

typedef unsigned long long addr_t;

#define IS64(image) (*(uint8_t *)(image) & 1)

#define MACHO(p) ((*(unsigned int *)(p) & ~1) == 0xfeedface)

static int for_ida = 0;
static int one_kext = 0;
static size_t align = 0xFFF;

static __inline size_t
round_page(size_t size)
{
    return (size + align) & ~align;
}

/* demangler *****************************************************************/

extern char *__cxa_demangle(const char *mangled_name, char *output_buffer, size_t *length, int *status);
#define demangle_name(name) __cxa_demangle((name) + 1, NULL, NULL, NULL)

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

/* disassembler **************************************************************/

static int HighestSetBit(int N, uint32_t imm)
{
	int i;
	for (i = N - 1; i >= 0; i--) {
		if (imm & (1 << i)) {
			return i;
		}
	}
	return -1;
}

static uint64_t ZeroExtendOnes(unsigned M, unsigned N)	// zero extend M ones to N width
{
	(void)N;
	return ((uint64_t)1 << M) - 1;
}

static uint64_t RORZeroExtendOnes(unsigned M, unsigned N, unsigned R)
{
	uint64_t val = ZeroExtendOnes(M, N);
	if (R == 0) {
		return val;
	}
	return ((val >> R) & (((uint64_t)1 << (N - R)) - 1)) | ((val & (((uint64_t)1 << R) - 1)) << (N - R));
}

static uint64_t Replicate(uint64_t val, unsigned bits)
{
	uint64_t ret = val;
	unsigned shift;
	for (shift = bits; shift < 64; shift += bits) {	// XXX actually, it is either 32 or 64
		ret |= (val << shift);
	}
	return ret;
}

static int DecodeBitMasks(unsigned immN, unsigned imms, unsigned immr, int immediate, uint64_t *newval)
{
	unsigned levels, S, R, esize;
	int len = HighestSetBit(7, (immN << 6) | (~imms & 0x3F));
	if (len < 1) {
		return -1;
	}
	levels = ZeroExtendOnes(len, 6);
	if (immediate && (imms & levels) == levels) {
		return -1;
	}
	S = imms & levels;
	R = immr & levels;
	esize = 1 << len;
	*newval = Replicate(RORZeroExtendOnes(S + 1, esize, R), esize);
	return 0;
}

static int DecodeMov(uint32_t opcode, uint64_t total, int first, uint64_t *newval)
{
	unsigned o = (opcode >> 29) & 3;
	unsigned k = (opcode >> 23) & 0x3F;
	unsigned rn, rd;
	uint64_t i;

	if (k == 0x24 && o == 1) {			// MOV (bitmask imm) <=> ORR (immediate)
		unsigned s = (opcode >> 31) & 1;
		unsigned N = (opcode >> 22) & 1;
		if (s == 0 && N != 0) {
			return -1;
		}
		rn = (opcode >> 5) & 0x1F;
		if (rn == 31) {
			unsigned imms = (opcode >> 10) & 0x3F;
			unsigned immr = (opcode >> 16) & 0x3F;
			return DecodeBitMasks(N, imms, immr, 1, newval);
		}
	} else if (k == 0x25) {				// MOVN/MOVZ/MOVK
		unsigned s = (opcode >> 31) & 1;
		unsigned h = (opcode >> 21) & 3;
		if (s == 0 && h > 1) {
			return -1;
		}
		i = (opcode >> 5) & 0xFFFF;
		h *= 16;
		i <<= h;
		if (o == 0) {				// MOVN
			*newval = ~i;
			return 0;
		} else if (o == 2) {			// MOVZ
			*newval = i;
			return 0;
		} else if (o == 3 && !first) {		// MOVK
			*newval = (total & ~((uint64_t)0xFFFF << h)) | i;
			return 0;
		}
	} else if ((k | 1) == 0x23 && !first) {		// ADD (immediate)
		unsigned h = (opcode >> 22) & 3;
		if (h > 1) {
			return -1;
		}
		rd = opcode & 0x1F;
		rn = (opcode >> 5) & 0x1F;
		if (rd != rn) {
			return -1;
		}
		i = (opcode >> 10) & 0xFFF;
		h *= 12;
		i <<= h;
		if (o & 2) {				// SUB
			*newval = total - i;
			return 0;
		} else {				// ADD
			*newval = total + i;
			return 0;
		}
	}

	return -1;
}

/* patchfinder ***************************************************************/

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#define static /* pragma ignored "-Wunused-function" is broken on some gcc */
#define memmem(a, b, c, d) (void *)boyermoore_horspool_memmem((const uint8_t *)(a), b, (const uint8_t *)(c), d)
#include "patchfinder.c"
#undef static
#pragma GCC diagnostic pop

static addr_t
step_thumb(const uint8_t *buf, addr_t start, size_t length, uint32_t what, uint32_t mask)
{
    addr_t end = start + length;
    while (start < end) {
        uint32_t x = *(uint32_t *)(buf + start);
        if ((x & mask) == what) {
            return start;
        }
        start += insn_is_32bit((uint16_t *)(buf + start)) ? 4 : 2;
    }
    return 0;
}

static addr_t
calc32(const uint8_t *buf, addr_t start, addr_t end, int r)
{
    addr_t i;
    uint32_t value[16];

    memset(value, 0, sizeof(value));

    end &= ~1;
    for (i = start & ~1; i < end; ) {
        uint16_t *current_instruction = (uint16_t *)(buf + i);
        if (insn_is_mov_imm(current_instruction)) {
            value[insn_mov_imm_rd(current_instruction)] = insn_mov_imm_imm(current_instruction);
        } else if (insn_is_ldr_literal(current_instruction)) {
            addr_t literal_address = (i & ~3) + 4 + insn_ldr_literal_imm(current_instruction);
            value[insn_ldr_literal_rt(current_instruction)] = *(uint32_t *) (buf + literal_address);
        } else if (insn_is_movt(current_instruction)) {
            value[insn_movt_rd(current_instruction)] |= insn_movt_imm(current_instruction) << 16;
        } else if (insn_is_add_reg(current_instruction)) {
            int reg = insn_add_reg_rd(current_instruction);
            if (insn_add_reg_rm(current_instruction) == 15 && insn_add_reg_rn(current_instruction) == reg) {
                value[reg] += i + 4;
            }
        } else if (insn_is_add_reg_imm(current_instruction)) {
            value[insn_add_reg_imm_rd(current_instruction)] = value[insn_add_reg_imm_rn(current_instruction)] + insn_add_reg_imm_imm(current_instruction);
        } else if ((*current_instruction & 0xFF00) == 0x4600) {
            uint8_t regs = *current_instruction;
            int rn = (regs >> 3) & 15;
            int rd = (regs & 7) | ((regs & 0x80) >> 4);
            value[rd] = value[rn];
        }
        i += insn_is_32bit(current_instruction) ? 4 : 2;
    }
    return value[r];
}

static addr_t
calc32mov(const uint8_t *buf, addr_t start, addr_t end, int r)
{
    addr_t i;
    uint32_t value[16];

    memset(value, 0, sizeof(value));

    end &= ~1;
    for (i = start & ~1; i < end; ) {
        uint16_t *current_instruction = (uint16_t *)(buf + i);
        if (insn_is_mov_imm(current_instruction)) {
            value[insn_mov_imm_rd(current_instruction)] = insn_mov_imm_imm(current_instruction);
        } else if (insn_is_movt(current_instruction)) {
            value[insn_movt_rd(current_instruction)] |= insn_movt_imm(current_instruction) << 16;
        }
        i += insn_is_32bit(current_instruction) ? 4 : 2;
    }
    return value[r];
}

static addr_t
step_64(const uint8_t *buf, addr_t start, size_t length, uint32_t what, uint32_t mask)
{
    addr_t end = start + length;
    while (start < end) {
        uint32_t x = *(uint32_t *)(buf + start);
        if ((x & mask) == what) {
            return start;
        }
        start += 4;
    }
    return 0;
}

static addr_t
calc64(const uint8_t *buf, addr_t start, addr_t end, int r)
{
    addr_t i;
    uint64_t value[32];

    memset(value, 0, sizeof(value));

    end &= ~3;
    for (i = start & ~3; i < end; i += 4) {
        uint32_t op = *(uint32_t *)(buf + i);
        unsigned reg = op & 0x1F;
        if ((op & 0x9F000000) == 0x90000000) {
            signed adr = ((op & 0x60000000) >> 18) | ((op & 0xFFFFE0) << 8);
            //printf("%llx: ADRP X%d, 0x%llx\n", i, reg, ((long long)adr << 1) + (i & ~0xFFF));
            value[reg] = ((long long)adr << 1) + (i & ~0xFFF);
        } else if ((op & 0xFF000000) == 0x91000000) {
            unsigned rn = (op >> 5) & 0x1F;
            unsigned shift = (op >> 22) & 3;
            unsigned imm = (op >> 10) & 0xFFF;
            if (shift == 1) {
                imm <<= 12;
            } else {
                assert(shift == 0);
            }
            //printf("%llx: ADD X%d, X%d, 0x%x\n", i, reg, rn, imm);
            value[reg] = value[rn] + imm;
        } else if ((op & 0xF9C00000) == 0xF9400000) {
            unsigned rn = (op >> 5) & 0x1F;
            unsigned imm = ((op >> 10) & 0xFFF) << 3;
            //printf("%llx: LDR X%d, [X%d, 0x%x]\n", i, reg, rn, imm);
            value[reg] = value[rn] + imm;	// XXX address, not actual value
        } else if ((op & 0x9F000000) == 0x10000000) {
            signed adr = ((op & 0x60000000) >> 18) | ((op & 0xFFFFE0) << 8);
            //printf("%llx: ADR X%d, 0x%llx\n", i, reg, ((long long)adr >> 11) + i);
            value[reg] = ((long long)adr >> 11) + i;
        } else if ((op & 0xFF000000) == 0x58000000) {
            unsigned adr = (op & 0xFFFFE0) >> 3;
            //printf("%llx: LDR X%d, =0x%llx\n", i, reg, adr + i);
            value[reg] = adr + i;		// XXX address, not actual value
        }
    }
    return value[r];
}

static addr_t
calc64mov(const uint8_t *buf, addr_t start, addr_t end, int r)
{
    addr_t i;
    uint64_t value[32];

    memset(value, 0, sizeof(value));

    end &= ~3;
    for (i = start & ~3; i < end; i += 4) {
        uint32_t op = *(uint32_t *)(buf + i);
        unsigned reg = op & 0x1F;
        uint64_t newval;
        int rv = DecodeMov(op, value[reg], 0, &newval);
        if (rv == 0) {
            if (((op >> 31) & 1) == 0) {
                newval &= 0xFFFFFFFF;
            }
            value[reg] = newval;
        }
    }
    return value[r];
}

/* generic macho *************************************************************/

static addr_t
get_base(uint8_t *buf, size_t size)
{
    unsigned i;
    const struct mach_header *hdr = (struct mach_header *)buf;
    const uint8_t *q = buf + sizeof(struct mach_header);

    (void)size;

    if (!MACHO(buf)) {
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

static const char *
is_import(int32_t address)
{
    unsigned i, k;
    struct symtab_command *ksym = NULL;
    struct dysymtab_command *kdys = NULL;
    int is64 = 0;
    const struct mach_header *hdr;
    const uint8_t *q;

    if (!one_kext) {
        return NULL;
    }

    if (IS64(kernel)) {
        is64 = 4;
    }

    hdr = (struct mach_header *)kernel;
    q = kernel + sizeof(struct mach_header) + is64;

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SYMTAB) {
            struct symtab_command *sym = (struct symtab_command *)q;
            ksym = sym;
        }
        if (cmd->cmd == LC_DYSYMTAB) {
            struct dysymtab_command *dys = (struct dysymtab_command *)q;
            kdys = dys;
        }
        q = q + cmd->cmdsize;
    }

    if (kdys && kdys->extreloff && ksym->symoff) {
        const struct relocation_info *r = (struct relocation_info *)(kernel + kdys->extreloff);
        if (is64) {
            const struct nlist_64 *s = (struct nlist_64 *)(kernel + ksym->symoff);
            for (k = 0; k < kdys->nextrel; k++, r++) {
                assert(!r->r_pcrel && r->r_length == 3 && r->r_extern && r->r_type == GENERIC_RELOC_VANILLA);
                if (address == r->r_address) {
                    return (char *)kernel + ksym->stroff + s[r->r_symbolnum].n_un.n_strx;
                }
            }
        } else {
            const struct nlist *s = (struct nlist *)(kernel + ksym->symoff);
            for (k = 0; k < kdys->nextrel; k++, r++) {
                assert(!r->r_pcrel && r->r_length == 2 && r->r_extern && r->r_type == GENERIC_RELOC_VANILLA);
                if (address == r->r_address) {
                    return (char *)kernel + ksym->stroff + s[r->r_symbolnum].n_un.n_strx;
                }
            }
        }
    }

    return NULL;
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

static addr_t
kdb_get_symaddr(sqlite3 *db, const char *symbol)
{
    int rv;
    char sql[4096];
    int err = 0;
    int row = 0;

    sqlite3_stmt *stmt;
    sqlite3_int64 x = 0;

    snprintf(sql, sizeof(sql), "SELECT Value FROM Symbols WHERE Symbol IS '%s'", symbol);
    rv = sqlite3_prepare_v2(db, sql, strlen(sql) + 1, &stmt, NULL);
    if (rv) {
        return 0;
    }

    while (1) {
        rv = sqlite3_step(stmt);
        if (rv == SQLITE_ROW) {
            if (row) {
                err = 1;
                break;
            }
            x = sqlite3_column_int64(stmt, 0);
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
        return 0;
    }
    return x;
}

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

static void
process_table32(addr_t table, addr_t base, const char *name, unsigned sz, sqlite3 *db)
{
    unsigned i;
    addr_t sbase;
    addr_t start = table - 3 * sizeof(uint32_t);
    assert(((uint32_t *)(kernel + table))[-3] == 0);
    assert(((uint32_t *)(kernel + table))[-2] == 0);
    assert(((uint32_t *)(kernel + table))[-1] == 0);
    assert(((uint32_t *)(kernel + table))[0] != 0);
    while (((uint32_t *)(kernel + start))[-1] == 0 && !is_import(start - sizeof(uint32_t))) {
        start -= sizeof(uint32_t);
        table -= sizeof(uint32_t);
    }
    while (((uint32_t *)(kernel + start))[-1] || is_import(start - sizeof(uint32_t))) {
        start -= sizeof(uint32_t);
    }

    i = 0;
    sbase = start + base;
    if (for_ida > 0) {
        //i += 2;
        //sbase -= 2 * sizeof(uint32_t);
        printf("\tid = AddStrucEx(-1, \"" VPREFIX "%s\", 0);\n", name);
    } else if (for_ida < 0) {
        printf("struct %s {\n", name);
    } else {
        printf("%s.vtable=0x%llx (0x%llx)\n" "\t0\n\t0\n", name, start - 2 * sizeof(uint32_t), start - 2 * sizeof(uint32_t) + base);
    }
    while (start < table - 3 * sizeof(uint32_t)) {
        addr_t val = *(uint32_t *)(kernel + start);
        char *sym = kdb_get_addrsym(db, val);
        if (!sym) {
            const char *tmp = is_import(start);
            if (tmp) {
                sym = strdup(tmp);
            }
        }
        if (!sym) {
            char tmp[256];
            snprintf(tmp, sizeof(tmp), "sub_%08llx", val);
            sym = strdup(tmp);
        }
        if (for_ida > 0) {
            printf("\tmember(id, 0x%llx, \"%s\", %zu);\n", val, sym, i * sizeof(uint32_t));
            i++;
            //printf("Message(\"[%%s]\\n\", Demangle(\"%s\", 0));\n", sym);
        } else if (for_ida < 0) {
            char *paren, *dem = demangle_name(sym);
            assert(dem);
            paren = strchr(dem, '(');//)
            assert(paren);
            printf("\t" RETTYPE "(*%.*s)%s;\n", (int)(paren - dem), dem, paren);
            free(dem);
        } else {
            printf("\t%s\n", sym);
        }
        free(sym);
        start += sizeof(uint32_t);
    }

    if (for_ida > 0) {
        printf("\tMakeStruct(0x%llx, \"" VPREFIX "%s\");\n", sbase, name);

        printf("\tid = AddStrucEx(-1, \"" OPREFIX "%s\", 0);\n", name);
        printf("\tAddStrucMember(id, \"%s\", %u, 0x25500400, 0XFFFFFFFF, %zu, 0XFFFFFFFF, 0, 0x000002);\n", "vtable", 0, sizeof(uint32_t));
        printf("\tSetType(GetMemberId(id, %u), \"" VPREFIX "%s *\");\n", 0, name);
        if (sz > sizeof(uint32_t)) {
            sz -= sizeof(uint32_t);
            if (sz > 1) {
                printf("\tAddStrucMember(id, \"field_%zX\", %#zX, 0x000400, -1, %u);\n", sizeof(uint32_t), sizeof(uint32_t), sz - 1);
            }
            sz += sizeof(uint32_t) - 1;
            printf("\tAddStrucMember(id, \"field_%X\", %#X, 0x000400, -1, 1);\n", sz, sz);
        }
    } else if (for_ida < 0) {
        printf("};\n");
    }
}

static void
process_table64(addr_t table, addr_t base, const char *name, unsigned sz, sqlite3 *db)
{
    unsigned i;
    addr_t sbase;
    addr_t start = table - 3 * sizeof(uint64_t);
    assert(((uint64_t *)(kernel + table))[-3] == 0);
    assert(((uint64_t *)(kernel + table))[-2] == 0);
    assert(((uint64_t *)(kernel + table))[-1] == 0);
    assert(((uint64_t *)(kernel + table))[0] != 0);
    while (((uint64_t *)(kernel + start))[-1] == 0 && !is_import(start - sizeof(uint64_t))) {
        start -= sizeof(uint64_t);
        table -= sizeof(uint64_t);
    }
    while (((uint64_t *)(kernel + start))[-1] || is_import(start - sizeof(uint64_t))) {
        start -= sizeof(uint64_t);
    }

    i = 0;
    sbase = start + base;
    if (for_ida > 0) {
        //i += 2;
        //sbase -= 2 * sizeof(uint64_t);
        printf("\tid = AddStrucEx(-1, \"" VPREFIX "%s\", 0);\n", name);
    } else if (for_ida < 0) {
        printf("struct %s {\n", name);
    } else {
        printf("%s.vtable=0x%llx (0x%llx)\n" "\t0\n\t0\n", name, start - 2 * sizeof(uint64_t), start - 2 * sizeof(uint64_t) + base);
    }
    while (start < table - 3 * sizeof(uint64_t)) {
        addr_t val = *(uint64_t *)(kernel + start);
        char *sym = kdb_get_addrsym(db, val);
        if (!sym) {
            const char *tmp = is_import(start);
            if (tmp) {
                sym = strdup(tmp);
            }
        }
        if (!sym) {
            char tmp[256];
            snprintf(tmp, sizeof(tmp), "sub_%08llx", val);
            sym = strdup(tmp);
        }
        if (for_ida > 0) {
            printf("\tmember(id, 0x%llx, \"%s\", %zu);\n", val, sym, i * sizeof(uint64_t));
            i++;
            //printf("Message(\"[%%s]\\n\", Demangle(\"%s\", 0));\n", sym);
        } else if (for_ida < 0) {
            char *paren, *dem = demangle_name(sym);
			if (!dem) {
				//printf("\nProblem SYMBOL!!: -  %s\n",sym);
				dem = sym;
				 printf("\t" RETTYPE "(*%s)();\n", dem);
			}
			else {
            assert(dem);
            paren = strchr(dem, '(');//)
            assert(paren);
            printf("\t" RETTYPE "(*%.*s)%s;\n", (int)(paren - dem), dem, paren);
            free(dem);
			}
        } else {
            printf("\t%s\n", sym);
        }
        free(sym);
        start += sizeof(uint64_t);
    }

    if (for_ida > 0) {
        printf("\tMakeStruct(0x%llx, \"" VPREFIX "%s\");\n", sbase, name);

        printf("\tid = AddStrucEx(-1, \"" OPREFIX "%s\", 0);\n", name);
        printf("\tAddStrucMember(id, \"%s\", %u, 0x35500400, 0XFFFFFFFFFFFFFFFF, %zu, 0XFFFFFFFFFFFFFFFF, 0, 0x000009);\n", "vtable", 0, sizeof(uint64_t));
        printf("\tSetType(GetMemberId(id, %u), \"" VPREFIX "%s *\");\n", 0, name);
        if (sz > sizeof(uint64_t)) {
            sz -= sizeof(uint64_t);
            if (sz > 1) {
                printf("\tAddStrucMember(id, \"field_%zX\", %#zX, 0x000400, -1, %u);\n", sizeof(uint64_t), sizeof(uint64_t), sz - 1);
            }
            sz += sizeof(uint64_t) - 1;
            printf("\tAddStrucMember(id, \"field_%X\", %#X, 0x000400, -1, 1);\n", sz, sz);
        }
    } else if (for_ida < 0) {
        printf("};\n");
    }
}

static void
parse_one(size_t offset, addr_t base, sqlite3 *db)
{
    addr_t symval = kdb_get_symaddr(db, "__ZN11OSMetaClassC2EPKcPKS_j");
    addr_t __ZN11OSMetaClassC2EPKcPKS_j = 0;
    addr_t stub__ZN11OSMetaClassC2EPKcPKS_j = 0;
    size_t i, size;
    // 1. get __ZN11OSMetaClassC2EPKcPKS_j import site
    addr_t addr = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__nl_symbol_ptr", &size);
    if (!addr) {
        addr = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__got", &size);
    }
    if (addr && size) {
        addr += offset;
        if (IS64(kernel)) {
            const uint64_t *ptr = (uint64_t *)(kernel + addr);
            size /= sizeof(uint64_t);
            for (i = 0; i < size; i++) {
                if (!symval) {
                    const char *impsym = is_import(addr + i * sizeof(uint64_t));
                    if (impsym && !strcmp(impsym, "__ZN11OSMetaClassC2EPKcPKS_j")) {
                        __ZN11OSMetaClassC2EPKcPKS_j = addr + i * sizeof(uint64_t);
                        break;
                    }
                } else if (ptr[i] == symval) {
                    __ZN11OSMetaClassC2EPKcPKS_j = addr + i * sizeof(uint64_t);
                    break;
                }
            }
        } else {
            const uint32_t *ptr = (uint32_t *)(kernel + addr);
            size /= sizeof(uint32_t);
            for (i = 0; i < size; i++) {
                if (!symval) {
                    const char *impsym = is_import(addr + i * sizeof(uint32_t));
                    if (impsym && !strcmp(impsym, "__ZN11OSMetaClassC2EPKcPKS_j")) {
                        __ZN11OSMetaClassC2EPKcPKS_j = addr + i * sizeof(uint32_t);
                        break;
                    }
                } else if (ptr[i] == symval) {
                    __ZN11OSMetaClassC2EPKcPKS_j = addr + i * sizeof(uint32_t);
                    break;
                }
            }
        }
    }
    // 2. get __ZN11OSMetaClassC2EPKcPKS_j stub
    if (__ZN11OSMetaClassC2EPKcPKS_j) {
        addr = get_sect_data(kernel + offset, kernel_size - offset, "__TEXT", "__stub", &size);
        if (!addr) {
            addr = get_sect_data(kernel + offset, kernel_size - offset, "__TEXT", "__stubs", &size);
        }
        if (addr && size) {
            addr += offset;
            if (IS64(kernel)) {
                while (size >= 0xc) {
                    addr_t value = calc64(kernel, addr, addr + 0xc, 16);
                    if (value == __ZN11OSMetaClassC2EPKcPKS_j) {
                        stub__ZN11OSMetaClassC2EPKcPKS_j = addr;
                        break;
                    }
                    addr += 0xc;
                    size -= 0xc;
                }
            } else {
                while (size >= 0x10) {
                    addr_t value = calc32(kernel, addr, addr + 0x10, 12);
                    if (value == __ZN11OSMetaClassC2EPKcPKS_j) {
                        stub__ZN11OSMetaClassC2EPKcPKS_j = addr;
                        break;
                    }
                    addr += 0x10;
                    size -= 0x10;
                }
            }
        }
    }
    // 3. parse constructors
    if (one_kext && !stub__ZN11OSMetaClassC2EPKcPKS_j) {
        stub__ZN11OSMetaClassC2EPKcPKS_j = kdb_get_symaddr(db, "__ZN11OSMetaClassC2EPKcPKS_j.stub");
    }
    if (stub__ZN11OSMetaClassC2EPKcPKS_j) {
        base -= offset;
        addr = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__mod_init_func", &size);
        if (!addr) {
            addr = get_sect_data(kernel + offset, kernel_size - offset, "__DATA", "__constructor", &size);
        }
        if (addr && size) {
            addr += offset;
            if (IS64(kernel)) {
                const uint64_t *ptr = (uint64_t *)(kernel + addr);
                size /= sizeof(uint64_t);
                // 4. inside each constructor function find __ZN11OSMetaClassC2EPKcPKS_j.stub(..., name, ...); ... *ptr = table;
                for (i = 0; i < size; i++) {
                    addr_t ctor = ptr[i] - base;
                    addr_t ret = step_64(kernel, ctor, 0x1200, 0xd65f03c0, 0xFFFFFFFF);
                    if (ret) {
                        addr_t scan = ctor;
                        for (;;) {
                            unsigned reg;
                            addr_t call, name, stor, table;
                            long long w;
                            // 4.1 find __ZN11OSMetaClassC2EPKcPKS_j.stub(..., name, ...);
                            call = step_64(kernel, scan, ret - scan, 0x94000000, 0xFC000000);
                            if (!call) {
                                break;
                            }
                            w = *(uint32_t *)(kernel + call) & 0x3FFFFFF;
                            w <<= 64 - 26;
                            w >>= 64 - 26 - 2;
                            if (stub__ZN11OSMetaClassC2EPKcPKS_j == call + w) {
                                unsigned sz = calc64mov(kernel, ctor, call, 3);
                                name = calc64(kernel, ctor, call, 1);
                                if (!name) {
                                    break;
                                }
                                // 4.2 find *ptr = table;
                                stor = step_64(kernel, call, ret - call, 0xF9000000, 0xFFC00000);
                                if (!stor) {
                                    break;
                                }
                                reg = kernel[stor] & 0x1F;
                                table = calc64(kernel, ctor, stor, reg);
                                process_table64(table, base, (const char *)kernel + name, sz, db);
                            }
                            scan = call + 4;
                        }
                    }
                }
            } else {
                const uint32_t *ptr = (uint32_t *)(kernel + addr);
                size /= sizeof(uint32_t);
                // 4. inside each constructor function find __ZN11OSMetaClassC2EPKcPKS_j.stub(..., name, ...); ... *ptr = table;
                for (i = 0; i < size; i++) {
                    addr_t ctor = (ptr[i] & ~1) - base;
                    addr_t ret = step_thumb(kernel, ctor, 0x300, 0xbd00, 0xFF00);
                    addr_t ret2 = step_thumb(kernel, ctor, 0x300, 0x4000e8bd, 0xE000FFFF); // POP.W {LR}, but not SP,PC
                    if (ret || ret2) {
                        addr_t scan = ctor;
                        if (ret2 && (!ret || ret > ret2)) {
                            ret = ret2;
                        }
                        for (;;) {
                            unsigned reg;
                            addr_t call, name, stor, table;
                            // 4.1 find __ZN11OSMetaClassC2EPKcPKS_j.stub(..., name, ...);
                            call = step_thumb(kernel, scan, ret - scan, 0xD000F000, 0xD000F800);
                            if (!call) {
                                break;
                            }
                            if ((stub__ZN11OSMetaClassC2EPKcPKS_j & ~1) == call + insn_bl_imm32((uint16_t *)(kernel + call)) + 4) {
                                unsigned sz = calc32mov(kernel, ctor, call, 3);
                                name = calc32(kernel, ctor, call, 1);
                                if (!name) {
                                    break;
                                }
                                // 4.2 find *ptr = table;
                                stor = step_thumb(kernel, call, ret - call, 0x6000, 0xFF00);
                                if (!stor) {
                                    // XXX STR.W
                                    break;
                                }
                                reg = kernel[stor] & 7;
                                table = calc32(kernel, ctor, stor, reg);
                                process_table32(table, base, (const char *)kernel + name, sz, db);
                            }
                            scan = call + 4;
                        }
                    }
                }
            }
        }
    }
}

static int
parse_kexts(size_t offset, sqlite3 *db)
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
        parse_one(offset, base, db);
    }

    if (next) {
        return parse_kexts(next, db);
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

    while (--argc > 0) {
        const char *p = *++argv;
        if (!strcmp(p, "-s")) {
            one_kext = 1;
            continue;
        }
        if (!strcmp(p, "-i")) {
            for_ida = 1;
            continue;
        }
        if (!strcmp(p, "-h")) {
            for_ida = -1;
            continue;
        }
        krnl = p;
    }

    if (!krnl) {
        fprintf(stderr, "usage: %s [options] kernel\n", argv[0]);
        fprintf(stderr, "\t-s parse single kext\n");
        fprintf(stderr, "\t-i output ida script\n");
        fprintf(stderr, "\t-h output C header file\n");
        return 1;
    }

    rv = init_kernel(krnl);
    if (rv) {
        fprintf(stderr, "[e] cannot read kernel\n");
        return -1;
    }

    db = make_core_db();
    if (db) {
        if (for_ida > 0) {
            printf("#include <idc.idc>\n");
            printf("\nstatic member(id, ea, name, off)\n");
            printf("{\n");
            printf("    auto str, num;\n");
            printf("    auto index;\n");
            printf("    auto left, right;\n");
            printf("    auto dem, proto;\n");
            printf("\n");
            printf("    dem = 0;\n");
            printf("    num = ltoa(off, 10);\n");
            printf("    str = Demangle(name, 0);\n");
            printf("    if (str != 0 && strstr(str, \"~\") < 0) {\n");
            printf("        index = strstr(str, \"(\");//)\n");
            printf("        if (index >= 0) {\n");
            printf("            left = substr(str, 0, index);\n");
            printf("            dem = left + \".\" + num;\n");
            printf("        }\n");
            printf("    }\n");
            printf("    if (dem == 0) {\n");
            printf("        dem = name + \".\" + num;\n");
            printf("    }\n");
            printf("\n");
            printf("    proto = 0;\n");
            printf("    str = GetType(ea);\n");
            printf("    if (str) {\n");
            printf("        index = strstr(str, \"(\");//)\n");
            printf("        if (index >= 0) {\n");
            printf("            left = substr(str, 0, index);\n");
            printf("            right = substr(str, index, -1);\n");
            printf("            proto = left + \"(*)\" + right;\n");
            printf("        }\n");
            printf("    } else {\n");
            printf("        index = strstr(name, \"__ZNK\");\n");
            printf("        if (index == 0) {\n");
            printf("            right = substr(name, index + 5, -1);\n");
            printf("            str = Demangle(\"__ZN\" + right, 0);\n");
            printf("        } else {\n");
            printf("            str = Demangle(name, 0);\n");
            printf("        }\n");
            printf("        index = strstr(str, \"(\");//)\n");
            printf("        if (index >= 0) {\n");
            printf("            right = substr(str, index, -1);\n");
            printf("            proto = \"" RETTYPE "__fastcall(*)\" + right;\n");
            printf("        }\n");
            printf("    }\n");
            printf("    if (proto == 0) {\n");
            printf("        proto = \"" RETTYPE "__fastcall(*)()\";\n");
            printf("    }\n");
            printf("\n");
            if (IS64(kernel)) {
                printf("    AddStrucMember(id, dem, off, 0x35500400, 0XFFFFFFFFFFFFFFFF, 8, 0XFFFFFFFFFFFFFFFF, 0, 0x000009);\n");
            } else {
                printf("    AddStrucMember(id, dem, off, 0x25500400, 0XFFFFFFFF, 4, 0XFFFFFFFF, 0, 0x000002);\n");
            }
            printf("    SetType(GetMemberId(id, off), proto);\n");
            printf("}\n");
            printf("\nstatic main(void)\n{\n\tauto id;\n");
        }
        if (one_kext) {
            parse_one(0, get_base(kernel, kernel_size), db);
        } else {
            parse_kexts(0, db);
        }
        if (for_ida > 0) {
            printf("}\n");
        }
        sqlite3_close(db);
    }

    term_kernel();
    return 0;
}
