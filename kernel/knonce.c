/*
 *  ghetto apnonce writer
 *
 *  Copyright (c) 2015, 2016 xerub
 */

#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <ctype.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#include <mach-o/loader.h>

#ifdef __ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__
#include <IOKit/IOKitLib.h>
#undef round_page
#define HOST_KERNEL_PORT 4
#endif

typedef unsigned long long addr_t;

struct dependency {
    uint8_t *buf;
    size_t size;
    addr_t base;
    const char *name;
};

#define round_page(size) ((size + 0xFFF) & ~0xFFF)

#define IS64(image) (*(uint8_t *)(image) & 1)

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
step_thumb_back(const uint8_t *buf, addr_t start, size_t length, uint32_t what, uint32_t mask)
{
    addr_t end = start - length;
    while (start >= end) {
        uint32_t x = *(uint32_t *)(buf + start);
        if ((x & mask) == what) {
            return start;
        }
        start -= ((buf[start - 3] & 0xF8) > 0xE0) ? 4 : 2;
    }
    return 0;
}

static addr_t
bof32(const uint8_t *buf, addr_t start, addr_t where)
{
    for (where &= ~1; where >= start; where -= 2) {
        uint16_t op = *(uint16_t *)(buf + where);
        if ((op & 0xFF00) == 0xB500) {
            //printf("%x: PUSH {LR}\n", where);
            return where;
        }
        if (where - 4 >= start && (buf[where - 3] & 0xF8) > 0xE0) {
            where -= 2;
        }
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
xref32(const uint8_t *buf, addr_t start, addr_t end, addr_t what)
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
                if (value[reg] == what) {
                    return i;
                }
            }
        }
        i += insn_is_32bit(current_instruction) ? 4 : 2;
    }
    return 0;
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
step_64_back(const uint8_t *buf, addr_t start, size_t length, uint32_t what, uint32_t mask)
{
    addr_t end = start - length;
    while (start >= end) {
        uint32_t x = *(uint32_t *)(buf + start);
        if ((x & mask) == what) {
            return start;
        }
        start -= 4;
    }
    return 0;
}

static addr_t
bof64(const uint8_t *buf, addr_t start, addr_t where)
{
    for (; where >= start; where -= 4) {
        uint32_t op = *(uint32_t *)(buf + where);
        if ((op & 0xFFC003FF) == 0x910003FD) {
            unsigned delta = (op >> 10) & 0xFFF;
            //printf("%x: ADD X29, SP, #0x%x\n", where, delta);
            if ((delta & 0xF) == 0) {
                addr_t prev = where - ((delta >> 4) + 1) * 4;
                uint32_t au = *(uint32_t *)(buf + prev);
                if ((au & 0xFFC003E0) == 0xA98003E0) {
                    //printf("%x: STP x, y, [SP,#-imm]!\n", prev);
                    return prev;
                }
            }
        }
    }
    return 0;
}

static addr_t
xref64(const uint8_t *buf, addr_t start, addr_t end, addr_t what)
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
        if (value[reg] == what) {
            return i;
        }
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

/* machofinder ***************************************************************/

static addr_t
find_dref(const uint8_t *buf, size_t size, addr_t data, int nth, int bof)
{
    addr_t x;
    addr_t offset, end;
    size_t sz;

    offset = get_sect_data(buf, size, "__TEXT", "__text", &sz);
    if (!offset) {
        return 0;
    }
    end = offset + sz;

    if (IS64(buf)) {
        addr_t off = offset;
        do {
            x = xref64(buf, off, end, data);
            if (!x) {
                return 0;
            }
            off = x + 4;
        } while (nth--);
        if (bof) {
            x = bof64(buf, offset, x);
        }
    } else {
        addr_t off = offset;
        do {
            x = xref32(buf, off, end, data);
            if (!x) {
                return 0;
            }
            off = x + 4;
        } while (nth--);
        if (bof) {
            x = bof32(buf, offset, x);
        }
    }
    return x;
}

static addr_t
find_sref(const uint8_t *buf, size_t size, const char *string, int bof)
{
    unsigned char *str = boyermoore_horspool_memmem(buf, size, (const void *)string, strlen(string));
    if (!str) {
        return 0;
    }
    return find_dref(buf, size, str - buf, 0, bof);
}

/* kernel stuff **************************************************************/

#ifdef __ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__
#include <mach/mach.h>

#ifdef __LP64__
#define KDELTA 0x4000 /* XXX 7.x-8.x: 0x2000 */
#else
#define KDELTA 0x1000
#endif

static vm_address_t
get_kernel_base(task_t *kernel_task)
{
    kern_return_t rv;
    vm_region_submap_info_data_64_t info;
    vm_size_t size;
    mach_msg_type_number_t info_count = VM_REGION_SUBMAP_INFO_COUNT_64;
    unsigned int depth = 0;
    vm_address_t addr = 0x81200000; /* arm64: addr = 0xffffff8000000000 */

#ifdef HOST_KERNEL_PORT
    *kernel_task = 0;
    rv = host_get_special_port(mach_host_self(), HOST_LOCAL_NODE, HOST_KERNEL_PORT, kernel_task);
    if (rv != KERN_SUCCESS || *kernel_task == 0)
#endif
    rv = task_for_pid(mach_task_self(), 0, kernel_task);
    if (rv != KERN_SUCCESS) {
        return -1;
    }

    while ((rv = vm_region_recurse_64(*kernel_task, &addr, &size, &depth, (vm_region_info_t)&info, &info_count)) == KERN_SUCCESS) {
        if (size > 1024 * 1024 * 1024) {
#ifdef __LP64__
            vm_address_t where = 16 * 0x200000;
#else
            vm_address_t where = 1 * 0x200000;
#endif
            for (where += addr; where >= addr; where -= 0x200000) {
                vm_size_t sz;
                uint8_t head[2048];
                sz = sizeof(head);
                rv = vm_read_overwrite(*kernel_task, where + KDELTA, sizeof(head), (vm_address_t)head, &sz);
                if (rv == 0 && sz == sizeof(head) && (*(uint32_t *)head & ~1) == 0xfeedface
                    && boyermoore_horspool_memmem(head, sizeof(head), (const uint8_t *)"__KLD", 5)) {
                    return where + KDELTA;
                }
#ifdef __LP64__
                sz = sizeof(head);
                rv = vm_read_overwrite(*kernel_task, where + KDELTA / 2, sizeof(head), (vm_address_t)head, &sz);
                if (rv == 0 && sz == sizeof(head) && (*(uint32_t *)head & ~1) == 0xfeedface
                    && boyermoore_horspool_memmem(head, sizeof(head), (const uint8_t *)"__KLD", 5)) {
                    return where + KDELTA / 2;
                }
#endif
            }
            break;
        }
        addr += size;
    }

    return -1;
}

uint8_t *kernel = NULL;
#ifdef __LP64__
size_t kernel_size = 0x2600000;
#else
size_t kernel_size = 0x1200000;
#endif
task_t kernel_task = TASK_NULL;
uint64_t kernel_base = 0;
struct kdb *kernel_db;

static vm_size_t
kread(vm_address_t where, uint8_t *p, vm_size_t size)
{
    int rv;
    size_t offset = 0;
    while (offset < size) {
        vm_size_t sz, chunk = 2048;
        if (chunk > size - offset) {
            chunk = size - offset;
        }
        rv = vm_read_overwrite(kernel_task, where + offset, chunk, (vm_address_t)(p + offset), &sz);
        if (rv || sz == 0) {
            fprintf(stderr, "[e] error reading kernel @0x%zx\n", offset + where);
            break;
        }
        offset += sz;
    }
    return offset;
}

static vm_size_t
kwrite(vm_address_t where, const uint8_t *p, vm_size_t size)
{
    int rv;
    size_t offset = 0;
    while (offset < size) {
        vm_size_t chunk = 2048;
        if (chunk > size - offset) {
            chunk = size - offset;
        }
        rv = vm_write(kernel_task, where + offset, (vm_offset_t)p + offset, chunk);
        if (rv) {
            fprintf(stderr, "[e] error writing kernel @0x%zx\n", offset + where);
            break;
        }
        offset += chunk;
    }
    return offset;
}

static vm_size_t
kwrite_uint64(vm_address_t where, uint64_t value)
{
    return kwrite(where, (uint8_t *)&value, sizeof(value));
}

static vm_size_t
kwrite_uint32(vm_address_t where, uint32_t value)
{
    return kwrite(where, (uint8_t *)&value, sizeof(value));
}

static vm_address_t
kalloc(vm_size_t size)
{
    int rv;
    vm_address_t addr = 0;
    rv = vm_allocate(kernel_task, &addr, round_page(size), 1);
    assert(rv == KERN_SUCCESS);
    return addr;
}

static void
kfree(vm_address_t addr, vm_size_t size)
{
    vm_deallocate(kernel_task, addr, round_page(size));
}

static int
init_kernel(const char *filename)
{
    (void)filename;

    kernel_base = get_kernel_base(&kernel_task);
    if (kernel_base == (vm_address_t)-1) {
        return -1;
    }

    kernel = malloc(kernel_size);
    if (!kernel) {
        return -1;
    }

    kernel_size = kread(kernel_base, kernel, kernel_size);
    return 0;
}

static void
term_kernel(void)
{
    free(kernel);
}

#else	/* !__ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__ */

uint8_t *kernel = MAP_FAILED;
size_t kernel_size = 0;
int kernel_fd = -1;
uint64_t kernel_base = 0;
struct kdb *kernel_db;

static size_t
kread(addr_t where, uint8_t *p, size_t size)
{
    (void)(where && p);
    return size;
}

static size_t
kwrite(addr_t where, const uint8_t *p, size_t size)
{
    (void)(where && p);
    return size;
}

static size_t
kwrite_uint64(addr_t where, uint64_t value)
{
    return kwrite(where, (uint8_t *)&value, sizeof(value));
}

static size_t
kwrite_uint32(addr_t where, uint32_t value)
{
    return kwrite(where, (uint8_t *)&value, sizeof(value));
}

static uintptr_t
kalloc(size_t size)
{
    return (uintptr_t)malloc(size);
}

static void
kfree(uintptr_t addr, size_t size)
{
    (void)size;
    free((void *)addr);
}

static int
init_kernel(const char *filename)
{
    kernel_fd = open(filename, O_RDONLY);
    if (kernel_fd < 0) {
        return -1;
    }

    kernel_size = lseek(kernel_fd, 0, SEEK_END);

    kernel = mmap(NULL, kernel_size, PROT_READ, MAP_PRIVATE, kernel_fd, 0);
    if (kernel != MAP_FAILED) {
        if ((*(uint32_t *)kernel & ~1) == 0xfeedface) {
            kernel_base = get_base(kernel, kernel_size);
            return 0;
        }
        munmap(kernel, kernel_size);
        kernel = MAP_FAILED;
    }

    close(kernel_fd);
    kernel_fd = -1;
    return -1;
}

static void
term_kernel(void)
{
    munmap(kernel, kernel_size);
    close(kernel_fd);
}
#endif	/* !__ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__ */

/* kernel kext ***************************************************************/

static addr_t
off_PRELINK_TEXT(void)
{
    unsigned i;
    const uint8_t *p = kernel;
    addr_t offset = 0;
    const struct mach_header *hdr = (struct mach_header *)p;
    const uint8_t *q = p + sizeof(struct mach_header);

    if (kernel_size < 0x1000) {
        return 0;
    }

    if (IS64(p)) {
        q += 4;
    }

    for (i = 0; i < hdr->ncmds; i++) {
        const struct load_command *cmd = (struct load_command *)q;
        if (cmd->cmd == LC_SEGMENT) {
            const struct segment_command *seg = (struct segment_command *)q;
            if (!strcmp(seg->segname, "__PRELINK_TEXT")) {
                offset = seg->fileoff;
                break;
            }
        }
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (struct segment_command_64 *)q;
            if (!strcmp(seg->segname, "__PRELINK_TEXT")) {
                offset = seg->fileoff;
                break;
            }
        }
        q = q + cmd->cmdsize;
    }

    return offset;
}

static addr_t
find_kext(const char *kextid, addr_t *next)
{
    addr_t koff, kbase, ksize;
    addr_t offset = off_PRELINK_TEXT();
    size_t len = strlen(kextid) + 1; /* XXX with zero, too */
    const uint8_t *p;

    *next = 0;

    if (offset == 0) {
        return 0;
    }

    while (1) {
        p = boyermoore_horspool_memmem(kernel + offset + 1, kernel_size - offset - 1, (const void *)kextid, len);
        if (!p) {
            return 0;
        }
        offset = p - kernel;

        if (((int *)p)[-1] == 0 || !isdigit(p[64])) {
            continue;
        }

        if (IS64(kernel)) {
            kbase = *(uint64_t *)(p - 0x10 + 0x9c);
            ksize = *(uint64_t *)(p - 0x10 + 0xa4);
        } else {
            kbase = *(uint32_t *)(p - 0xc + 0x94);
            ksize = *(uint32_t *)(p - 0xc + 0x98);
        }
        if (((kbase | ksize) & 0xFFF) || kbase < kernel_base || ksize > 0x1000000) {
            continue;
        }

        for (koff = offset & ~0xFFF; koff && offset - koff < 0x100000; koff -= 0x1000) {
            if (*(uint32_t *)(kernel + koff) == *(uint32_t *)kernel) {
                addr_t other = (offset & ~0xFFF) + 0x1000;
                while (other < kernel_size && other < offset + 0x100000) {
                    uint32_t magic = *(uint32_t *)(kernel + other);
                    if (magic == *(uint32_t *)kernel || magic == 0x6369643C) {
                        *next = other;
                        return koff;
                    }
                    other += 0x1000;
                }
                break;
            }
        }
    }

    return 0;
}

static int
load_dep(const char *kextid, struct dependency *dep)
{
    uint8_t *buf;
    size_t size;
    addr_t kext, next;

    kext = find_kext(kextid, &next);
    if (!kext) {
        return -1;
    }
    size = next - kext;

    printf("%s: 0x%llx -> 0x%llx\n", kextid, kext, next);

    buf = malloc(size);
    if (!buf) {
        return -1;
    }

    memcpy(buf, kernel + kext, size);

    dep->buf = buf;
    dep->size = size;
    dep->base = get_base(buf, size);
    dep->name = kextid;
    return 0;
}

static void
free_dep(struct dependency *dep)
{
    free(dep->buf);
}

/* the real mccoy ************************************************************/

static void
dump_file(const char *filename, int n, void *buf, size_t size)
{
    FILE *f;
    char tmp[256];
    if (n >= 0) {
        snprintf(tmp, sizeof(tmp), "%s%d", filename, n);
        filename = tmp;
    }
    f = fopen(filename, "wb");
    fwrite(buf, 1, size, f);
    fclose(f);
}

static uint8_t stuff32[] = {
    0x80, 0xb5, /* push {r7, lr} */
    0x6f, 0x46, /* mov  r7, sp */
    0x02, 0x49, /* ldr  r1, [pc, #8] */
    0x03, 0x4a, /* ldr  r2, [pc, #12] */
    0x01, 0x60, /* str  r1, [r0, #0] */
    0x42, 0x60, /* str  r2, [r0, #4] */
    0x80, 0xbd, /* pop  {r7, pc} */
    0x00, 0xbf, /* nop */
    1, 1, 1, 1,
    2, 2, 2, 2,
};

static uint32_t stuff64[] = {
    0xa9bf7bfd, /* stp	x29, x30, [sp,#-16]! */
    0x910003fd, /* mov	x29, sp */
    0x58000081, /* ldr	x1, 18 <BNCN> */
    0xf9000001, /* str	x1, [x0] */
    0xa8c17bfd, /* ldp	x29, x30, [sp],#16 */
    0xd65f03c0, /* ret */
    1, 1,       /* BNCN */
};

static addr_t
tell_me_where32(void)
{
    int rv;
    unsigned adr, imm;
    uint32_t op1, op2;
    addr_t ref, call, stub, where;
    struct dependency dep;

    rv = load_dep("com.apple.driver.AppleMobileApNonce", &dep);
    assert(rv == 0);

    ref = find_sref(dep.buf, dep.size, "0x%016llx", 0);
    assert(ref);

    call = step_thumb_back(dep.buf, ref, 0x20, 0xD000F000, 0xD000F800);
    assert(call);

    stub = call + insn_bl_imm32((uint16_t *)(dep.buf + call)) + 4;

    where = calc32(dep.buf, stub, stub + 16, 12);
    assert(where);
    where += dep.base;

    free_dep(&dep);
    return where;
}

static addr_t
tell_me_where64(void)
{
    int rv;
    unsigned adr, imm;
    uint32_t op1, op2;
    addr_t ref, call, stub, where;
    long long w;
    struct dependency dep;

    rv = load_dep("com.apple.driver.AppleMobileApNonce", &dep);
    assert(rv == 0);

    ref = find_sref(dep.buf, dep.size, "0x%016llx", 0);
    assert(ref);

    call = step_64_back(dep.buf, ref, 0x20, 0x94000000, 0xFC000000);
    assert(call);

    w = *(uint32_t *)(dep.buf + call) & 0x3FFFFFF;
    w <<= 64 - 26;
    w >>= 64 - 26 - 2;

    stub = call + w;

    op1 = *(uint32_t *)(dep.buf + stub);
    op2 = *(uint32_t *)(dep.buf + stub + 4);

    adr = ((op1 & 0x60000000) >> 17) | ((op1 & 0xFFFFE0) << 9);
    imm = ((op2 >> 10) & 0xFFF) << 3;

    where = adr + ((dep.base + stub) & ~0xFFF) + imm;

    free_dep(&dep);
    return where;
}

int
main(int argc, char **argv)
{
    size_t rv;
    char *kernel_ver;
    addr_t vm_kernel_slide;
    addr_t TRAMPOLINE_ADDR;
    uint8_t *stuff;
    size_t sizeof_stuff;

    addr_t BNCN, where, what;
    uint8_t *p;

    if (argc != 2) {
        printf("usage: knonce BNCN\n");
        return 1;
    }

    BNCN = strtoull(argv[1], NULL, 0);
    p = (uint8_t *)&what;
    p[0] = BNCN >> 56;
    p[1] = BNCN >> 48;
    p[2] = BNCN >> 40;
    p[3] = BNCN >> 32;
    p[4] = BNCN >> 24;
    p[5] = BNCN >> 16;
    p[6] = BNCN >> 8;
    p[7] = BNCN;

    /* read in kernel, solve some shit, etc. */

    rv = init_kernel("krnl");
    if (rv) {
        fprintf(stderr, "[e] cannot read kernel\n");
        return -1;
    }

    kernel_ver = (char *)boyermoore_horspool_memmem(kernel, kernel_size, (unsigned char *)"Darwin Kernel Version", sizeof("Darwin Kernel Version") - 1);

    if (IS64(kernel)) {
        unsigned v = 0;
        if (kernel_ver) {
            kernel_ver = strstr(kernel_ver, "root:xnu-");
            if (kernel_ver) {
                v = atoi(kernel_ver + 9);
            }
        }
        assert(v);
        if (v < 2783) {
            vm_kernel_slide = kernel_base - 0xFFFFFF8000202000; // 7.x
        } else if (v >= 3248) {
            vm_kernel_slide = kernel_base - 0xFFFFFF8004004000; // 9.x
        } else {
            vm_kernel_slide = kernel_base - 0xFFFFFF8002002000; // 8.x
        }
        stuff = (uint8_t *)stuff64;
        sizeof_stuff = sizeof(stuff64);
    } else {
        vm_kernel_slide = kernel_base - 0x80001000;
        stuff = stuff32;
        sizeof_stuff = sizeof(stuff32);
    }
    printf("vm_kernel_slide = 0x%llx\n", vm_kernel_slide);

    /* upload and execute */

    TRAMPOLINE_ADDR = kalloc(sizeof_stuff);
    printf("trampoline: 0x%llx\n", TRAMPOLINE_ADDR);

    printf("BNCN = 0x%llx\n", what);
    if (IS64(kernel)) {
        ((uint64_t *)stuff64)[3] = what;
        where = tell_me_where64();
        printf("patching 0x%llx\n", where);
#ifdef __ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__
        rv = kwrite_uint64(where, TRAMPOLINE_ADDR);
        assert(rv == sizeof(uint64_t));
#endif
    } else {
        ((uint64_t *)stuff32)[2] = what;
        where = tell_me_where32();
        printf("patching 0x%llx\n", where);
#ifdef __ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__
        rv = kwrite_uint32(where, TRAMPOLINE_ADDR + 1);
        assert(rv == sizeof(uint32_t));
#endif
    }
    dump_file("_tramp", -1, stuff, sizeof_stuff);

    rv = kwrite(TRAMPOLINE_ADDR, stuff, sizeof_stuff);
    assert(rv == sizeof_stuff);

#ifdef __ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__
    vm_prot_t prot = VM_PROT_READ | VM_PROT_EXECUTE;
    rv = vm_protect(kernel_task, TRAMPOLINE_ADDR, round_page(sizeof_stuff), 1, prot);
    assert(rv == KERN_SUCCESS);
    rv = vm_protect(kernel_task, TRAMPOLINE_ADDR, round_page(sizeof_stuff), 0, prot);
    assert(rv == KERN_SUCCESS);
#endif	/* __ENVIRONMENT_IPHONE_OS_VERSION_MIN_REQUIRED__ */

    //kfree(TRAMPOLINE_ADDR, sizeof_stuff);

    printf("done\n");

    term_kernel();
    return system("apnonce generate");
}
