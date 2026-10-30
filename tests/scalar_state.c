#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef uint64_t Vector __attribute__((vector_size(16)));

static uint64_t seed = UINT64_C(0x510e527fade682d1);

static uint64_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

static Vector operand(uint32_t low) {
    return (Vector){(random_bits() & UINT64_C(0xffffffff00000000)) | low, random_bits()};
}

#define EXEC(instruction) __asm__ volatile( \
    "msr nzcv, %[nzcv]\nmsr fpsr, %[fpsr]\n" instruction \
    "\nmrs %[nzcv_after], nzcv\nmrs %[fpsr_after], fpsr" \
    : [vd] "+&w"(result), [xd] "+&r"(xresult), \
      [nzcv_after] "=&r"(nzcv_after), [fpsr_after] "=&r"(fpsr_after) \
    : [a] "w"(a), [b] "w"(b), [c] "w"(c), [xsrc] "r"(a[0]), \
      [nzcv] "r"(nzcv << 28), [fpsr] "r"(fpsr) : "cc")

static void record(FILE *out, uint64_t op, uint64_t dn, Vector a, Vector b, Vector c) {
    Vector before = {random_bits(), random_bits()}, result = before;
    uint64_t xbefore = random_bits(), xresult = xbefore;
    uint64_t nzcv = random_bits() & 15, fpsr = random_bits() & UINT64_C(0x0800009f);
    uint64_t nzcv_after, fpsr_after;
    switch (op) {
        case 0: EXEC("fmov %w[xd], %s[a]"); break;
        case 1: EXEC("fmov %s[vd], %w[xsrc]"); break;
        case 2: EXEC("fmov %s[vd], #0.5"); break;
        case 3: EXEC("frsqrte %s[vd], %s[a]"); break;
        case 4: EXEC("frsqrts %s[vd], %s[a], %s[b]"); break;
        case 5: EXEC("fmul %s[vd], %s[a], %s[b]"); break;
        case 6: EXEC("fmadd %s[vd], %s[a], %s[b], %s[c]"); break;
        case 7: EXEC("fmsub %s[vd], %s[a], %s[b], %s[c]"); break;
        case 8: EXEC("fnmsub %s[vd], %s[a], %s[b], %s[c]"); break;
        default: EXEC("fnmadd %s[vd], %s[a], %s[b], %s[c]"); break;
    }
    uint64_t row[16] = {op, dn, a[0], a[1], b[0], b[1], c[0], c[1],
        before[0], before[1], xbefore, (fpsr << 32) | nzcv, xresult,
        result[0], result[1], (fpsr_after << 32) | (nzcv_after >> 28)};
    if (fwrite(row, sizeof row, 1, out) != 1) { perror("fwrite"); exit(1); }
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s output.bin random-count-per-op-per-DN\n", argv[0]);
        return 2;
    }
    char *end;
    errno = 0;
    uint64_t count = strtoull(argv[2], &end, 10);
    if (errno || !*argv[2] || *end) return 2;
    FILE *out = fopen(argv[1], "wb");
    if (!out) { perror("fopen"); return 1; }
    uint64_t old_fpcr, old_fpsr;
    __asm__ volatile("mrs %0, fpcr\nmrs %1, fpsr" : "=r"(old_fpcr), "=r"(old_fpsr));
    const uint32_t edge[] = {
        0, 0x80000000, 1, 2, 0x007fffff, 0x00800000, 0x00800001,
        0x80000001, 0x807fffff, 0x80800000, 0x3f000000, 0x3f7fffff,
        0x3f800000, 0x3f800001, 0x3fc00000, 0x40000000, 0x40400000,
        0xbf800000, 0xbf800001, 0x7f7fffff, 0xff7fffff,
        0x7f800000, 0xff800000, 0x7f800001, 0x7fc00000, 0x7fc12345,
        0xff800001, 0xffc12345, 0x33800000, 0xb3800000, 0x34000000
    };
    size_t n = sizeof edge / sizeof *edge;
    uint64_t rows = 0;
    for (uint64_t dn = 0; dn < 2; ++dn) {
        uint64_t fpcr = dn << 25;
        __asm__ volatile("msr fpcr, %0\nisb" : : "r"(fpcr));
        for (uint64_t op = 0; op < 10; ++op) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = 0; j < n; ++j)
                    for (size_t k = 0; k < n; ++k) {
                        Vector a = operand(edge[i]), b = operand(edge[j]), c = operand(edge[k]);
                        record(out, op, dn, a, b, c);
                        ++rows;
                    }
            for (uint64_t i = 0; i < count; ++i) {
                Vector a = {random_bits(), random_bits()};
                Vector b = {random_bits(), random_bits()};
                Vector c = {random_bits(), random_bits()};
                record(out, op, dn, a, b, c);
                ++rows;
            }
        }
    }
    __asm__ volatile("msr fpcr, %0\nmsr fpsr, %1\nisb" : : "r"(old_fpcr), "r"(old_fpsr));
    if (fclose(out)) { perror("fclose"); return 1; }
    printf("scalar_rows=%" PRIu64 " random_per_op_per_DN=%" PRIu64 " seed=510e527fade682d1\n", rows, count);
    return 0;
}
