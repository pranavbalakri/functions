#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t seed = UINT64_C(0x6a09e667f3bcc909);

static uint32_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return (uint32_t)(z ^ (z >> 31));
}

static float as_float(uint32_t bits) {
    float x;
    memcpy(&x, &bits, sizeof x);
    return x;
}

static void record(FILE *out, uint32_t op, uint32_t dn, uint32_t a, uint32_t b, uint32_t c) {
    float x = as_float(a), y = as_float(b), z = as_float(c), result;
    uint64_t flags;
    switch (op) {
        case 0:
            __asm__ volatile("msr fpsr, xzr\nfrsqrte %s0, %s2\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x));
            break;
        case 1:
            __asm__ volatile("msr fpsr, xzr\nfrsqrts %s0, %s2, %s3\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y));
            break;
        case 2:
            __asm__ volatile("msr fpsr, xzr\nfmul %s0, %s2, %s3\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y));
            break;
        case 3:
            __asm__ volatile("msr fpsr, xzr\nfmadd %s0, %s2, %s3, %s4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
            break;
        case 4:
            __asm__ volatile("msr fpsr, xzr\nfmsub %s0, %s2, %s3, %s4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
            break;
        case 5:
            __asm__ volatile("msr fpsr, xzr\nfnmsub %s0, %s2, %s3, %s4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
            break;
        default:
            __asm__ volatile("msr fpsr, xzr\nfnmadd %s0, %s2, %s3, %s4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
    }
    uint32_t bits;
    memcpy(&bits, &result, sizeof bits);
    uint32_t row[8] = {op, dn, a, b, c, bits, (uint32_t)flags, 0};
    if (fwrite(row, sizeof row, 1, out) != 1) {
        perror("fwrite");
        exit(1);
    }
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s output.bin random-count-per-op-per-DN\n", argv[0]);
        return 2;
    }
    errno = 0;
    char *end;
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
    const size_t n = sizeof edge / sizeof *edge;
    uint64_t rows = 0;
    for (uint32_t dn = 0; dn < 2; ++dn) {
        uint64_t fpcr = (uint64_t)dn << 25;
        __asm__ volatile("msr fpcr, %0\nisb" : : "r"(fpcr));
        for (uint32_t op = 0; op < 7; ++op) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = 0; j < n; ++j)
                    for (size_t k = 0; k < n; ++k) {
                        record(out, op, dn, edge[i], edge[j], edge[k]);
                        ++rows;
                    }
            for (uint64_t i = 0; i < count; ++i) {
                uint32_t a = random_bits(), b = random_bits(), c = random_bits();
                record(out, op, dn, a, b, c);
                ++rows;
            }
        }
        for (uint32_t e = 1; e < 255; ++e)
            for (uint32_t f = 0; f < 256; ++f) {
                record(out, 0, dn, (e << 23) | (f << 15), 0, 0);
                record(out, 0, dn, (e << 23) | (f << 15) | 0x7fff, 0, 0);
                rows += 2;
            }
        for (uint32_t bit = 0; bit < 23; ++bit) {
            record(out, 0, dn, UINT32_C(1) << bit, 0, 0);
            record(out, 0, dn, (UINT32_C(1) << (bit + 1)) - 1, 0, 0);
            rows += 2;
        }
        for (uint32_t i = 0; i < 100000; ++i) {
            uint32_t e = 1 + random_bits() % 253;
            uint32_t a = (e << 23) | (random_bits() & 0x7fffff);
            uint32_t b = ((254 - e) << 23) | (random_bits() & 0x7fffff);
            float x = as_float(a), y = as_float(b), product;
            __asm__ volatile("fmul %s0, %s1, %s2" : "=w"(product) : "w"(x), "w"(y));
            uint32_t c;
            memcpy(&c, &product, sizeof c);
            for (uint32_t op = 3; op < 7; ++op) {
                uint32_t addend = c ^ (op == 3 || op == 6 ? 0x80000000 : 0);
                record(out, op, dn, a, b, addend - 1);
                record(out, op, dn, a, b, addend);
                record(out, op, dn, a, b, addend + 1);
                rows += 3;
            }
        }
    }
    __asm__ volatile("msr fpcr, %0\nmsr fpsr, %1\nisb" : : "r"(old_fpcr), "r"(old_fpsr));
    if (fclose(out)) { perror("fclose"); return 1; }
    printf("rows=%" PRIu64 " random_per_op_per_DN=%" PRIu64 " seed=6a09e667f3bcc909\n", rows, count);
    return 0;
}
