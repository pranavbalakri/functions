#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t seed = UINT64_C(0x6a09e667f3bcc909);

static uint64_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

static double as_double(uint64_t bits) {
    double x;
    memcpy(&x, &bits, sizeof x);
    return x;
}

static void record(FILE *out, uint64_t op, uint64_t dn, uint64_t a, uint64_t b, uint64_t c) {
    double x = as_double(a), y = as_double(b), z = as_double(c), result;
    uint64_t flags;
    switch (op) {
        case 0:
            __asm__ volatile("msr fpsr, xzr\nfrsqrte %d0, %d2\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x));
            break;
        case 1:
            __asm__ volatile("msr fpsr, xzr\nfrsqrts %d0, %d2, %d3\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y));
            break;
        case 2:
            __asm__ volatile("msr fpsr, xzr\nfmul %d0, %d2, %d3\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y));
            break;
        case 3:
            __asm__ volatile("msr fpsr, xzr\nfmadd %d0, %d2, %d3, %d4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
            break;
        case 4:
            __asm__ volatile("msr fpsr, xzr\nfmsub %d0, %d2, %d3, %d4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
            break;
        case 5:
            __asm__ volatile("msr fpsr, xzr\nfnmsub %d0, %d2, %d3, %d4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
            break;
        default:
            __asm__ volatile("msr fpsr, xzr\nfnmadd %d0, %d2, %d3, %d4\nmrs %1, fpsr"
                             : "=w"(result), "=r"(flags) : "w"(x), "w"(y), "w"(z));
    }
    uint64_t bits;
    memcpy(&bits, &result, sizeof bits);
    uint64_t row[8] = {op, dn, a, b, c, bits, (uint64_t)flags, 0};
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
    const uint64_t edge[] = {
        0, 0x8000000000000000, 1, 2, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001,
        0x8000000000000001, 0x800fffffffffffff, 0x8010000000000000, 0x3fe0000000000000, 0x3fefffffffffffff,
        0x3ff0000000000000, 0x3ff0000000000001, 0x3ff8000000000000, 0x4000000000000000, 0x4008000000000000,
        0xbff0000000000000, 0xbff0000000000001, 0x7fefffffffffffff, 0xffefffffffffffff,
        0x7ff0000000000000, 0xfff0000000000000, 0x7ff0000000000001, 0x7ff8000000000000, 0x7ff8000000012345,
        0xfff0000000000001, 0xfff8000000012345, 0x3ca0000000000000, 0xbca0000000000000, 0x3cb0000000000000
    };
    const size_t n = sizeof edge / sizeof *edge;
    uint64_t rows = 0;
    for (uint64_t dn = 0; dn < 2; ++dn) {
        uint64_t fpcr = (uint64_t)dn << 25;
        __asm__ volatile("msr fpcr, %0\nisb" : : "r"(fpcr));
        for (uint64_t op = 0; op < 7; ++op) {
            for (size_t i = 0; i < n; ++i)
                for (size_t j = 0; j < n; ++j)
                    for (size_t k = 0; k < n; ++k) {
                        record(out, op, dn, edge[i], edge[j], edge[k]);
                        ++rows;
                    }
            for (uint64_t i = 0; i < count; ++i) {
                uint64_t a = random_bits(), b = random_bits(), c = random_bits();
                record(out, op, dn, a, b, c);
                ++rows;
            }
        }
        for (uint64_t e = 1; e < 2047; ++e)
            for (uint64_t f = 0; f < 256; ++f) {
                record(out, 0, dn, (e << 52) | (f << 44), 0, 0);
                record(out, 0, dn, (e << 52) | (f << 44) | 0x00000fffffffffff, 0, 0);
                rows += 2;
            }
        for (uint64_t bit = 0; bit < 52; ++bit) {
            record(out, 0, dn, UINT64_C(1) << bit, 0, 0);
            record(out, 0, dn, (UINT64_C(1) << (bit + 1)) - 1, 0, 0);
            rows += 2;
        }
        for (uint64_t i = 0; i < 100000; ++i) {
            uint64_t e = 1 + random_bits() % 2045;
            uint64_t a = (e << 52) | (random_bits() & 0x000fffffffffffff);
            uint64_t b = ((2046 - e) << 52) | (random_bits() & 0x000fffffffffffff);
            double x = as_double(a), y = as_double(b), product;
            __asm__ volatile("fmul %d0, %d1, %d2" : "=w"(product) : "w"(x), "w"(y));
            uint64_t c;
            memcpy(&c, &product, sizeof c);
            for (uint64_t op = 3; op < 7; ++op) {
                uint64_t addend = c ^ (op == 3 || op == 6 ? 0x8000000000000000 : 0);
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
