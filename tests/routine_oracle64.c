#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern double verified_sqrt(double);

static uint64_t seed = UINT64_C(0xbb67ae8584caa73b);

static uint64_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return (uint64_t)(z ^ (z >> 31));
}

static void record(FILE *out, uint64_t dn, uint64_t input) {
    double x;
    memcpy(&x, &input, sizeof x);
    __asm__ volatile("msr fpsr, xzr");
    double y = verified_sqrt(x);
    uint64_t flags;
    __asm__ volatile("mrs %0, fpsr" : "=r"(flags));
    uint64_t bits;
    memcpy(&bits, &y, sizeof bits);
    uint64_t row[4] = {dn, input, bits, (uint64_t)flags};
    if (fwrite(row, sizeof row, 1, out) != 1) { perror("fwrite"); exit(1); }
}

int main(int argc, char **argv) {
    if (argc != 3) return 2;
    char *end;
    errno = 0;
    uint64_t count = strtoull(argv[2], &end, 10);
    if (errno || !*argv[2] || *end) return 2;
    FILE *out = fopen(argv[1], "wb");
    if (!out) { perror("fopen"); return 1; }
    uint64_t old_fpcr, old_fpsr, rows = 0;
    __asm__ volatile("mrs %0, fpcr\nmrs %1, fpsr" : "=r"(old_fpcr), "=r"(old_fpsr));
    for (uint64_t dn = 0; dn < 2; ++dn) {
        uint64_t fpcr = (uint64_t)dn << 25;
        __asm__ volatile("msr fpcr, %0\nisb" : : "r"(fpcr));
        for (uint64_t i = 0; i < count; ++i) { record(out, dn, random_bits()); ++rows; }
        for (uint64_t e = 0; e < 2048; ++e) {
            uint64_t base = e << 52;
            uint64_t edge[] = {base, base + 1, base | 0x000fffffffffffff, base | 0x0008000000000000};
            for (size_t i = 0; i < 4; ++i) {
                record(out, dn, edge[i]);
                record(out, dn, edge[i] | 0x8000000000000000);
                rows += 2;
            }
        }
        for (uint64_t i = 0; i < 52; ++i) {
            record(out, dn, UINT64_C(1) << i);
            record(out, dn, (UINT64_C(1) << (i + 1)) - 1);
            rows += 2;
        }
    }
    __asm__ volatile("msr fpcr, %0\nmsr fpsr, %1\nisb" : : "r"(old_fpcr), "r"(old_fpsr));
    if (fclose(out)) return 1;
    printf("routine_rows=%" PRIu64 " random_per_DN=%" PRIu64 " seed=bb67ae8584caa73b\n", rows, count);
    return 0;
}
