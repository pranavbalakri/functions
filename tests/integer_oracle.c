#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t seed = UINT64_C(0x3c6ef372fe94f82b);

static uint64_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

#define EXEC(instruction) __asm__ volatile("msr nzcv, %[initial]\n" instruction "\nmrs %[flags], nzcv" \
    : [r] "+&r"(result), [flags] "=r"(flags), [taken] "+&r"(taken) \
    : [a] "r"(a), [b] "r"(b), [initial] "r"(initial) : "cc")
#define BRANCH(instruction) EXEC(instruction " 1f\nmov %[taken], #0\nb 2f\n1:\nmov %[taken], #1\n2:")

static void record(FILE *out, uint64_t op, uint64_t a, uint64_t b, uint64_t before, uint64_t nzcv) {
    uint64_t result = before, flags, taken = 0, initial = nzcv << 28;
    switch (op) {
        case 0: EXEC("lsl %[r], %[a], %[b]"); break;
        case 1: EXEC("umull %[r], %w[a], %w[b]"); break;
        case 2: EXEC("cmp %[a], %[b]"); break;
        case 3: EXEC("cmp %w[a], %w[b]"); break;
        case 4: BRANCH("b.lo"); break;
        case 5: BRANCH("b.eq"); break;
        case 6: BRANCH("b.hi"); break;
        default: BRANCH("b"); break;
    }
    uint64_t row[8] = {op, a, b, before, nzcv, result, flags >> 28, taken};
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
    uint64_t edge[] = {0, 1, 31, 32, 63, 64, 65, 0x7fffffff, 0x80000000,
        0xffffffff, UINT64_C(0x100000000), UINT64_C(0x7fffffffffffffff),
        UINT64_C(0x8000000000000000), UINT64_MAX};
    uint64_t rows = 0;
    for (uint64_t op = 0; op < 8; ++op) {
        for (uint64_t i = 0; i < count; ++i) {
            uint64_t a = random_bits(), b = random_bits(), r = random_bits();
            record(out, op, a, b, r, random_bits() & 15);
            ++rows;
        }
        for (size_t i = 0; i < sizeof edge / sizeof *edge; ++i)
            for (size_t j = 0; j < sizeof edge / sizeof *edge; ++j)
                for (uint64_t flags = 0; flags < 16; ++flags) {
                    record(out, op, edge[i], edge[j], random_bits(), flags);
                    ++rows;
                }
    }
    if (fclose(out)) return 1;
    printf("integer_rows=%" PRIu64 " random_per_op=%" PRIu64 " seed=3c6ef372fe94f82b\n", rows, count);
    return 0;
}
