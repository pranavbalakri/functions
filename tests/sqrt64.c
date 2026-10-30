#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern double verified_sqrt(double);

static uint64_t seed = UINT64_C(0x243f6a8885a308d3);
static uint64_t checked, failures;

static uint64_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

static uint64_t parse(const char *s) {
    char *end;
    errno = 0;
    uint64_t n = strtoull(s, &end, 0);
    if (errno || !*s || *end) { fprintf(stderr, "invalid integer: %s\n", s); exit(2); }
    return n;
}

static void check(uint64_t bits) {
    double x, actual, reference;
    uint64_t got, expected;
    memcpy(&x, &bits, sizeof x);
    actual = verified_sqrt(x);
    __asm__ volatile("fsqrt %d0, %d1" : "=w"(reference) : "w"(x));
    memcpy(&got, &actual, sizeof got);
    memcpy(&expected, &reference, sizeof expected);
    if (got != expected) {
        if (failures < 20)
            printf("mismatch input=%016" PRIx64 " got=%016" PRIx64 " expected=%016" PRIx64 "\n", bits, got, expected);
        ++failures;
    }
    ++checked;
}

static void neighbors(uint64_t bits) {
    check(bits - 1);
    check(bits);
    check(bits + 1);
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s random-count DN\n", argv[0]);
        return 2;
    }
    uint64_t count = parse(argv[1]), dn = parse(argv[2]);
    if (dn > 1) return 2;
    uint64_t initial_seed = seed ^ (dn << 63);
    seed = initial_seed;
    uint64_t old_fpcr, old_fpsr, fpcr = dn << 25;
    __asm__ volatile("mrs %0, fpcr\nmrs %1, fpsr" : "=r"(old_fpcr), "=r"(old_fpsr));
    __asm__ volatile("msr fpcr, %0\nisb" : : "r"(fpcr));
    struct timespec start, finish;
    clock_gettime(CLOCK_MONOTONIC, &start);
    const uint64_t edge[] = {
        0, UINT64_C(0x8000000000000000), 1, 2, UINT64_C(0x000fffffffffffff),
        UINT64_C(0x0010000000000000), UINT64_C(0x7fefffffffffffff),
        UINT64_C(0x7ff0000000000000), UINT64_C(0xfff0000000000000),
        UINT64_C(0x7ff0000000000001), UINT64_C(0x7ff8000000000000),
        UINT64_C(0x7ff8000000012345), UINT64_C(0xfff0000000000001),
        UINT64_C(0xfff8000000012345), UINT64_MAX
    };
    for (size_t i = 0; i < sizeof edge / sizeof *edge; ++i) neighbors(edge[i]);
    for (uint64_t e = 1; e < 2047; ++e) {
        neighbors(e << 52);
        neighbors((e << 52) | UINT64_C(0x8000000000000000));
    }
    for (uint64_t bit = 0; bit < 52; ++bit) neighbors(UINT64_C(1) << bit);
    for (uint64_t i = 1; i <= 1048576; ++i) {
        double r = (double)i, square = r * r;
        uint64_t bits;
        memcpy(&bits, &square, sizeof bits);
        neighbors(bits);
        check(random_bits() & UINT64_C(0x000fffffffffffff));
    }
    for (uint64_t i = 0; i < 1048576; ++i) {
        uint64_t bits = ((UINT64_C(512) + random_bits() % 1022) << 52) |
            (random_bits() & UINT64_C(0x000fffffffffffff));
        double r, square;
        memcpy(&r, &bits, sizeof r);
        square = r * r;
        memcpy(&bits, &square, sizeof bits);
        neighbors(bits);
    }
    for (uint64_t i = 0; i < count; ++i) check(random_bits());
    clock_gettime(CLOCK_MONOTONIC, &finish);
    __asm__ volatile("msr fpcr, %0\nmsr fpsr, %1\nisb" : : "r"(old_fpcr), "r"(old_fpsr));
    double seconds = finish.tv_sec - start.tv_sec + (finish.tv_nsec - start.tv_nsec) * 1e-9;
    printf("checked=%" PRIu64 " random=%" PRIu64 " DN=%" PRIu64 " failures=%" PRIu64 " seconds=%.3f seed=%016" PRIx64 "\n", checked, count, dn, failures, seconds, initial_seed);
    return failures != 0;
}
