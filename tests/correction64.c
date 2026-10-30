#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern double test_correct64(uint64_t, uint64_t, uint64_t);

static uint64_t seed = UINT64_C(0xa54ff53a5f1d36f1);

static uint64_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

static uint64_t reference(uint64_t bits) {
    double x, y;
    memcpy(&x, &bits, sizeof x);
    __asm__ volatile("fsqrt %d0, %d1" : "=w"(y) : "w"(x));
    uint64_t result;
    memcpy(&result, &y, sizeof result);
    return result;
}

static uint64_t candidate(uint64_t bits, int64_t offset) {
    uint64_t r = reference(bits);
    int64_t q = r == UINT64_C(0x4000000000000000) ? INT64_C(0x20000000000000)
        : (int64_t)((r & UINT64_C(0xfffffffffffff)) + UINT64_C(0x10000000000000));
    q += offset;
    if (q < INT64_C(0x10000000000000)) q = INT64_C(0x10000000000000);
    if (q > INT64_C(0x20000000000000)) q = INT64_C(0x20000000000000);
    return (uint64_t)q;
}

static int check(uint64_t bits, uint64_t q) {
    __uint128_t n4 = (__uint128_t)(UINT64_C(0x10000000000000) |
        (bits & UINT64_C(0xfffffffffffff))) << ((bits >> 52) - 969);
    double y = test_correct64(q, (uint64_t)n4, (uint64_t)(n4 >> 64));
    uint64_t got;
    memcpy(&got, &y, sizeof got);
    uint64_t expected = reference(bits);
    if (got == expected) return 0;
    printf("correction failure input=%016" PRIx64 " seed=%" PRIu64 " got=%016" PRIx64 " expected=%016" PRIx64 "\n",
        bits, q, got, expected);
    return 1;
}

int main(void) {
    uint64_t old_fpcr, old_fpsr;
    __asm__ volatile("mrs %0, fpcr\nmrs %1, fpsr\nmsr fpcr, xzr\nisb"
        : "=r"(old_fpcr), "=r"(old_fpsr));
    uint64_t count = 0, failures = 0;
    for (uint64_t i = 0; i < 1000000; ++i) {
        uint64_t bits = UINT64_C(0x3ff0000000000000) + (random_bits() & UINT64_C(0x1fffffffffffff));
        failures += check(bits, candidate(bits, (int64_t)(random_bits() % 17) - 8));
        ++count;
        if (failures) break;
    }
    uint64_t edge[] = {UINT64_C(0x3ff0000000000000), UINT64_C(0x3ff0000000000001),
        UINT64_C(0x3fffffffffffffff), UINT64_C(0x4000000000000000),
        UINT64_C(0x400ffffffffffffe), UINT64_C(0x400fffffffffffff)};
    for (size_t i = 0; i < sizeof edge / sizeof *edge && !failures; ++i) {
        failures += check(edge[i], candidate(edge[i], -4096));
        failures += check(edge[i], candidate(edge[i], 4096));
        count += 2;
    }
    __asm__ volatile("msr fpcr, %0\nmsr fpsr, %1\nisb" : : "r"(old_fpcr), "r"(old_fpsr));
    printf("forced_correction_cases=%" PRIu64 " failures=%" PRIu64 " seed=a54ff53a5f1d36f1\n", count, failures);
    return failures != 0;
}
