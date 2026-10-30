# Binary64 validation record

Date: 2026-10-30 (America/New_York).

Machine: Apple M4, macOS 15.6, Apple clang 17.0.0, Lean 4.35.0.
The tests set nearest-even rounding, gradual underflow, and masked exceptions;
DN is tested both clear and set. They restore FPCR and FPSR on completion.

The routine has 81 instructions and 324 bytes, with no relocations or FSQRT.
Machine-code SHA-256:
`b63edd8d724d24ce60aa9432d880d52cb02a37e2dfd2e0d5d42069b64a48bfd0`.

```sh
export PATH="$HOME/.elan/bin:$PATH"
make test64
```

| Check | Cases | Result |
| --- | ---: | --- |
| FRSQRTE D model versus hardware | 4,154,894 | Matching result bits and FPSR |
| FRSQRTS D model versus hardware | 2,059,582 | Matching result bits and FPSR |
| FMUL D model versus hardware | 2,059,582 | Matching result bits and FPSR |
| Each of FMADD/FMSUB/FNMSUB/FNMADD D | 2,659,582 | Matching result bits and FPSR |
| Additional integer/branch forms | 25,129,600 | Matching registers, NZCV, and PC |
| Scalar moves/FP with complete SIMD state | 4,595,820 | Matching destination, FPSR, and NZCV |
| Full machine execution versus algorithm and hardware | 2,232,976 | Matching result bits and FPSR |
| Forced correction-loop starts | 1,000,012 | Matching hardware FSQRT |
| Assembly versus FSQRT, DN=0 | 1,007,352,509 | Zero bitwise mismatches |
| Assembly versus FSQRT, DN=1 | 1,007,352,509 | Zero bitwise mismatches |

The instruction oracle uses seed `6a09e667f3bcc909`, one million random operand
triples per operation per DN setting, all triples of 31 boundary values,
estimate-bin endpoints for every normal exponent, subnormal normalization
boundaries, and correlated FMA cancellation cases. Its 18,912,386 comparisons
run the compiled Lean definitions against recorded hardware results.

Each assembly run includes one billion random encodings. DN=0 uses seed
`243f6a8885a308d3`; DN=1 uses `a43f6a8885a308d3`. Each also checks the neighbors of
every positive normal power of two and its negative, subnormal powers of two,
one million random subnormals, the squares of integers 1 through 1,048,576 and
their neighbors, and 1,048,576 randomly generated rounded squares and their
neighbors. Explicit edge cases cover signed zeros, infinities, NaNs, the largest
double, and the normal/subnormal boundary. Comparisons are bitwise.

The integer oracle covers 25 additional forms with one million random tuples
per form, all pairs of 18 boundary values, and all 16 NZCV settings. The
scalar-state oracle uses 200,000 random tuples per instruction per DN setting
and all triples of 31 boundary values, with random SIMD upper bits and initial
flags. The machine oracle uses 1.1 million random inputs per DN setting plus
exponent and subnormal boundaries. Forced-correction tests start up to eight
steps on either side of the answer and up to 4,096 steps away on edge cases.
The test-only entry label adds no instructions to the production routine.

Outputs are preserved in [binary64.log](binary64.log). These tests are separate
from the universal algorithm and machine proofs. `algorithm64_correct`,
`machine_sqrt64_correct`, `machine64_correct`, and `sqrt64_relocated_correct`
prove the result specification for every input and both DN settings, including
arbitrary caller registers and aligned code addresses, without enumeration.

The final build checks the same production instruction bytes used by these
hardware tests. The trust-zero kernel audit covers both complete machine proofs,
including correction termination, exact 128-bit arithmetic, input preparation,
return, and relocation. Audited theorems depend only on subsets of `propext`,
`Classical.choice`, and `Quot.sound`; see [proof-audit.log](proof-audit.log).
