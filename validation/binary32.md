# Binary32 validation record

Date: 2026-10-29 (America/New_York).

Machine: Apple M4, macOS 15.6, Apple clang 17.0.0, Lean 4.35.0, elan 4.2.4.
The initial FPCR probe returned zero. Test processes separately selected FPCR
zero and `0x02000000` and restored their previous environment on completion.

Machine-code SHA-256:
`e0c47d6d1eec8645b72741a183fc7d744220df5d4049786e2828a76982d5ba00`.
There are 67 instructions, 268 bytes, no relocations, and no `FSQRT`.

## Reproduction

```sh
export PATH="$HOME/.elan/bin:$PATH"
make test
```

The checks below were run through their individual Make targets and executables.
The latest build/audit log is in ignored `build/correction-validation.log`;
important outputs are preserved in [binary32.log](binary32.log). The unchanged FP
model retains its earlier 17,077,262-case validation; all core, machine, and full
input tests were rerun after adding the correction. Tests are distinct from
Lean proofs. `make test` reproduces the complete set.

| Check | Cases | Result |
| --- | ---: | --- |
| FRSQRTE S model versus hardware | 2,319,770 | Zero mismatches in result bits and FPSR |
| FRSQRTS S model versus hardware | 2,059,582 | Zero mismatches in result bits and FPSR |
| FMUL S model versus hardware | 2,059,582 | Zero mismatches in result bits and FPSR |
| FMADD S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| FMSUB S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| FNMSUB S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| FNMADD S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| Integer/branch model versus hardware | 8,025,088 | Zero register, NZCV, PC, or preserved-state mismatches |
| Scalar moves/FP with full SIMD operands (2026-10-30) | 4,595,820 | Zero destination, FPSR, or NZCV mismatches |
| Forced correction-loop starts | 1,000,012 | Zero mismatches with FSQRT |
| Exact integer certificates for the Lean core | 16,777,216 | All strict midpoint inequalities hold |
| Extracted-code execution versus algorithm and hardware | 2,204,188 | Zero mismatches in result bits and FPSR |
| Hardware FSQRT comparison, DN=0 | 4,294,967,296 | Zero bitwise mismatches |
| Hardware FSQRT comparison, DN=1 | 4,294,967,296 | Zero bitwise mismatches |

The FP instruction generator uses seed `6a09e667f3bcc909`, with one million random
operand tuples per instruction per DN setting. It additionally checks all triples
from 31 edge values, estimate-bin endpoints across every normal exponent,
subnormal normalization boundaries, and 2.4 million correlated FMA cancellation
cases. The total is 17,077,262 instruction comparisons.

The whole-routine generator uses seed `bb67ae8584caa73b`, with 1.1 million random
inputs per DN setting plus exponent boundaries, signed special values, and
subnormal boundaries. It compares output bits from the algorithm, the machine
model running the extracted words, and the hardware routine. It also compares
the machine model's FPSR with that routine's FPSR, not with FSQRT's flags.

The full binary32 sweeps include every power of two, every subnormal, every NaN
payload, the largest finite value, and every representable neighbor of a perfect
square. Their comparison is bitwise, not numerical equality of C floats.

The integer oracle tests X LSLV, UMULL, W/X CMP, B, B.EQ, B.LO, and B.HI, with
one million random tuples per operation plus every pair from 14 boundary values
and all 16 NZCV settings. Its seed is `3c6ef372fe94f82b`. The forced-correction
test uses seed `a54ff53a5f1d36f1`, deliberately starts above and below the answer,
and includes endpoint seeds millions of steps away. The test-only exported
correction label adds no instructions to the production routine.

The scalar-state oracle uses seed `510e527fade682d1`, with 200,000 random operand
tuples per instruction per DN setting and all triples from the same 31 edge
values. It tests FMOV W←S, FMOV S←W, FMOV S immediate, and the seven floating-point
operations listed above. Source and destination SIMD upper bits are randomized,
as are the initial X destination, NZCV, and writable FPSR flags. Hardware records
contain the complete 128-bit SIMD destination, 64-bit GPR destination, FPSR, and
NZCV after the instruction. The checker also verifies the model's preservation
of other registers and FPCR and its PC increment. Outputs are recorded in
[scalar-state.log](scalar-state.log). The assembly routine and instruction model
were unchanged, so the exhaustive sweeps were not repeated for this addition.

## Proof audit

`make all` and `lake env lean --trust=0 Audit.lean` passed. The estimate-table bound
has no axiom dependencies. The other audited results use subsets of `propext`,
`Classical.choice`, and `Quot.sound`. No `sorryAx` or native-computation axiom is
present. `algorithm32_correct` proves the algorithm for every binary32 input.
`machine_sqrt32_correct` proves machine execution from entry through return with
arbitrary register contents, supported controls, entry PC zero, and a return
address outside the code. `machine32_correct` proves the executable fixture's
result specification for every input and both DN settings. The 2026-10-30 audit
is recorded in [proof-audit.log](proof-audit.log). Relocation to arbitrary code
addresses remains open; see [the exact obligations](../docs/BINARY32.md).
