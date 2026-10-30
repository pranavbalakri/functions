# Binary32 validation record

Date: 2026-10-29 (America/New_York).

Machine: Apple M4, macOS 15.6, Apple clang 17.0.0, Lean 4.35.0, elan 4.2.4.
The initial FPCR probe returned zero. Test processes separately selected FPCR
zero and `0x02000000` and restored their previous environment on completion.

Machine-code SHA-256:
`11d3b708814cafc159f049efcb4cfc78eba1feec7e198952a1f7403300d3eee6`.
There are 43 instructions, 172 bytes, no relocations, and no `FSQRT`.

## Reproduction

```sh
export PATH="$HOME/.elan/bin:$PATH"
make test
```

The complete final run's log is in ignored `build/validation.log`; the important
output lines are preserved in [binary32.log](binary32.log). `make test` exited
successfully. These result counts do not make the tests into Lean theorems.

| Check | Cases | Result |
| --- | ---: | --- |
| FRSQRTE S model versus hardware | 2,319,770 | Zero mismatches in result bits and FPSR |
| FRSQRTS S model versus hardware | 2,059,582 | Zero mismatches in result bits and FPSR |
| FMUL S model versus hardware | 2,059,582 | Zero mismatches in result bits and FPSR |
| FMADD S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| FMSUB S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| FNMSUB S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| FNMADD S model versus hardware | 2,659,582 | Zero mismatches in result bits and FPSR |
| Exact integer certificates for the Lean core | 16,777,216 | All strict midpoint inequalities hold |
| Extracted-code execution versus algorithm and hardware | 2,204,188 | Zero mismatches in result bits and FPSR |
| Hardware FSQRT comparison, DN=0 | 4,294,967,296 | Zero bitwise mismatches |
| Hardware FSQRT comparison, DN=1 | 4,294,967,296 | Zero bitwise mismatches |

The instruction generator uses seed `6a09e667f3bcc909`, with one million random
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

## Proof audit

`make all` and `lake env lean --trust=0 Audit.lean` passed. The estimate-table bound
has no axiom dependencies. The other audited results use subsets of `propext`,
`Classical.choice`, and `Quot.sound`. No `sorryAx` or native-computation axiom is
present. The all-input correctness and machine-equivalence theorems are still
unproved; see [the exact open obligations](../docs/BINARY32.md).
