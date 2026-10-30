# Progress

Completed 2026-10-30 (America/New_York).

- Binary32 and binary64 assembly, algorithm proofs, complete machine proofs,
  relocation proofs, and hardware validation are complete. Both routines avoid
  FSQRT and use the approved exact midpoint correction after Newton/FMA steps.
- `algorithm32_correct` and `algorithm64_correct` prove the independent
  nearest-even specifications for every input encoding and either DN setting,
  including subnormals, signed zeros, infinities, negative inputs, and NaNs.
- `machine_sqrt32_correct` and `machine_sqrt64_correct` prove termination and
  the same results from the extracted instructions, with arbitrary caller
  registers under the stated FP controls. `sqrt32_relocated_correct` and
  `sqrt64_relocated_correct` cover every aligned code address.
- Binary32 passed two full 2^32 input sweeps, 17,077,262 FP instruction checks,
  33,103,488 integer/branch checks, 4,595,820 scalar-state checks, 2,204,188
  machine comparisons, and 1,000,012 forced-correction tests.
- Binary64 passed 2,014,705,018 FSQRT comparisons, including two billion random
  inputs; 18,912,386 FP instruction checks; 25,129,600 integer/branch checks;
  4,595,820 scalar-state checks; 2,232,976 machine comparisons; and 1,000,012
  forced-correction tests.
- Final `make all` passed, including the trust-zero kernel axiom audit and
  reassembly/extraction checks. Production bytes match the hardware-tested
  versions. Audited theorems use only the standard `propext`, `Classical.choice`,
  and `Quot.sound` foundations. No admitted goals, new axioms, or native proof
  computation were used.
- [Theorem, trust, and reproduction](docs/BUILD.md).
  [Binary32 proof](docs/BINARY32.md). [Binary64 proof](docs/BINARY64.md).
  [Binary32 validation](validation/binary32.md).
  [Binary64 validation](validation/binary64.md).

No open obligations remain for the requested square-root result. General
floating-point overflow/underflow rounding theorems and tighter timing bounds
are possible future work; neither is an assumption or missing step in these
proofs. The Arm model's correspondence to hardware remains an explicit trusted
boundary, supported by the recorded differential tests.

Only the README Layout section was updated.
