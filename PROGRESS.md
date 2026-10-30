# Progress

Updated 2026-10-30 (America/New_York).

- README describes the intended completed project. Actual status is recorded here.
- Binary32 uses 67 AArch64 instructions: reciprocal-root estimation, two Newton
  refinements, FMA residual correction, and the user-approved exact integer
  midpoint correction. No FSQRT or double floating-point arithmetic. Subnormals
  use exact 2^48 scaling, and the core input lies in [1,4).
- `algorithm32_correct` proves `SqrtSpec32` for every input and both DN settings:
  nearest-even square root for positive finite values, preserved signed zeros
  and positive infinity, and exact NaN results.
- `machine_sqrt32_correct` now proves execution of every path of the extracted
  code, from entry through RET. It allows arbitrary initial register contents,
  assumes supported FP controls, 32-entry register arrays, entry PC zero, and a
  return address outside the code. It proves termination within 12*2^23+61
  instructions and preserves X5–X30, V6–V31, and FPCR.
- `sqrt32_relocated_correct` extends this result to every aligned code address,
  with the same controls, return-address requirement, bound, and register frame.
  It proves translation of every extracted opcode and composes these steps;
  address arithmetic is modulo 2^64, including wraparound.
- `machine32_correct` proves the executable machine fixture returns the specified
  result for all 2^32 encodings and both DN settings. No enumeration is used in
  the all-input proof. The correction proof needs no estimate accuracy bound.
- Assembly passed both full 2^32 hardware sweeps, 2,204,188 machine comparisons,
  16,777,216 core certificates, 8,025,088 integer/branch comparisons, and
  1,000,012 forced-correction tests. FP operations passed 17,077,262 comparisons;
  another 4,595,820 scalar-state cases cover moves, arbitrary SIMD upper bits,
  existing FPSR flags, and NZCV.
- No admitted goals, new axioms, or native proof computation. Kernel axiom audits
  pass. [Validation](validation/binary32.md). [Proof details](docs/BINARY32.md).

Remaining: add single-step tests for the remaining integer forms, then implement
and prove binary64. General overflow/underflow rounding lemmas
are future reusable work; binary32 needs only the exact scaling cases proved.

Ask before native proof computation. Only the README Layout section may be edited.
