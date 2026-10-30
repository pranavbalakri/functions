# Progress

Updated 2026-10-29 (America/New_York).

- README describes the intended completed project. Actual status is recorded here.
- The user approved an exact integer midpoint correction after the Markstein/FMA
  steps. Binary32 now uses 67 AArch64 instructions, no FSQRT, and no double
  floating-point arithmetic. Subnormals use 2^48 scaling; the core uses [1,4).
- Proved the correction loop terminates within its supplied distance bound and
  returns the unique nearest integer square root. Its binary32 instance proves
  `coreCorrect32` for all 2^24 normalized inputs, without exhaustive proof
  computation or assumptions about the initial estimate's accuracy.
- `normalizedCore32_correct` proves strict distance minimization against every
  different finite binary32 value. Normalization/rescaling and special cases
  still need proofs before this becomes an all-input algorithm theorem.
- Reusable proofs cover exact dyadic arithmetic, nearest-even coefficient
  rounding, uniqueness, estimate-table bounds, and binary32 decoding.
- Machine lemmas now cover register writes/frame properties, symbolic decoding
  of correction instructions, exact fixed-width midpoint comparisons, and a
  three-instruction block executed from the extracted code. Whole-loop and
  whole-program composition remain open.
- The revised assembly passed both complete 2^32 hardware sweeps, 2,204,188
  machine/algorithm/hardware comparisons, all 16,777,216 core checks, 8,025,088
  integer/branch instruction comparisons, and 1,000,012 forced-correction tests.
  The unchanged FP model previously passed 17,077,262 comparisons.
- No new axioms, admitted proofs, or native proof computation. Axiom audits pass.
  [Validation](validation/binary32.md). [Proof details](docs/BINARY32.md).

Remaining: prove input normalization, rescaling, and special cases; prove machine
execution and termination for arbitrary permitted caller states and code
placement; finish the reusable binary32 rounding/encoding bridge. Additional
single-step tests for moves and arbitrary SIMD upper lanes remain.

The binary32 end-to-end theorem is incomplete. Do not start binary64 until it is
proved. Ask before native proof computation. Only the README Layout section may
be edited.
