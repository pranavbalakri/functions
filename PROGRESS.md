# Progress

Updated 2026-10-30 (America/New_York).

- README describes the intended completed project. Actual status is recorded here.
- The user approved an exact integer midpoint correction after the Markstein/FMA
  steps. Binary32 now uses 67 AArch64 instructions, no FSQRT, and no double
  floating-point arithmetic. Subnormals use 2^48 scaling; the core uses [1,4).
- Proved the correction loop terminates within its supplied distance bound and
  returns the unique nearest integer square root. Its binary32 instance proves
  `coreCorrect32` for all 2^24 normalized inputs, without exhaustive proof
  computation or assumptions about the initial estimate's accuracy.
- `algorithm32_correct` proves the complete binary32 algorithm satisfies
  `SqrtSpec32` for every input and both DN settings: nearest-even square root for
  positive finite values, preserved signed zeros/infinity, and exact NaN bits.
  The proof includes exact 2^48 subnormal scaling and exponent rescaling.
- Reusable proofs cover exact dyadic arithmetic, nearest-even coefficient
  rounding, uniqueness, estimate-table bounds, and binary32 decoding.
- `normalized_correction_loop_correct` proves the actual extracted correction
  loop terminates within 12*2^23+10 instructions and returns the algorithm's
  corrected significand. It preserves every GPR except X0/X2, all SIMD registers,
  FPCR and FPSR.
- `correction_return_correct` connects that loop to result encoding and RET.
  It proves the returned S0 bits equal the algorithm's rescaled result, preserves
  the caller's link register, and requires a return address outside the code.
- `normalized_body_correct` connects all instructions from byte offset 100
  through RET: Markstein/FMA evaluation, exact loop setup, correction, and result
  encoding. `normalized_body_rounds` proves nearest-even rounding for the scaled
  normalized input. It permits arbitrary SIMD contents and needs no estimate
  accuracy assumption. GPRs X4–X30, SIMD registers V6–V31, and FPCR are preserved.
- `normalization_return_correct` extends that result back to byte offset 68.
  The signed arithmetic shift, parity mask, exponent packing, and scalar move
  produce exactly the algorithm's normalized input and saved scale exponent.
- The revised assembly passed both complete 2^32 hardware sweeps, 2,204,188
  machine/algorithm/hardware comparisons, all 16,777,216 core checks, 8,025,088
  integer/branch instruction comparisons, and 1,000,012 forced-correction tests.
  The unchanged FP model previously passed 17,077,262 comparisons.
- Another 4,595,820 hardware comparisons cover scalar moves and floating-point
  instructions with arbitrary SIMD upper bits, existing FPSR flags, and NZCV.
- No new axioms, admitted proofs, or native proof computation. Axiom audits pass.
  [Validation](validation/binary32.md). [Proof details](docs/BINARY32.md).

Remaining: connect input classification and subnormal scaling (offsets 0–64)
to the proved normalization/body; cover arbitrary code placement.
General overflow/underflow rounding lemmas are future reusable work; the corrected
algorithm does not need them.

The binary32 end-to-end theorem is incomplete. Do not start binary64 until it is
proved. Ask before native proof computation. Only the README Layout section may
be edited.
