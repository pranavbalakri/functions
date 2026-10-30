# Progress

Updated 2026-10-29 (America/New_York).

- README presents the intended completed project. Actual proof status is recorded
  here; the README's wording does not establish completion.

- Binary32 implementation: 43 AArch64 instructions, no FSQRT, no double-precision
  arithmetic. Subnormals use 2^48 scaling; the core operates in [1,4).
- Both full 2^32 hardware sweeps passed, one each for DN=0 and DN=1.
- Added the exact dyadic FP model, a decoder/executor for the used instruction
  forms, extracted machine bytes, hardware oracles, and reproducible Make targets.
- Retrieved and pinned the original Arm 2023-03 pseudocode archive.
- Kernel proofs cover estimate-table bounds, the correction identity, midpoint
  certificate soundness, and absence of half-integer square-root ties.
- Proved exact real semantics of dyadic addition, multiplication, and halving;
  nearest-even rounding for every integer right shift and every signed dyadic
  at a chosen exponent; rounding uniqueness; and the unique rounded significand
  implied by a square-root certificate. [Rounding proofs](docs/ROUNDING.md).
- No new axioms, admitted proofs, or native_decide. Axiom audits pass.
- Final `make test` passed: 17,077,262 instruction comparisons, all 16,777,216
  normalized-core certificates, 2,204,188 machine comparisons, and both full
  binary32 sweeps. [Validation record](validation/binary32.md).

Blocking proof work: connect the proved dyadic rounding rule to binary32 encoding,
exponent selection, overflow, and underflow;
prove CoreCorrect32 universally, prove scaling/special cases, and prove symbolic
machine-to-algorithm equality for arbitrary permitted caller states. A direct
kernel exhaustive proof hit the recursion limit. Passing executable checks are
not proofs. [Details](docs/BINARY32.md).

Phase 1's binary32 implementation/testing milestone is ready; the required
binary32 end-to-end proof is incomplete. Do not begin binary64 until it is proved.
Separate single-step integer/move/branch and SIMD upper-lane conformance tests also
remain. Ask before any native proof computation.
