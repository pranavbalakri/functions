# Functions

This repository contains Lean-verified assembly implementations of the square root function, using reciprocal square-root estimation, Newton's method, and residual corrections using multiplication and addition operations. 

## Layout

- `asm/`: assembly routines and extracted machine code.
- `VerifiedSqrt/Float/`: reusable floating-point arithmetic and rounding lemmas.
- `VerifiedSqrt/Arm/`: instruction semantics, decoding, and machine-proof support.
- `VerifiedSqrt/Sqrt/`: square-root algorithms and correctness proofs.
- `tests/`: C hardware oracles and comparison harnesses.
- `validation/`: recorded test results.
