# Functions

> This README describes the intended completed project. See [PROGRESS.md](PROGRESS.md) for its current implementation and proof status.

This repository contains Lean-verified AArch64 assembly implementations of
single- and double-precision square root for Apple Silicon, without using `FSQRT`.

The routines use a Markstein-style algorithm: start with Arm's reciprocal
square-root estimate, refine it through Newton iterations, then apply a residual
correction using fused multiply-add operations. Subnormal inputs are scaled by
an even power of two, and short branches handle zeros, negative numbers,
infinities, and NaNs.

## Correctness

For every input, the returned bits match the true square root rounded to nearest,
ties to even, with Arm-compatible behavior for signed zeros and special values.
The theorem assumes nearest-even rounding, gradual underflow, and the documented
[floating-point control settings](docs/ARM_MODEL.md).

Lean 4 and Mathlib verify the floating-point algorithm against exact real
arithmetic. A separate machine proof establishes that the assembled instruction
bytes execute according to that algorithm under a minimal Arm model transcribed
from the architecture pseudocode. Proofs contain no `sorry` or added axioms.

The routines are tested bit for bit against hardware `FSQRT`: exhaustively for
single precision and on billions of random inputs plus directed edge cases for
double precision. Instruction-level tests also compare the Lean model with
Apple Silicon hardware.

## Build and test

On an Apple Silicon Mac with Xcode command-line tools and Lean installed through
elan:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get Mathlib.Analysis.Real.Sqrt Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
make all
make test
```

Lean and Mathlib versions are pinned. `make all` builds the proofs, audits their
axiom dependencies, assembles the routines, and checks the extracted machine
code. `make test` runs the hardware comparisons.

## Trust

The trusted base consists of Lean's kernel and standard logical foundations,
the fidelity of the Arm model, the assembler and code-extraction process, and
the hardware matching the model. Hardware tests provide evidence for that
correspondence; the correctness argument is checked by Lean.

## Layout

- `asm/`: assembly routines and extracted machine code.
- `VerifiedSqrt/Float/`: reusable floating-point arithmetic and rounding lemmas.
- `VerifiedSqrt/Arm/`: instruction semantics, decoding, and machine-proof support.
- `VerifiedSqrt/Sqrt/`: square-root algorithms and correctness proofs.
- `tests/`: C hardware oracles and comparison harnesses.
- `validation/`: recorded test results.
