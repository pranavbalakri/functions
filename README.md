# Functions

This repository contains Lean-verified assembly implementations of the square root function, using reciprocal square-root estimation, Newton's method, and residual corrections using multiplication and addition operations. 

## Layout

- `asm/`: assembly routines and extracted machine code.
- `VerifiedSqrt/Float/`: reusable floating-point arithmetic and rounding lemmas.
- `VerifiedSqrt/Arm/`: instruction semantics, decoding, and machine proofs.
- `VerifiedSqrt/Sqrt/`: square-root algorithms and correctness proofs.
- `tests/`: C hardware oracles and comparison harnesses.
- `validation/`: recorded test results and kernel axiom audit.
- [docs/BUILD.md](docs/BUILD.md): precise theorem, assumptions, and reproduction guide.
- [PROGRESS.md](PROGRESS.md): completed milestones.

For every binary32 or binary64 input, the assembled routine returns the true
square root rounded to nearest, ties to even, with IEEE special-value handling.
The machine theorems assume nearest-even rounding, gradual underflow, masked
exceptions, ordinary Arm FP behavior, and valid code/call conditions. They cover
arbitrary initial registers and aligned code addresses.

The trusted boundary is the Arm instruction model, the assembler and code
extraction/deployment tools, Lean's kernel and standard foundational axioms, and
hardware matching the model. There are no admitted goals, new axioms, or native
proof computation. The [guide](docs/BUILD.md) specifies this boundary and the
exact NaN/control behavior.

With elan and Xcode command-line tools installed on Apple Silicon:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
make all
make test
make test64
```

`make all` rebuilds and audits the proofs and checks the assembled bytes.
`make test` exhausts binary32 under both DN settings; `make test64` runs two
billion random binary64 inputs plus edge cases. Both include model-versus-hardware
instruction checks.
