# Theorem, trust, and reproduction

Both `verified_sqrtf` and `verified_sqrt` terminate and return the correctly
rounded square root for every input bit pattern, under the modeled AArch64
execution and floating-point controls. Positive finite inputs return the true
real square root rounded to nearest, ties to even. Both signed zeros and positive
infinity are preserved. Negative nonzero non-NaN inputs return the default quiet
NaN. Input NaNs are quieted with their sign and payload preserved when DN is
clear; DN selects the default quiet NaN.

The strongest theorems are `Arm.sqrt32_relocated_correct` and
`Arm.sqrt64_relocated_correct`. They execute the actual instruction words in
`Arm/Sqrt32Code.lean` and `Arm/Sqrt64Code.lean`, with arbitrary initial registers,
at any aligned load address. Their preconditions are:

- 32-entry general and SIMD register arrays, with PC at the code entry.
- FPCR round-to-nearest-even, FZ/FIZ/AH/NEP clear, and exception traps masked.
  DN is unrestricted; initial FPSR is unrestricted.
- X30 points outside the loaded instruction array. The model assumes accessible
  code and enabled FP/SIMD execution; it does not model virtual memory or privilege
  traps.

Binary32 preserves X5–X30, V6–V31, and FPCR; binary64 preserves X7–X30, V6–V31,
and FPCR. The specification concerns returned bits. It does not assert that the
routine accumulates the same FPSR exception flags as a single FSQRT instruction.

The instruction bounds are `12*2^23+61` and `20*2^52+75`. These conservative
termination bounds allow any initial approximation bit pattern. They are not
performance estimates. The Newton/FMA pipeline supplies the practical starting
point; exact integer midpoint correction supplies the rounding guarantee.

## Trusted boundary

1. **The formal instruction model and its transcription from Arm pseudocode.**
   The model is Lean code, not new axioms. Kernel checking proves statements
   about this model; it does not prove that the transcription describes every
   physical implementation. [Model provenance](ARM_MODEL.md) identifies the Arm
   archive and supported controls.
2. **The assembler and deployment correspondence.** Apple clang's assembler and
   linker, Apple's `otool`, and `scripts/extract_code.py` connect the assembly
   source and executable code to the instruction arrays. Rebuilding checks the
   extracted words, code hashes, absence of relocations, and absence of FSQRT.
   The machine proof itself runs the extracted words.
3. **Lean's kernel and its standard foundations.** `Audit.lean` reports only
   subsets of `propext`, `Classical.choice`, and `Quot.sound`. There are no new
   axioms, admitted goals, or native proof computation. Mathlib supplies
   kernel-checked real-number reasoning. Neither the C compiler nor Lean's
   native execution is used to discharge a correctness theorem.
4. **Hardware matching the model under these controls.** Differential tests on
   this Apple M4 supply evidence for this assumption. They compare compiled Lean
   definitions with actual instructions. The operating system and execution
   environment must preserve the stated controls and code/call conditions.

The test harnesses, compilers, and host runtime are trusted to report empirical
results accurately; those results are separate from the universal proofs.

## Rebuild

Use an Apple Silicon Mac with Xcode command-line tools (`xcode-select --install`)
and [elan](https://github.com/leanprover/elan). The repository pins Lean and
Mathlib 4.35.0, with dependency revisions in `lake-manifest.json`.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
make all
```

`make all` builds the proof and executable model checkers, runs
`lake env lean --trust=0 Audit.lean`, reassembles both routines, compares their
extracted instruction words with the Lean arrays, and builds the C harnesses.
The Mathlib cache avoids recompilation; the trust-zero audit checks the imported
proofs with Lean's kernel.

The libraries can also be checked without compiling the C harnesses:

```sh
lake build VerifiedSqrt
lake env lean --trust=0 Audit.lean
```

## Rerun hardware validation

```sh
make test
make test64
```

`make test` validates the binary32 model and correction, checks normalized-core
certificates, compares full machine executions, then tests all 2^32 encodings
once with DN clear and once with DN set. `make test64` validates the binary64
model and full machine execution, forces correction steps in both directions,
and tests one billion random inputs per DN setting plus directed edge cases.
Both targets use deterministic seeds and restore FPCR/FPSR after testing.
The binary model-test recordings consume several gigabytes under ignored `build/`.

Recorded counts, seeds, hardware, and outputs are in
[validation/binary32.md](../validation/binary32.md) and
[validation/binary64.md](../validation/binary64.md).
The mathematical proofs do not enumerate the input space. Finite estimate-table
lemmas use kernel computation; `native_decide` is not used.
