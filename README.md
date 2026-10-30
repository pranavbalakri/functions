# Verified AArch64 square root

The binary32 implementation and exhaustive hardware tests are complete. The
end-to-end correctness proof is incomplete. Binary64 has not started, because it
must follow the binary32 proof. See [PROGRESS.md](PROGRESS.md).

`asm/sqrt32.S` exports `float verified_sqrtf(float)`. It contains 43 AArch64
instructions, uses only single-precision FP arithmetic, and contains no `FSQRT`.
Every one of the 2^32 binary32 input patterns matched hardware `FSQRT` in both
default-NaN modes on this Apple M4. Exhaustive testing is not the Lean proof.

## Intended theorem

For every binary32 input first, then every binary64 input, the assembled routine
returns the true square root rounded to nearest, ties to even, with gradual
underflow. Signed zeros, negative numbers, infinities, and NaNs have exactly the
Arm `FSQRT` result bits, including NaN quieting and payload selection under the
specified controls. The routine does not execute `FSQRT`.

This theorem is not yet proved. The current Lean results establish an integer
midpoint certificate's soundness, exclusion of half-integer square roots, the
exact residual-correction identity, and bounds on all 384 estimate-table entries.
They do not establish universal correctness of the routine.

## Algorithm and model

Positive subnormals are multiplied by 2^48. Integer exponent adjustment then
reduces every positive finite input to `z` in `[1,4)`, keeping track of an even
power of two. The core uses `FRSQRTE`, two `FRSQRTS` refinements, `s = z*y`,
`h = y/2`, `r = fma(-s,s,z)`, and `fma(r,h,s)`. The result's exponent is adjusted
back exactly. Special inputs take short branches. See
[the algorithm and proof status](docs/BINARY32.md).

The minimal Lean model uses exact integers and dyadics. It decodes the extracted
instruction words and models 64-bit general registers, 128-bit SIMD registers,
PC, NZCV, FPCR, and FPSR. Unsupported encodings and controls return `none`.
It represents a user-mode instruction fragment, with the test program based at
address zero; it does not model the operating system, virtual memory, or traps.
[Source provenance and scope](docs/ARM_MODEL.md) identify the original Arm
pseudocode archive and the implemented subset.

The tested controls are `FPCR=0` and `FPCR=0x02000000`: nearest-even, FZ/FIZ/AH/NEP
clear, exception traps masked, and default-NaN off/on. The model also permits
unrelated control bits that do not affect this instruction subset. These are
explicit model assumptions; no final theorem with weakened input coverage or
hidden control-state assumptions is claimed. The return-value goal does not
promise that the entire routine sets the same FPSR flags as `FSQRT`.

## Trust boundary

The intended theorem depends on:

1. The model faithfully expressing the selected Arm pseudocode, including
   decoding, rounding, special values, and control bits.
2. `clang` and code extraction/loading supplying the exact instruction bytes
   checked by the machine theorem and executed by hardware.
3. Lean's kernel and its standard logical foundations. The real-number lemmas
   use `propext`, `Classical.choice`, and `Quot.sound`. The estimate-table theorem
   has no axiom dependencies. No new axioms or admitted proofs are added.
4. The hardware matching that model and executing under the stated preconditions.

The C compiler, test harnesses, and Lean's compiled evaluator additionally affect
the empirical test evidence. They do not turn a passing test into a theorem.
No `native_decide` or `decide +native` has been used. Approval is required before
using either; the current proof audit introduces no native-computation axiom.

## Rebuild

Use an Apple Silicon Mac with Xcode command-line tools and elan installed from
the [official instructions](https://github.com/leanprover/elan#installation).
Lean is pinned to 4.35.0 and Mathlib to `v4.35.0`, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`; the manifest locks dependencies.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get Mathlib.Analysis.Real.Sqrt Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
make all
```

This builds the current proofs and checkers, runs `Audit.lean` with `--trust=0`,
compiles the C harnesses, and reassembles the routine to check its committed
machine bytes. `#print axioms` audits the named proof results. There is no
completed assembly theorem to rebuild yet.

`scripts/extract_code.py` reads the Mach-O `__text` section, rejects relocations
and `FSQRT`, and produces `asm/sqrt32.bin` and
`VerifiedSqrt/Arm/Sqrt32Code.lean`. `--check` compares fresh assembler output with
those files. Disassembly is written to `build/sqrt32.disasm`.

## Rerun tests

```sh
export PATH="$HOME/.elan/bin:$PATH"
make test
```

The test target runs:

- A read-only FPCR environment probe.
- Hardware-versus-Lean instruction checks: one million random tuples per FP
  instruction per DN setting, plus special values, estimate-bin boundaries,
  halfway cases, and correlated cancellation tests.
- Exact midpoint checks of the Lean core on all 16,777,216 normalized inputs.
- Hardware/algorithm/machine comparison on 1.1 million random inputs per DN
  setting, plus exponent boundaries and special values.
- All 4,294,967,296 input patterns against hardware `FSQRT`, once per DN setting.

The oracle files in `build/` take approximately 560 MiB. Tests set their own FPCR
and restore it afterward. Seeds and counts are printed. The current machine is
an Apple M4 running macOS 15.6 with Apple clang 17.0.0.
[Validation results](validation/binary32.md) record the tested code hash and counts.

## File boundaries

- `VerifiedSqrt/Float/`: reusable dyadics and real-number lemmas.
- `VerifiedSqrt/Arm/`: instruction semantics, decoding, execution, and extracted code.
- `VerifiedSqrt/Sqrt/`: square-root algorithm and certificate obligations.
- `tests/`: native C hardware oracles and exhaustive comparisons.
- `Check*.lean`: executable validation programs, not theorem declarations.

The historical [Phase 0 decision](docs/MODEL_DECISION.md) explains why LNSym and
the inspected Sail-to-Lean snapshot were not selected.
