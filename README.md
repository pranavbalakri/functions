# Verified AArch64 square root

Phase 0 only: model selection and Lean/Mathlib setup. There is no square-root
routine or machine correctness theorem yet. See [PROGRESS.md](PROGRESS.md).

The selected approach is a minimal Lean model transcribed from Arm pseudocode.
LNSym lacks the required FP arithmetic; the inspected Sail-to-Lean snapshot lacks
usable instruction definitions and uses inexact arithmetic for exact reals.
[The model decision](docs/MODEL_DECISION.md) records pinned revisions, source
evidence, and the required hardware validation.

## Intended theorem

For every binary32 input first, then every binary64 input, the AArch64 routine
returns exactly the correctly rounded square root with nearest-even rounding and
flush-to-zero disabled, without executing `FSQRT`. For nonnegative finite values
this means rounding the true real square root once. Signed zeros, negative
values, infinities, and NaNs must have the same result bits as Arm `FSQRT`, including
NaN quieting and payload behavior under the specified floating-point controls.
The precise remaining machine-state preconditions must be written explicitly.

This is the target, not a theorem proved by this checkout. The only current
theorem, `VerifiedSqrt.real_sqrt_square`, checks that Mathlib real-square-root
reasoning works. It says nothing about floating-point rounding or assembly.

## Trust boundary

The eventual result will depend on:

1. The instruction model being a faithful transcription of the selected Arm
   pseudocode, including decoding, FP controls, special values, and rounding.
2. `clang`'s assembler and the extraction/loading process supplying the exact
   instruction bytes used in the machine theorem and executable.
3. Lean's kernel and its standard logical foundations. The setup theorem uses
   `propext`, `Classical.choice`, and `Quot.sound`; these are existing Lean/Mathlib
   foundations, not new FP axioms.
4. This Apple Silicon hardware behaving according to the modeled architecture
   and controls when executing those bytes.

Random testing supplies evidence for item 4, not a proof. A C compiler, test
harness, and Lean's compiled evaluator affect empirical test results, not the
logical theorem. Check imported proof artifacts as well as local declarations
when auditing the proof; ordinary cached builds alone do not establish that audit.
No `native_decide` has been used. Introducing it requires prior user approval.

## Rebuild the current setup

The project pins Lean 4.35.0 and Mathlib tag `v4.35.0`, resolved to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Dependency revisions are locked in
`lake-manifest.json`. Lean is installed through elan in `~/.elan` on this Mac;
shell startup files were not changed.

On a new machine, install elan using the
[official instructions](https://github.com/leanprover/elan#installation).
Then, from this repository:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lean --version
lake exe cache get Mathlib.Analysis.Real.Sqrt
lake build
lake env lean --trust=0 VerifiedSqrt/Setup.lean
```

The last command checks with imported-module trust disabled and prints the setup
theorem's axiom dependencies. Both it and `lake build` passed on this Mac. There
is no assembly proof to rebuild yet.

## Rerun the current hardware check

On an AArch64 Mac with the Xcode command-line tools:

```sh
mkdir -p build
clang -std=c11 -O2 -Wall -Wextra -Werror tests/fp_environment.c -o build/fp_environment
./build/fp_environment
```

On this Apple M4 with macOS 15.6 and Apple clang 17.0.0, it reported:

```text
FPCR=0x0000000000000000
RMode=0 FZ=0 DN=0
exception_enables=0x00 AH=0 FIZ=0
```

This reads the controls of the test process; it does not establish the controls
of every future caller. Instruction-model conformance tests, the full binary32
sweep, and the billions-of-input binary64 comparison are pending. Their commands
will be added when those tests exist.

## Planned separation

General rounding lemmas will live in `VerifiedSqrt/Float/`, instruction semantics
and machine proof glue in `VerifiedSqrt/Arm/`, and square-root-specific algorithm
and machine proofs in `VerifiedSqrt/Sqrt/`. The next step is implementing and
validating the selected model, after the Phase 0 report.
