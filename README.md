# ktv-swap-lean-comparator

Independent comparator verification, via `leanprover/comparator`, that
`guanyangwang/ktv-swap-lean` proves the fixed-margin lazy swap-chain spectral
gap bound from Theorem 2.2 of *Spectral Gap for the Binary Fixed-Margin Swap
Chain*.

## What to audit

Audit `ChallengeDefs.lean` and `Challenge.lean`. `ChallengeDefs.lean` imports only Mathlib and defines:

- binary matrices with prescribed row and column sums;
- the ordered-distinct rectangle proposal;
- the `1/2`-lazy swap operator;
- the finite rational Poincare/Dirichlet-form spectral-gap predicate.

`Challenge.lean` then states that the lazy swap operator has gap at least

```text
1 / choose(|Col|, 2) * 1 / choose(|Row|, 2).
```

If you believe `ChallengeDefs.lean` and `Challenge.lean` say the intended theorem, then a successful comparator run certifies that the `ktv-swap-lean` library proves it using only
the axioms `propext`, `Quot.sound`, and `Classical.choice`.

`Solution.lean` imports `ChallengeDefs.lean` and the KTV proof library, then bridges the Mathlib-only statement to the library theorem by an explicit equivalence of state spaces. Comparator rebuilds both modules in a
sandbox, exports them with `lean4export`, compares the statements, checks the
axioms, and replays the proof through the Lean kernel.

## Run it

```bash
./verify.sh
```

This is intended for Linux. It downloads pinned `comparator`, `lean4export`,
and `landrun`, fetches the Mathlib cache, and runs the check. Expected final
output:

```text
Your solution is okay!
```

On macOS, real `landrun` is not available; use a Linux machine or CI for the
trusted sandboxed comparator run.
