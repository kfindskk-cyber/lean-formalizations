# Lean 4 formalizations — Ziping Guo

Machine-checked Lean 4 / Mathlib proofs of results from my published notes on Zenodo.
Every theorem below compiles with no `sorry` and depends only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Contents

| File | Source paper | Formalized statements |
|---|---|---|
| [`Formalizations/CrossTerms.lean`](Formalizations/CrossTerms.lean) | *Quadratic Cross Terms and a Complete Finite Factorisation Corridor* — [doi:10.5281/zenodo.23887893](https://doi.org/10.5281/zenodo.23887893) | If `a x² + b x + c = (p x + r)(q x + s)` for all real `x`, then `a = pq`, `b = ps + qr`, `c = rs`, and the cross terms `X = ps`, `Y = qr` satisfy `X + Y = b`, `XY = ac`, `(X − Y)² = b² − 4ac`. |
| [`Formalizations/PowerSumDefects.lean`](Formalizations/PowerSumDefects.lean) | *Sharp Linear Inequalities for Three Weighted Power-Sum Defects* — [doi:10.5281/zenodo.23887933](https://doi.org/10.5281/zenodo.23887933) | For `M_j = Σ wᵢ aᵢʲ` and the defect `G = M_{e+2k+r} M_e − M_{e+k+r} M_{e+k}`: the exact pairwise decomposition `2G = Σᵢ Σⱼ wᵢ wⱼ (aᵢaⱼ)ᵉ (aᵢᵏ − aⱼᵏ)(aᵢᵏ⁺ʳ − aⱼᵏ⁺ʳ)`, nonnegativity `G ≥ 0` for `w ≥ 0`, `a > 0`, and the remainder identity `1/P − 1/Q + (P − Q)/Q² = (P − Q)²/(PQ²)`. |

Main theorem names:

```
Formalizations.CrossTerms.coeffs_of_factorization
Formalizations.CrossTerms.cross_terms
Formalizations.PowerSumDefects.remainder_identity
Formalizations.PowerSumDefects.remainder_nonneg
Formalizations.PowerSumDefects.pair_term_nonneg
Formalizations.PowerSumDefects.two_G_eq_pair_sum
Formalizations.PowerSumDefects.G_nonneg
```

## Build and check

Requires [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.36.0-rc2`)
and the Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
git clone https://github.com/kfindskk-cyber/lean-formalizations.git
cd lean-formalizations
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean CheckAxioms.lean
```

Expected output of the last command:

```
'Formalizations.CrossTerms.coeffs_of_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'Formalizations.CrossTerms.cross_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Formalizations.PowerSumDefects.remainder_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Formalizations.PowerSumDefects.remainder_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Formalizations.PowerSumDefects.pair_term_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Formalizations.PowerSumDefects.two_G_eq_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Formalizations.PowerSumDefects.G_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Notes

The formal proofs were written with the help of Claude (Anthropic). Correctness does not rest on
that: every statement is checked by the Lean kernel, and `CheckAxioms.lean` shows exactly which
axioms each result uses.

More results from the same series of notes will be added here.

## License

Copyright (c) 2026 Ziping Guo. All rights reserved. The files are public so that the proofs can be
read, built and verified; see [`LICENSE`](LICENSE).
