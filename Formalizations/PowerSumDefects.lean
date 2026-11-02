/-
Copyright (c) 2026 Ziping Guo. All rights reserved.
Authors: Ziping Guo

Formalized results from
  Ziping Guo, "Sharp Linear Inequalities for Three Weighted Power-Sum Defects",
  Zenodo, 2026. https://doi.org/10.5281/zenodo.23887933
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted power-sum defects: pairwise decomposition and nonnegativity

For weights `wᵢ` and bases `aᵢ` put `M_j = ∑ᵢ wᵢ aᵢʲ`.  The paper studies the defect
`G_k = M_{m+k+r} M_{m-k} - M_{m+r} M_m` (`k ≤ m`).  Writing `e = m - k`, all exponents become
sums of natural numbers:

  `G = M_{e+2k+r} · M_e - M_{e+k+r} · M_{e+k}`.

Main results:

* `two_G_eq_pair_sum`: the exact pairwise decomposition
  `2 G = ∑ᵢ ∑ⱼ wᵢ wⱼ (aᵢ aⱼ)ᵉ (aᵢᵏ - aⱼᵏ)(aᵢᵏ⁺ʳ - aⱼᵏ⁺ʳ)`;
* `G_nonneg`: `G ≥ 0` for nonnegative weights and positive bases;
* `remainder_identity`, `remainder_nonneg`: the rational remainder identity
  `1/P - 1/Q + (P - Q)/Q² = (P - Q)²/(P Q²)` used for the finite remainders.
-/

@[expose] public section

open Finset

namespace Formalizations.PowerSumDefects

/-! ### Two elementary facts -/

/-- Remainder identity: for `P, Q > 0`,
`1/P - 1/Q + (P - Q)/Q² = (P - Q)²/(P Q²)`. -/
theorem remainder_identity (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) :
    1 / P - 1 / Q + (P - Q) / Q ^ 2 = (P - Q) ^ 2 / (P * Q ^ 2) := by
  field_simp
  ring

theorem remainder_nonneg (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) :
    0 ≤ 1 / P - 1 / Q + (P - Q) / Q ^ 2 := by
  rw [remainder_identity P Q hP hQ]
  positivity

/-- Each pair term is nonnegative: for `a, b > 0`,
`(aᵏ - bᵏ)(aᵏ⁺ʳ - bᵏ⁺ʳ) ≥ 0`. -/
theorem pair_term_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (k r : ℕ) :
    0 ≤ (a ^ k - b ^ k) * (a ^ (k + r) - b ^ (k + r)) := by
  rcases le_total a b with h | h
  · apply mul_nonneg_of_nonpos_of_nonpos
    · exact sub_nonpos.mpr (pow_le_pow_left₀ ha.le h k)
    · exact sub_nonpos.mpr (pow_le_pow_left₀ ha.le h (k + r))
  · apply mul_nonneg
    · exact sub_nonneg.mpr (pow_le_pow_left₀ hb.le h k)
    · exact sub_nonneg.mpr (pow_le_pow_left₀ hb.le h (k + r))

/-! ### Power sums and the defect -/

variable {n : ℕ}

/-- Weighted power sum `M_j = ∑ᵢ wᵢ aᵢʲ`. -/
noncomputable def M (w a : Fin n → ℝ) (j : ℕ) : ℝ := ∑ i, w i * a i ^ j

/-- Defect `G = M_{e+2k+r} M_e - M_{e+k+r} M_{e+k}`. -/
noncomputable def G (w a : Fin n → ℝ) (e k r : ℕ) : ℝ :=
  M w a (e + 2 * k + r) * M w a e - M w a (e + k + r) * M w a (e + k)

lemma M_mul_M (w a : Fin n → ℝ) (p q : ℕ) :
    M w a p * M w a q = ∑ i, ∑ j, w i * a i ^ p * (w j * a j ^ q) := by
  unfold M
  exact Finset.sum_mul_sum _ _ _ _

/-- Pairwise decomposition (symmetric form):
`2 G = ∑ᵢ ∑ⱼ wᵢ wⱼ (aᵢ aⱼ)ᵉ (aᵢᵏ - aⱼᵏ)(aᵢᵏ⁺ʳ - aⱼᵏ⁺ʳ)`. -/
theorem two_G_eq_pair_sum (w a : Fin n → ℝ) (e k r : ℕ) :
    2 * G w a e k r =
      ∑ i, ∑ j, w i * w j * (a i * a j) ^ e *
        ((a i ^ k - a j ^ k) * (a i ^ (k + r) - a j ^ (k + r))) := by
  have h : 2 * G w a e k r =
      (M w a (e + 2 * k + r) * M w a e + M w a e * M w a (e + 2 * k + r)) -
      (M w a (e + k) * M w a (e + k + r) + M w a (e + k + r) * M w a (e + k)) := by
    unfold G; ring
  rw [h, M_mul_M, M_mul_M, M_mul_M, M_mul_M, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Nonnegativity: with nonnegative weights and positive bases, `G ≥ 0`. -/
theorem G_nonneg (w a : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 < a i) (e k r : ℕ) :
    0 ≤ G w a e k r := by
  have h2 : 0 ≤ 2 * G w a e k r := by
    rw [two_G_eq_pair_sum]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    have hij : 0 ≤ w i * w j * (a i * a j) ^ e := by
      have := ha i; have := ha j; have := hw i; have := hw j; positivity
    exact mul_nonneg hij (pair_term_nonneg (a i) (a j) (ha i) (ha j) k r)
  linarith

end Formalizations.PowerSumDefects
