/-
Copyright (c) 2026 Ziping Guo. All rights reserved.
Authors: Ziping Guo

Formalized result from
  Ziping Guo, "Quadratic Cross Terms and a Complete Finite Factorisation Corridor",
  Zenodo, 2026. https://doi.org/10.5281/zenodo.23887893
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Cross terms of a factored quadratic

If `a x² + b x + c = (p x + r)(q x + s)` holds for every real `x`, then the two cross terms
`X = p s` and `Y = q r` satisfy

* `X + Y = b`,
* `X * Y = a * c`,
* `(X - Y)² = b² - 4 a c`.

This is the discriminant identity used at the start of the paper.  The coefficients are
recovered from the values of the polynomial identity at `x = 0, 1, -1`; no polynomial-ring
machinery is needed.
-/

@[expose] public section

namespace Formalizations.CrossTerms

/-- Comparing coefficients: the identity at `x = 0, 1, -1` already forces
`a = p q`, `b = p s + q r`, `c = r s`. -/
theorem coeffs_of_factorization {a b c p q r s : ℝ}
    (h : ∀ x : ℝ, a * x ^ 2 + b * x + c = (p * x + r) * (q * x + s)) :
    a = p * q ∧ b = p * s + q * r ∧ c = r * s := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * h2 - h0
  · linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * h2
  · linear_combination h0

/-- The cross terms `X = p s`, `Y = q r` of a factorization have sum `b`, product `a c`,
and squared difference equal to the discriminant `b² - 4 a c`. -/
theorem cross_terms {a b c p q r s : ℝ}
    (h : ∀ x : ℝ, a * x ^ 2 + b * x + c = (p * x + r) * (q * x + s)) :
    p * s + q * r = b ∧ (p * s) * (q * r) = a * c ∧
      (p * s - q * r) ^ 2 = b ^ 2 - 4 * a * c := by
  obtain ⟨ha, hb, hc⟩ := coeffs_of_factorization h
  subst ha hb hc
  exact ⟨rfl, by ring, by ring⟩

end Formalizations.CrossTerms
