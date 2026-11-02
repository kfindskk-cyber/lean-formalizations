import Formalizations

/-! Every main theorem should depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no extra axioms.
Run with `lake env lean CheckAxioms.lean`. -/

#print axioms Formalizations.CrossTerms.coeffs_of_factorization
#print axioms Formalizations.CrossTerms.cross_terms
#print axioms Formalizations.PowerSumDefects.remainder_identity
#print axioms Formalizations.PowerSumDefects.remainder_nonneg
#print axioms Formalizations.PowerSumDefects.pair_term_nonneg
#print axioms Formalizations.PowerSumDefects.two_G_eq_pair_sum
#print axioms Formalizations.PowerSumDefects.G_nonneg
