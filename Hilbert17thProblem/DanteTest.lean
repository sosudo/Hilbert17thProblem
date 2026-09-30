import Mathlib
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsOrderedRing K]

theorem mk_le_one_iff_nonneg (z : K) :
    (ArchimedeanClass.addValuation K).toValuation z ≤ 1 ↔ 0 ≤ ArchimedeanClass.mk z := by
  simp [AddValuation.toValuation_apply]
  simp [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]

theorem Finitely_iff_mk (z : K) :
    z ∈ Valuation.valuationSubring ((ArchimedeanClass.addValuation K).toValuation) ↔ 0 ≤ ArchimedeanClass.mk z := by
  rw [Valuation.mem_valuationSubring_iff]
  exact mk_le_one_iff_nonneg z
