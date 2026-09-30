import Mathlib
import Hilbert17thProblem.GabletonScratch
import Hilbert17thProblem.GabletonRealClosureBridge

namespace Hilbert17thProblem

open scoped BigOperators
open scoped Classical

noncomputable section

/-- THE pure remaining gate: if a real polynomial with real coefficients evaluates
strictly below zero at some point of an ordered real-closed extension of `ℝ`, then it is
strictly below zero at some real point.  This is the (constant-coefficient) Artin sign
transfer; installed Mathlib has no model-theoretic RCF elimination, so it must be built
algebraically (univariate sum-of-squares base case + induction). -/
theorem realClosed_negative_transfer
    (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (hq : q ≠ 0)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    [Algebra ℝ K]
    (a : Fin n → K) (hneg : MvPolynomial.aeval a q < 0) :
    ∃ x : Fin n → ℝ, q.eval x < 0 := by
  sorry

/-- The deep lemma follows from the pure transfer via the ordered real-closed extension
adapter:  `-(algebraMap q) ∈ O` places `algebraMap q` strictly in the negative cone of O,
which the order-preserving map into the real-closed extension `K` carries to strict
negativity at the variable-point of `K`, where the pure transfer produces the real point. -/
theorem corrected_deep_lemma_via_transfer
    (n : ℕ) (q : MvPolynomial (Fin n) ℝ) (hq : q ≠ 0)
    (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))) (hO : O.IsOrdering)
    (hneg : -(algebraMap (MvPolynomial (Fin n) ℝ)
        (FractionRing (MvPolynomial (Fin n) ℝ)) q) ∈ O) :
    ∃ x : Fin n → ℝ, q.eval x < 0 := by
  let F := FractionRing (MvPolynomial (Fin n) ℝ)
  let qF : F := algebraMap (MvPolynomial (Fin n) ℝ) F q
  obtain ⟨K, hfieldK, hlinK, hstrictK, hrck, algFK, hpos⟩ :=
    _root_.exists_orderPreserving_realClosedExtension_of_isOrdering (F := F) O hO
  letI : Field K := hfieldK
  letI : LinearOrder K := hlinK
  letI : IsStrictOrderedRing K := hstrictK
  letI : IsRealClosed K := hrck
  letI : Algebra F K := algFK
  letI : Algebra ℝ K :=
    RingHom.toAlgebra (i := (algebraMap F K).comp (algebraMap ℝ F))
  -- qF ≠ 0 (injective fraction-map image of nonzero q).
  have hqF0 : qF ≠ 0 := by
    have h := (IsFractionRing.injective (MvPolynomial (Fin n) ℝ) F).ne_iff.mpr hq
    simpa [qF] using h
  -- qF ∉ O, since qF ∈ O with -qF ∈ O would force qF = 0.
  have hqF_notO : qF ∉ O := by
    intro hqF_in
    exact hqF0 (RingPreordering.eq_zero_of_mem_of_neg_mem hqF_in hneg)
  have hnq_notO : -(-qF) ∉ O := by
    have : -(-qF) = qF := by ring
    rwa [this]
  -- Strictly positive in O at the point -qF.
  have hposK : 0 < algebraMap F K (-qF) :=
    hpos (-qF) (by exact ⟨hneg, hnq_notO⟩)
  have hltK : algebraMap F K qF < 0 := by
    exact neg_pos.mp (by
      rw [← map_neg]
      exact hposK)
  -- Point in K: the images of the canonical generators.
  let b : Fin n → K := fun i =>
    (algebraMap F K) ((algebraMap (MvPolynomial (Fin n) ℝ) F) (MvPolynomial.X i))
  -- The evaluation at `b` coincides with pushing `q` through F.
  have hkv : MvPolynomial.aeval b q < 0 := by
    have h : MvPolynomial.aeval b q = algebraMap F K qF := by
      rw [MvPolynomial.aeval_eq_eval₂Hom]
      change (MvPolynomial.eval₂Hom (algebraMap ℝ K) b) q =
        (algebraMap F K) ((algebraMap (MvPolynomial (Fin n) ℝ) F) q)
      rw [show (MvPolynomial.eval₂Hom (algebraMap ℝ K) b) =
          (algebraMap F K).comp (algebraMap (MvPolynomial (Fin n) ℝ) F) by
        apply MvPolynomial.ringHom_ext
        · intro r
          rw [MvPolynomial.eval₂Hom_C]
          change (algebraMap F K) (algebraMap ℝ F r) =
            (algebraMap F K) ((algebraMap (MvPolynomial (Fin n) ℝ) F) (MvPolynomial.C r))
          have hcr : (algebraMap (MvPolynomial (Fin n) ℝ) F) (MvPolynomial.C r) =
              algebraMap ℝ F r := by
            rw [IsScalarTower.algebraMap_eq ℝ (MvPolynomial (Fin n) ℝ) F]
            simp [MvPolynomial.algebraMap_eq]
          rw [hcr]
        · intro i
          simp [b]]
      rfl
    rwa [h]
  exact realClosed_negative_transfer n q hq b hkv

end

end Hilbert17thProblem
