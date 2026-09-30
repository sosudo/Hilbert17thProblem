import Mathlib
import Hilbert17thProblem.GabletonScratch
import Hilbert17thProblem.GabletonRealClosureBridge

namespace Hilbert17thProblem

open scoped BigOperators

noncomputable section

/-- From the ordering hypothesis we obtain a real-closed ordered field K, an ordered algebra
over F = FractionRing (MvPolynomial (Fin n) RR), and a coefficient ring hom psi : RR ->+* K
such that p evaluates strictly negatively at the coordinate point y in K.  This is the
"up" direction of the transfer: the ordering gives a K-point where p is strictly negative. -/
theorem ups_set_yields_K_point
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0)
    (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))) (hO : O.IsOrdering)
    (hneg : -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p) ∈ O) :
    ∃ (K : Type) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (_ : IsRealClosed K) (ψ : ℝ →+* K),
      ∃ y : Fin n → K, MvPolynomial.eval₂Hom ψ y p < 0 := by
  let F := FractionRing (MvPolynomial (Fin n) ℝ)
  have hne : algebraMap (MvPolynomial (Fin n) ℝ) F p ≠ 0 := by
    intro hEq
    have hp' : p = 0 := by
      apply IsFractionRing.injective (MvPolynomial (Fin n) ℝ) F
      simpa using hEq
    exact hp hp'
  have hin' : -(algebraMap (MvPolynomial (Fin n) ℝ) F p) ∈ O := by
    simpa [F] using hneg
  have hnot : algebraMap (MvPolynomial (Fin n) ℝ) F p ∉ O := by
    intro hpO
    have hz : algebraMap (MvPolynomial (Fin n) ℝ) F p = 0 :=
      RingPreordering.eq_zero_of_mem_of_neg_mem hpO (by simpa [F] using hneg)
    exact hne hz
  have hnegneg_not : -(-(algebraMap (MvPolynomial (Fin n) ℝ) F p)) ∉ O := by
    intro hd
    exact hnot ((neg_neg (algebraMap (MvPolynomial (Fin n) ℝ) F p)) ▸ hd)
  have hOO : -(algebraMap (MvPolynomial (Fin n) ℝ) F p) ∈ O ∧
      -(-(algebraMap (MvPolynomial (Fin n) ℝ) F p)) ∉ O := by
    constructor
    · exact hin'
    · exact hnegneg_not
  obtain ⟨K, hField, hLinear, hStrict, hReal, hAlg, hpos⟩ :=
    exists_orderPreserving_realClosedExtension_of_isOrdering (F := F) O hO
  letI : Field K := hField
  letI : LinearOrder K := hLinear
  letI : IsStrictOrderedRing K := hStrict
  letI : IsRealClosed K := hReal
  letI : Algebra F K := hAlg
  let ψ : ℝ →+* K := (algebraMap F K).comp ((algebraMap (MvPolynomial (Fin n) ℝ) F).comp MvPolynomial.C)
  have hKneg : (algebraMap F K (-(algebraMap (MvPolynomial (Fin n) ℝ) F p)) : K) > 0 :=
    hpos (-(algebraMap (MvPolynomial (Fin n) ℝ) F p)) hOO
  let y : Fin n → K := fun i => algebraMap F K (algebraMap (MvPolynomial (Fin n) ℝ) F (MvPolynomial.X i))
  have hev : MvPolynomial.eval₂Hom ψ y p = algebraMap F K (algebraMap (MvPolynomial (Fin n) ℝ) F p) := by
    change MvPolynomial.eval₂Hom ψ y p = _
    apply MvPolynomial.hom_eq_hom (f := MvPolynomial.eval₂Hom ψ y)
      (g := (algebraMap F K).comp (algebraMap (MvPolynomial (Fin n) ℝ) F))
    · ext r
      simp [ψ]
    · intro i
      simp [y]
  have hKneg' : (algebraMap F K (algebraMap (MvPolynomial (Fin n) ℝ) F p) : K) < 0 := by
    have h : -(algebraMap F K (algebraMap (MvPolynomial (Fin n) ℝ) F p)) > (0 : K) := by
      simpa using hKneg
    exact neg_pos.mp h
  refine ⟨K, hField, hLinear, hStrict, hReal, ψ, y, ?_⟩
  rw [hev]
  exact hKneg'

end

end Hilbert17thProblem
