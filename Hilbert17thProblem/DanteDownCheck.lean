import Mathlib
import Hilbert17thProblem.GabletonRealClosureBridge

namespace Hilbert17thProblem

noncomputable section

/-- Fully-verified "up direction": for any ordering O of K = FractionRing(MvPolynomial(Fin n) R)
carrying a nonzero `-p ∈ O`, the bridge produces a real-closed ordered extension L of K in which
`-p` is (strictly) positive. The entire remaining content of `corrected_deep_lemma` is the DOWN
direction: pushing positivity inside an arbitrary real-closed extension L of R down to a point of
R^n. That down-direction is precisely RCF model-completeness / Artin-Lang existential closure,
absent from installed Mathlib. -/
theorem upDirection_verified
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0)
    (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))) (hO : O.IsOrdering)
    (hneg : -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p) ∈ O) :
    ∃ (K : Type) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (_ : IsRealClosed K) (_ : Algebra (FractionRing (MvPolynomial (Fin n) ℝ)) K),
      0 < algebraMap (FractionRing (MvPolynomial (Fin n) ℝ)) K
          (-(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p)) := by
  rcases exists_orderPreserving_realClosedExtension_of_isOrdering O hO with
    ⟨K, hF, hLin, hSR, hRC, hAlg, hpos⟩
  refine ⟨K, hF, hLin, hSR, hRC, hAlg, ?_⟩
  let a : FractionRing (MvPolynomial (Fin n) ℝ) :=
    -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p)
  have ha1 : a ∈ O := by simpa [a] using hneg
  have ha2 : -a ∉ O := by
    intro hnot
    have hzero : a = 0 := RingPreordering.eq_zero_of_mem_of_neg_mem (P := O) ha1 hnot
    have : p = 0 := by
      have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) ℝ)
          (FractionRing (MvPolynomial (Fin n) ℝ))) :=
        IsFractionRing.injective (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
      have : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p = 0 := by
        rw [←neg_neg (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p)]
        exact neg_eq_zero.mpr (by simpa [a] using hzero)
      exact hinj (by simpa using this)
    exact hp this
  exact hpos a ⟨ha1, ha2⟩

end

end Hilbert17thProblem
