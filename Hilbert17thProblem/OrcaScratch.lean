import Mathlib

noncomputable section

open scoped BigOperators

namespace Hilbert17thProblem

/-- If `p * q^2` is a sum of squares of polynomials (`s`), then `p` is a sum of squares of
rational functions `s_i / q` in the fraction ring. This is the standard "clearing denominators"
half of the Artin/Hilbert-17 statement: it converts the existence of a polynomial SOS multiple
`p * q^2` into the exact `Fin`-indexed shape demanded by `MainTheorem`. -/
lemma frac_sos_of_mul_sos {n : ℕ} {m : ℕ} (p q : MvPolynomial (Fin n) ℝ) (hq : q ≠ 0)
    (s : Fin m → MvPolynomial (Fin n) ℝ)
    (hsos : p * q ^ 2 = ∑ i : Fin m, (s i) ^ 2) :
    ∃ f : Fin m → FractionRing (MvPolynomial (Fin n) ℝ),
      algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p =
        ∑ i : Fin m, (f i) ^ 2 := by
  refine ⟨fun i => algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (s i) /
    algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q, ?_⟩
  have hqK : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q ≠ 0 := by
    have h := (Function.Injective.ne_iff (IsFractionRing.injective (MvPolynomial (Fin n) ℝ)
      (FractionRing (MvPolynomial (Fin n) ℝ)))).mpr hq
    simpa using h
  have hcong := congrArg (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))) hsos
  rw [map_mul] at hcong
  rw [map_sum] at hcong
  simp only [map_pow] at hcong
  calc
    algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p
        = (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p *
            (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q)^2) /
            (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q)^2 := by
          field_simp [hqK]
    _ = (∑ i : Fin m, (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (s i))^2) /
            (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q)^2 := by
          rw [hcong]
    _ = ∑ i : Fin m, (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (s i))^2 /
            (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q)^2 := by
          rw [Finset.sum_div]
    _ = ∑ i : Fin m, (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (s i) /
            algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q)^2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring


/-- The multivariate real polynomial ring `MvPolynomial (Fin n) ℝ` is semireal: `-1` is not a sum
of squares. Proof: exhibit the "evaluate at the origin and require a nonnegative value" preordering
and apply `RingPreordering.mem_of_isSumSq`, then contradict `0 ≤ -1`. This gives the base semireal
ring needed to set up the preordering/ordering machinery for the Artin-SOS development. -/
lemma isSemireal_mvPolynomial {n : ℕ} : IsSemireal (MvPolynomial (Fin n) ℝ) := by
  let pt : Fin n → ℝ := fun _ => 0
  let E : MvPolynomial (Fin n) ℝ →+* ℝ := MvPolynomial.eval pt
  let P : Set (MvPolynomial (Fin n) ℝ) := {r | 0 ≤ E r}
  let hP : RingPreordering (MvPolynomial (Fin n) ℝ) :=
    RingPreordering.mk' P
      (by intro x y hx hy; dsimp [P] at *; rw [map_add]; exact add_nonneg hx hy)
      (by intro x y hx hy; dsimp [P] at *; rw [map_mul]; exact mul_nonneg hx hy)
      (by intro x; dsimp [P]; rw [map_mul]; exact mul_self_nonneg (E x))
      (by dsimp [P]; rw [map_neg, map_one]; norm_num)
  constructor
  intro s hs h
  have hsP : 0 ≤ E s := by
    simpa [P, hP] using (RingPreordering.mem_of_isSumSq (P := hP) hs)
  have : E (1 + s) = 0 := by rw [h]; exact map_zero E
  rw [map_add, map_one] at this
  have hEs : E s = -1 := by linarith
  have : (0:ℝ) ≤ -1 := by rw [← hEs]; exact hsP
  norm_num at this

end Hilbert17thProblem
