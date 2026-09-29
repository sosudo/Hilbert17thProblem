import Mathlib
import Hilbert17thProblem.Basic
import Hilbert17thProblem.GabletonScratch

namespace Hilbert17thProblem

open scoped BigOperators
open scoped Classical

noncomputable section

/-- In any preordering of a field every square is in the cone. -/
theorem sq_mem_ordering (n : ℕ)
    (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ)))
    (r : FractionRing (MvPolynomial (Fin n) ℝ)) : r ^ 2 ∈ O := by
  exact O.mem_of_isSquare ⟨r, by ring⟩

/-- A nonnegative real constant maps into every ordering cone. -/
theorem nonneg_real_mem_ordering (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))) :
    algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
      (MvPolynomial.C r) ∈ O := by
  obtain ⟨s, hs⟩ := IsRealClosed.exists_eq_pow_of_nonneg (R := ℝ) hr (by norm_num : 2 ≠ 0)
  have hpoly : (MvPolynomial.C r : MvPolynomial (Fin n) ℝ) = (MvPolynomial.C s : MvPolynomial (Fin n) ℝ) ^ 2 := by
    rw [hs]
    exact RingHom.map_pow (MvPolynomial.C (R := ℝ)) s 2
  have hmap : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C r)
      = (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C s)) ^ 2 := by
    rw [hpoly]
    simp [pow_two]
  rw [hmap]
  exact sq_mem_ordering n O (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C s))

/-- Restriction of any ordering to the embedded copy of ℝ is the standard order on ℝ. -/
theorem real_mem_order_iff_nonneg (n : ℕ)
    (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ)))
    (hO : O.IsOrdering) (r : ℝ) :
    (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
      (MvPolynomial.C r)) ∈ O ↔ 0 ≤ r := by
  constructor
  · intro hm
    by_contra hnot
    have hrlt : r < 0 := lt_of_not_ge hnot
    have hnonneg : 0 ≤ -r := by linarith
    have hmempos : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
        (MvPolynomial.C (-r)) ∈ O := nonneg_real_mem_ordering n (-r) hnonneg O
    have hnegmap : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
        (MvPolynomial.C (-r)) =
        -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
          (MvPolynomial.C r)) := by simp
    have hnegmem : -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
        (MvPolynomial.C r)) ∈ O := by simpa [hnegmap] using hmempos
    have hzero : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
        (MvPolynomial.C r) = 0 :=
      RingPreordering.eq_zero_of_mem_of_neg_mem hm hnegmem
    have hzero' : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
        (MvPolynomial.C r) =
        algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C 0) := by
      simpa using hzero
    have hCr : MvPolynomial.C r = MvPolynomial.C 0 :=
      IsFractionRing.injective (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) hzero'
    have hr0 : r = 0 := (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ).injective hCr
    linarith
  · intro h0r
    exact nonneg_real_mem_ordering n r h0r O

/-- "Finite element infra": if `x` is finite (bounded above by a real `M` in the cone
sense `C M - x ∈ O`), then the reals below `x` (`x - C r ∈ O`) are bounded above by `M`, so
the standard part is real (Dedekind completeness of ℝ). -/
theorem finite_element_real_cut
    (n : ℕ) (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ)))
    (hO : O.IsOrdering)
    (x : FractionRing (MvPolynomial (Fin n) ℝ))
    (hx : ∃ M : ℝ, 0 ≤ M ∧
      (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C M) - x) ∈ O) :
    (∃ a : ℝ, ∀ r : ℝ, (x - algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C r)) ∈ O
      → r ≤ a) := by
  rcases hx with ⟨M, hM0, hxleM⟩
  refine ⟨M, ?_⟩
  intro r hr
  have hsum : (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C M) - x) +
      (x - algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C r)) ∈ O :=
    O.add_mem hxleM hr
  have hcompute : (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C M) - x) +
      (x - algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C r)) =
      algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C (M - r)) := by
    have h1 : (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C M) - x) +
        (x - algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C r)) =
        algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C M) -
          algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C r) := by
      ring_nf
    rw [h1]
    rw [← RingHom.map_sub]
    simp
  have hmem : algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.C (M - r)) ∈ O := by
    simpa [hcompute] using hsum
  have hnonneg : 0 ≤ M - r := (real_mem_order_iff_nonneg n O hO (M - r)).mp hmem
  linarith

end

end Hilbert17thProblem
