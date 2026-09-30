import Mathlib
import Hilbert17thProblem.GabletonScratch
import Hilbert17thProblem.DanteUpSet

namespace Hilbert17thProblem

open scoped BigOperators

noncomputable section

section StdPart

variable {K : Type*} [Field K] [LinearOrder K] [IsOrderedRing K]

/-- An element of K is finite (bounded by a natural) iff it lies in the valuation subring
of the Archimedean-class additive valuation. This is Mathlib's real-place finite part. -/
def Finitely (z : K) : Prop :=
  z ∈ Valuation.valuationSubring ((ArchimedeanClass.addValuation K).toValuation)

theorem finitely_add {x y : K} (hx : Finitely x) (hy : Finitely y) : Finitely (x + y) :=
  add_mem hx hy

theorem finitely_mul {x y : K} (hx : Finitely x) (hy : Finitely y) : Finitely (x * y) :=
  mul_mem hx hy

theorem finitely_neg {x : K} (hx : Finitely x) : Finitely (-x) :=
  neg_mem hx

theorem finitely_zero : Finitely (0 : K) := zero_mem _
theorem finitely_one : Finitely (1 : K) := one_mem _

/-- z is finite iff its Archimedean class is nonnegative. -/
theorem Finitely_iff_mk (z : K) : Finitely z ↔ 0 ≤ ArchimedeanClass.mk z := by
  dsimp [Finitely]
  rw [Valuation.mem_valuationSubring_iff]
  simp [AddValuation.toValuation_apply]

theorem finitely_of_mk {z : K} (hz : 0 ≤ ArchimedeanClass.mk z) : Finitely z :=
  (Finitely_iff_mk z).2 hz

/-- An order-preserving image of a real constant is finite. -/
theorem finitely_ofReal {ψ : ℝ →+*o K} (r : ℝ) : Finitely (ψ r) := by
  by_cases hr : r = 0
  · subst hr; simp [finitely_zero]
  · apply finitely_of_mk
    have hmk0 : ArchimedeanClass.mk (ψ r) = 0 := by
      have h := ArchimedeanClass.mk_map_of_archimedean' (S := ℝ) (R := K) ψ hr
      rw [h, ArchimedeanClass.mk_eq_zero_of_archimedean (h := hr)]
    rw [hmk0]

/-- Standard part is additive on finite elements. -/
theorem stdPart_add_fin {x y : K} (hx : Finitely x) (hy : Finitely y) :
    ArchimedeanClass.stdPart (x + y) = ArchimedeanClass.stdPart x + ArchimedeanClass.stdPart y := by
  exact ArchimedeanClass.stdPart_add ((Finitely_iff_mk x).1 hx) ((Finitely_iff_mk y).1 hy)

/-- Standard part is multiplicative on finite elements. -/
theorem stdPart_mul_fin {x y : K} (hx : Finitely x) (hy : Finitely y) :
    ArchimedeanClass.stdPart (x * y) = ArchimedeanClass.stdPart x * ArchimedeanClass.stdPart y := by
  exact ArchimedeanClass.stdPart_mul ((Finitely_iff_mk x).1 hx) ((Finitely_iff_mk y).1 hy)

/-- Standard part of a real constant is the constant. -/
theorem stdPart_mapReal {ψ : ℝ →+*o K} (r : ℝ) :
    ArchimedeanClass.stdPart (ψ r) = r :=
  ArchimedeanClass.stdPart_map_real ψ r

/-- Standard part of a nonpositive finite element is nonpositive. -/
theorem stdPart_le_zero_of_le {z : K} (hz : Finitely z) (h : z ≤ 0) :
    ArchimedeanClass.stdPart z ≤ 0 := by
  have hm1 : z ∈ {x : K | 0 ≤ ArchimedeanClass.mk x} := by
    simpa using (Finitely_iff_mk z).1 hz
  have hm2 : (0 : K) ∈ {x : K | 0 ≤ ArchimedeanClass.mk x} := by
    simpa using (Finitely_iff_mk (0 : K)).1 finitely_zero
  have hmono := ArchimedeanClass.stdPart_monotoneOn hm1 hm2 h
  simpa [ArchimedeanClass.stdPart_zero] using hmono

/-- Polynomial evaluation at a finite K-point yields a finite element. -/
theorem eval_fin {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (ψ : ℝ →+*o K)
    (y : Fin n → K) (hy : ∀ i : Fin n, Finitely (y i)) :
    Finitely (MvPolynomial.eval₂Hom ψ.1 y p) := by
  refine MvPolynomial.induction_on
    (motive := fun q => Finitely (MvPolynomial.eval₂Hom ψ.1 y q)) p ?_ ?_ ?_
  · intro r; exact finitely_ofReal (ψ := ψ) r
  · intro q r ihq ihr
    rw [map_add]
  · intro q i ih
    rw [map_mul, MvPolynomial.eval₂Hom_X']
    exact finitely_mul ih (hy i)
  · intro q i ih; exact finitely_mul ih (hy i)

/-- Standard part commutes with polynomial evaluation on finite inputs:
`stdPart (eval2Hom ψ y p) = p.eval (stdPart ∘ y)`. -/
theorem stdPart_eval₂Hom {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (ψ : ℝ →+*o K)
    (y : Fin n → K) (hy : ∀ i : Fin n, Finitely (y i)) :
    ArchimedeanClass.stdPart (MvPolynomial.eval₂Hom ψ.1 y p) =
      p.eval (fun i : Fin n => ArchimedeanClass.stdPart (y i)) := by
  refine MvPolynomial.induction_on
    (motive := fun q => ArchimedeanClass.stdPart (MvPolynomial.eval₂Hom ψ.1 y q) =
      q.eval (fun i : Fin n => ArchimedeanClass.stdPart (y i))) p ?_ ?_ ?_
  · intro r
    rw [MvPolynomial.eval₂Hom_C]
    exact stdPart_mapReal r
  · intro q r ihq ihr
    rw [map_add, stdPart_add_fin (eval_fin q ψ y hy) (eval_fin r ψ y hy)]
    simp only [MvPolynomial.eval_add, ihq, ihr]
  · intro q i ih
    rw [map_mul]
    rw [stdPart_mul_fin (eval_fin q ψ y hy) (eval_fin (MvPolynomial.X i) ψ y hy)]
    rw [ih]
    rw [show ArchimedeanClass.stdPart (MvPolynomial.eval₂Hom ψ.1 y (MvPolynomial.X i)) = ArchimedeanClass.stdPart (y i) by rw [MvPolynomial.eval₂Hom_X']]
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]

/-- If p evaluates nonpositively at a finite K-point, it evaluates nonpositively at the
real point stdPart ∘ y. (Strict `< 0` would additionally require ruling out negative
infinitesimals; this is the clean place-theoretic transfer.) -/
theorem eval_nonpos_transfer {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (ψ : ℝ →+*o K)
    (y : Fin n → K) (hy : ∀ i : Fin n, Finitely (y i))
    (h : MvPolynomial.eval₂Hom ψ.1 y p ≤ 0) :
    p.eval (fun i : Fin n => ArchimedeanClass.stdPart (y i)) ≤ 0 := by
  rw [← stdPart_eval₂Hom p ψ y hy]
  exact stdPart_le_zero_of_le (eval_fin p ψ y hy) h

end StdPart

end

end Hilbert17thProblem
