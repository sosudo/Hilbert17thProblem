import Mathlib.Algebra.Order.Ring.StandardPart
import Mathlib.FieldTheory.IsRealClosed.Basic
import Hilbert17thProblem.GabletonRealClosureBridge

/-!
# Standard-part (real-place) infrastructure for the Artin-Lang sign transfer

`corrected_deep_lemma` needs: an ordering `O` of the rational-function field
`F = FractionRing (MvPolynomial (Fin n) ℝ)` with `-p ∈ O` yields a real point
`a : Fin n → ℝ` with `p.eval a < 0`.  The route is to embed `F` into a real-closed
ordered `L` (adapter), then specialize the generator images via the standard part
(real place) to `ℝ`, using Mathlib's `ArchimedeanClass.stdPart`.

This file records the two foundational, build-verified building blocks:
  1. an order embedding `ℝ →+*o L` of the reals into a real-closed ordered extension,
  2. the standard-part sign-transfer lemmas.
-/

open scoped Classical
open ArchimedeanClass

namespace Hilbert17thProblem

/-- An order-embedding of `ℝ` into a real-closed ordered extension `L` whose
scalar-respect map sends strictly positive reals to strictly positive elements. -/
def realEmbedding_of_realClosed
    (L : Type) [Field L] [LinearOrder L] [IsStrictOrderedRing L] [IsRealClosed L]
    [Algebra ℝ L] (h : ∀ r : ℝ, 0 < r → 0 < algebraMap ℝ L r) : ℝ →+*o L where
  toFun := algebraMap ℝ L
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp
  monotone' := by
    intro a b hab
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hpos : 0 ≤ algebraMap ℝ L (b - a) := by
      rcases (le_iff_lt_or_eq.mp hba) with hlt | heq
      · exact le_of_lt (h (b - a) hlt)
      · rw [← heq]; simp
    simpa [map_sub, sub_nonneg] using hpos

/-- Standard-part sign transfer: a real strictly below the standard part of a finite
element is carried strictly below the element itself. -/
theorem lt_of_lt_stdPart' {L : Type} [Field L] [LinearOrder L] [IsOrderedRing L]
    (f : ℝ →+*o L) {x : L} (hx : 0 ≤ mk x) {r : ℝ} (h : r < stdPart x) :
    f r < x :=
  ArchimedeanClass.lt_of_lt_stdPart f hx h

/-- Standard-part sign transfer, upper side: a real strictly above the standard part. -/
theorem stdPart_lt_of_lt' {L : Type} [Field L] [LinearOrder L] [IsOrderedRing L]
    (f : ℝ →+*o L) {x : L} (hx : 0 ≤ mk x) {r : ℝ} (h : stdPart x < r) :
    x < f r :=
  ArchimedeanClass.lt_of_stdPart_lt f hx h

end Hilbert17thProblem
