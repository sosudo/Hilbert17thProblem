import Mathlib
import Hilbert17thProblem.OrcaTransfer

namespace Hilbert17thProblem

noncomputable section

/-- `IsSumSq` is preserved by ring homomorphisms. -/
lemma map_isSumSq {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) {x : R} (hx : IsSumSq x) : IsSumSq (f x) := by
  induction hx with
  | zero => simp
  | sq_add a s ih =>
      rw [map_add, map_mul]
      exact IsSumSq.sq_add (f a) ih

/-- A sum-of-squares polynomial evaluates (via `aeval` at a point of a linearly ordered semiring)
to a nonnegative value. -/
lemma isSumSq_aeval_nonneg {K : Type*} [CommSemiring K] [LinearOrder K] [IsStrictOrderedRing K]
    [ExistsAddOfLE K] [Algebra ℝ K] {n : ℕ} {q : MvPolynomial (Fin n) ℝ} (x : Fin n → K)
    (hsq : IsSumSq q) : 0 ≤ MvPolynomial.aeval x q := by
  have hmap : IsSumSq (MvPolynomial.aeval x q) :=
    map_isSumSq ((MvPolynomial.aeval x : MvPolynomial (Fin n) ℝ →ₐ[ℝ] K).toRingHom) hsq
  exact IsSumSq.nonneg hmap

end

end Hilbert17thProblem
