import Mathlib

namespace Hilbert17thProblem

open scoped BigOperators

noncomputable section

-- MP direction: fold IsSumSq structure into an explicit Fin-sum.
lemma isSumSq.forward (R : Type*) [AddCommMonoid R] [Mul R]
    {s : R} (h : IsSumSq s) :
    ∃ (m : ℕ), ∃ f : Fin m → R,
      s = ∑ i : Fin m, (f i) * (f i) := by
  induction h with
  | zero =>
      refine ⟨0, fun i => Fin.elim0 i, ?_⟩
      simp
  | sq_add a hs ih =>
      rcases ih with ⟨m, f, hf⟩
      let g : Fin (m + 1) → R := Fin.cases a f
      refine ⟨m + 1, g, ?_⟩
      rw [Fin.sum_univ_succ]
      simp [g, ← hf]


-- MPR direction: explicit Fin-sum of products is a sum of squares.
lemma isSumSq.backward (R : Type*) [AddCommMonoid R] [Mul R]
    (m : ℕ) (f : Fin m → R) :
    IsSumSq (∑ i : Fin m, (f i) * (f i)) := by
  induction m with
  | zero =>
      simpa using (IsSumSq.zero : IsSumSq (0 : R))
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have hterm : IsSumSq ((f 0) * (f 0)) := by
        simpa using IsSumSq.sq_add (f 0) (IsSumSq.zero (R := R))
      have htail :
          IsSumSq (∑ i : Fin m, (f (Fin.succ i)) * (f (Fin.succ i))) :=
        ih (fun i => f i.succ)
      exact IsSumSq.add hterm htail

theorem isSumSq_iff_exists_fin
    (R : Type*) [AddCommMonoid R] [Mul R] (s : R) :
    IsSumSq s ↔
      ∃ (m : ℕ), ∃ f : Fin m → R,
        s = ∑ i : Fin m, (f i) * (f i) := by
  constructor
  · exact fun h => isSumSq.forward R h
  · rintro ⟨m, f, rfl⟩
    exact isSumSq.backward R m f

end

end Hilbert17thProblem
