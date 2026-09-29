import Mathlib
import Hilbert17thProblem.Basic
import Hilbert17thProblem.GabletonScratch

namespace Hilbert17thProblem

open scoped BigOperators
open scoped Classical

noncomputable section

/-- The bridge: a globally nonnegative polynomial, canonically injected into the rational
function field, lies in every ordering. If this holds, `MainTheorem` follows. -/
theorem MainTheorem_of_orderings
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : IsGloballyNonnegative p)
    (bridge : ∀ O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ)), O.IsOrdering →
        algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p ∈ O) :
    ∃ m : ℕ, ∃ f : Fin m → FractionRing (MvPolynomial (Fin n) ℝ),
        algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p =
          ∑ i : Fin m, (f i) ^ 2 := by
  let K := FractionRing (MvPolynomial (Fin n) ℝ)
  letI : IsSemireal K := isSemireal_mvFractionRing (n := n)
  let a : K := algebraMap (MvPolynomial (Fin n) ℝ) K p
  have haSOS : a ∈ sumSqPreordering := by
    by_contra hnot
    obtain ⟨O, hO, hneg⟩ := exists_isOrdering_and_neg_mem (F := K) hnot
    have hpos : a ∈ O := bridge O hO
    have ha0 : a = 0 := RingPreordering.eq_zero_of_mem_of_neg_mem hpos hneg
    have hzeroSOS : a ∈ sumSqPreordering := by rw [ha0]; exact IsSumSq.zero
    exact hnot hzeroSOS
  have haIs : IsSumSq a := by simpa [sumSqPreordering] using haSOS
  obtain ⟨m, f, hf⟩ := (isSumSq_iff_exists_fin (R := K) (x := a)).mp haIs
  refine ⟨m, f, by simpa [a, K] using hf⟩

/-- THE single remaining hard lemma (the geometric / Artin transfer content): if a nonzero
polynomial `p` is strictly negative in some ordering `O` of the rational-function field, then
it takes a strictly negative value at some real point. This is the statement that
quantifier-free polynomial inequalities transfer down from real-closed extensions to `ℝ`
(real-closed fields are model-complete / existentially closed); it is not present in
installed Mathlib and must be developed (real-place/Baer-Krull specialization or RCF
sign-transfer). The `p ≠ 0` hypothesis is essential: at `p = 0` we have `-0 = 0 ∈ O` but no
real point evaluates strictly negative. -/
theorem corrected_deep_lemma
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0)
    (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))) (hO : O.IsOrdering)
    (hneg : -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p) ∈ O) :
    ∃ x : Fin n → ℝ, p.eval x < 0 := by
  sorry

/-- The bridge follows from the corrected deep lemma (covers `p = 0` separately). -/
theorem bridge_of_corrected_deep_lemma
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : IsGloballyNonnegative p)
    (hcp : ∀ (q : MvPolynomial (Fin n) ℝ), q ≠ 0 →
      ∀ (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))), O.IsOrdering →
        -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q) ∈ O →
        ∃ x : Fin n → ℝ, q.eval x < 0) :
    ∀ (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))), O.IsOrdering →
      algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p ∈ O := by
  intro O hO
  let K := FractionRing (MvPolynomial (Fin n) ℝ)
  let a : K := algebraMap (MvPolynomial (Fin n) ℝ) K p
  by_cases hpO : a ∈ O
  · exact hpO
  · by_cases hpz : p = 0
    · subst hpz
      simpa [a] using (zero_mem O : (0 : K) ∈ O)
    · have hneg : -a ∈ O := (mem_or_neg_mem O a).resolve_left hpO
      obtain ⟨x, hx⟩ := hcp p hpz O hO (by simpa [a] using hneg)
      have hle : 0 ≤ p.eval x := hp x
      exact False.elim (lt_irrefl 0 (hle.trans_lt hx))

/-- `MainTheorem` follows once the single deep lemma is proved; `p = 0` is discharged by
`bridge_of_corrected_deep_lemma` so the remaining work is exactly `corrected_deep_lemma`. -/
theorem MainTheorem_of_corrected_deep_lemma
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : IsGloballyNonnegative p)
    (hcp : ∀ (q : MvPolynomial (Fin n) ℝ), q ≠ 0 →
      ∀ (O : RingPreordering (FractionRing (MvPolynomial (Fin n) ℝ))), O.IsOrdering →
        -(algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) q) ∈ O →
        ∃ x : Fin n → ℝ, q.eval x < 0) :
    ∃ m : ℕ, ∃ f : Fin m → FractionRing (MvPolynomial (Fin n) ℝ),
        algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ)) p =
          ∑ i : Fin m, (f i) ^ 2 := by
  exact MainTheorem_of_orderings n p hp (bridge_of_corrected_deep_lemma n p hp hcp)

end

end Hilbert17thProblem
