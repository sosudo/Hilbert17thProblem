import Mathlib

noncomputable section

open Polynomial

namespace GabletonRCF

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Every monic irreducible over an ordered real-closed field is linear or a positive
sum-of-two-squares quadratic. -/
theorem linear_or_positive_quadratic_of_monic_irreducible
    {f : R[X]} (hmonic : f.Monic) (hirr : Irreducible f) :
    f.natDegree = 1 ∨ ∃ a b : R, b ≠ 0 ∧ f = (X - C a) ^ 2 + C (b ^ 2) := by
  by_cases hdeg1 : f.natDegree = 1
  · exact Or.inl hdeg1
  have hpos : 0 < f.natDegree := hirr.natDegree_pos
  by_cases hdeg2 : f.natDegree ≤ 2
  · -- First derive the quadratic normal form, then show its constant difference is a square.
    have h2 : f.natDegree = 2 := by omega
    -- f is X^2 + B X + C.
    have hB : f.coeff 1 = - 2 * (f.coeff 1 / (-2)) := by
      field_simp
    have hC : f.coeff 0 = (f.coeff 1 / (-2))^2 + (f.coeff 0 - (f.coeff 1 / (-2))^2) := by ring
    have hf2 : f = X * X + C (f.coeff 1) * X + C (f.coeff 0) := by
      ext i
      rcases Nat.lt_or_ge i 3 with h | h
      · interval_cases i
        · simp
        · simp
        · have hc : f.coeff 2 = f.leadingCoeff := by
            simp only [leadingCoeff, h2]
          rw [hc, hmonic.leadingCoeff]
          simp
        · exact absurd h (by omega)
      · have hd : (X * X + C (f.coeff 1) * X + C (f.coeff 0)).natDegree ≤ 2 := by
          have h1 : (X * X).natDegree = 2 := by simp
          have h2 : (C (f.coeff 1) * X).natDegree ≤ 1 := by
            simpa using natDegree_C_mul_le (f.coeff 1) (X : R[X])
          have h3 : (C (f.coeff 0)).natDegree ≤ 0 := by simp
          omega
        rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega))]
    -- The shifted quadratic has no root, so its constant term is positive.
    set a : R := f.coeff 1 / (-2) with ha
    set d : R := f.coeff 0 - a ^ 2 with hd
    have hshift : f = (X - C a) ^ 2 + C d := by
      have expand : (X - C a : R[X]) ^ 2 + C d
          = X * X + C (-2 * a) * X + C (a * a + d) := by
        simp only [map_mul, map_neg, map_add]
        rw [show ((2:R)) = 1 + 1 by norm_num, C_add, C_1]
        ring
      rw [hf2, expand]
      have hC1 : C (f.coeff 1) = C (-2 * a) := by
        exact congrArg C hB
      have hC0 : C (f.coeff 0) = C (a * a + d) := by
        rw [hC]
        exact congrArg C (by ring)
      rw [hC1, hC0]
    -- Over a real-closed field, `d` must be a nonzero square: otherwise
    -- its negative square would give a root of the shifted irreducible quadratic.
    rcases IsRealClosed.isSquare_or_isSquare_neg (R := R) d with hsq | hnsq
    · obtain ⟨b, hb⟩ := hsq
      refine Or.inr ⟨a, b, ?_, ?_⟩
      · intro h0
        subst h0
        -- If `b = 0`, then `f` has the root `a`, contradicting irreducibility.
        exfalso
        have hroot : f.IsRoot a := by
          rw [hshift, hb]
          simp
          ring
        exact hirr.not_isRoot_of_natDegree_ne_one hdeg1 hroot
      · rw [hshift, hb]
        exact congrArg (fun x => (X - C a) ^ 2 + C x) (sq b).symm
    · exfalso
      obtain ⟨b, hb⟩ := hnsq
      have hroot : f.IsRoot (a + b) := by
        rw [hshift]
        change ((X - C a : R[X]) ^ 2 + C d).eval (a+b) = 0
        rw [show d = -(b*b) by linarith]
        simp only [eval_add, eval_pow, eval_sub, eval_C, eval_X]
        ring
      exact hirr.not_isRoot_of_natDegree_ne_one hdeg1 hroot
  · exfalso
    -- This branch needs the theorem that irreducibles over an RCF have degree ≤ 2.
    sorry


/-- A simple self-contained polynomial intermediate-value theorem for ordered RCFs. -/
theorem exists_root_of_nonpos_of_nonneg {f : R[X]} {a b : R} (hab : a ≤ b)
    (ha : f.eval a ≤ 0) (hb : 0 ≤ f.eval b) :
    ∃ c : R, a ≤ c ∧ c ≤ b ∧ f.eval c = 0 := by
  sorry

end GabletonRCF
