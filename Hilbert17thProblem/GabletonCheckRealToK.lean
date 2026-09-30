import Hilbert17thProblem.GabletonRealClosureBridge

noncomputable section

theorem algebraMap_real_nonneg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Algebra ℝ K] {r : ℝ} (hr : 0 ≤ r) : 0 ≤ algebraMap ℝ K r := by
  obtain ⟨s, hs⟩ := IsRealClosed.exists_eq_pow_of_nonneg (R := ℝ) hr (by norm_num : (2:ℕ) ≠ 0)
  have hsq : algebraMap ℝ K r = (algebraMap ℝ K s) ^ (2:ℕ) := by
    have hp : algebraMap ℝ K (s ^ (2:ℕ)) = (algebraMap ℝ K s) ^ (2:ℕ) := by
      rw [← map_pow]
    rw [hs, hp]
  rw [hsq]
  exact sq_nonneg _

theorem algebraMap_real_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Algebra ℝ K] {r : ℝ} (hr : 0 < r) : 0 < algebraMap ℝ K r := by
  have h := algebraMap_real_nonneg (K := K) hr.le
  rcases lt_or_eq_of_le h with h' | h'
  · exact h'
  · exfalso
    have hzero : algebraMap ℝ K r = 0 := h'.symm
    have hinj : Function.Injective (algebraMap ℝ K) := by
      exact Module.IsTorsionFree.to_faithfulSMul (R := ℝ) (A := K)
        |>.algebraMap_injective
    exact hr.ne' (hinj (by
      rw [map_zero]
      exact hzero))
