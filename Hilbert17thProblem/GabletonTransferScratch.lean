import Mathlib
import Hilbert17thProblem.GabletonRealClosureBridge
import Hilbert17thProblem.GabletonCheckRealToK

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
  [Algebra ℝ K]

-- scratch helper: the canonical real scalar is the composition through the polynomial algebra.
example (r : ℝ) (x : Fin 0 → K) :
    (MvPolynomial.aeval x) (MvPolynomial.C ((algebraMap ℝ K) r)) = algebraMap ℝ K r := by
  simp
