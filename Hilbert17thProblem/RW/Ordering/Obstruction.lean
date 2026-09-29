/-
Ported from Mocho Go's `lean-ratfunc-witt-local-global` (commit 127e790),
Apache License 2.0. This file retains only the abstract ordered real-closed
extension principle needed for Hilbert's 17th problem.
-/
import Mathlib
import Hilbert17thProblem.RW.Ordering.Basic

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

/-- Every ordered field embeds order-preservingly into a real-closed ordered
field. -/
def OrderedFieldRealClosedExtension : Prop :=
  ∀ (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F],
    ∃ (K : Type v), ∃ (_ : Field K), ∃ (_ : LinearOrder K),
      ∃ (_ : IsStrictOrderedRing K), ∃ (_ : IsRealClosed K), ∃ (_ : Algebra F K),
        ∀ x : F, 0 < x → 0 < algebraMap F K x

end RatFunc
end RatFuncWittLocalGlobal
