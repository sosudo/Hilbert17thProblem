import Mathlib
import Hilbert17thProblem.GabletonScratch
import Hilbert17thProblem.RW.RealClosure.Final

set_option maxSynthPendingDepth 10 in
/-- Every ordering of a field `F` has a same-universe ordered real-closed
extension whose structure map sends strictly positive elements to strictly
positive elements. -/
theorem exists_orderPreserving_realClosedExtension_of_isOrdering
    {F : Type u} [Field F] (O : RingPreordering F) (hO : O.IsOrdering) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K)
      (_ : IsStrictOrderedRing K) (_ : IsRealClosed K) (_ : Algebra F K),
      ∀ x : F, 0 < x → 0 < algebraMap F K x := by
  haveI hO' : O.IsOrdering := hO
  haveI : LinearOrder F :=
    RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering O
  haveI : IsStrictOrderedRing F :=
    RatFuncWittLocalGlobal.RingPreordering.isStrictOrderedRingOfIsOrdering O
  exact RatFuncWittLocalGlobal.OrderedRealClosure.orderedFieldRealClosedExtension_same_universe F
