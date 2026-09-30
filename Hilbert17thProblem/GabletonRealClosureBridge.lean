import Mathlib
import Hilbert17thProblem.GabletonScratch
import Hilbert17thProblem.RW.RealClosure.Final

set_option maxSynthPendingDepth 10 in

/--
Every ordering of a field `F` has a same-universe ordered real-closed
extension whose structure map sends elements strictly positive in the
ordering cone to strictly positive elements.
-/
theorem exists_orderPreserving_realClosedExtension_of_isOrdering
    {F : Type u} [Field F]
    (O : RingPreordering F) (hO : O.IsOrdering) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K)
      (_ : IsStrictOrderedRing K) (_ : IsRealClosed K) (_ : Algebra F K),
      ∀ x : F, (x ∈ O ∧ -x ∉ O) → 0 < algebraMap F K x := by
  letI hO' : O.IsOrdering := hO
  let hlin : LinearOrder F :=
    RatFuncWittLocalGlobal.RingPreordering.linearOrderOfIsOrdering O
  letI : LinearOrder F := hlin
  letI : PartialOrder F := hlin.toPartialOrder
  letI : IsStrictOrderedRing F := by
    change @IsStrictOrderedRing F _ hlin.toPartialOrder
    exact
      RatFuncWittLocalGlobal.RingPreordering.isStrictOrderedRingOfIsOrdering O
  obtain ⟨K, hField, hLinear, hStrict, hRealClosed, hAlg, hpos⟩ :=
    RatFuncWittLocalGlobal.OrderedRealClosure.orderedFieldRealClosedExtension_same_universe F
  refine ⟨K, hField, hLinear, hStrict, hRealClosed, hAlg, ?_⟩
  intro x hx
  apply hpos
  exact
    (RatFuncWittLocalGlobal.RingPreordering.zero_lt_linearOrderOfIsOrdering_iff O).2 hx
