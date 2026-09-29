/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Hilbert17thProblem.RW.RealClosure.Quadratic.Order
import Hilbert17thProblem.RW.RealClosure.Odd.Maximal
import Hilbert17thProblem.RW.Ordering.Obstruction
import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# The maximal ordered intermediate field is real closed

The quadratic and odd-degree maximality bridges provide exactly the two
premises required by `IsRealClosed.of_linearOrderedField`.
-/

namespace RatFuncWittLocalGlobal
namespace OrderedRealClosure

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A maximal ordered intermediate field is real closed. -/
theorem maximal_isRealClosed
    (M : Intermediate F) (hmax : IsMax M) : IsRealClosed M.carrier :=
  IsRealClosed.of_linearOrderedField
    (fun {_} hx => nonnegative_isSquare_of_isMax (F := F) M hmax hx)
    (fun {_} hp => exists_root_of_odd_natDegree_of_isMax (F := F) M hmax hp)

/-- Every ordered field has a real-closed ordered extension in the same universe.

The extension is the carrier of a maximal ordered intermediate field in an
algebraic closure; its algebra map is the canonical intermediate-field map.
-/
theorem orderedFieldRealClosedExtension_same_universe :
    RatFunc.OrderedFieldRealClosedExtension.{u, u} := by
  intro F _instField _instLinearOrder _instStrictOrdered
  obtain ⟨M, _hbase, hmax, _halgebraic, hpos⟩ :=
    exists_maximal_ordered_algebraic_extension (F := F)
  let _ : IsRealClosed M.carrier := maximal_isRealClosed (F := F) M hmax
  exact ⟨M.carrier, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hpos⟩

end OrderedRealClosure
end RatFuncWittLocalGlobal
