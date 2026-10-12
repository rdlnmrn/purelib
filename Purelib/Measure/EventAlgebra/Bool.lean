module
import Purelib.Measure.Distribution.Mixture.Basic
public import Purelib.Measure.EventAlgebra.Basic

section
@[expose] public section

/-!
# Explicit finite event algebras

An event algebra here is finite presented data: an explicitly enumerated code
type, an executable interpretation of each code as a Boolean event, and
certified Boolean operations.  No powerset, sigma-algebra, generated closure,
or enumeration of an ambient carrier is formed.
-/

namespace Purelib.Measure

/-! ## A concrete four-event algebra on `Bool` -/

/-- Enumerate all four Boolean events using their values at false and true as exact codes.

Complement, union and intersection act coordinatewise on those retained truth tables, with complete enumeration and
evaluation certificates. -/
def boolEventAlgebra : EventAlgebra Bool where
  Code := Bool × Bool
  codes := [(false, false), (false, true), (true, false), (true, true)]
  listed code := by
    rcases code with ⟨first, second⟩
    cases first with
    | false =>
        cases second with
        | false => exact List.Mem.head _
        | true => exact List.Mem.tail _ (List.Mem.head _)
    | true =>
        cases second with
        | false => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
        | true => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  codeEq left right := inferInstance
  evaluate code item := if item then code.2 else code.1
  empty := (false, false)
  univ := (true, true)
  complement code := (!code.1, !code.2)
  union left right := (left.1 || right.1, left.2 || right.2)
  intersection left right := (left.1 && right.1, left.2 && right.2)
  evaluate_empty item := by cases item <;> rfl
  evaluate_univ item := by cases item <;> rfl
  evaluate_complement event item := by cases item <;> rfl
  evaluate_union left right item := by cases item <;> rfl
  evaluate_intersection left right item := by cases item <;> rfl

end Purelib.Measure

end
