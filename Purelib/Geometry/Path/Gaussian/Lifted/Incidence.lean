module

public import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite oriented incidence of original lifted paths

These readings retain the coordinate and sheet of each original ordered vertex.
Their equality compares finite oriented incidence only. It supplies no equality
of sheet-transport maps or integrals on independently prepared cycles.
-/

public section
namespace Purelib.Geometry.Path.Gaussian.Lifted.Incidence

open Purelib.Data.Gaussian
open Purelib.Geometry.Path.Gaussian.Lifted.Basic

set_option genInjectivity false in
/-- The exact coordinate and original bounded sheet label of a lifted-path vertex. -/
structure Reading (sheets : Nat) where
  /-- The original Gaussian coordinate of the vertex. -/
  coordinate : Basic.Canonical
  /-- The original finite sheet index at that coordinate. -/
  sheet : Fin sheets
  deriving @[expose] DecidableEq

constructive_injectivity Reading

/-- Read both original fields of a lifted vertex without changing its bounded sheet index. -/
@[expose] def reading {sheets : Nat} (point : LiftedPoint sheets) : Reading sheets :=
  ⟨point.coordinate, point.sheet⟩

/-- Read every original vertex in its retained oriented order, including the last endpoint. -/
@[expose] def vertices {sheets : Nat} : {start finish : LiftedPoint sheets} →
    LiftedPath sheets start finish → List (Reading sheets)
  | _, _, .nil point => [reading point]
  | start, _, .cons _ rest => reading start :: vertices rest

/-- The original starting coordinate and sheet are the first retained vertex. -/
theorem vertices_head {sheets : Nat} {start finish : LiftedPoint sheets}
    (path : LiftedPath sheets start finish) : (vertices path).head? = some (reading start) := by
  cases path <;> rfl

set_option genInjectivity false in
/-- Retained unequal ordered incidence readings of two original lifted paths. -/
structure Mismatch {sheets : Nat} {leftStart leftFinish rightStart rightFinish : LiftedPoint sheets}
    (left : LiftedPath sheets leftStart leftFinish) (right : LiftedPath sheets rightStart rightFinish) where
  /-- The retained original left incidence sequence. -/
  first : List (Reading sheets)
  /-- The retained original right incidence sequence. -/
  second : List (Reading sheets)
  /-- The first sequence reads the exact original left path. -/
  first_eq : first = vertices left
  /-- The second sequence reads the exact original right path. -/
  second_eq : second = vertices right
  /-- The actual ordered coordinate/sheet readings differ. -/
  different : first ≠ second

constructive_injectivity Mismatch

/-- A retained mismatch disproves precisely equality of the two finite oriented incidence sequences. -/
theorem Mismatch.not_equal {sheets : Nat} {leftStart leftFinish rightStart rightFinish : LiftedPoint sheets}
    {left : LiftedPath sheets leftStart leftFinish} {right : LiftedPath sheets rightStart rightFinish}
    (mismatch : Mismatch left right) : vertices left ≠ vertices right := by
  intro same
  exact mismatch.different (mismatch.first_eq.trans (same.trans mismatch.second_eq.symm))

/-- Check original finite oriented incidence, returning its exact equality or retained mismatching readings. -/
@[expose] def compare {sheets : Nat} {leftStart leftFinish rightStart rightFinish : LiftedPoint sheets}
    (left : LiftedPath sheets leftStart leftFinish) (right : LiftedPath sheets rightStart rightFinish) :
    Except (Mismatch left right) {_witness : Unit // vertices left = vertices right} :=
  let first := vertices left
  let second := vertices right
  if same : first = second then .ok ⟨(), same⟩ else .error ⟨first, second, rfl, rfl, same⟩

/-- Unequal original starting sheets prevent an oriented-incidence identity despite matching coordinates. -/
theorem not_equal_of_startSheet_ne {sheets : Nat}
    {leftStart leftFinish rightStart rightFinish : LiftedPoint sheets}
    (left : LiftedPath sheets leftStart leftFinish) (right : LiftedPath sheets rightStart rightFinish)
    (different : leftStart.sheet ≠ rightStart.sheet) : vertices left ≠ vertices right := by
  intro same
  have heads := congrArg List.head? same
  rw [vertices_head, vertices_head] at heads
  have readings : reading leftStart = reading rightStart := Option.some.inj heads
  exact different (congrArg Reading.sheet readings)

/-- Unequal original starting coordinates prevent equality of oriented vertex readings. -/
theorem not_equal_of_startCoordinate_ne {sheets : Nat}
    {leftStart leftFinish rightStart rightFinish : LiftedPoint sheets}
    (left : LiftedPath sheets leftStart leftFinish) (right : LiftedPath sheets rightStart rightFinish)
    (different : leftStart.coordinate ≠ rightStart.coordinate) : vertices left ≠ vertices right := by
  intro same
  have heads := congrArg List.head? same
  rw [vertices_head, vertices_head] at heads
  have readings : reading leftStart = reading rightStart := Option.some.inj heads
  exact different (congrArg Reading.coordinate readings)

end Purelib.Geometry.Path.Gaussian.Lifted.Incidence
end
