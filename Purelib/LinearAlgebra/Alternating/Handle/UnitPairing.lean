module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Vector.Unit
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

section
public section

/-!
# Integer weights of the actual transformed cycle rows

The inverse of the dual coordinate map is the transpose of the ordinary
basis change. Applying it to coordinate unit vectors therefore constructs
integer rows for linear combinations of cycles. Pairing those rows with the
original values evaluates the corresponding row of the final handle form.
-/

namespace Purelib.LinearAlgebra.Alternating.Handle.UnitPairing

open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K] {n : Nat}

/-- A left unit vector at an unused coordinate pairs to zero. -/
theorem handlePairing_unit_unused (raw : List (Handle.Basic.PivotIndices n)) (row : Fin n)
    (values : Data.Vector K n) (unused : row ∉ Handle.Basic.handleIndices raw) :
    Handle.Pairing.handlePairing raw (Unit.unitVector row) values = 0 := by
  induction raw with
  | nil => rfl
  | cons pair rest ih =>
      have first : pair.1 ≠ row := fun same => unused (by
        change row ∈ pair.1 :: pair.2 :: Handle.Basic.handleIndices rest
        rw [← same]; exact List.mem_cons_self)
      have last : pair.2 ≠ row := fun same => unused (by
        change row ∈ pair.1 :: pair.2 :: Handle.Basic.handleIndices rest
        rw [← same]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have tail : row ∉ Handle.Basic.handleIndices rest := fun member =>
        unused (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
      rw [Handle.Pairing.handlePairing, Unit.unitVector_apply, Unit.unitVector_apply, if_neg first, if_neg last, ih
        tail]
      ring1

open Purelib.LinearAlgebra.Alternating in
/-- A disjoint handle has the usual row signs: the first row reads the
second coordinate, and the second row reads the negative first coordinate. -/
theorem handlePairing_unit_handle (raw : List (Handle.Basic.PivotIndices n)) (disjoint : (Handle.Basic.handleIndices
  raw).Nodup)
    (pair : Handle.Basic.PivotIndices n) (member : pair ∈ raw) (values : Data.Vector K n) :
    Handle.Pairing.handlePairing raw (Unit.unitVector pair.1) values = values pair.2 ∧
      Handle.Pairing.handlePairing raw (Unit.unitVector pair.2) values = -values pair.1 := open Purelib in by
  induction raw with
  | nil => exact (List.not_mem_nil member).elim
  | cons head rest ih =>
      obtain ⟨firstClear, restUnique⟩ := List.pairwise_cons.mp disjoint
      obtain ⟨lastClear, tailUnique⟩ := List.pairwise_cons.mp restUnique
      have distinct : head.1 ≠ head.2 := fun same => firstClear _ List.mem_cons_self same
      have firstTail : head.1 ∉ Handle.Basic.handleIndices rest := fun found => firstClear _ (List.mem_cons_of_mem _
        found) rfl
      rcases Data.List.Membership.mem_cons.mp member with same | tailMember
      · subst pair
        constructor
        · rw [Handle.Pairing.handlePairing, Unit.unitVector_apply, Unit.unitVector_apply, if_pos rfl, if_neg (Ne.symm
            distinct),
            Handle.UnitPairing.handlePairing_unit_unused rest head.1 values firstTail]
          ring1
        · rw [Handle.Pairing.handlePairing, Unit.unitVector_apply, Unit.unitVector_apply, if_neg distinct, if_pos rfl,
            Handle.UnitPairing.handlePairing_unit_unused rest head.2 values (fun found => lastClear _ found rfl)]
          ring1
      · have coordinateMember (position : Fin n) (either : position = pair.1 ∨ position = pair.2) :
            position ∈ Handle.Basic.handleIndices rest := by
          apply Data.List.Flatten.mem_flatMap.mpr
          refine ⟨pair, tailMember, ?_⟩
          rcases either with same | same
          · rw [same]; exact List.mem_cons_self
          · rw [same]; exact List.mem_cons_of_mem _ List.mem_cons_self
        have zero (position : Fin n) (either : position = pair.1 ∨ position = pair.2) :
            Handle.Pairing.handlePairing (head :: rest) (Unit.unitVector position) values = Handle.Pairing.handlePairing
              rest (Unit.unitVector position) values := by
          have atFirst : head.1 ≠ position := fun same => firstTail (same.symm ▸ coordinateMember position either)
          have atLast : head.2 ≠ position := fun same => lastClear position (coordinateMember position either) same
          rw [Handle.Pairing.handlePairing, Unit.unitVector_apply, Unit.unitVector_apply, if_neg atFirst, if_neg atLast]
          ring1
        obtain ⟨first, last⟩ := ih tailUnique tailMember
        exact ⟨(zero _ (Or.inl rfl)).trans first, (zero _ (Or.inr rfl)).trans last⟩

end Purelib.LinearAlgebra.Alternating.Handle.UnitPairing

end

section
section
public section

/-! Coordinate-unit readings of the retained disjoint finite handle form. -/
namespace Purelib.LinearAlgebra.Alternating.Handle.UnitPairing

open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra.Vector

variable {n : Nat} {raw : List (Handle.Basic.PivotIndices n)}

/-- Exchanging the two integral vectors negates their handle pairing. -/
theorem handlePairing_skew (raw : List (Handle.Basic.PivotIndices n))
    (left right : Data.Vector Int n) :
    Handle.Pairing.handlePairing raw left right = -Handle.Pairing.handlePairing raw right left := by
  induction raw with
  | nil => rfl
  | cons head rest ih =>
      rw [Handle.Pairing.handlePairing, Handle.Pairing.handlePairing, ih]
      ring1

open Purelib.LinearAlgebra.Alternating
/-- Right unit vectors read the opposite handle coordinate with the reversed sign convention.

The first unit reads the negative last value and the last unit reads the first value. -/
theorem handlePairing_right_unit_handle (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (pair : Handle.Basic.PivotIndices n) (member : pair ∈ raw) (values : Data.Vector Int n) :
    Handle.Pairing.handlePairing raw values (Unit.unitVector pair.1) = -values pair.2 ∧
      Handle.Pairing.handlePairing raw values (Unit.unitVector pair.2) = values pair.1 := by
  have left := Handle.UnitPairing.handlePairing_unit_handle raw disjoint pair member values
  constructor
  · exact (Handle.UnitPairing.handlePairing_skew raw _ _).trans (congrArg Neg.neg left.1)
  · exact (Handle.UnitPairing.handlePairing_skew raw _ _).trans ((congrArg Neg.neg left.2).trans (neg_neg _))

/-- First-coordinate unit vectors pair to zero for disjoint handles. -/
theorem handlePairing_units_first_first (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Handle.Pairing.handlePairing raw (Unit.unitVector first.1 : Data.Vector Int n) (Unit.unitVector last.1)
      = 0 := by
  rw [(Handle.UnitPairing.handlePairing_unit_handle raw disjoint first firstMember _).1, Unit.unitVector_apply]
  exact if_neg (Ne.symm (Handle.Basic.handle_first_ne_last disjoint last first lastMember firstMember))

/-- Last-coordinate unit vectors pair to zero for disjoint handles. -/
theorem handlePairing_units_last_last (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Handle.Pairing.handlePairing raw (Unit.unitVector first.2 : Data.Vector Int n) (Unit.unitVector last.2)
      = 0 := by
  rw [(Handle.UnitPairing.handlePairing_unit_handle raw disjoint first firstMember _).2, Unit.unitVector_apply,
    if_neg (Handle.Basic.handle_first_ne_last disjoint first last firstMember lastMember), neg_zero]

/-- A first unit pairs with a last unit as the indicator that their handles coincide. -/
theorem handlePairing_units_first_last (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Handle.Pairing.handlePairing raw (Unit.unitVector first.1 : Data.Vector Int n) (Unit.unitVector last.2)
      =
      if first = last then 1 else 0 := by
  rw [(Handle.UnitPairing.handlePairing_unit_handle raw disjoint first firstMember _).1, Unit.unitVector_apply]
  by_cases same : first = last
  · rw [if_pos same, if_pos (congrArg Prod.snd same)]
  · rw [if_neg same, if_neg (fun equal => same ((Handle.Basic.handle_last_eq_last disjoint first last firstMember
      lastMember).mp equal))]

/-- A last unit pairs with a first unit as the negative indicator that their handles coincide. -/
theorem handlePairing_units_last_first (disjoint : (Handle.Basic.handleIndices raw).Nodup)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Handle.Pairing.handlePairing raw (Unit.unitVector first.2 : Data.Vector Int n) (Unit.unitVector last.1)
      =
      -(if first = last then 1 else 0) := by
  rw [Handle.UnitPairing.handlePairing_skew, Handle.UnitPairing.handlePairing_units_first_last disjoint last first
    lastMember firstMember]
  by_cases same : first = last
  · rw [if_pos same, if_pos same.symm]
  · rw [if_neg same, if_neg (Ne.symm same)]

end Purelib.LinearAlgebra.Alternating.Handle.UnitPairing

end

end
