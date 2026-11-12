module

public import Init.Prelude
public import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Approximation.Schedule.Common

set_option genInjectivity false in
/-- A deterministic common finite schedule. Every request is advanced to explicit source, target, and comparison
indices, and each index stream is monotone. -/
structure CommonSchedule where
  /-- The source stage selected for each request. -/ sourceIndex : Nat -> Nat
  /-- The target stage selected for each request. -/ targetIndex : Nat -> Nat
  /-- The comparison stage selected for each request. -/ comparisonIndex : Nat -> Nat
  /-- The selected source stage meets the requested floor. -/ source_ge : forall request, request ≤ sourceIndex request
  /-- The selected target stage meets the requested floor. -/ target_ge : forall request, request ≤ targetIndex request
  /-- The selected comparison stage meets the requested floor. -/ comparison_ge : forall request, request ≤
    comparisonIndex request
  /-- Source stages increase monotonically with requests. -/ source_mono : forall {first second}, first ≤ second ->
    sourceIndex first ≤ sourceIndex second
  /-- Target stages increase monotonically with requests. -/ target_mono : forall {first second}, first ≤ second ->
    targetIndex first ≤ targetIndex second
  /-- Comparison stages increase monotonically with requests. -/ comparison_mono : forall {first second}, first ≤ second
    ->
    comparisonIndex first ≤ comparisonIndex second

constructive_injectivity CommonSchedule

namespace CommonSchedule

open Purelib.Data.Nat

/-- Advance both retained schedules to their coordinatewise maximum.

Each selected stream remains monotone and meets both original floors. The
original schedules remain available to transport their cached comparisons
to these later indices. -/
def join (left right : CommonSchedule) : CommonSchedule where
  sourceIndex := fun request => max (left.sourceIndex request) (right.sourceIndex request)
  targetIndex := fun request => max (left.targetIndex request) (right.targetIndex request)
  comparisonIndex := fun request => max (left.comparisonIndex request) (right.comparisonIndex request)
  source_ge := fun request => Nat.le_trans (left.source_ge request) (Order.le_max_left _ _)
  target_ge := fun request => Nat.le_trans (left.target_ge request) (Order.le_max_left _ _)
  comparison_ge := fun request => Nat.le_trans (left.comparison_ge request) (Order.le_max_left _ _)
  source_mono := fun order => Order.max_le_max (left.source_mono order) (right.source_mono order)
  target_mono := fun order => Order.max_le_max (left.target_mono order) (right.target_mono order)
  comparison_mono := fun order => Order.max_le_max (left.comparison_mono order) (right.comparison_mono order)

/-- The joined target stream is at least the first original target stream. -/
theorem target_le_join_left (left right : CommonSchedule) (request : Nat) :
    left.targetIndex request ≤ (left.join right).targetIndex request := Order.le_max_left _ _

/-- The joined target stream is at least the second original target stream. -/
theorem target_le_join_right (left right : CommonSchedule) (request : Nat) :
    right.targetIndex request ≤ (left.join right).targetIndex request := Order.le_max_right _ _

/-- The joined comparison stream is at least the first original comparison stream. -/
theorem comparison_le_join_left (left right : CommonSchedule) (request : Nat) :
    left.comparisonIndex request ≤ (left.join right).comparisonIndex request := Order.le_max_left _ _

/-- The joined comparison stream is at least the second original comparison stream. -/
theorem comparison_le_join_right (left right : CommonSchedule) (request : Nat) :
    right.comparisonIndex request ≤ (left.join right).comparisonIndex request := Order.le_max_right _ _

open Purelib
/-- The request itself is a deterministic common schedule. -/
def identity : Approximation.Schedule.Common.CommonSchedule
  where
  sourceIndex := id
  targetIndex := id
  comparisonIndex := id
  source_ge := fun request => Nat.le_refl request
  target_ge := fun request => Nat.le_refl request
  comparison_ge := fun request => Nat.le_refl request
  source_mono := fun order => order
  target_mono := fun order => order
  comparison_mono := fun order => order

/-- The identity schedule selects the requested source stage. -/
@[simp] theorem identity_sourceIndex (request : Nat) :
    Approximation.Schedule.Common.CommonSchedule.identity.sourceIndex request = request := rfl

/-- The identity schedule selects the requested target stage. -/
@[simp] theorem identity_targetIndex (request : Nat) :
    Approximation.Schedule.Common.CommonSchedule.identity.targetIndex request = request := rfl

/-- The identity schedule selects the requested comparison stage. -/
@[simp] theorem identity_comparisonIndex (request : Nat) :
    Approximation.Schedule.Common.CommonSchedule.identity.comparisonIndex request = request := rfl

end CommonSchedule
end Purelib.Approximation.Schedule.Common

end
