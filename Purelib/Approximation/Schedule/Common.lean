module

public import Init.Prelude
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
