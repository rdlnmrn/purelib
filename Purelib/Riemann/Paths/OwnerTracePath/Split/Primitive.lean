module

public import Purelib.Riemann.Paths.OwnerTracePath.Split
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Append

/-! # Original primitive observations on actual materialized path splits

The already computed complete split owns both actual path pieces. The
existing primitive split reads their same old Vertex and stationary
comparison caches, preserving the literal shared observation. Whole suffix
identities transport those same pieces without observing any vertex again.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}

namespace Split

variable {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start first finish last}
    (divided : Split path) (observed : Primitive.Spine expression accuracy path)

/-- Split the SAME given old Spine using the already computed actual prefix, suffix and complete append equation. -/
def observations : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    divided.initial divided.suffix.path :=
  Primitive.Spine.split (expression := expression) (accuracy := accuracy) divided.initial divided.suffix.path
    (Primitive.Spine.castPath divided.append_eq.symm observed)

/-- The whole observation split is its exact original factory on those actual retained path pieces. -/
theorem observations_eq : observations divided observed =
    Primitive.Spine.split (expression := expression) (accuracy := accuracy) divided.initial divided.suffix.path
      (Primitive.Spine.castPath divided.append_eq.symm observed) := by
  unfold observations
  rfl

/-- The actual prefix keeps the entire original source Vertex and its actual old request. -/
theorem observations_first : (observations divided observed).before.first = observed.first :=
  (congrArg (fun value : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
      divided.initial divided.suffix.path => value.before.first) (observations_eq divided observed)).trans
    ((Primitive.Spine.split_first _).trans (Primitive.Spine.castPath_first divided.append_eq.symm observed))

/-- The literal old suffix keeps the entire original terminal Vertex and all of its old observation data. -/
theorem observations_last : (observations divided observed).after.last = observed.last :=
  (congrArg (fun value : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
      divided.initial divided.suffix.path => value.after.last) (observations_eq divided observed)).trans
    ((Primitive.Spine.split_last _).trans (Primitive.Spine.castPath_last divided.append_eq.symm observed))

/-- Reindex the SAME prefix observation using equality of its whole retained suffix tuple. -/
def prefixObservations {expected : Suffix last} (same : divided.suffix = expected)
    (before : Primitive.Spine expression accuracy divided.initial) :
    Primitive.Spine expression accuracy (prefixCast divided same) := by
  cases same
  exact before

/-- Whole suffix reindexing preserves the complete old prefix observation execution heterogeneously. -/
theorem prefixObservations_heq {expected : Suffix last} (same : divided.suffix = expected)
    (before : Primitive.Spine expression accuracy divided.initial) :
    HEq (prefixObservations divided same before) before := by
  cases same
  rfl

/-- Whole suffix transport retains the actual old prefix source scalar. -/
theorem prefixObservations_first_value {expected : Suffix last} (same : divided.suffix = expected)
    (before : Primitive.Spine expression accuracy divided.initial) :
    (prefixObservations divided same before).first.value = before.first.value := by
  cases same
  rfl

/-- Whole suffix transport retains the actual old prefix terminal scalar. -/
theorem prefixObservations_last_value {expected : Suffix last} (same : divided.suffix = expected)
    (before : Primitive.Spine expression accuracy divided.initial) :
    (prefixObservations divided same before).last.value = before.last.value := by
  cases same
  rfl

end Split

namespace Suffix

variable {finish : Canonical} {last : Owner (polynomial.eval finish)}

/-- Reindex the SAME old suffix Spine along equality of its complete point/Owner/path tuple. -/
def observationsCast {first second : Suffix last} (same : first = second)
    (observed : Primitive.Spine expression accuracy first.path) :
    Primitive.Spine expression accuracy (pathCast same) := by
  cases same
  exact observed

/-- The whole original suffix observation cache survives its complete-suffix transport unchanged. -/
theorem observationsCast_heq {first second : Suffix last} (same : first = second)
    (observed : Primitive.Spine expression accuracy first.path) :
    HEq (observationsCast same observed) observed := by
  cases same
  rfl

/-- Complete-suffix transport keeps the literal old source scalar. -/
theorem observationsCast_first_value {first second : Suffix last} (same : first = second)
    (observed : Primitive.Spine expression accuracy first.path) :
    (observationsCast same observed).first.value = observed.first.value := by
  cases same
  rfl

/-- Complete-suffix transport keeps the literal old terminal scalar. -/
theorem observationsCast_last_value {first second : Suffix last} (same : first = second)
    (observed : Primitive.Spine expression accuracy first.path) :
    (observationsCast same observed).last.value = observed.last.value := by
  cases same
  rfl

end Suffix

namespace Primitive.Spine

variable {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start first finish last}

/-- Exact endpoint and whole-Owner transport keeps the SAME old initial scalar. -/
theorem castEndpoints_first_value {nextStart nextFinish : Canonical}
    {nextFirst : Owner (polynomial.eval nextStart)} {nextLast : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (firstEq : HEq first nextFirst) (lastEq : HEq last nextLast)
    (observed : Spine expression accuracy path) :
    (castEndpoints startEq finishEq firstEq lastEq observed).first.value = observed.first.value := by
  cases startEq
  cases finishEq
  cases eq_of_heq firstEq
  cases eq_of_heq lastEq
  rfl

/-- Exact endpoint and whole-Owner transport keeps the SAME old final scalar. -/
theorem castEndpoints_last_value {nextStart nextFinish : Canonical}
    {nextFirst : Owner (polynomial.eval nextStart)} {nextLast : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (firstEq : HEq first nextFirst) (lastEq : HEq last nextLast)
    (observed : Spine expression accuracy path) :
    (castEndpoints startEq finishEq firstEq lastEq observed).last.value = observed.last.value := by
  cases startEq
  cases finishEq
  cases eq_of_heq firstEq
  cases eq_of_heq lastEq
  rfl

end Primitive.Spine

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
