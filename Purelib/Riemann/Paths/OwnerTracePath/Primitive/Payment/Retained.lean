module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment

/-! # Checked aggregate payment of a retained observation spine

The original local request and all observations remain unchanged. The
actual link count determines an inverse available whole request and the
local request needed for a supplied target. The retained comparison is an
allocation test: failure leaves that exact numerical requirement unpaid.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Budget
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}
variable {start finish : Canonical} {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
variable {path : OwnerPath polynomial start left finish right}

/-- A checked allocation retains the whole old spine, both requests, actual count, computed budgets and decision.

The original Decidable carries either the sufficient allocation proof or
its negation. An unpaid allocation does not assert that the observed sum
violates the target. Its inverse available request and count-squared
estimate remain valid for the same unchanged observations in either case.
-/
abbrev Payment (observed : Spine expression accuracy path) (target : AccuracyRequest) (count : Nat) :=
  Σ original : {values : Spine expression accuracy path × AccuracyRequest × AccuracyRequest × Nat //
    values.1 = observed ∧ values.2.1 = accuracy ∧ values.2.2.1 = target ∧ values.2.2.2 = count ∧
      path.vertices.length = values.2.2.2},
  Σ budgets : {values : AccuracyRequest × AccuracyRequest × Rational //
    values.1 = localRequest original.val.2.2.1 original.val.2.2.2 ∧
    values.2.1 = requestFor original.val.2.1 original.val.2.2.2 ∧
    values.2.2 = Aggregate.countCoordinate original.val.2.2.2 *
      (Aggregate.countCoordinate original.val.2.2.2 * original.val.2.1.tolerance)},
  let compared : Decidable (original.val.2.1.tolerance ≤ budgets.val.1.tolerance) := inferInstance
  {decision : Decidable (original.val.2.1.tolerance ≤ budgets.val.1.tolerance) // decision = compared}

namespace Payment

/-- Compute the finite allocation once while retaining every old observation and its unchanged local request.

The count certificate concerns the literal supplied path. No path, Query,
Point, join, Vertex or stationary comparison is constructed here.
-/
def build (observed : Spine expression accuracy path) (target : AccuracyRequest) (count : Nat)
    (sameCount : path.vertices.length = count) : Payment observed target count :=
  let old := observed
  let oldAccuracy := accuracy
  let requested := target
  let actualCount := count
  let required := localRequest requested actualCount
  let available := requestFor oldAccuracy actualCount
  let estimate := Aggregate.countCoordinate actualCount *
    (Aggregate.countCoordinate actualCount * oldAccuracy.tolerance)
  let allocation : Decidable (oldAccuracy.tolerance ≤ required.tolerance) := inferInstance
  ⟨⟨⟨old, oldAccuracy, requested, actualCount⟩, rfl, rfl, rfl, rfl, sameCount⟩,
    ⟨⟨required, available, estimate⟩, rfl, rfl, rfl⟩, ⟨allocation, rfl⟩⟩

variable {observed : Spine expression accuracy path} {requested : AccuracyRequest} {budgetCount : Nat}
variable (attempted : Payment observed requested budgetCount)

/-- Read the SAME whole observation spine; payment checking never re-observes its vertices. -/
def retained : Spine expression accuracy path := attempted.1.val.1

/-- Read the actual unchanged local request retained with the old observations. -/
def oldAccuracy : AccuracyRequest := attempted.1.val.2.1

/-- Read the supplied whole-word target as retained data. -/
def target : AccuracyRequest := attempted.1.val.2.2.1

/-- Read the exact original path-link occurrence count. -/
def count : Nat := attempted.1.val.2.2.2

/-- Read the local request actually required by this whole target and literal occurrence count. -/
def required : AccuracyRequest := attempted.2.1.val.1

/-- Read the whole request already payable by the unchanged observations at this actual count. -/
def available : AccuracyRequest := attempted.2.1.val.2.1

/-- Read the computed count-squared error estimate, with both actual count factors retained. -/
def estimate : Rational := attempted.2.1.val.2.2

/-- Inspect the original finite allocation decision, retaining the positive or negative proof.

The negative branch identifies only insufficient allocation evidence at
the old request. It keeps the complete attempted spine and exact required
request; it is not an invalidity or impossibility certificate for the sum.
-/
def allocation : Decidable (attempted.oldAccuracy.tolerance ≤ attempted.required.tolerance) :=
  attempted.2.2.val

/-- The complete original observation cache is retained literally. -/
theorem retained_eq : attempted.retained = observed := attempted.1.property.1

/-- No smaller local request has been substituted for the old observations. -/
theorem oldAccuracy_eq : attempted.oldAccuracy = accuracy := attempted.1.property.2.1

/-- The supplied target remains the same complete request. -/
theorem target_eq : attempted.target = requested := attempted.1.property.2.2.1

/-- The retained numerical count is the supplied occurrence count. -/
theorem count_eq : attempted.count = budgetCount := attempted.1.property.2.2.2.1

/-- The count is certified by the SAME retained path, including repeated and stationary links. -/
theorem path_count : path.vertices.length = attempted.count := attempted.1.property.2.2.2.2

/-- The remaining local request is computed from the actual retained target and count. -/
theorem required_eq : attempted.required = localRequest attempted.target attempted.count :=
  attempted.2.1.property.1

/-- The available whole request is the inverse original allocation at the unchanged old request. -/
theorem available_eq : attempted.available = requestFor attempted.oldAccuracy attempted.count :=
  attempted.2.1.property.2.1

/-- Both factors in the estimate are the actual retained occurrence count. -/
theorem estimate_eq : attempted.estimate = Aggregate.countCoordinate attempted.count *
    (Aggregate.countCoordinate attempted.count * attempted.oldAccuracy.tolerance) := attempted.2.1.property.2.2

/-- The retained decision is the original comparison on these SAME two actual request tolerances. -/
theorem allocation_eq : attempted.allocation =
    (inferInstance : Decidable (attempted.oldAccuracy.tolerance ≤ attempted.required.tolerance)) :=
  attempted.2.2.property

/-- The actual cached observations satisfy the computed finite estimate in either allocation branch. -/
theorem estimate_bound : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum attempted.retained.jumps) ≤
    attempted.estimate := by
  have bounded := attempted.retained.jumps_error_le
  rewrite [attempted.path_count] at bounded
  have estimate := attempted.estimate_eq
  rewrite [Aggregate.countCoordinate_eq, attempted.oldAccuracy_eq] at estimate
  exact Eq.mpr (congrArg (fun upper =>
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum attempted.retained.jumps) ≤ upper) estimate) bounded

/-- The inverse available request is always paid by the SAME old observations and actual count. -/
theorem available_bound : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum attempted.retained.jumps) <
    attempted.available.tolerance := by
  have inverse := (congrArg
    (fun request : AccuracyRequest => (localRequest request attempted.count).tolerance)
      attempted.available_eq).trans
    (congrArg AccuracyRequest.tolerance (localRequest_requestFor attempted.oldAccuracy attempted.count))
  have localBound : attempted.oldAccuracy.tolerance ≤
      (localRequest attempted.available attempted.count).tolerance :=
    Eq.mpr (congrArg (fun upper => attempted.oldAccuracy.tolerance ≤ upper) inverse)
      (Data.Rat.Fraction.Order.Basic.le_refl _)
  rewrite [attempted.oldAccuracy_eq] at localBound
  exact attempted.retained.jumps_error_lt attempted.available.positive attempted.path_count.le localBound

/-- A positive original allocation result pays the supplied target using exactly the retained observations. -/
theorem target_bound (paid : attempted.oldAccuracy.tolerance ≤ attempted.required.tolerance) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum attempted.retained.jumps) < attempted.target.tolerance := by
  rewrite [attempted.oldAccuracy_eq, attempted.required_eq] at paid
  exact attempted.retained.jumps_error_lt attempted.target.positive attempted.path_count.le paid

end Payment

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

end
