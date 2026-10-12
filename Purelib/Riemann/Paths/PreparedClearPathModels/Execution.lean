module
public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Nat.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction.Order.Basic

public section

namespace Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Approximation.Rational

set_option genInjectivity false in
/-- The original per-segment execution route, retained unchanged during continuation. -/
inductive Policy where
  /-- Execute the actual finite dyadic preparation. -/ | direct
  /-- Check variation against the predicted dyadic clearance. -/ | predicted
  /-- Check variation against the uniform prepared clearance. -/ | uniform
  /-- Check the full original dyadic mesh-safety predicate. -/ | mesh

variable {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}

set_option genInjectivity false in
/-- One acquired complete segment with the exact requested dyadic data and geometry.

The prepared subdivision and its terminal owner are retained. The equations certify its original request list, parameter
edges, step count and clear-path readback; constructing a whole-path bank need not acquire this segment again. -/
structure Segment (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter)
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start)) where
  /-- The actual complete segment acquired at the original starting owner. -/ prepared : CompleteSegment head within
    owner
  /-- The retained subdivision requests exactly the original dyadic endpoints and diameter. -/ requests :
    prepared.subdivision.requests = PreparedSheetContinuation.Subdivision.dyadicRequests
      depth zeroEndpoint oneEndpoint rootDiameter positive
  /-- The retained subdivision has exactly the original dyadic parameter edges. -/ parameterEdges :
    prepared.subdivision.parameterEdges = ClearSheetContinuation.Subdivision.dyadicEdges depth zeroEndpoint oneEndpoint
  /-- The retained subdivision has the original dyadic step count. -/ stepCount : prepared.subdivision.stepCount = 2
    ^ depth
  /-- The retained segment geometry reads back to its original requested dyadic refinement. -/ clearPath :
    prepared.clearPath = dyadicRefineSegment head within depth

namespace Segment

/-- Certify the actual successful dyadic subdivision without acquiring it again. -/
@[expose] def ofTryDyadic (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter)
    {subdivision : PreparedSubdivision head within zeroEndpoint (ownerAtStart head owner)}
    (success : PreparedSheetContinuation.Subdivision.tryDyadic head within zeroEndpoint oneEndpoint
      (ownerAtStart head owner) depth rootDiameter positive = some subdivision) :
    Segment depth rootDiameter positive head within owner :=
  ⟨CompleteSegment.ofTryDyadic head within owner depth rootDiameter positive success,
    CompleteSegment.ofTryDyadic_requests head within owner depth rootDiameter positive success,
    CompleteSegment.ofTryDyadic_parameterEdges head within owner depth rootDiameter positive success,
    CompleteSegment.ofTryDyadic_stepCount head within owner depth rootDiameter positive success,
    CompleteSegment.ofTryDyadic_clearPath head within owner depth rootDiameter positive success⟩

/-- Acquire and certify the original mesh-safe segment once. -/
@[expose] def ofSafe (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe head zeroEndpoint oneEndpoint
      (ownerAtStart head owner) depth rootDiameter positive) : Segment depth rootDiameter positive head within owner :=
  ⟨CompleteSegment.ofSafeDyadic head within owner depth rootDiameter positive safe,
    CompleteSegment.ofSafeDyadic_requests head within owner depth rootDiameter positive safe,
    CompleteSegment.ofSafeDyadic_parameterEdges head within owner depth rootDiameter positive safe,
    CompleteSegment.ofSafeDyadic_stepCount head within owner depth rootDiameter positive safe,
    CompleteSegment.ofSafeDyadic_clearPath head within owner depth rootDiameter positive safe⟩

/-- Acquire the original predicted-clearance segment once and retain its exact specification laws. -/
@[expose] def ofVariation (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter)
    (below : Geometric.Basic.quarterRadius
      (ClearSheetContinuation.variationBound head zeroEndpoint.parameter oneEndpoint.parameter) depth <
      PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor head zeroEndpoint oneEndpoint
        (ownerAtStart head owner) depth rootDiameter positive) : Segment depth rootDiameter positive head within
          owner :=
  let safe := dyadicSafeOfVariation head owner depth rootDiameter positive below
  ⟨completeSegmentOfVariation head within owner depth rootDiameter positive below,
    CompleteSegment.ofSafeDyadic_requests head within owner depth rootDiameter positive safe,
    CompleteSegment.ofSafeDyadic_parameterEdges head within owner depth rootDiameter positive safe,
    CompleteSegment.ofSafeDyadic_stepCount head within owner depth rootDiameter positive safe,
    CompleteSegment.ofSafeDyadic_clearPath head within owner depth rootDiameter positive safe⟩

/-- Stitch a cached successful segment to the original tail at its actual finish owner.

The certificate uses the retained segment and tail directly; the generated requests and geometric equations compose
without running either preparation again. -/
@[expose] def prepend {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle} {within : head.WithinAmbient}
    {owner : Owner (polynomial.eval start)} (segment : Segment depth rootDiameter positive head within owner)
    (tail : Geometry.ClearPath polynomial ambient middle finish)
    (remaining : CertifiedDyadic depth rootDiameter positive tail segment.prepared.finishOwner) :
    CertifiedDyadic depth rootDiameter positive (.cons head tail) owner where
  within := .cons within remaining.within
  prepared := .cons head tail owner within segment.prepared remaining.prepared
  generated := ⟨segment.requests, remaining.generated⟩
  prepared_allEdgesProper := by
    change StrictParameterEdges segment.prepared.subdivision.parameterEdges ∧ AllEdgesProper remaining.prepared
    rw [segment.parameterEdges]
    exact ⟨dyadicEdges_strictParameterEdges depth zeroEndpoint oneEndpoint (by decide),
      remaining.prepared_allEdgesProper⟩
  prepared_stepCount := by
    change segment.prepared.subdivision.stepCount + remaining.prepared.stepCount = _
    rw [segment.stepCount, remaining.prepared_stepCount]
    change 2 ^ depth + 2 ^ depth * tail.segmentCount = 2 ^ depth * (tail.segmentCount + 1)
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_comm _ _
  prepared_toClearPath := by
    change segment.prepared.clearPath.append remaining.prepared.toClearPath = _
    rw [segment.clearPath, remaining.prepared_toClearPath]
    rfl

end Segment

/-- The original scalar predicted-clearance guard at this actual segment and starting owner. -/
@[reducible, expose] def PredictedGuard
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (owner : Owner (polynomial.eval start)) (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) : Prop :=
  Geometric.Basic.quarterRadius (ClearSheetContinuation.variationBound head
    zeroEndpoint.parameter oneEndpoint.parameter) depth <
  PreparedSheetContinuation.Subdivision.dyadicMeshPredictedClearanceFloor head zeroEndpoint oneEndpoint
    (ownerAtStart head owner) depth rootDiameter positive

/-- The original scalar uniform-clearance guard, without a substituted predicted inequality. -/
@[reducible, expose] def UniformGuard
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (depth : Nat) (rootDiameter : Fraction.Rational) : Prop :=
  Geometric.Basic.quarterRadius (ClearSheetContinuation.variationBound head
    zeroEndpoint.parameter oneEndpoint.parameter) depth <
  PreparedSheetContinuation.uniformPreparedClearanceFloor head rootDiameter

set_option genInjectivity false in
/-- The precise stopped head and execution policy's unfulfilled condition.

A zero segment budget suspends before acquiring the head. Other constructors retain the original failed guard or actual
finite preparation equation; none claims a mathematical absence of a root or an impossible path. -/
inductive StopReason (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter)
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start)) : Policy → Type where
  /-- No head acquisition was attempted because the finite segment budget is exhausted. -/
  | budget (policy : Policy) : StopReason depth rootDiameter positive head within owner policy
  /-- The actual direct finite preparation returned no subdivision. -/
  | unavailable (equation : PreparedSheetContinuation.Subdivision.tryDyadic head within zeroEndpoint oneEndpoint
      (ownerAtStart head owner) depth rootDiameter positive = none) :
      StopReason depth rootDiameter positive head within owner .direct
  /-- The original predicted-clearance inequality failed. -/
  | predicted (failed : ¬ PredictedGuard head owner depth rootDiameter positive) :
      StopReason depth rootDiameter positive head within owner .predicted
  /-- The original uniform-clearance inequality failed. -/
  | uniform (failed : ¬ UniformGuard head depth rootDiameter) :
      StopReason depth rootDiameter positive head within owner .uniform
  /-- The original full dyadic mesh-safety condition failed. -/
  | mesh (failed : ¬ PreparedSheetContinuation.Subdivision.DyadicMeshSafe head zeroEndpoint oneEndpoint
      (ownerAtStart head owner) depth rootDiameter positive) :
      StopReason depth rootDiameter positive head within owner .mesh

namespace StopReason

/-- Count actual original segment attempts; a budget suspension acquires no head. -/
@[expose] def consumed {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle} {within : head.WithinAmbient}
    {owner : Owner (polynomial.eval start)} {policy : Policy} :
    StopReason depth rootDiameter positive head within owner policy → Nat
  | .budget _ => 0
  | .unavailable _ => 1
  | .predicted _ => 1
  | .uniform _ => 1
  | .mesh _ => 1

end StopReason

set_option genInjectivity false in
/-- A retained successful prefix ending at the exact stopped original segment and unresolved dependent tail.

Every cached head carries its actual complete segment, requested dyadic data and terminal owner. The remaining prefix is
indexed by that terminal owner, so continuing cannot substitute another owner or replay earlier segment preparation. -/
inductive Inconclusive (policy : Policy) (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) :
    {start finish : Gaussian} → (path : Geometry.ClearPath polynomial ambient start finish) →
      path.WithinAmbient → Owner (polynomial.eval start) → Type
  /-- Retain the current original head, untouched tail, owner, containment and exact stopping condition. -/
  | stopped {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Geometry.ClearPath polynomial ambient middle finish)
      (within : (Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start))
      (reason : StopReason depth rootDiameter positive head within.head owner policy) :
      Inconclusive policy depth rootDiameter positive (.cons head tail) within owner
  /-- Retain a completed head and the stopped continuation at its original finish owner. -/
  | prefix {start middle finish : Gaussian}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : Geometry.ClearPath polynomial ambient middle finish)
      (within : (Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start))
      (segment : Segment depth rootDiameter positive head within.head owner)
      (remaining : Inconclusive policy depth rootDiameter positive tail within.tail segment.prepared.finishOwner) :
      Inconclusive policy depth rootDiameter positive (.cons head tail) within owner

namespace Inconclusive

/-- The number of successfully retained original segments before the stopped head. -/
@[expose] def completed {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} : {start finish : Gaussian} →
    {path : Geometry.ClearPath polynomial ambient start finish} → {within : path.WithinAmbient} →
    {owner : Owner (polynomial.eval start)} → Inconclusive policy depth rootDiameter positive path within owner → Nat
  | _, _, _, _, _, .stopped _ _ _ _ _ => 0
  | _, _, _, _, _, .prefix _ _ _ _ _ remaining => remaining.completed + 1

/-- Actual segment attempts include every cached success and any attempted failed head. -/
@[expose] def consumed {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} : {start finish : Gaussian} →
    {path : Geometry.ClearPath polynomial ambient start finish} → {within : path.WithinAmbient} →
    {owner : Owner (polynomial.eval start)} → Inconclusive policy depth rootDiameter positive path within owner → Nat
  | _, _, _, _, _, .stopped _ _ _ _ reason => reason.consumed
  | _, _, _, _, _, .prefix _ _ _ _ _ remaining => remaining.consumed + 1

end Inconclusive

set_option genInjectivity false in
/-- A successful exact dyadic bank or a retained finite stopped execution. -/
inductive Outcome (policy : Policy) (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start)) where
  /-- The complete prepared result retains all original dyadic and ownership certificates. -/
  | complete (certificate : CertifiedDyadic depth rootDiameter positive path owner)
  /-- The finite stopped attempt retains every already acquired successful segment and unresolved original tail. -/
  | inconclusive (stopped : Inconclusive policy depth rootDiameter positive path within owner)

namespace Outcome

/-- The actual number of attempted original segments in this retained execution. -/
@[expose] def consumed {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {path : Geometry.ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)} :
    Outcome policy depth rootDiameter positive path within owner → Nat
  | .complete _ => path.segmentCount
  | .inconclusive stopped => stopped.consumed

/-- The number of original segments whose complete subdivisions have actually been retained. -/
@[expose] def completed {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {path : Geometry.ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)} :
    Outcome policy depth rootDiameter positive path within owner → Nat
  | .complete _ => path.segmentCount
  | .inconclusive stopped => stopped.completed

/-- Attach one cached successful head to either a successful or stopped original tail. -/
@[expose] def prepend {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
    (tail : Geometry.ClearPath polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start))
    (segment : Segment depth rootDiameter positive head within.head owner) :
    Outcome policy depth rootDiameter positive tail within.tail segment.prepared.finishOwner →
      Outcome policy depth rootDiameter positive (.cons head tail) within owner
  | .complete remaining => .complete (segment.prepend tail remaining)
  | .inconclusive remaining => .inconclusive (.prefix head tail within owner segment remaining)

/-- Prepending a retained successful segment adds exactly one original segment attempt. -/
theorem consumed_prepend {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
    (tail : Geometry.ClearPath polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start))
    (segment : Segment depth rootDiameter positive head within.head owner)
    (remaining : Outcome policy depth rootDiameter positive tail within.tail segment.prepared.finishOwner) :
    (prepend tail within owner segment remaining).consumed = remaining.consumed + 1 := by
  cases remaining <;> rfl

end Outcome

set_option genInjectivity false in
/-- A bounded execution retaining its actual finite segment budget and paid work count.

Depth, diameter, safety policy, original path, ambient containment and starting owner index this result. Its typed
  outcome
keeps the successful prefix and exact stopping reason; projecting only the optional bank discards that explanation. -/
structure Execution (policy : Policy) (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start)) where
  /-- The actual supplied finite budget of original segment attempts. -/ budget : Nat
  /-- The complete or stopped execution at these exact original inputs. -/
  outcome : Outcome policy depth rootDiameter positive path within owner
  /-- The actual retained execution consumed no more original segment attempts than supplied. -/
  consumed_le : outcome.consumed ≤ budget

namespace StopReason

/-- A stopped head consumes at most one original segment attempt. -/
theorem consumed_le_one {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle} {within : head.WithinAmbient}
    {owner : Owner (polynomial.eval start)} {policy : Policy}
    (reason : StopReason depth rootDiameter positive head within owner policy) : reason.consumed ≤ 1 := by
  cases reason with
  | budget => exact Nat.zero_le 1
  | unavailable => exact Nat.le_refl 1
  | predicted => exact Nat.le_refl 1
  | uniform => exact Nat.le_refl 1
  | mesh => exact Nat.le_refl 1

/-- A diagnostic label for the retained policy-specific stopping certificate. -/
@[expose] def label {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle} {within : head.WithinAmbient}
    {owner : Owner (polynomial.eval start)} {policy : Policy} :
    StopReason depth rootDiameter positive head within owner policy → String
  | .budget _ => "segment budget exhausted"
  | .unavailable _ => "finite dyadic preparation unavailable"
  | .predicted _ => "predicted clearance guard failed"
  | .uniform _ => "uniform clearance guard failed"
  | .mesh _ => "dyadic mesh safety guard failed"

end StopReason

namespace Inconclusive

/-- Read a diagnostic label from the actual stopped head without acquiring any cached segment again. -/
@[expose] def stoppingReason {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} : {start finish : Gaussian} →
    {path : Geometry.ClearPath polynomial ambient start finish} → {within : path.WithinAmbient} →
    {owner : Owner (polynomial.eval start)} → Inconclusive policy depth rootDiameter positive path within owner → String
  | _, _, _, _, _, .stopped _ _ _ _ reason => reason.label
  | _, _, _, _, _, .prefix _ _ _ _ _ remaining => remaining.stoppingReason

end Inconclusive

/-- Acquire one head through the selected original algorithm and retain its actual successful result or failed guard. -/
@[expose] def executeHead (policy : Policy)
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) :
    Sum (Segment depth rootDiameter positive head within owner)
      (StopReason depth rootDiameter positive head within owner policy) :=
  match policy with
  | .direct =>
      match success : PreparedSheetContinuation.Subdivision.tryDyadic head within zeroEndpoint oneEndpoint
          (ownerAtStart head owner) depth rootDiameter positive with
      | none => .inr (.unavailable success)
      | some subdivision => .inl (Segment.ofTryDyadic head within owner depth rootDiameter positive
          (subdivision := subdivision) success)
  | .predicted =>
      if below : PredictedGuard head owner depth rootDiameter positive then
        .inl (Segment.ofVariation head within owner depth rootDiameter positive below)
      else .inr (.predicted below)
  | .uniform =>
      if below : UniformGuard head depth rootDiameter then
        let predicted : PredictedGuard head owner depth rootDiameter positive :=
          lt_of_lt_of_le below
            (PreparedSheetContinuation.Subdivision.uniformPreparedClearanceFloor_le_dyadicPredicted
              head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth rootDiameter positive)
        .inl (Segment.ofVariation head within owner depth rootDiameter positive predicted)
      else .inr (.uniform below)
  | .mesh =>
      if safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe head zeroEndpoint oneEndpoint
          (ownerAtStart head owner) depth rootDiameter positive then
        .inl (Segment.ofSafe head within owner depth rootDiameter positive safe)
      else .inr (.mesh safe)

namespace Execution

variable {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {path : Geometry.ClearPath polynomial ambient start finish} {within : path.WithinAmbient}
    {owner : Owner (polynomial.eval start)}

/-- Read the actual number of segment attempts retained by this execution. -/
@[expose] def consumed (run : Execution policy depth rootDiameter positive path within owner) : Nat :=
  run.outcome.consumed

/-- Read the exact number of successfully cached original segments. -/
@[expose] def completed (run : Execution policy depth rootDiameter positive path within owner) : Nat :=
  run.outcome.completed

/-- Read the actual stopped-branch label while keeping its full certificate in the retained outcome. -/
@[expose] def stoppingReason (run : Execution policy depth rootDiameter positive path within owner) : Option String :=
  match run.outcome with
  | .complete _ => none
  | .inconclusive stopped => some stopped.stoppingReason

/-- Project the certified successful bank; an inconclusive projection retains its explanation in the original execution.
-/
@[expose] def bank? (run : Execution policy depth rootDiameter positive path within owner) :
    Option (DyadicBank depth rootDiameter positive path owner) :=
  match run.outcome with
  | .complete certificate => some (.certified certificate)
  | .inconclusive _ => none

/-- Add one already acquired head to a bounded tail execution, retaining the same data and spent-work certificate. -/
@[expose] def prepend {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
    (tail : Geometry.ClearPath polynomial ambient middle finish)
    (wholeWithin : (Geometry.ClearPath.cons head tail).WithinAmbient) (sourceOwner : Owner (polynomial.eval start))
    (segment : Segment depth rootDiameter positive head wholeWithin.head sourceOwner)
    (remaining : Execution policy depth rootDiameter positive tail wholeWithin.tail segment.prepared.finishOwner) :
    Execution policy depth rootDiameter positive (.cons head tail) wholeWithin sourceOwner where
  budget := remaining.budget + 1
  outcome := Outcome.prepend tail wholeWithin sourceOwner segment remaining.outcome
  consumed_le := by
    rw [Outcome.consumed_prepend]
    exact Nat.succ_le_succ remaining.consumed_le

end Execution

/-- Execute at most the supplied number of original segments with a checked bound on actual consumed work.

A zero budget stops before acquiring a nonempty head. Each acquired segment follows the original policy and the tail
starts at that cached segment's actual finish owner. -/
@[expose] def boundedOutcome (policy : Policy) :
    {start finish : Gaussian} → (path : Geometry.ClearPath polynomial ambient start finish) →
      (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) →
      (depth : Nat) → (rootDiameter : Fraction.Rational) → (positive : 0 < rootDiameter) → (budget : Nat) →
        {result : Outcome policy depth rootDiameter positive path within owner // result.consumed ≤ budget}
  | _, _, .nil point, within, owner, _depth, _rootDiameter, _positive, _budget =>
      ⟨.complete ⟨within, .nil point owner, trivial, trivial, rfl, rfl⟩, Nat.zero_le _⟩
  | _, _, .cons head tail, within, owner, _depth, _rootDiameter, _positive, 0 =>
      ⟨.inconclusive (.stopped head tail within owner (.budget policy)), Nat.le_refl _⟩
  | _, _, .cons head tail, within, owner, depth, rootDiameter, positive, budget + 1 =>
      match executeHead policy head within.head owner depth rootDiameter positive with
      | .inr reason =>
          ⟨.inconclusive (.stopped head tail within owner reason),
            reason.consumed_le_one.trans (Nat.succ_le_succ (Nat.zero_le budget))⟩
      | .inl segment =>
          let remaining := boundedOutcome policy tail within.tail segment.prepared.finishOwner
            depth rootDiameter positive budget
          ⟨Outcome.prepend tail within owner segment remaining.val, by
            rw [Outcome.consumed_prepend]
            exact Nat.succ_le_succ remaining.property⟩

/-- Run a finite segment budget and retain the supplied budget with its actual typed execution outcome. -/
@[expose] def executeBounded (policy : Policy) (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) (budget : Nat) :
    Execution policy depth rootDiameter positive path within owner :=
  let result := boundedOutcome policy path within owner depth rootDiameter positive budget
  ⟨budget, result.val, result.property⟩

/-- The retained execution budget is exactly the supplied number of original segment attempts. -/
theorem executeBounded_budget (policy : Policy) (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) (budget : Nat) :
    (executeBounded policy path within owner depth rootDiameter positive budget).budget = budget := rfl

namespace StopReason

/-- Continue an unattempted head or retain the exact already failed mathematical guard. -/
@[expose] def continueHead {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter}
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (tail : Geometry.ClearPath polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start)) :
    {policy : Policy} → (reason : StopReason depth rootDiameter positive head within.head owner policy) →
    (extraBudget : Nat) →
      {result : Outcome policy depth rootDiameter positive (.cons head tail) within owner //
        result.consumed ≤ reason.consumed + extraBudget}
  | policy, .budget _, extraBudget =>
      let result := boundedOutcome policy (.cons head tail) within owner depth rootDiameter positive extraBudget
      ⟨result.val, result.property.trans_eq (Nat.zero_add extraBudget).symm⟩
  | .direct, .unavailable equation, _extraBudget =>
      ⟨.inconclusive (.stopped head tail within owner (.unavailable equation)), Nat.le_add_right _ _⟩
  | .predicted, .predicted failed, _extraBudget =>
      ⟨.inconclusive (.stopped head tail within owner (.predicted failed)), Nat.le_add_right _ _⟩
  | .uniform, .uniform failed, _extraBudget =>
      ⟨.inconclusive (.stopped head tail within owner (.uniform failed)), Nat.le_add_right _ _⟩
  | .mesh, .mesh failed, _extraBudget =>
      ⟨.inconclusive (.stopped head tail within owner (.mesh failed)), Nat.le_add_right _ _⟩

end StopReason

namespace Inconclusive

/-- Continue only the unattempted suffix of a budget-stopped execution and keep every cached successful head.

The extra budget is paid against the previous actual consumed work. A retained failed mathematical guard is immutable at
these same inputs, so it is returned unchanged rather than repeating the preparation that already failed. -/
@[expose] def resume {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} : {start finish : Gaussian} →
    {path : Geometry.ClearPath polynomial ambient start finish} → {within : path.WithinAmbient} →
    {owner : Owner (polynomial.eval start)} →
    (stopped : Inconclusive policy depth rootDiameter positive path within owner) → (extraBudget : Nat) →
      {result : Outcome policy depth rootDiameter positive path within owner //
        result.consumed ≤ stopped.consumed + extraBudget}
  | _, _, _, _, _, .stopped head tail within owner reason, extraBudget =>
      StopReason.continueHead head tail within owner reason extraBudget
  | _, _, _, _, _, .prefix head tail within owner segment unfinished, extraBudget =>
      let remaining := unfinished.resume extraBudget
      ⟨Outcome.prepend tail within owner segment remaining.val, by
        rw [Outcome.consumed_prepend]
        change remaining.val.consumed + 1 ≤ (unfinished.consumed + 1) + extraBudget
        have bound := Nat.succ_le_succ remaining.property
        exact bound.trans_eq (Nat.add_right_comm unfinished.consumed extraBudget 1)⟩

end Inconclusive

namespace Execution

/-- Add finite segment budget to the retained continuation, without repeating any completed segment.

Successful banks and immutable guarded failures retain their original data. A budget suspension prepares only its saved
unresolved suffix at the same depth, diameter, safety policy and exact finish owner of the retained prefix. -/
@[expose] def resume {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {path : Geometry.ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)}
    (run : Execution policy depth rootDiameter positive path within owner) (extraBudget : Nat) :
    Execution policy depth rootDiameter positive path within owner :=
  match equation : run.outcome with
  | .complete certificate =>
      have previous : (Outcome.complete certificate :
          Outcome policy depth rootDiameter positive path within owner).consumed ≤ run.budget :=
        equation ▸ run.consumed_le
      ⟨run.budget + extraBudget, .complete certificate, previous.trans (Nat.le_add_right _ _)⟩
  | .inconclusive stopped =>
      have previous : stopped.consumed ≤ run.budget := by
        have bound := run.consumed_le
        rw [equation] at bound
        exact bound
      let continued := stopped.resume extraBudget
      ⟨run.budget + extraBudget, continued.val,
        continued.property.trans (Nat.add_le_add_right previous extraBudget)⟩

/-- Resuming retains the original supplied budget and adds exactly the new finite allowance. -/
theorem resume_budget {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {path : Geometry.ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)}
    (run : Execution policy depth rootDiameter positive path within owner) (extraBudget : Nat) :
    (run.resume extraBudget).budget = run.budget + extraBudget := by
  cases run with
  | mk budget outcome bound => cases outcome <;> rfl

end Execution

/-- Execute the original direct preparation with enough segment budget to attempt the full finite path. -/
@[expose] def execute (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) :
    Execution .direct depth rootDiameter positive path within owner :=
  executeBounded .direct path within owner depth rootDiameter positive path.segmentCount

/-- Execute the original predicted-clearance procedure while retaining any stopped dependent prefix. -/
@[expose] def executePredicted (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) :
    Execution .predicted depth rootDiameter positive path within owner :=
  executeBounded .predicted path within owner depth rootDiameter positive path.segmentCount

/-- Execute the original uniform-clearance procedure while retaining any stopped dependent prefix. -/
@[expose] def executeUniform (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) :
    Execution .uniform depth rootDiameter positive path within owner :=
  executeBounded .uniform path within owner depth rootDiameter positive path.segmentCount

/-- Execute the original full mesh-safety procedure while retaining any stopped dependent prefix. -/
@[expose] def executeMeshSafe (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) :
    Execution .mesh depth rootDiameter positive path within owner :=
  executeBounded .mesh path within owner depth rootDiameter positive path.segmentCount

/-- Read the actual retained prepared path, omitting only the execution diagnostics. -/
@[expose] def Outcome.prepared? {policy : Policy} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {path : Geometry.ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)} :
    Outcome policy depth rootDiameter positive path within owner → Option (PreparedPath path owner)
  | .complete certificate => some certificate.prepared
  | .inconclusive _ => none

/-- The selected original algorithm's optional prepared path, before execution diagnostics were retained. -/
@[expose] def originalPrepared (policy : Policy)
    (path : Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start)) (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) : Option (PreparedPath path owner) :=
  match policy with
  | .direct => tryDyadic path within owner depth rootDiameter positive
  | .predicted => (ClearanceCheckedDyadic.execute? depth rootDiameter positive path within owner).map
      fun checked => checked.checked.prepared
  | .uniform => (ClearanceCheckedDyadic.executeUniform? depth rootDiameter positive path within owner).map
      fun checked => checked.checked.prepared
  | .mesh => (ClearanceCheckedDyadic.executeMeshSafe? depth rootDiameter positive path within owner).map
      fun checked => checked.prepared

/-- A sufficient segment budget preserves the actual prepared path produced by each original execution algorithm. -/
theorem executeBounded_originalPrepared (policy : Policy) (depth : Nat)
    (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) :
    {start finish : Gaussian} → (path : Geometry.ClearPath polynomial ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) →
    (executeBounded policy path within owner depth rootDiameter positive path.segmentCount).outcome.prepared? =
      originalPrepared policy path within owner depth rootDiameter positive := by
  intro start finish path
  induction path with
  | nil point => intro within owner; cases policy <;> rfl
  | cons head tail ih =>
      intro within owner
      change (boundedOutcome policy (.cons head tail) within owner depth rootDiameter positive
        (tail.segmentCount + 1)).val.prepared? = _
      cases policy with
      | direct =>
          simp only [originalPrepared, tryDyadic]
          split
          · rename_i success
            have selected : executeHead .direct head within.head owner depth rootDiameter positive =
                .inr (.unavailable success) := by
              unfold executeHead
              split
              · rfl
              · rename_i subdivision equation
                cases equation.symm.trans success
            simp only [boundedOutcome, selected]
            rfl
          · rename_i subdivision success
            have selected : executeHead .direct head within.head owner depth rootDiameter positive =
                .inl (Segment.ofTryDyadic head within.head owner depth rootDiameter positive success) := by
              unfold executeHead
              split
              · rename_i equation
                cases equation.symm.trans success
              · rename_i other equation
                have same := Option.some.inj (equation.symm.trans success)
                cases same
                rfl
            simp only [boundedOutcome, selected]
            dsimp only [Segment.ofTryDyadic]
            have agreement := ih within.tail
              (CompleteSegment.ofTryDyadic head within.head owner depth rootDiameter positive success).finishOwner
            simp only [executeBounded, originalPrepared] at agreement
            generalize equation : boundedOutcome Policy.direct tail within.tail
              (CompleteSegment.ofTryDyadic head within.head owner depth rootDiameter positive success).finishOwner
                depth rootDiameter positive tail.segmentCount = result at *
            cases result with
            | mk result bound =>
              cases result <;> dsimp only [Outcome.prepend, Outcome.prepared?] at agreement ⊢
              all_goals rw [← agreement]
              all_goals rfl
      | predicted =>
          by_cases below : PredictedGuard head owner depth rootDiameter positive
          · simp only [boundedOutcome, executeHead, originalPrepared, ClearanceCheckedDyadic.execute?,
              PredictedGuard, dif_pos below]
            have agreement := ih within.tail
              (completeSegmentOfVariation head within.head owner depth rootDiameter positive below).finishOwner
            simp only [executeBounded, originalPrepared] at agreement
            dsimp only [Segment.ofVariation]
            generalize equation : boundedOutcome Policy.predicted tail within.tail
              (completeSegmentOfVariation head within.head owner depth rootDiameter positive below).finishOwner
                depth rootDiameter positive tail.segmentCount = result at *
            cases original : ClearanceCheckedDyadic.execute? depth rootDiameter positive tail within.tail
              (completeSegmentOfVariation head within.head owner depth rootDiameter positive below).finishOwner with
            | none =>
                rw [original] at agreement
                cases result with
                | mk result bound =>
                  cases result <;> dsimp only [Outcome.prepend, Outcome.prepared?, Option.map] at agreement ⊢
                  · cases agreement
            | some checked =>
                rw [original] at agreement
                cases result with
                | mk result bound =>
                  cases result <;> dsimp only [Outcome.prepend, Outcome.prepared?, Option.map] at agreement ⊢
                  · have equality := Option.some.inj agreement
                    change some (cons head tail owner within.head _ _) = some (cons head tail owner within.head _ _)
                    exact congrArg
                      (fun prepared => some (cons head tail owner within.head _ prepared)) equality
                  · cases agreement
          · simp only [boundedOutcome, executeHead, originalPrepared, ClearanceCheckedDyadic.execute?,
              PredictedGuard, dif_neg below]
            rfl
      | uniform =>
          by_cases below : UniformGuard head depth rootDiameter
          · simp only [boundedOutcome, executeHead, originalPrepared, ClearanceCheckedDyadic.executeUniform?,
              UniformGuard, dif_pos below]
            let predicted := lt_of_lt_of_le below
              (PreparedSheetContinuation.Subdivision.uniformPreparedClearanceFloor_le_dyadicPredicted
                head zeroEndpoint oneEndpoint (ownerAtStart head owner) depth rootDiameter positive)
            have agreement := ih within.tail
              (completeSegmentOfVariation head within.head owner depth rootDiameter positive predicted).finishOwner
            simp only [executeBounded, originalPrepared] at agreement
            dsimp only [Segment.ofVariation]
            generalize equation : boundedOutcome Policy.uniform tail within.tail
              (completeSegmentOfVariation head within.head owner depth rootDiameter positive predicted).finishOwner
                depth rootDiameter positive tail.segmentCount = result at *
            cases original : ClearanceCheckedDyadic.executeUniform? depth rootDiameter positive tail within.tail
              (completeSegmentOfVariation head within.head owner depth rootDiameter positive predicted).finishOwner with
            | none =>
                rw [original] at agreement
                cases result with
                | mk result bound =>
                  cases result <;> dsimp only [Outcome.prepend, Outcome.prepared?, Option.map] at agreement ⊢
                  · cases agreement
            | some checked =>
                rw [original] at agreement
                cases result with
                | mk result bound =>
                  cases result <;> dsimp only [Outcome.prepend, Outcome.prepared?, Option.map] at agreement ⊢
                  · have equality := Option.some.inj agreement
                    change some (cons head tail owner within.head _ _) = some (cons head tail owner within.head _ _)
                    exact congrArg
                      (fun prepared => some (cons head tail owner within.head _ prepared)) equality
                  · cases agreement
          · simp only [boundedOutcome, executeHead, originalPrepared, ClearanceCheckedDyadic.executeUniform?,
              UniformGuard, dif_neg below]
            rfl
      | mesh =>
          by_cases below : PreparedSheetContinuation.Subdivision.DyadicMeshSafe head zeroEndpoint oneEndpoint
            (ownerAtStart head owner) depth rootDiameter positive
          · simp only [boundedOutcome, executeHead, originalPrepared, ClearanceCheckedDyadic.executeMeshSafe?,
              dif_pos below]
            have agreement := ih within.tail
              (CompleteSegment.ofSafeDyadic head within.head owner depth rootDiameter positive below).finishOwner
            simp only [executeBounded, originalPrepared] at agreement
            dsimp only [Segment.ofSafe]
            generalize equation : boundedOutcome Policy.mesh tail within.tail
              (CompleteSegment.ofSafeDyadic head within.head owner depth rootDiameter positive below).finishOwner
                depth rootDiameter positive tail.segmentCount = result at *
            cases original : ClearanceCheckedDyadic.executeMeshSafe? depth rootDiameter positive tail within.tail
              (CompleteSegment.ofSafeDyadic head within.head owner depth rootDiameter positive below).finishOwner with
            | none =>
                rw [original] at agreement
                cases result with
                | mk result bound =>
                  cases result <;> dsimp only [Outcome.prepend, Outcome.prepared?, Option.map] at agreement ⊢
                  · cases agreement
            | some checked =>
                rw [original] at agreement
                cases result with
                | mk result bound =>
                  cases result <;> dsimp only [Outcome.prepend, Outcome.prepared?, Option.map] at agreement ⊢
                  · have equality := Option.some.inj agreement
                    change some (cons head tail owner within.head _ _) = some (cons head tail owner within.head _ _)
                    exact congrArg
                      (fun prepared => some (cons head tail owner within.head _ prepared)) equality
                  · cases agreement
          · simp only [boundedOutcome, executeHead, originalPrepared, ClearanceCheckedDyadic.executeMeshSafe?,
              dif_neg below]
            rfl

/-- A failed actual head acquisition has attempted exactly one segment; it is never a budget suspension. -/
theorem executeHead_failed_consumed (policy : Policy)
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (within : head.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter)
    (reason : StopReason depth rootDiameter positive head within owner policy)
    (failed : executeHead policy head within owner depth rootDiameter positive = .inr reason) :
    reason.consumed = 1 := by
  cases policy <;> dsimp only [executeHead] at failed
  all_goals split at failed
  all_goals cases failed <;> rfl

/-- A cached successful head survives resumption unchanged, and only the dependent tail is continued. -/
theorem Execution.resume_prepend_outcome {policy : Policy} {depth : Nat}
    {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
    (tail : Geometry.ClearPath polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start))
    (segment : Segment depth rootDiameter positive head within.head owner)
    (remaining : Execution policy depth rootDiameter positive tail within.tail segment.prepared.finishOwner)
    (extraBudget : Nat) :
    ((remaining.prepend tail within owner segment).resume extraBudget).outcome =
      Outcome.prepend tail within owner segment (remaining.resume extraBudget).outcome := by
  cases remaining with
  | mk budget outcome bound => cases outcome <;> rfl

/-- A successful bounded head is attached using its retained complete segment and the exact original tail execution. -/
theorem executeBounded_cons_success (policy : Policy)
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (tail : Geometry.ClearPath polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head tail).WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) (budget : Nat)
    (segment : Segment depth rootDiameter positive head within.head owner)
    (success : executeHead policy head within.head owner depth rootDiameter positive = .inl segment) :
    executeBounded policy (.cons head tail) within owner depth rootDiameter positive (budget + 1) =
      (executeBounded policy tail within.tail segment.prepared.finishOwner depth rootDiameter positive budget).prepend
        tail within owner segment := by
  simp only [executeBounded, boundedOutcome, success]
  rfl

/-- Adding budget to a retained execution produces exactly the same outcome as a single attempt with the summed budget.

The equality concerns the actual cached prepared data and dependent source owners, as well as every stopped unresolved
case. Its implementation continues the saved suffix rather than acquiring successful prefix segments again. -/
theorem executeBounded_resume (policy : Policy) (depth : Nat)
    (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter) :
    {start finish : Gaussian} → (path : Geometry.ClearPath polynomial ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) → (budget extraBudget : Nat) →
    ((executeBounded policy path within owner depth rootDiameter positive budget).resume extraBudget).outcome =
      (executeBounded policy path within owner depth rootDiameter positive (budget + extraBudget)).outcome := by
  intro start finish path
  induction path with
  | nil point =>
      intro within owner budget extraBudget
      cases budget <;> cases extraBudget <;> rfl
  | cons head tail ih =>
      intro within owner budget extraBudget
      cases budget with
      | zero => rw [Nat.zero_add]; rfl
      | succ budget =>
          cases selected : executeHead policy head within.head owner depth rootDiameter positive with
          | inr reason =>
              have consumed := executeHead_failed_consumed policy head within.head owner depth rootDiameter positive
                reason selected
              rw [Nat.add_right_comm budget 1 extraBudget]
              simp only [executeBounded, boundedOutcome, selected]
              cases reason
              · cases consumed
              all_goals rfl
          | inl segment =>
              rw [executeBounded_cons_success policy head tail within owner depth rootDiameter positive budget segment
                selected]
              rw [Execution.resume_prepend_outcome]
              rw [Nat.add_right_comm budget 1 extraBudget]
              rw [executeBounded_cons_success policy head tail within owner depth rootDiameter positive
                (budget + extraBudget) segment selected]
              exact congrArg (Outcome.prepend tail within owner segment)
                (ih within.tail segment.prepared.finishOwner budget extraBudget)

end Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath.DyadicBank
