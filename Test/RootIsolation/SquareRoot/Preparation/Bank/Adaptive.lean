module
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.Riemann.Readings.BoundedPreparedSource

import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
public import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches

open Purelib.Riemann.Paths.PreparedClearPathModels

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.BoundedPreparedBanks

open Purelib.RootIsolation.SquareRoot.Preparation.Bank

open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache

@[expose] public section

/-!
Structural regressions for certified coarser bank selection.  These use the
ordinary finite preparation interface, without importing generated banks or
computing global root isolation.  The nonstationary executable regression is
in `scripts.AdaptivePreparedBanksHarness`.
-/

namespace Test.Riemann.AdaptivePreparedBanksTests

open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
open Purelib.Riemann.Paths.PreparedClearPathModels (sufficientDepth dyadicRefinePath)

variable {polynomial : Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.GaussianPolynomial} (rootDiameter :
  Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive.Coordinate)
  (positive : 0 < rootDiameter)

/-- The empty path selects refinement depth zero. -/
example : (Adaptive.select ([] : List (Adaptive.Task polynomial)) rootDiameter positive).depth = 0 :=
  Adaptive.empty_depth rootDiameter positive

/-- A single segment selects a depth no greater than a supplied sufficient depth. -/
example (task : Adaptive.Task polynomial) :
    (Adaptive.select [task] rootDiameter positive).depth ≤ sufficientDepth task.path rootDiameter := by
  simpa only [Adaptive.maximumDepth, Nat.max_zero] using
    (Adaptive.select [task] rootDiameter positive).depth_le_sufficient

/-- Selection from a minimum depth retains that lower bound. -/
example (tasks : List (Adaptive.Task polynomial)) (minimum : Nat) :
    minimum ≤ (Adaptive.selectFrom tasks rootDiameter positive minimum).depth :=
  (Adaptive.selectFrom tasks rootDiameter positive minimum).minimum_le

/-- A sufficient initial minimum is selected unchanged. -/
example (tasks : List (Adaptive.Task polynomial)) (minimum : Nat)
    (enough : Adaptive.maximumDepth rootDiameter tasks ≤ minimum) :
    (Adaptive.selectFrom tasks rootDiameter positive minimum).depth = minimum := by
  let selected := Adaptive.selectFrom tasks rootDiameter positive minimum
  have upper : selected.depth ≤ minimum := by
    simpa only [Nat.max_eq_right enough] using selected.depth_le.trans selected.upperDepth_eq.le
  exact Nat.le_antisymm upper selected.minimum_le

/-- The empty path selects the supplied minimum depth exactly. -/
example (minimum : Nat) :
    (Adaptive.selectFrom ([] : List (Adaptive.Task polynomial)) rootDiameter positive minimum).depth = minimum := by
  let selected := Adaptive.selectFrom ([] : List (Adaptive.Task polynomial)) rootDiameter positive minimum
  have upper : selected.depth ≤ minimum := by
    simpa only [Adaptive.maximumDepth, Nat.zero_max] using selected.depth_le.trans selected.upperDepth_eq.le
  exact Nat.le_antisymm upper selected.minimum_le

/-- The first prepared bank contains the dyadic number of segment entries. -/
example (first second : Adaptive.Task polynomial) :
    (Adaptive.select [first, second] rootDiameter positive).banks.head.prepared.stepCount =
      2 ^ (Adaptive.select [first, second] rootDiameter positive).depth * first.path.segmentCount :=
  (Adaptive.select [first, second] rootDiameter positive).banks.head.prepared_stepCount

/-- The second prepared bank contains the same dyadic number of segment entries. -/
example (first second : Adaptive.Task polynomial) :
    (Adaptive.select [first, second] rootDiameter positive).banks.tail.head.prepared.stepCount =
      2 ^ (Adaptive.select [first, second] rootDiameter positive).depth * second.path.segmentCount :=
  (Adaptive.select [first, second] rootDiameter positive).banks.tail.head.prepared_stepCount

/-- The prepared clear path is the exact dyadic refinement of its source path. -/
example (task : Adaptive.Task polynomial) :
    (Adaptive.select [task] rootDiameter positive).banks.head.prepared.toClearPath =
      dyadicRefinePath task.path (Adaptive.select [task] rootDiameter positive).banks.head.within
        (Adaptive.select [task] rootDiameter positive).depth :=
  (Adaptive.select [task] rootDiameter positive).banks.head.prepared_toClearPath_eq_dyadicRefinePath

/-- Caching preserves the original prepared path. -/
example (task : Adaptive.Task polynomial) :
    (DyadicBank.cache
      (Adaptive.select [task] rootDiameter positive).banks.head).prepared =
      (Adaptive.select [task] rootDiameter positive).banks.head.prepared := rfl

/-- Preparing an empty path returns the empty prepared path. -/
example (ambient : Adaptive.Box) (point : Adaptive.Gaussian) (owner : Adaptive.Owner (polynomial.eval point)) :
    Adaptive.preparePath (ambient := ambient) (.nil point) (.nil point) owner rootDiameter positive =
      PreparedPath.nil point owner := rfl

/-- The selected depth of an empty prepared path is zero. -/
example (ambient : Adaptive.Box) (point : Adaptive.Gaussian) (owner : Adaptive.Owner (polynomial.eval point)) :
    (Adaptive.select [Task.ofPath (ambient := ambient) (.nil point) (.nil point) owner]
      rootDiameter positive).depth = 0 := by
  have bounded := (Adaptive.select
    [Task.ofPath (ambient := ambient) (.nil point) (.nil point) owner]
    rootDiameter positive).depth_le_sufficient
  simpa only [Adaptive.maximumDepth, Task.ofPath, sufficientDepth, Nat.max_self, Nat.le_zero] using bounded

-- A failed cheap attempt proves its own exact outcome, not failure of the
-- stronger canonical preparation.  Ordered accepted prefixes are retained
-- by the report instead of reconstructed for this proof.
/-- A bounded source attempt retains the exact exhausted-budget error. -/
example {ambient : Adaptive.Box} {start finish : Adaptive.Gaussian}
    {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : PreparedSheetContinuation.Endpoint}
    {owner : Adaptive.Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : PreparedSheetContinuation.StepRequest}
    (report : BoundedPreparedSource.Inconclusive segment current owner request) :
    report.movingBudget = 2 ∧
      BoundedPreparedSource.check segment current owner request = .error report :=
  ⟨report.movingBudget_eq, report.check_error⟩

/-- A failed step retains its exact inconclusive evidence. -/
example {ambient : Adaptive.Box} {start finish : Adaptive.Gaussian}
    {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {current : PreparedSheetContinuation.Endpoint}
    {owner : Adaptive.Owner (polynomial.eval (segment.pointAt current.parameter))}
    {requests : List PreparedSheetContinuation.StepRequest}
    (report : BoundedPreparedBanks.StepFailure segment within current owner requests) :
    BoundedPreparedBanks.steps segment within current owner requests = .error report :=
  report.steps_error

/-- An inconclusive path attempt retains its exact failure evidence. -/
example (task : Adaptive.Task polynomial) (depth : Nat)
    (report : BoundedPreparedBanks.Inconclusive depth rootDiameter positive
      task.path task.within task.owner) :
    BoundedPreparedBanks.attempt depth rootDiameter positive
      task.path task.within task.owner = .error report := report.attempt_error

/-- The accepted cache retains the original prepared path. -/
example (task : Adaptive.Task polynomial) (depth : Nat)
    (accepted : BoundedPreparedBanks.PathSuccess depth rootDiameter positive
      task.path task.within task.owner) :
    (DyadicBank.cache
      accepted.bank).prepared = accepted.prepared := rfl

/-- An unordered request returns the explicit unordered-request outcome. -/
example {ambient : Adaptive.Box} {start finish : Adaptive.Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (current : PreparedSheetContinuation.Endpoint)
    (owner : Adaptive.Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : PreparedSheetContinuation.StepRequest)
    (remaining : List PreparedSheetContinuation.StepRequest)
    (backwards : ¬ current.parameter ≤ request.endpoint.parameter) :
    BoundedPreparedBanks.steps segment within current owner (request :: remaining) =
      .error (.unordered current owner request remaining backwards) :=
  StepFailure.steps_error _

end Test.Riemann.AdaptivePreparedBanksTests
