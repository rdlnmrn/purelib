module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy

/-! # Retained target requests as original covered source requests

The same sufficient-stage selection and whole target attempt supply the
original source Requested constructor. No search, preparation, lookup,
check or completion runs in this change of view. The original shifted
Request remains the receiver and owns the exact cover and chain indices.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {nonempty : geometry.parents ≠ []} {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (retained : Requested geometry nonempty current floor rootStage accuracy)

/-- View the same selected target attempt as an original source request on its literal covered cycle.

Both original factory equalities are consumed by Requested.ofRetained.
The entire target Request stays the nominal parent of the cover and chain;
only the existing sufficient selection and attempt are packaged. Body
exposure permits their unchanged selected-stage indices to reduce.
-/
@[expose] def asSource : StageAttempt.Requested (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) retained.request.covered retained.request.chain
    current floor rootStage accuracy :=
  StageAttempt.Requested.ofRetained retained.request.covered retained.request.chain
    current floor rootStage accuracy ⟨retained.selected, retained.selected_eq⟩
    retained.request.attempt retained.request.attempt_eq

/-- The whole source view is the original retained constructor on the same selection and attempt caches. -/
private theorem asSource_factory : retained.asSource =
    StageAttempt.Requested.ofRetained retained.request.covered retained.request.chain
      current floor rootStage accuracy ⟨retained.selected, retained.selected_eq⟩
      retained.request.attempt retained.request.attempt_eq := rfl

/-- The source view retains the entire sufficient-stage Selection, including its original search certificate. -/
theorem asSource_selected : retained.asSource.selected = retained.selected := by rfl

/-- The source stage is the literal selected target stage. -/
theorem asSource_stage : retained.asSource.selected.stage = retained.selected.stage := by rfl

/-- The complete original attempt, with Targets, preparations, bank and checking outcomes, is unchanged. -/
theorem asSource_attempt : retained.asSource.attempt = retained.request.attempt := by rfl

/-- The source view retains the same whole original global target allocation. -/
theorem asSource_targets : retained.asSource.targets = retained.targets := by rfl

/-- The same whole original preparation product remains at the source view's actual cached Targets. -/
theorem asSource_prepared : retained.asSource.prepared = retained.prepared := by rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Requested

end
