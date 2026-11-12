module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Whole-accuracy views of the SAME actual shifted target Request

The whole original positive request equality changes only its displayed
accuracy index. Selected stage, Request, global Targets, preparations and
all source/model callbacks remain the original retained values.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {nonempty : geometry.parents ≠ []} {current floor rootStage : Nat} {first last : AccuracyRequest}

/-- The exact original target Requested type at another displayed accuracy, retaining every original index.

This is only the original nominal Requested application. The explicit
retained input keeps its geometry, original nonempty proof, stage starts,
floor and root stage in client signatures without reconstructing that type.
-/
@[expose] def AtAccuracy (_retained : Requested geometry nonempty current floor rootStage first)
    (accuracy : AccuracyRequest) : Type _ := Requested geometry nonempty current floor rootStage accuracy

/-- Display the SAME whole original target Request at an exactly equal positive accuracy index.

Only equality elimination runs. No selection, StageAttempt, source, model,
query or completion is constructed; all original factory certificates are
retained with their complete actual input/output owners.
-/
@[expose] def castAccuracy (equal : first = last)
    (retained : Requested geometry nonempty current floor rootStage first) :
    Requested geometry nonempty current floor rootStage last := by
  cases equal
  exact retained

variable (equal : first = last) (retained : Requested geometry nonempty current floor rootStage first)

/-- Read the original target model at its literal channel and stage through the same retained request.

The exact model operation keeps the original cover, based chain and
preparation-family callback. Naming this readback changes no stage,
source, callback or programme owner and executes no new request.
-/
@[expose] def modelAt (channel : Fin 6) (stage : Nat) : PathModel :=
  model (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
    retained.request.covered retained.request.chain retained.request.attempt.preparationFamily channel stage

/-- The model readback is the original model on the same complete request and preparation family. -/
theorem modelAt_eq (channel : Fin 6) (stage : Nat) : retained.modelAt channel stage =
    model retained.request.covered retained.request.chain
      retained.request.attempt.preparationFamily channel stage := rfl

/-- The raw original model sample is the same scalar as the typed model readback.

Both sides use this request's literal cover, chain, preparation family,
channel and stage. The retained whole model equality is projected once;
no model, sample or preparation callback is executed by this proof.
-/
theorem modelAt_integralSample (channel : Fin 6) (stage : Nat) :
    (model retained.request.covered retained.request.chain
      retained.request.attempt.preparationFamily channel stage).integralSample =
    (retained.modelAt channel stage).integralSample :=
  congrArg (fun original : PathModel => original.integralSample) (retained.modelAt_eq channel stage).symm

/-- Whole-accuracy transport retains the complete SAME original sufficient target request. -/
theorem castAccuracy_heq : HEq (retained.castAccuracy equal) retained := by
  cases equal
  rfl

/-- The original selected stage is identical after whole-accuracy transport. -/
theorem castAccuracy_stage : (retained.castAccuracy equal).selected.stage = retained.selected.stage := by
  cases equal
  rfl

/-- The entire original target Request and all actual checking caches remain retained. -/
theorem castAccuracy_request : HEq (retained.castAccuracy equal).request retained.request := by
  cases equal
  rfl

/-- The original whole target global allocation remains the SAME owned data. -/
theorem castAccuracy_targets : HEq (retained.castAccuracy equal).targets retained.targets := by
  cases equal
  rfl

/-- The complete original target preparation product and its model/query owners are retained. -/
theorem castAccuracy_prepared : HEq (retained.castAccuracy equal).prepared retained.prepared := by
  cases equal
  rfl

/-- Whole-accuracy transport preserves an existing identity to the same other preparation owner.

The supplied identity is the actual preceding data readback. Equality
elimination changes only this request's accuracy display and keeps that
other owner intact; it supplies no numerical or geometric comparison.
-/
theorem castAccuracy_prepared_trans {Other : Type 1} {other : Other}
    (previous : HEq retained.prepared other) : HEq (retained.castAccuracy equal).prepared other := by
  cases equal
  exact previous

/-- Every original target model callback reads the SAME model at the SAME original stage.

The equality is scalar/data transport through the complete request, not
resampling, a smaller allowance, a new programme or a comparison bound.
-/
theorem castAccuracy_model (channel : Fin 6) (stage : Nat) :
    (retained.castAccuracy equal).modelAt channel stage = retained.modelAt channel stage := by
  cases equal
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Requested

end
