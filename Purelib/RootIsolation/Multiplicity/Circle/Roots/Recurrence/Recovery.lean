module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Outside
public import Purelib.Polynomial.Recurrence.Mode.Hermite.Recovery

/-!
# Paid outside-coordinate recovery in the original recurrence ledger

The same full characteristic basis, original owner labels and physical
floors prepare one complete late-window request before observations. Its
actual common root association pays the source-fixed matrix error bounds.
Only a genuine physical coefficient lower bound forces a window obstruction;
formal nonzeroness in the original coefficient algebra is insufficient.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Recovery

open Purelib
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.Polynomial.Recurrence.Mode
open Multiplicity.Roots.Stages.Reading renaming Request → StageRequest

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}
variable {inventory : PositiveInventory clearance input family} {argument : PositiveArgument inventory} {rows : Nat}

/-- Full original recurrence coefficients, including inside and zero-root coordinates. -/
abbrev Coefficients (retained : Recurrence argument rows) :=
  Vec retained.prepared.separation.Scalar retained.recurrence.fullWord.length

/-- The original source-fixed full-basis recovery request at the same cached outside labels and floor. -/
abbrev Schedule (retained : Recurrence argument rows)
    (outside : Reading.Bounds.Outside retained.bounds retained.owners)
    (coefficients : Coefficients retained) (lower target : Rational) :=
  Hermite.Recovery.Request retained.recurrence.basis retained.parameters.finalWeight retained.parameters.finalGain
    coefficients (fun tag => outside.selected tag) outside.commonFloor lower target

set_option genInjectivity false in
/-- One original full-window recovery schedule and its actual backward root-model budget.

Both positive physical thresholds precede the schedule's late index and
tolerance. Every parent remains the same original recurrence ledger; no
root bank, full basis, owner alignment or geometric bound is rebuilt.
-/
structure Request (retained : Recurrence argument rows) (coefficients : Coefficients retained)
    (lower target : Rational) where
  /-- The physical coefficient threshold is positive before selecting the late index. -/
  lowerPositive : 0 < lower
  /-- The desired window bound is positive before preparing any observation. -/
  targetPositive : 0 < target
  /-- Original outside labels, physical floors and their source-fixed common endpoint. -/
  outside : Reading.Bounds.Outside retained.bounds retained.owners
  /-- The outside cache is the original constructor on the same retained owners and physical bounds. -/
  outside_eq : outside = Reading.Bounds.Outside.prepare retained.bounds retained.owners
  /-- The same full original basis prepares its paid complete late-window schedule. -/
  schedule : Schedule retained outside coefficients lower target
  /-- The complete schedule is the original producer at those exact source-fixed thresholds. -/
  schedule_eq : schedule = Hermite.Recovery.Request.prepare retained.recurrence.basis
    retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
    coefficients (fun tag => outside.selected tag) outside.commonFloor outside.commonFloorAboveOne
    lower lowerPositive target targetPositive
  /-- The original whole-context backward request pays that exact computed endpoint tolerance. -/
  stages : StageRequest retained.parameters schedule.tolerance
  /-- The actual stage request is computed once from the retained recovery schedule. -/
  stages_eq : stages = StageRequest.prepare retained.parameters schedule.tolerance schedule.tolerance_positive

namespace Request

/-- Retain checked complete recovery and budget caches without replaying any original producer. -/
@[expose] def ofCaches (retained : Recurrence argument rows) (coefficients : Coefficients retained)
    (lower target : Rational) (lowerPositive : 0 < lower) (targetPositive : 0 < target)
    (outside : Reading.Bounds.Outside retained.bounds retained.owners)
    (outsideEq : outside = Reading.Bounds.Outside.prepare retained.bounds retained.owners)
    (schedule : Schedule retained outside coefficients lower target)
    (scheduleEq : schedule = Hermite.Recovery.Request.prepare retained.recurrence.basis
      retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
      coefficients (fun tag => outside.selected tag) outside.commonFloor outside.commonFloorAboveOne
      lower lowerPositive target targetPositive)
    (stages : StageRequest retained.parameters schedule.tolerance)
    (stagesEq : stages = StageRequest.prepare retained.parameters schedule.tolerance schedule.tolerance_positive) :
    Request retained coefficients lower target :=
  { lowerPositive, targetPositive, outside, outside_eq := outsideEq, schedule, schedule_eq := scheduleEq
    stages, stages_eq := stagesEq }

/-- Prepare the same original full-window recovery and root-model payment before making observations. -/
@[expose] def prepare (retained : Recurrence argument rows) (coefficients : Coefficients retained)
    (lower : Rational) (lowerPositive : 0 < lower) (target : Rational) (targetPositive : 0 < target) :
    Request retained coefficients lower target :=
  let outside := Reading.Bounds.Outside.prepare retained.bounds retained.owners
  let schedule := Hermite.Recovery.Request.prepare retained.recurrence.basis
    retained.parameters.finalWeight retained.parameters.finalGain retained.parameters.finalGain_nonnegative
    coefficients (fun tag => outside.selected tag) outside.commonFloor outside.commonFloorAboveOne
    lower lowerPositive target targetPositive
  let stages := StageRequest.prepare retained.parameters schedule.tolerance schedule.tolerance_positive
  ofCaches retained coefficients lower target lowerPositive targetPositive outside rfl schedule rfl stages rfl

variable {retained : Recurrence argument rows} {coefficients : Coefficients retained} {lower target : Rational}

/-- Complete retained source-fixed cache equations restore the same original preparation. -/
theorem restore (request : Request retained coefficients lower target) :
    request = prepare retained coefficients lower request.lowerPositive target request.targetPositive := by
  cases request with
  | mk lowerPositive targetPositive outside outsideEq schedule scheduleEq stages stagesEq =>
      cases outsideEq
      cases scheduleEq
      cases stagesEq
      rfl

/-- The exact original common-root association type at the same retained backward budget. -/
abbrev Association (request : Request retained coefficients lower target) :=
  Reading.Bank.Association retained.prepared.separation.prepared.contexts_eq argument
    retained.bounds request.stages.budget

/-- The exact original Gaussian reading owned by a same-budget retained association. -/
abbrev Reading (request : Request retained coefficients lower target) (association : request.Association) :=
  association.model.finalReading

end Request

set_option genInjectivity false in
/-- The actual same-ledger root model and observed full-window recovery caches.

The original factor association is prepared once from the retained request.
Its exact common reading supplies the Gaussian recovery cache, including
the original late values and physically outside-only inverse coefficients.
-/
structure Observation {retained : Recurrence argument rows} {coefficients : Coefficients retained}
    {lower target : Rational} (request : Request retained coefficients lower target) where
  /-- The original automatic common-root association at this exact retained budget. -/
  association : request.Association
  /-- The complete association is the original producer on the same already retained ledger caches. -/
  association_eq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages
  /-- The actual full late-window reading and outside-only physical recovery. -/
  observed : Hermite.Recovery.Observation request.schedule association.model.finalReading
  /-- All observed caches come from the same actual common reading once. -/
  observed_eq : observed = Hermite.Recovery.Observation.prepare request.schedule association.model.finalReading

namespace Observation

variable {retained : Recurrence argument rows} {coefficients : Coefficients retained} {lower target : Rational}
variable {request : Request retained coefficients lower target}

/-- Retain checked complete association and observation caches without rebuilding their source owners. -/
@[expose] def ofCaches (request : Request retained coefficients lower target) (association : request.Association)
    (associationEq : association = Reading.Bank.prepare retained.prepared argument retained.bounds request.stages)
    (observed : Hermite.Recovery.Observation request.schedule association.model.finalReading)
    (observedEq : observed = Hermite.Recovery.Observation.prepare request.schedule association.model.finalReading) :
    Observation request := { association, association_eq := associationEq, observed, observed_eq := observedEq }

/-- Construct one original paid common model and consume its reading in the same complete late-window cache. -/
@[expose] def prepare (request : Request retained coefficients lower target) : Observation request :=
  let association := Reading.Bank.prepare retained.prepared argument retained.bounds request.stages
  let observed := Hermite.Recovery.Observation.prepare request.schedule association.model.finalReading
  ofCaches request association rfl observed rfl

/-- Read the same actual common Gaussian model directly from its retained association. -/
@[expose] def reading (observation : Observation request) := observation.association.model.finalReading

/-- The actual common reading retains the fixed source gain chosen before this recovery request. -/
theorem gain_eq (observation : Observation request) :
    observation.reading.gain = retained.parameters.finalGain := observation.association.final_gain

/-- The same original backward budget pays the computed recovery tolerance. -/
theorem error_le (observation : Observation request) :
    observation.reading.error ≤ request.schedule.tolerance := observation.association.error_le

/-- The same original embedded Gaussian coefficient retains its exact scalar value in the actual common reading. -/
theorem read_scalar (observation : Observation request) (value : Canonical) :
    observation.reading.read (retained.prepared.separation.prepared.stages.embed value) = value :=
  observation.association.read_scalar value

/-- An original Gaussian scalar coefficient reads exactly with no multiplication-error payment. -/
theorem coefficient_scalar (observation : Observation request) (column : Fin retained.recurrence.fullWord.length)
    (value : Canonical)
    (same : coefficients column = retained.prepared.separation.prepared.stages.embed value) :
    observation.observed.coefficientValues column = value := by
  rewrite [observation.observed.coefficientValues_eq, same]
  exact observation.read_scalar value

/-- Each observed entry reads the same original full-basis combination at its chosen late index. -/
theorem window_eq (observation : Observation request) (index : Fin retained.recurrence.fullWord.length) :
    observation.observed.values index = observation.reading.read
      (LinearAlgebra.Matrix.Rectangular.apply
        (retained.recurrence.basis.horizonFrom request.schedule.start retained.recurrence.fullWord.length)
        coefficients index) := by
  rewrite [observation.observed.values_eq, request.schedule.values_eq, request.schedule.matrix_eq]
  rfl

/-- Every cached physical outside root is bounded by the same source-fixed common outside floor. -/
theorem outside (observation : Observation request) (tag : Fin retained.prepared.bank.blocks.length)
    (selected : request.outside.selected tag = true) :
    request.outside.commonFloor ≤ Norm.Basic.normSq (observation.observed.roots tag) := by
  rewrite [observation.observed.roots_eq]
  have original := Reading.Bank.outside retained.prepared retained.owners observation.association tag
    (request.outside.outside tag selected)
  rewrite [← request.outside.floors_at] at original
  exact (request.outside.common_le tag selected).trans original

/-- The public finite outcome concerns this exact original full-word coefficient occurrence. -/
abbrev Outcome (observation : Observation request) (column : Fin retained.recurrence.fullWord.length) :=
  Hermite.Recovery.Observation.Outcome observation.observed column

/-- Search the same already observed late window, retaining the actual obstruction or physical threshold failure. -/
@[expose] def check (observation : Observation request) (column : Fin retained.recurrence.fullWord.length)
    (selected : request.outside.selected (retained.recurrence.fullWord[column.val]'column.isLt) = true) :
    observation.Outcome column :=
  observation.observed.check observation.gain_eq observation.outside observation.error_le column selected

/-- Genuine physical coefficient evidence forces a concrete large entry of the same original complete late window. -/
@[expose] def obstruction (observation : Observation request) (column : Fin retained.recurrence.fullWord.length)
    (selected : request.outside.selected (retained.recurrence.fullWord[column.val]'column.isLt) = true)
    (coefficientBound : lower ≤ Norm.Basic.normSq (observation.observed.coefficientValues column)) :
    {index : Fin retained.recurrence.fullWord.length //
      target < Norm.Basic.normSq (observation.observed.values index)} :=
  observation.observed.obstruction observation.gain_eq observation.outside observation.error_le
    column selected coefficientBound

/-- A source-fixed nonzero Gaussian coefficient supplies its physical recovery evidence automatically.

The request threshold is its original positive Gaussian quadrance, chosen
before observations. Exact original scalar ownership supplies the actual
coefficient readback; no faithfulness premise for formal coefficients is used.
-/
@[expose] def scalar_obstruction (observation : Observation request)
    (column : Fin retained.recurrence.fullWord.length)
    (selected : request.outside.selected (retained.recurrence.fullWord[column.val]'column.isLt) = true)
    (value : Canonical)
    (same : coefficients column = retained.prepared.separation.prepared.stages.embed value)
    (threshold : lower = Norm.Basic.normSq value) :
    {index : Fin retained.recurrence.fullWord.length //
      target < Norm.Basic.normSq (observation.observed.values index)} := by
  apply observation.obstruction column selected
  exact (threshold.trans (congrArg Norm.Basic.normSq (observation.coefficient_scalar column value same)).symm).le

/-- Complete retained cache equations restore the same automatic paid observation. -/
theorem restore (observation : Observation request) : observation = prepare request := by
  cases observation with
  | mk association associationEq observed observedEq =>
      cases associationEq
      cases observedEq
      rfl

end Observation
end Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Recovery

end
