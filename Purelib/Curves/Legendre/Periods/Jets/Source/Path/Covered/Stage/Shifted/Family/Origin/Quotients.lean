module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Quotients
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference.Accuracy
import Purelib.Calculus.Jet.DifferenceQuotient
public import Purelib.Approximation.AccuracyRequest.Scaling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip.Increment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Nat.Order

/-! # Actual original-source derivatives of the retained zero/increment member pair

The original source jet and both independently retained members precede
accuracy. One origin Selection is computed before the original quotient
producer runs. Its literal maximum floor then pays every later original
source reading and all four value/first-derivative quotients.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- Every sufficiently late actual source/increment quotient approximates the original source first or second channel.

Order zero compares the value quotient with the actual source first
programme. Order one compares the first-channel quotient with its actual
source second programme. The source and shifted Frames remain distinct;
this is a finite all-later sample bound, not a derivative-realization input.
-/
abbrev SourceQuotientBounds {parameter increment : Canonical} {frame : Paths.Frame parameter}
    {target : Paths.Frame (parameter + increment)} (sourceJet : SynchronizedPeriodJet frame)
    (targetJet : SynchronizedPeriodJet target) (accuracy : AccuracyRequest) (firstFloor lastFloor : Nat) : Prop :=
  ∀ (order coordinate : Fin 2) (firstIndex lastIndex : Nat), firstFloor ≤ firstIndex → lastFloor ≤ lastIndex →
    Norm.Basic.normSq
      ((((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((targetJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((targetJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model lastIndex).integralSample -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) / increment -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.first coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.second coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) < accuracy.tolerance

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (sourceCompleted : source.attempt.OccurrenceFamily) (sourceJet : SynchronizedPeriodJet frame)
    (sourceFactory : sourceJet = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun stage => (sourceCompleted stage).val))
    {increment : Canonical}
    {zeroAdmitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (zero : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage 0 zeroAdmitted)
    (last : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)

/-- Compute one positive source-quotient request paying both the original strip and all four reference rows. -/
def sourceQuotientRequest (accuracy : AccuracyRequest) : AccuracyRequest :=
  allocation.incrementRequest
    (ShiftedGeometry.BetweenRows.referenceRequest (covered := covered) (accuracy.divide 16 (by decide +kernel)))

/-- Every increment paid by the source-quotient request stays in the same original strip allocation. -/
theorem sourceQuotientRequest_le_allocation (accuracy : AccuracyRequest) :
    (sourceQuotientRequest (covered := covered) (allocation := allocation) accuracy).tolerance ≤ allocation.bound := by
  unfold sourceQuotientRequest
  exact allocation.incrementRequest_le_bound _

/-- The same computed positive request pays the original four-row radius at one sixteenth tolerance. -/
theorem sourceQuotientRequest_le_reference (accuracy : AccuracyRequest) :
    (sourceQuotientRequest (covered := covered) (allocation := allocation) accuracy).tolerance ≤
      (ShiftedGeometry.BetweenRows.referenceRequest (covered := covered)
        (accuracy.divide 16 (by decide +kernel))).tolerance := by
  unfold sourceQuotientRequest
  exact allocation.incrementRequest_le_accuracy _

/-- The exact original origin Selection, original quotient-floor cache and paid all-four source bounds.

The whole Selection factory and the literal maximum/original-right floors
remain in this reducible view. It introduces no alternate schedule or
replacement jet; both supplied member caches stay nominal inputs.
-/
@[expose] def SourceQuotientFloors (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (originStart : Nat) : Type _ :=
    (origin : { value : Selection (errorScale (parent :: parents)) originStart
        ((accuracy.tolerance / 16) * Norm.Basic.normSq increment) //
      value = Selection.build (errorScale (parent :: parents))
        (errorScale_nonnegative (parameter := parameter) (frame := frame) (basis := basis) (parent :: parents))
        originStart ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)
        (Order.Arithmetic.mul_pos_direct
          (accuracy.divide 16 (by decide +kernel)).positive (Norm.Basic.normSq_pos nonzero)) }) ×
    (original : QuotientFloors (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (firstOffset := 0) (lastOffset := increment)
      (firstAdmitted := zeroAdmitted) (lastAdmitted := admitted) zero last) ×
    { floors : Nat × Nat // floors = (Nat.max original.val.1 origin.val.stage, original.val.2) ∧
      SourceQuotientBounds (parameter := parameter) (increment := increment) (frame := frame)
      (target := last.targetFrame) sourceJet last.jet accuracy floors.1 floors.2 }

include sourceCompleted sourceFactory in
/-- The actual origin Selection and existing quotient-floor certificate pay all four original-source quotients. -/
private theorem source_quotients_accurate (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤ (ShiftedGeometry.BetweenRows.referenceRequest
      (covered := covered) (accuracy.divide 16 (by decide +kernel))).tolerance)
    {originStart : Nat}
    (origin : Selection (errorScale (parent :: parents)) originStart
      ((accuracy.tolerance / 16) * Norm.Basic.normSq increment))
    (original : QuotientFloors (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) (firstOffset := 0) (lastOffset := increment)
      (firstAdmitted := zeroAdmitted) (lastAdmitted := admitted) zero last) :
    SourceQuotientBounds (parameter := parameter) (increment := increment) (frame := frame)
      (target := last.targetFrame) sourceJet last.jet accuracy
      (Nat.max original.val.1 origin.stage) original.val.2 := by
  intro order coordinate firstIndex lastIndex firstAfter lastAfter
  let share := accuracy.divide 16 (by decide +kernel)
  let base := ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.value coordinate).integral)
    (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.first coordinate).integral)
      (fun index => Fin.elim0 index)) order).model firstIndex).integralSample
  let slope := ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((sourceJet.first coordinate).integral)
    (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((sourceJet.second coordinate).integral)
      (fun index => Fin.elim0 index)) order).model firstIndex).integralSample
  let oldBase := ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((zero.jet.value coordinate).integral)
    (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((zero.jet.first coordinate).integral)
      (fun index => Fin.elim0 index)) order).model firstIndex).integralSample
  let oldSlope := ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((zero.jet.first coordinate).integral)
    (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((zero.jet.second coordinate).integral)
      (fun index => Fin.elim0 index)) order).model firstIndex).integralSample
  let output := ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((last.jet.value coordinate).integral)
    (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((last.jet.first coordinate).integral)
      (fun index => Fin.elim0 index)) order).model lastIndex).integralSample
  have originAfter := (Order.le_max_right original.val.1 origin.stage).trans firstAfter
  have originalAfter := (Order.le_max_left original.val.1 origin.stage).trans firstAfter
  have originPaid := origin.later_accurate (Nat.le_refl origin.stage)
  have baseBound := Shifted.source_base_difference_le
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (sourceCurrent := current) (sourceFloor := floor) (sourceRootStage := rootStage) (accuracy := reference)
    (target := zero.targetFrame) (admitted := zeroAdmitted) (widths := widths) (roots := roots)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    source ranges allocation zero.member sourceCompleted zero.completed sourceJet zero.jet sourceFactory zero.jet_eq
    order coordinate origin.stage firstIndex firstIndex originAfter originAfter
  have slopeBound := Shifted.source_slope_difference_le
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (sourceCurrent := current) (sourceFloor := floor) (sourceRootStage := rootStage) (accuracy := reference)
    (target := zero.targetFrame) (admitted := zeroAdmitted) (widths := widths) (roots := roots)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    source ranges allocation zero.member sourceCompleted zero.completed sourceJet zero.jet sourceFactory zero.jet_eq
    order coordinate origin.stage firstIndex firstIndex originAfter originAfter
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    small.trans (ShiftedGeometry.BetweenRows.referenceRequest_le_unit (covered := covered) share)
  have delta := Basic.sub_zero increment
  have deltaNonzero : increment - 0 ≠ 0 := fun equal => nonzero (delta.symm.trans equal)
  have deltaSmall := (congrArg Norm.Basic.normSq delta).trans_le small
  have originalPaid := ShiftedGeometry.BetweenRows.QuotientBounds.accurate
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (remaining := parents) (covered := covered)
    (firstOffset := 0) (lastOffset := increment) (firstFrame := zero.targetFrame) (lastFrame := last.targetFrame)
    (firstJet := zero.jet) (lastJet := last.jet) (firstFloor := original.val.1) (lastFloor := original.val.2)
    original.property share deltaNonzero deltaSmall order coordinate firstIndex lastIndex originalAfter lastAfter
  have denominator := congrArg (fun value : Canonical =>
    Canonical.normSq ((output - oldBase) / value - oldSlope)) delta
  have oldPaid : Norm.Basic.normSq ((output - oldBase) / increment - oldSlope) < accuracy.tolerance / 16 :=
    (Norm.Basic.normSq_eq_canonical _).trans_lt (denominator.symm.trans_lt originalPaid)
  exact Calculus.Jet.DifferenceQuotient.perturbation_lt accuracy increment base output slope oldBase oldSlope
    nonzero unit (baseBound.trans_lt originPaid) (slopeBound.trans_lt originPaid) oldPaid

include sourceCompleted sourceFactory in
/-- Select the origin payment before one original quotient producer and retain its actual all-later source floors.

The supplied zero/increment members and source jet are fixed original
caches. One Selection pays both needed source/zero discrepancies for all
four rows. The original quotientFloors operation constructs its genuine
comparison pair once, with its first comparison starting above the selected
origin stage. This dependency computes the origin before that preparation.
Only the returned first floor is enlarged; every later pair
then obeys the requested actual source first/second quotient estimate.
-/
def sourceQuotientFloors (accuracy : AccuracyRequest) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤ (ShiftedGeometry.BetweenRows.referenceRequest
      (covered := covered) (accuracy.divide 16 (by decide +kernel))).tolerance)
    (firstStart lastStart freshStart originStart : Nat) (spatial : AccuracyRequest) :
    SourceQuotientFloors (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
      (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
      (targetRootStage := targetRootStage) sourceJet zero last accuracy nonzero originStart :=
  let share := accuracy.divide 16 (by decide +kernel)
  let origin := Selection.build (errorScale (parent :: parents))
    (errorScale_nonnegative (parameter := parameter) (frame := frame) (basis := basis) (parent :: parents))
    originStart (share.tolerance * Norm.Basic.normSq increment)
    (Order.Arithmetic.mul_pos_direct share.positive (Norm.Basic.normSq_pos nonzero))
  have unit := small.trans (ShiftedGeometry.BetweenRows.referenceRequest_le_unit (covered := covered) share)
  have delta := Basic.sub_zero increment
  have deltaNonzero : increment - 0 ≠ 0 := fun equal => nonzero (delta.symm.trans equal)
  let original := quotientFloors (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots)
    (widths := widths) (targetCurrent := targetCurrent) (targetFloor := targetFloor)
    (targetRootStage := targetRootStage) (firstOffset := 0) (lastOffset := increment)
    (firstAdmitted := zeroAdmitted) (lastAdmitted := admitted) zero last
    (Nat.max firstStart origin.stage) lastStart freshStart
    ((congrArg Norm.Basic.normSq delta).trans_le unit) deltaNonzero spatial
  let floors := (Nat.max original.val.1 origin.stage, original.val.2)
  ⟨⟨origin, rfl⟩, original, ⟨floors, rfl, source_quotients_accurate
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (source := source) (ranges := ranges) (allocation := allocation) (root := root) (roots := roots) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    sourceCompleted sourceJet sourceFactory zero last accuracy nonzero small origin original⟩⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
