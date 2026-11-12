module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Reselection
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Calculus.Jet.Quadratic.Perturbation
import Purelib.Calculus.Jet.Quadratic.Chord
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Alignment
import Purelib.Tactic.Ring

/-! # Fixed-reference all-later parameter quotient bounds

The existing two-offset certificate keeps its actual independently paid
selected readings. Three original approximation comparisons pay the
reference readings at every permitted later pair. Their perturbation
factors are one; the original factor therefore becomes four times F+3.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows.Integral

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Comparison)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- Every sufficiently late pair of fixed-reference readings pays the actual two-offset divided-difference bound.

The three supplied objects are original finite approximation comparisons,
with their actual left floors and right-stage payments. No numerical
Taylor or reading-error inequality is an input. The same retained weighted
certificate supplies the selected base, output, slope and factor; its
perturbation derives the displayed reference bound internally.
-/
theorem reference_differenceQuotient_le
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      Acquisition.Segment.RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      Acquisition.Segment.RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (lastWhole_eq : lastWhole =
      ShiftedGeometry.build prepared ranges allocation lastAdmitted lastWidths lastBlocks oldGeometry oldRoots)
    {firstReferenceCurrent lastReferenceCurrent : Nat}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstReference : Requested firstWhole firstNonempty firstReferenceCurrent firstFloor firstRootStage
      firstAccuracy)
    (lastReference : Requested lastWhole lastNonempty lastReferenceCurrent lastFloor lastRootStage lastAccuracy)
    (firstCompleted : firstReference.request.attempt.OccurrenceFamily)
    (lastCompleted : lastReference.request.attempt.OccurrenceFamily)
    (firstJet : SynchronizedPeriodJet firstFrame) (lastJet : SynchronizedPeriodJet lastFrame)
    (firstFactory : firstJet = StageAttempt.OccurrenceCompletion.jet (parameter := parameter + firstOffset)
      (frame := firstFrame) (basis := basis) (count := count) (floor := firstFloor) (rootStage := firstRootStage)
      firstReference.request.covered firstReference.request.chain (fun selected => (firstCompleted selected).val))
    (lastFactory : lastJet = StageAttempt.OccurrenceCompletion.jet (parameter := parameter + lastOffset)
      (frame := lastFrame) (basis := basis) (count := count) (floor := lastFloor) (rootStage := lastRootStage)
      lastReference.request.covered lastReference.request.chain (fun selected => (lastCompleted selected).val))
    (order coordinate : Fin 2) {firstStart lastStart freshStart : Nat}
    (base : Comparison
      (firstReference.request.programme (Specification.Table.baseIndex order coordinate)).approximation
      (firstReference.request.originalProgramme (Specification.Table.baseIndex order coordinate)).approximation
      firstStart freshStart (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero).tolerance)
    (slope : Comparison
      (firstReference.request.programme (Specification.Table.slopeIndex order coordinate)).approximation
      (firstReference.request.originalProgramme (Specification.Table.slopeIndex order coordinate)).approximation
      firstStart freshStart (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero).tolerance)
    (output : Comparison
      (lastReference.request.programme (Specification.Table.baseIndex order coordinate)).approximation
      (lastReference.request.originalProgramme (Specification.Table.baseIndex order coordinate)).approximation
      lastStart freshStart (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero).tolerance)
    (basePaid : base.rightIndex ≤ firstRequested.selected.stage)
    (slopePaid : slope.rightIndex ≤ firstRequested.selected.stage)
    (outputPaid : output.rightIndex ≤ lastRequested.selected.stage)
    (firstIndex lastIndex : Nat) (firstAfter : Nat.max base.leftIndex slope.leftIndex ≤ firstIndex)
    (lastAfter : output.leftIndex ≤ lastIndex) :
    Canonical.normSq
      ((((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((lastJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((lastJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model lastIndex).integralSample -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((firstJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((firstJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) / (lastOffset - firstOffset) -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((firstJet.first coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((firstJet.second coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) ≤
      4 * (ValueBlocks.factor (covered := covered) order coordinate + 3) *
        Canonical.normSq (lastOffset - firstOffset) := by
  let baseReading := ((firstReference.request.programme
    (Specification.Table.baseIndex order coordinate)).model firstIndex).integralSample
  let outputReading := ((lastReference.request.programme
    (Specification.Table.baseIndex order coordinate)).model lastIndex).integralSample
  let slopeReading := ((firstReference.request.programme
    (Specification.Table.slopeIndex order coordinate)).model firstIndex).integralSample
  have baseComparison := firstRequested.comparison_selected
    (parameter := parameter) (increment := firstOffset) (basis := basis) (target := firstFrame)
    (count := count) (geometry := firstWhole) (current := firstCurrent) (floor := firstFloor)
    (rootStage := firstRootStage)
    (accuracy := spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))
    (referenceIndex := firstReference.selected.stage) (referenceRootStage := firstRootStage)
    (comparisonAccuracy := Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)
    (channel := Specification.Table.baseIndex order coordinate) firstReference.request base
    ((Order.le_max_left base.leftIndex slope.leftIndex).trans firstAfter) basePaid
  have outputComparison := lastRequested.comparison_selected
    (parameter := parameter) (increment := lastOffset) (basis := basis) (target := lastFrame)
    (count := count) (geometry := lastWhole) (current := lastCurrent) (floor := lastFloor)
    (rootStage := lastRootStage)
    (accuracy := spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))
    (referenceIndex := lastReference.selected.stage) (referenceRootStage := lastRootStage)
    (comparisonAccuracy := Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)
    (channel := Specification.Table.baseIndex order coordinate) lastReference.request output lastAfter outputPaid
  have slopeComparison := firstRequested.comparison_selected
    (parameter := parameter) (increment := firstOffset) (basis := basis) (target := firstFrame)
    (count := count) (geometry := firstWhole) (current := firstCurrent) (floor := firstFloor)
    (rootStage := firstRootStage)
    (accuracy := spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))
    (referenceIndex := firstReference.selected.stage) (referenceRootStage := firstRootStage)
    (comparisonAccuracy := Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)
    (channel := Specification.Table.slopeIndex order coordinate) firstReference.request slope
    ((Order.le_max_right base.leftIndex slope.leftIndex).trans firstAfter) slopePaid
  have baseReadback := actual.base (parameter := parameter) (firstOffset := firstOffset)
    (lastOffset := lastOffset) (frame := frame) (basis := basis) (firstFrame := firstFrame) (lastFrame := lastFrame)
    (count := count) (floor := floor) (covered := covered) (prepared := prepared) (ranges := ranges)
    (allocation := allocation) (firstBlocks := firstBlocks) (lastBlocks := lastBlocks)
    (firstRequested := firstRequested) (lastRequested := lastRequested) (rows := rows)
    firstWhole_eq order coordinate
  have outputReadback := actual.output (parameter := parameter) (firstOffset := firstOffset)
    (lastOffset := lastOffset) (frame := frame) (basis := basis) (firstFrame := firstFrame) (lastFrame := lastFrame)
    (count := count) (floor := floor) (covered := covered) (prepared := prepared) (ranges := ranges)
    (allocation := allocation) (firstBlocks := firstBlocks) (lastBlocks := lastBlocks)
    (firstRequested := firstRequested) (lastRequested := lastRequested) (rows := rows)
    lastWhole_eq order coordinate
  have slopeReadback := actual.slope (parameter := parameter) (firstOffset := firstOffset)
    (lastOffset := lastOffset) (frame := frame) (basis := basis) (firstFrame := firstFrame) (lastFrame := lastFrame)
    (count := count) (floor := floor) (covered := covered) (prepared := prepared) (ranges := ranges)
    (allocation := allocation) (firstBlocks := firstBlocks) (lastBlocks := lastBlocks)
    (firstRequested := firstRequested) (lastRequested := lastRequested) (rows := rows)
    firstWhole_eq order coordinate
  have baseBound : Norm.Basic.normSq (baseReading - (actual.certificates order coordinate).base) ≤
      1 * Norm.Basic.normSq (lastOffset - firstOffset) ^ 2 :=
    ((congrArg (fun reading : Canonical => Norm.Basic.normSq (baseReading - reading))
      baseReadback).trans_le baseComparison.le).trans_eq (Field.one_mul _).symm
  have outputBound : Norm.Basic.normSq (outputReading - (actual.certificates order coordinate).output) ≤
      1 * Norm.Basic.normSq (lastOffset - firstOffset) ^ 2 :=
    ((congrArg (fun reading : Canonical => Norm.Basic.normSq (outputReading - reading))
      outputReadback).trans_le outputComparison.le).trans_eq (Field.one_mul _).symm
  have slopeBound : Norm.Basic.normSq (slopeReading - (actual.certificates order coordinate).slope) ≤
      1 * Norm.Basic.normSq (lastOffset - firstOffset) ^ 2 :=
    ((congrArg (fun reading : Canonical => Norm.Basic.normSq (slopeReading - reading))
      slopeReadback).trans_le slopeComparison.le).trans_eq (Field.one_mul _).symm
  have oneNonnegative : (0 : Rational) ≤ 1 := by decide +kernel
  let retained := (actual.certificates order coordinate).perturb baseReading outputReading slopeReading
    1 1 1 oneNonnegative oneNonnegative oneNonnegative unit baseBound outputBound slopeBound
  have quotient := retained.differenceQuotient_le nonzero
  change Canonical.normSq ((outputReading - baseReading) / (lastOffset - firstOffset) - slopeReading) ≤
    4 * ((actual.certificates order coordinate).factor + 1 + 1 + 1) *
      Canonical.normSq (lastOffset - firstOffset) at quotient
  have factor := congrArg (fun value : Rational => 4 * (value + 1 + 1 + 1))
    (actual.factor_eq order coordinate)
  have scalar : 4 * (ValueBlocks.factor (covered := covered) order coordinate + 1 + 1 + 1) =
      4 * (ValueBlocks.factor (covered := covered) order coordinate + 3) := by ring1
  have bounded := quotient.trans_eq (congrArg
    (fun value : Rational => value * Canonical.normSq (lastOffset - firstOffset)) (factor.trans scalar))
  have firstBase := firstReference.request.occurrence_base_model (parameter := parameter)
    (increment := firstOffset) (target := firstFrame) (basis := basis) (count := count)
    (geometry := firstWhole) (index := firstReference.selected.stage) (floor := firstFloor)
    (rootStage := firstRootStage) firstCompleted firstJet firstFactory order coordinate firstIndex
  have lastBase := lastReference.request.occurrence_base_model (parameter := parameter)
    (increment := lastOffset) (target := lastFrame) (basis := basis) (count := count)
    (geometry := lastWhole) (index := lastReference.selected.stage) (floor := lastFloor)
    (rootStage := lastRootStage) lastCompleted lastJet lastFactory order coordinate lastIndex
  have firstSlope := firstReference.request.occurrence_slope_model (parameter := parameter)
    (increment := firstOffset) (target := firstFrame) (basis := basis) (count := count)
    (geometry := firstWhole) (index := firstReference.selected.stage) (floor := firstFloor)
    (rootStage := firstRootStage) firstCompleted firstJet firstFactory order coordinate firstIndex
  have difference := congrArg₂ (fun output base : Canonical => output - base)
    (congrArg (fun value : PathModel => value.integralSample) lastBase)
    (congrArg (fun value : PathModel => value.integralSample) firstBase)
  have displayed := congrArg₂ (fun difference slope : Canonical =>
    Canonical.normSq (difference / (lastOffset - firstOffset) - slope)) difference
    (congrArg (fun value : PathModel => value.integralSample) firstSlope)
  exact displayed.trans_le bounded

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows.Integral

end
