module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Reselection
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Position.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Alignment
import Purelib.Data.List.DependentProduct
import Purelib.Data.Nat.Order
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Alignment

/-! # Four reference-jet quotients from one actual requested row bank

The two reference Requests, positional completions and given jets precede
the derivative request. One pair of six-channel comparisons pays one fresh
Request pair. The same Positions, Alignments, BetweenRows and Integral
then serve all four adjacent-derivative coordinate bounds.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- All four adjacent-derivative coordinate quotients of the SAME given jets obey the original geometry factor.

The displayed natural floors apply to the actual original jet readings.
Both independent Frame owners and all six original programmes remain
unchanged; this is the exact quantified inequality, without new data.
-/
abbrev QuotientBounds
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: remaining))
    (firstJet : SynchronizedPeriodJet firstFrame) (lastJet : SynchronizedPeriodJet lastFrame)
    (firstFloor lastFloor : Nat) : Prop :=
  ∀ (order coordinate : Fin 2) (firstIndex lastIndex : Nat), firstFloor ≤ firstIndex → lastFloor ≤ lastIndex →
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
      4 * (ValueBlocks.factor (covered := covered) order coordinate + 3) * Canonical.normSq (lastOffset - firstOffset)

/-- The exact continuation retaining the original two comparison banks and their one shared requested-row construction.

Every argument is an existing owner or certificate: both fresh Requests,
actual Positions and Alignments, the complete four-row cache and its one
Integral. The final proposition is derived internally by the constructor;
it is not an input admission or a replacement context record.
-/
abbrev ReferenceConsumer
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound)
    (lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound)
    (firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest)
    (firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths)
    (lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths)
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstReferenceCurrent firstFloor firstRootStage lastReferenceCurrent lastFloor lastRootStage : Nat}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstReference : Requested firstWhole firstNonempty firstReferenceCurrent firstFloor firstRootStage firstAccuracy)
    (lastReference : Requested lastWhole lastNonempty lastReferenceCurrent lastFloor lastRootStage lastAccuracy)
    (firstJet : SynchronizedPeriodJet firstFrame) (lastJet : SynchronizedPeriodJet lastFrame)
    (firstStart lastStart freshStart : Nat)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (nonzero : lastOffset - firstOffset ≠ 0) (spatial : AccuracyRequest) (Result : Type u) : Type _ :=
  (first : firstReference.request.Comparisons firstStart freshStart
    (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)) →
  (last : lastReference.request.Comparisons lastStart freshStart
    (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)) →
  (firstFresh : Requested firstWhole firstNonempty
    (Nat.max freshStart (Nat.max (Request.Comparisons.rightFloor first) (Request.Comparisons.rightFloor last)))
    firstFloor firstRootStage (spatial.minimum (Variation.Sampling.incrementRequest
      (lastOffset - firstOffset) nonzero))) →
  (lastFresh : Requested lastWhole lastNonempty
    (Nat.max freshStart (Nat.max (Request.Comparisons.rightFloor first) (Request.Comparisons.rightFloor last)))
    lastFloor lastRootStage (spatial.minimum (Variation.Sampling.incrementRequest
      (lastOffset - firstOffset) nonzero))) →
  (∀ channel, (first.get channel).rightIndex ≤ firstFresh.selected.stage) →
  (∀ channel, (last.get channel).rightIndex ≤ lastFresh.selected.stage) →
  (firstPositions : Position.Family firstBlocks firstFresh.request) →
  (lastPositions : Position.Family lastBlocks lastFresh.request) →
  (firstAligned : DependentProduct (parent :: remaining) (fun outer =>
    Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
      (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)) →
  (lastAligned : DependentProduct (parent :: remaining) (fun outer =>
    Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
      (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)) →
  (rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
    firstBlocks lastBlocks unit nonzero spatial firstFresh lastFresh
    firstPositions lastPositions firstAligned lastAligned) →
  (_actual : Integral rows) →
  QuotientBounds covered firstJet lastJet
    (Request.Comparisons.leftFloor first) (Request.Comparisons.leftFloor last) → Result

/-- Reselect one actual Request pair and retain one four-row bank with all-later bounds for the fixed given jets.

Both reference completions, given jets and their original factory equations
precede derivative accuracy. One original withReselectedPair call retains
two six-channel comparisons before the fresh Requests. Exact original
geometry equations construct both Position families, original per-parent
root comparisons construct both Alignment products, and one row producer
and one Integral serve all four bounds. No request executes per row.
-/
def withReferenceQuotients
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound)
    (lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound)
    (firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest)
    (firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths)
    (lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths)
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (lastWhole_eq : lastWhole =
      ShiftedGeometry.build prepared ranges allocation lastAdmitted lastWidths lastBlocks oldGeometry oldRoots)
    {firstReferenceCurrent firstFloor firstRootStage lastReferenceCurrent lastFloor lastRootStage : Nat}
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstReference : Requested firstWhole firstNonempty firstReferenceCurrent firstFloor firstRootStage firstAccuracy)
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
    (firstStart lastStart freshStart : Nat)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (nonzero : lastOffset - firstOffset ≠ 0) (spatial : AccuracyRequest)
    {Result : Type u}
    (consume : ReferenceConsumer prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks firstReference lastReference firstJet lastJet firstStart lastStart freshStart
      unit nonzero spatial Result) : Result :=
  Requested.withReselectedPair
    (parameter := parameter) (firstOffset := firstOffset) (lastOffset := lastOffset) (basis := basis) (count := count)
    (firstFrame := firstFrame) (lastFrame := lastFrame)
    (firstPoint := startPoint parent) (lastPoint := startPoint parent)
    (firstRoot := (DependentProduct.get (parent :: remaining) firstBlocks 0).first.root.value.name)
    (lastRoot := (DependentProduct.get (parent :: remaining) lastBlocks 0).first.root.value.name)
    (firstGeometry := firstWhole) (lastGeometry := lastWhole)
    (firstNonempty := firstNonempty) (lastNonempty := lastNonempty)
    (firstCurrent := firstReferenceCurrent) (firstFloor := firstFloor) (firstRootStage := firstRootStage)
    (lastCurrent := lastReferenceCurrent) (lastFloor := lastFloor) (lastRootStage := lastRootStage)
    (firstAccuracy := firstAccuracy) (lastAccuracy := lastAccuracy)
    firstReference lastReference firstStart lastStart freshStart (lastOffset - firstOffset) nonzero spatial
    (fun first last firstFresh lastFresh firstPaid lastPaid _firstBounds _lastBounds =>
      let start := Nat.max freshStart (Nat.max (Request.Comparisons.rightFloor first)
        (Request.Comparisons.rightFloor last))
      let firstPositions := Position.Family.build
        (parameter := parameter) (increment := firstOffset) (frame := frame) (basis := basis) (target := firstFrame)
        (count := count) (firstParent := parent) (remaining := remaining) (covered := covered)
        (floor := floor) (original := original) (stage := stage) (targets := targets) (prepared := prepared)
        (ranges := ranges) (allocation := allocation) (admitted := firstAdmitted) (widths := firstWidths)
        (whole := firstWhole) (requestIndex := firstFresh.selected.stage)
        (globalFloor := firstFloor) (rootStage := firstRootStage) (oldGeometry := oldGeometry) (oldRoots := oldRoots)
        firstBlocks firstFresh.request firstWhole_eq
      let lastPositions := Position.Family.build
        (parameter := parameter) (increment := lastOffset) (frame := frame) (basis := basis) (target := lastFrame)
        (count := count) (firstParent := parent) (remaining := remaining) (covered := covered)
        (floor := floor) (original := original) (stage := stage) (targets := targets) (prepared := prepared)
        (ranges := ranges) (allocation := allocation) (admitted := lastAdmitted) (widths := lastWidths)
        (whole := lastWhole) (requestIndex := lastFresh.selected.stage)
        (globalFloor := lastFloor) (rootStage := lastRootStage) (oldGeometry := oldGeometry) (oldRoots := oldRoots)
        lastBlocks lastFresh.request lastWhole_eq
      let firstAligned := DependentProduct.ofFn (parent :: remaining) (fun outer =>
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.align)
      let lastAligned := DependentProduct.ofFn (parent :: remaining) (fun outer =>
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.align)
      let rows := BetweenRows.build
        (parameter := parameter) (firstOffset := firstOffset) (lastOffset := lastOffset) (frame := frame)
        (basis := basis) (firstFrame := firstFrame) (lastFrame := lastFrame) (count := count) (floor := floor)
        (parent := parent) (remaining := remaining) (covered := covered) (targets := targets)
        (firstWhole := firstWhole) (lastWhole := lastWhole)
        (firstNonempty := firstNonempty) (lastNonempty := lastNonempty)
        (firstCurrent := start) (firstFloor := firstFloor) (firstRootStage := firstRootStage)
        (lastCurrent := start) (lastFloor := lastFloor) (lastRootStage := lastRootStage)
        prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths firstBlocks lastBlocks
        unit nonzero spatial firstFresh lastFresh firstPositions lastPositions firstAligned lastAligned
      let actual := Integral.build
        (parameter := parameter) (firstOffset := firstOffset) (lastOffset := lastOffset) (frame := frame)
        (basis := basis) (firstFrame := firstFrame) (lastFrame := lastFrame) (count := count) (floor := floor)
        (parent := parent) (remaining := remaining) (covered := covered) (prepared := prepared)
        (ranges := ranges) (allocation := allocation) (firstBlocks := firstBlocks) (lastBlocks := lastBlocks)
        (firstRequested := firstFresh) (lastRequested := lastFresh) (rows := rows)
      have bounded : QuotientBounds covered firstJet lastJet
          (Request.Comparisons.leftFloor first) (Request.Comparisons.leftFloor last) := by
        intro order coordinate firstIndex lastIndex firstAfter lastAfter
        exact actual.reference_differenceQuotient_le
          (parameter := parameter) (firstOffset := firstOffset) (lastOffset := lastOffset) (frame := frame)
          (basis := basis) (firstFrame := firstFrame) (lastFrame := lastFrame) (count := count) (floor := floor)
          (parent := parent) (remaining := remaining) (covered := covered) (prepared := prepared)
          (ranges := ranges) (allocation := allocation) (firstAdmitted := firstAdmitted) (lastAdmitted := lastAdmitted)
          (firstWidths := firstWidths) (lastWidths := lastWidths)
          (firstBlocks := firstBlocks) (lastBlocks := lastBlocks)
          (firstWhole := firstWhole) (lastWhole := lastWhole)
          (firstNonempty := firstNonempty) (lastNonempty := lastNonempty)
          (firstCurrent := start) (firstFloor := firstFloor) (firstRootStage := firstRootStage)
          (lastCurrent := start) (lastFloor := lastFloor) (lastRootStage := lastRootStage)
          (unit := unit) (nonzero := nonzero) (spatial := spatial)
          (firstRequested := firstFresh) (lastRequested := lastFresh)
          (firstPositions := firstPositions) (lastPositions := lastPositions)
          (firstAligned := firstAligned) (lastAligned := lastAligned) (rows := rows)
          (oldGeometry := oldGeometry) (oldRoots := oldRoots)
          (firstReferenceCurrent := firstReferenceCurrent) (lastReferenceCurrent := lastReferenceCurrent)
          (firstAccuracy := firstAccuracy) (lastAccuracy := lastAccuracy)
          firstWhole_eq lastWhole_eq firstReference lastReference firstCompleted lastCompleted
          firstJet lastJet firstFactory lastFactory order coordinate
          (first.get (Specification.Table.baseIndex order coordinate))
          (first.get (Specification.Table.slopeIndex order coordinate))
          (last.get (Specification.Table.baseIndex order coordinate))
          (firstPaid (Specification.Table.baseIndex order coordinate))
          (firstPaid (Specification.Table.slopeIndex order coordinate))
          (lastPaid (Specification.Table.baseIndex order coordinate)) firstIndex lastIndex
          ((Data.Nat.Order.max_le (Request.Comparisons.left_le first (Specification.Table.baseIndex order coordinate))
            (Request.Comparisons.left_le first (Specification.Table.slopeIndex order coordinate))).trans firstAfter)
          ((Request.Comparisons.left_le last (Specification.Table.baseIndex order coordinate)).trans lastAfter)
      consume first last firstFresh lastFresh firstPaid lastPaid firstPositions lastPositions firstAligned lastAligned
        rows actual bounded)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows

end
