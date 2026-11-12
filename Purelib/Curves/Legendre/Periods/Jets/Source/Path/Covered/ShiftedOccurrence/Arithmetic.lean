module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Rows
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Taylor
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Fin
import Purelib.Data.Fin.Two
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport

/-! # Actual uniform/arithmetic comparisons for all four adjacent-derivative rows

The same original query bundles, Step, Joint, independently paid bank,
Alignment and direct Query supply ten unique channel comparisons. The
source-first entries serve both adjacent rows without comparison replay.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation (ArithmeticComparison)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint liftedCell)
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.RootContinuation

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {oldGeometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}

variable (located : Occurrence blocks request sourceIndex)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (oldObserved : CellModels.Observations frame
      (liftedCell ((firstParent :: remaining)[located.block.val]'located.block.isLt))
      (prepared.entry located.block).preparation.cell.models
      (prepared.entry located.block).preparation.query.requests (located.sourceInput input))
    (old_eq : oldObserved = (prepared.entry located.block).preparation.query.observe frame
      (located.sourceInput input) (located.sourceInput_inside input inside).1
        (located.sourceInput_inside input inside).2)
    (step : Variation.Point.Step oldObserved.retained.sample increment)
    (nonzero : increment ≠ 0) {sourceAdditional targetAdditional spatial : AccuracyRequest}
    (joint : Variation.Point.Step.Joint step nonzero sourceAdditional targetAdditional)
    (paid : Variation.Arithmetic.Reobservations joint.arithmetic spatial)
    (newObserved : request.Observation sourceIndex input)
    (new_eq : newObserved = (request.attempt.2.1.entry sourceIndex).preparation.query.observe
      target input inside.1 inside.2)
    (aligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (direct : PreparedEdge.Query
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge input inside)

/-- The actual three original uniform/arithmetic comparison types for one selected adjacent-derivative row.

The target observation retains the exact original Request.Observation
alias. The numerical entries are the same independent paid bank fields;
their original root states and full polynomial owners remain indexed.
-/
@[expose] def RowComparisons (order coordinate : Fin 2) :=
  let point := (prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput input)
  let firstRoot := oldObserved.retained.sample.certificate.castParameter (Variation.Point.radicand_eq parameter point)
  let lastRoot := step.root.castParameter (Variation.Point.radicand_eq (parameter + increment) point)
  let firstIdentity : PowerIdentity firstRoot.value 2 ((Paths.polynomial parameter).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity firstRoot.value 2 value)
      (Variation.Point.radicand_eq parameter point)) (PowerIdentity.ofSquare firstRoot.square)
  let lastIdentity : PowerIdentity lastRoot.value 2 ((Paths.polynomial (parameter + increment)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity lastRoot.value 2 value)
      (Variation.Point.radicand_eq (parameter + increment) point)) (PowerIdentity.ofSquare lastRoot.square)
  let numerics := paid.rowNumerics order coordinate
  ArithmeticComparison (oldObserved.channel (Specification.Table.baseIndex order coordinate))
      numerics.1 firstIdentity ×
    ArithmeticComparison (newObserved.channel (Specification.Table.baseIndex order coordinate))
      numerics.2.1 lastIdentity ×
    ArithmeticComparison (oldObserved.channel (Specification.Table.slopeIndex order coordinate))
      numerics.2.2 firstIdentity

/-- Ten unique actual channel comparisons on one original pair of query bundles and the SAME paid bank.

The five dependent vectors retain two source-value, target-value,
source-first, target-first and source-second comparisons. A source-first
entry is shared by the value slope and first base. No new owner or
observation is introduced by this exact existing-container type.
-/
@[expose] def ComparisonBank :=
  let point := (prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput input)
  let firstRoot := oldObserved.retained.sample.certificate.castParameter (Variation.Point.radicand_eq parameter point)
  let lastRoot := step.root.castParameter (Variation.Point.radicand_eq (parameter + increment) point)
  let firstIdentity : PowerIdentity firstRoot.value 2 ((Paths.polynomial parameter).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity firstRoot.value 2 value)
      (Variation.Point.radicand_eq parameter point)) (PowerIdentity.ofSquare firstRoot.square)
  let lastIdentity : PowerIdentity lastRoot.value 2 ((Paths.polynomial (parameter + increment)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity lastRoot.value 2 value)
      (Variation.Point.radicand_eq (parameter + increment) point)) (PowerIdentity.ofSquare lastRoot.square)
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (oldObserved.channel (Specification.Table.baseIndex 0 coordinate))
      (paid.rowNumerics 0 coordinate).1 firstIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (newObserved.channel (Specification.Table.baseIndex 0 coordinate))
      (paid.rowNumerics 0 coordinate).2.1 lastIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (oldObserved.channel (Specification.Table.slopeIndex 0 coordinate))
      (paid.rowNumerics 0 coordinate).2.2 firstIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (newObserved.channel (Specification.Table.baseIndex 1 coordinate))
      (paid.rowNumerics 1 coordinate).2.1 lastIdentity) ×
  Data.Vector.DependentVector (fun coordinate : Fin 2 =>
    ArithmeticComparison (oldObserved.channel (Specification.Table.slopeIndex 1 coordinate))
      (paid.rowNumerics 1 coordinate).2.2 firstIdentity)

include old_eq new_eq aligned direct inside in
/-- Construct each of the ten actual comparisons once on the SAME retained original queries and root channels.

The one actual signed target relation comes from the supplied materialized
Alignment and direct Query. The original whole query equations supply all
channel root names. The source and target bundles, Point.Step, scalar data
and paid evaluator observations execute no additional query or advancement.
-/
def comparisonBank : ComparisonBank located input oldObserved step nonzero joint paid newObserved := by
  let old := prepared.entry located.block
  let next := request.attempt.2.1.entry sourceIndex
  let point := (prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput input)
  let firstRoot := oldObserved.retained.sample.certificate.castParameter (Variation.Point.radicand_eq parameter point)
  let lastRoot := step.root.castParameter (Variation.Point.radicand_eq (parameter + increment) point)
  let firstIdentity : PowerIdentity firstRoot.value 2 ((Paths.polynomial parameter).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity firstRoot.value 2 value)
      (Variation.Point.radicand_eq parameter point)) (PowerIdentity.ofSquare firstRoot.square)
  let lastIdentity : PowerIdentity lastRoot.value 2 ((Paths.polynomial (parameter + increment)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity lastRoot.value 2 value)
      (Variation.Point.radicand_eq (parameter + increment) point)) (PowerIdentity.ofSquare lastRoot.square)
  let block := DependentProduct.get (firstParent :: remaining) blocks located.block
  have sourceName : firstRoot.value.name = oldObserved.retained.sample.certificate.value.name :=
    congrArg (fun value : Approximation.Gaussian.Name.Coherent.CoherentNamed => value.name)
      (oldObserved.retained.sample.certificate.castParameter_value (Variation.Point.radicand_eq parameter point))
  have targetName : lastRoot.value.name = step.root.value.name :=
    congrArg (fun value : Approximation.Gaussian.Name.Coherent.CoherentNamed => value.name)
      (step.root.castParameter_value (Variation.Point.radicand_eq (parameter + increment) point))
  let targetRoots := located.queryEquivalent aligned input inside oldObserved step newObserved direct
  have samePoint : point = next.preparation.cell.models.coordinate.point input :=
    ((old.queryPoint_eq (located.sourceInput input)).trans
      (block.shifted.originalPoint_eq located.child located.parent_eq input).symm).trans
        (next.queryPoint_eq input).symm
  let sourceValue := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.baseIndex 0 coordinate
    let channelName := old.preparation.query.channel_root_name frame (located.sourceInput input)
      (located.sourceInput_inside input inside).1 (located.sourceInput_inside input inside).2
      oldObserved old_eq channel
    let roots := NamedEquivalent.transport sourceName.symm channelName.symm
      (NamedEquivalent.refl oldObserved.retained.sample.certificate.value.name)
    ArithmeticComparison.build (oldObserved.channel channel) (paid.rowNumerics 0 coordinate).1
      firstIdentity (oldObserved.channel_point channel).symm roots)
  let targetValue := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.baseIndex 0 coordinate
    let channelName := next.preparation.query.channel_root_name target input inside.1 inside.2
      newObserved new_eq channel
    let roots := NamedEquivalent.transport targetName.symm channelName.symm targetRoots.symm
    ArithmeticComparison.build (newObserved.channel channel) (paid.rowNumerics 0 coordinate).2.1
      lastIdentity (samePoint.trans (newObserved.channel_point channel).symm) roots)
  let sourceFirst := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.slopeIndex 0 coordinate
    let channelName := old.preparation.query.channel_root_name frame (located.sourceInput input)
      (located.sourceInput_inside input inside).1 (located.sourceInput_inside input inside).2
      oldObserved old_eq channel
    let roots := NamedEquivalent.transport sourceName.symm channelName.symm
      (NamedEquivalent.refl oldObserved.retained.sample.certificate.value.name)
    ArithmeticComparison.build (oldObserved.channel channel) (paid.rowNumerics 0 coordinate).2.2
      firstIdentity (oldObserved.channel_point channel).symm roots)
  let targetFirst := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.baseIndex 1 coordinate
    let channelName := next.preparation.query.channel_root_name target input inside.1 inside.2
      newObserved new_eq channel
    let roots := NamedEquivalent.transport targetName.symm channelName.symm targetRoots.symm
    ArithmeticComparison.build (newObserved.channel channel) (paid.rowNumerics 1 coordinate).2.1
      lastIdentity (samePoint.trans (newObserved.channel_point channel).symm) roots)
  let sourceSecond := Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    let channel := Specification.Table.slopeIndex 1 coordinate
    let channelName := old.preparation.query.channel_root_name frame (located.sourceInput input)
      (located.sourceInput_inside input inside).1 (located.sourceInput_inside input inside).2
      oldObserved old_eq channel
    let roots := NamedEquivalent.transport sourceName.symm channelName.symm
      (NamedEquivalent.refl oldObserved.retained.sample.certificate.value.name)
    ArithmeticComparison.build (oldObserved.channel channel) (paid.rowNumerics 1 coordinate).2.2
      firstIdentity (oldObserved.channel_point channel).symm roots)
  exact ⟨sourceValue, targetValue, sourceFirst, targetFirst, sourceSecond⟩

namespace ComparisonBank

variable {located input oldObserved step nonzero joint paid newObserved}

variable (retained : ComparisonBank located input oldObserved step nonzero joint paid newObserved)

include retained in
/-- Select the actual original triple for one adjacent row from the ten SAME stored comparisons.

The original source-first entry is returned in both adjacent rows. The
finite selector performs no interpretation, comparison or observation.
-/
@[expose] def row (order coordinate : Fin 2) :
    RowComparisons located input oldObserved step nonzero joint paid newObserved order coordinate :=
  Data.Fin.casesDependent
    (motive := fun order : Fin 2 =>
      RowComparisons located input oldObserved step nonzero joint paid newObserved order coordinate)
    (Data.Fin.casesDependent
      (motive := fun coordinate : Fin 2 =>
        RowComparisons located input oldObserved step nonzero joint paid newObserved 0 coordinate)
      ((retained.1.get 0), (retained.2.1.get 0), (retained.2.2.1.get 0))
      (Data.Fin.casesDependent
        ((retained.1.get 1), (retained.2.1.get 1), (retained.2.2.1.get 1))
        (fun index => Fin.elim0 index)) coordinate)
    (Data.Fin.casesDependent
      (motive := fun index : Fin 1 =>
        RowComparisons located input oldObserved step nonzero joint paid newObserved index.succ coordinate)
      (Data.Fin.casesDependent
        (motive := fun coordinate : Fin 2 =>
          RowComparisons located input oldObserved step nonzero joint paid newObserved 1 coordinate)
        ((retained.2.2.1.get 0), (retained.2.2.2.1.get 0), (retained.2.2.2.2.get 0))
        (Data.Fin.casesDependent
          ((retained.2.2.1.get 1), (retained.2.2.2.1.get 1), (retained.2.2.2.2.get 1))
          (fun index => Fin.elim0 index)) coordinate)
      (fun index => Fin.elim0 index)) order

end ComparisonBank

include inside in
/-- The selected actual numeric certificate has its computed original-box row ceiling at the retained physical query. -/
theorem row_factor_le (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).factor ≤
      Variation.Point.Step.Joint.rowCeiling (prepared.entry located.block).preparation.cell.patch
        increment order coordinate :=
  joint.row_factor_le paid order coordinate
    ((prepared.entry located.block).preparation.cell.models.coordinate.point_inside
      (prepared.entry located.block).preparation.cell.startInside
      (prepared.entry located.block).preparation.cell.finishInside
      (located.sourceInput_inside input inside).1 (located.sourceInput_inside input inside).2)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
