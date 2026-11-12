module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Accuracy
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Transport

/-! # One exact joint request index for the same three actual global arithmetic comparisons

The original Joint factory identifies its whole increment-fourth request.
Both independently paid minimum requests are therefore the same common
request across physical query times. Exact index transports preserve all
original numeric readings and the already materialized comparison caches;
no interpretation, root, source callback or comparison is run again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint liftedCell)

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
    (step : Variation.Point.Step oldObserved.retained.sample increment)
    (nonzero : increment ≠ 0) {sourceAdditional targetAdditional spatial : AccuracyRequest}
    (joint : Variation.Point.Step.Joint step nonzero sourceAdditional targetAdditional)
    (paid : Variation.Arithmetic.Reobservations joint.arithmetic spatial)
    (newObserved : request.Observation sourceIndex input)

/-- Transport three selected SAME stored comparisons to the exactly equal whole common request.

The original numeric Reading and entire generic Comparison cache move
together. No interpreter, original query, numeric request or comparison
builder executes in this exact request-index transport.
-/
@[expose] def rowComparisonsAtCommon (order coordinate : Fin 2)
    (retained : RowComparisons located input oldObserved step nonzero joint paid newObserved order coordinate) :=
  let equal := joint.minimum_accuracy spatial
  (retained.1.castAccuracy equal, retained.2.1.castAccuracy equal, retained.2.2.castAccuracy equal)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
