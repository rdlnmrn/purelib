module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Repeat
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Queries
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Actual query agreement propagated through one retained parameter window

The old prepared family, actual globally allocated successor Request,
stored occurrence table and one retained Alignment per original block
remain the owners. Each invocation acquires its genuinely needed old
query/Step and direct-query caches once through their original factories.
Old signed query agreement and both actual Step payments derive agreement
of the two supplied successor observations. No new Completion is assumed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrences

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

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
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}

/-- Propagate genuine old all-point agreement to the literal successor Request's original prepared query family.

The supplied successor bundles are never observed again. The same stored
occurrences and Alignments select their actual original blocks. Each old
mapped source query/Step and direct child Query is genuinely materialized
once per invocation, in that order, then reused for both whole-key and
signed comparisons. No block acquisition, source preparation, stage or bank
is replayed, and no sharing across independent invocations is claimed.
-/
def queryAgreement (stored : Occurrences blocks request)
    (aligned : DependentProduct (firstParent :: remaining) (fun index =>
      Acquisition.Segment.RootComparisons.Alignment
        (DependentProduct.get (firstParent :: remaining) blocks index).comparison.paths
        (DependentProduct.get (firstParent :: remaining) blocks index).comparison.firstReference))
    (old : PreparedParents.QueryAgreement prepared) :
    PreparedParents.QueryAgreement (parameter := parameter + increment) (frame := target) (basis := basis)
      (count := count) (floor := globalFloor) (parents := request.shape.val.1 :: request.shape.val.2)
      (covered := request.covered) (original := request.chain.path) (stage := requestIndex)
      (targets := request.attempt.1.val) request.attempt.2.1 := by
  intro firstIndex lastIndex firstInput lastInput firstInside lastInside firstObserved lastObserved samePoint
  let firstLocation := DependentProduct.get (request.shape.val.1 :: request.shape.val.2) stored firstIndex
  let lastLocation := DependentProduct.get (request.shape.val.1 :: request.shape.val.2) stored lastIndex
  let firstAligned := DependentProduct.get (firstParent :: remaining) aligned firstLocation.block
  let lastAligned := DependentProduct.get (firstParent :: remaining) aligned lastLocation.block
  let firstOld := firstLocation.sourceStep (admitted := admitted) firstInput firstInside
  let lastOld := lastLocation.sourceStep (admitted := admitted) lastInput lastInside
  let firstDirect := PreparedEdge.Query.build
    ((request.shape.val.1 :: request.shape.val.2)[firstIndex.val]'firstIndex.isLt).edge firstInput firstInside
  let lastDirect := PreparedEdge.Query.build
    ((request.shape.val.1 :: request.shape.val.2)[lastIndex.val]'lastIndex.isLt).edge lastInput lastInside
  have oldKeys := (firstLocation.sourceKey_eq firstInput).trans
    (samePoint.trans (lastLocation.sourceKey_eq lastInput).symm)
  let oldRepeat : NamedEquivalent firstOld.1.retained.sample.certificate.value.name
      lastOld.1.retained.sample.certificate.value.name :=
    old firstLocation.block lastLocation.block (firstLocation.sourceInput firstInput)
      (lastLocation.sourceInput lastInput) (firstLocation.sourceInput_inside firstInput firstInside)
      (lastLocation.sourceInput_inside lastInput lastInside) firstOld.1 lastOld.1 oldKeys
  exact firstLocation.querySamplesEquivalent lastLocation firstAligned lastAligned
    firstInput lastInput firstInside lastInside firstOld.1 firstOld.2 lastOld.1 lastOld.2 oldRepeat
    firstObserved lastObserved firstDirect lastDirect samePoint

/-- Complete the literal successor Request from retained occurrences, Alignments and genuine old query agreement.

Both original parameter Steps derive the new all-query invariant before
completion. The same Request's old lookup caches and ready Commons are
consumed by its original StageAttempt completion; no desired successor
Distinct, RootChain, readiness or sample relation is an input.
-/
def complete (stored : Occurrences blocks request)
    (aligned : DependentProduct (firstParent :: remaining) (fun index =>
      Acquisition.Segment.RootComparisons.Alignment
        (DependentProduct.get (firstParent :: remaining) blocks index).comparison.paths
        (DependentProduct.get (firstParent :: remaining) blocks index).comparison.firstReference))
    (old : PreparedParents.QueryAgreement prepared) :
    PreparedParents.StageAttempt.Completion request.attempt :=
  request.attempt.completeQueries (queryAgreement stored aligned old)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrences

end
