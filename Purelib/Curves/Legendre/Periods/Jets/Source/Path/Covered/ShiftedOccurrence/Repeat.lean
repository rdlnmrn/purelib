module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Restriction
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Signed old repeats at the actual selected shifted-bank occurrence

An actual bank position identifies its unchanged global source preparation
and retained local acquisition. Two original observation bundles and their
already paid parameter Steps transport an old signed repeat to the new
query and this exact first-match bank owner. Equal keys select the occurrence;
the old signed comparison, both Step payments and retained RootPaths prove
agreement. No successful successor bank is presumed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
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
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}

/-- Read the identical physical point of an old mapped query and its retained globally located shifted child.

The old Cell coordinate law and actual local acquisition's child occurrence
law provide this scalar identity. Neither polynomial, source model, physical
parameterization nor continued sample is identified with a replacement owner.
-/
theorem sourcePoint_eq (located : Occurrence blocks request sourceIndex) (input : Rational) :
    (prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput input) =
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.point input :=
  ((prepared.entry located.block).queryPoint_eq (located.sourceInput input)).trans
    ((DependentProduct.get (firstParent :: remaining) blocks located.block).shifted.originalPoint_eq
      located.child located.parent_eq input).symm

/-- The mapped old query and literal successor query retain the SAME whole lifted key, including its sheet.

The coordinate laws concern the two original models separately. The actual
retained child's whole parent equation supplies its inherited sheet; no
signed root agreement is inferred from this key identity.
-/
theorem sourceKey_eq (located : Occurrence blocks request sourceIndex) (input : Rational) :
    (⟨(prepared.entry located.block).preparation.cell.models.coordinate.point (located.sourceInput input),
      ((firstParent :: remaining)[located.block.val]'located.block.isLt).edge.sheet⟩ : LiftedPoint 2) =
      ⟨(request.attempt.2.1.entry sourceIndex).preparation.cell.models.coordinate.point input,
        ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.sheet⟩ :=
  congrArg₂ (fun coordinate sheet => (⟨coordinate, sheet⟩ : LiftedPoint 2))
    ((located.sourcePoint_eq input).trans
      ((request.attempt.2.1.entry sourceIndex).queryPoint_eq input).symm)
    ((DependentProduct.get (firstParent :: remaining) blocks located.block).shifted.child_sheet
      located.child located.parent_eq).symm

/-- Compare two supplied successor query samples through their SAME retained old samples and paid parameter Steps.

Both original observation bundles, Steps, target bundles, direct Queries
and RootPath Alignments are consumed unchanged. Whole lifted-key equality
includes the actual inherited sheet. The old signed relation and the
original Step comparison derive the successor relation; no source query,
observation, Step, direct Query, acquisition or Alignment is rebuilt.
-/
def querySamplesEquivalent
    (located : Occurrence blocks request sourceIndex)
    {lastIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (lastLocated : Occurrence blocks request lastIndex)
    (aligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (lastAligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks lastLocated.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks lastLocated.block).comparison.firstReference)
    (input lastInput : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (lastInside : 0 ≤ lastInput ∧ lastInput ≤ 1)
    (oldObserved : CellModels.Observations frame
      (PreparedParent.liftedCell ((firstParent :: remaining)[located.block.val]'located.block.isLt))
      (prepared.entry located.block).preparation.cell.models
      (prepared.entry located.block).preparation.query.requests (located.sourceInput input))
    (step : Variation.Point.Step oldObserved.retained.sample increment)
    (lastOldObserved : CellModels.Observations frame
      (PreparedParent.liftedCell ((firstParent :: remaining)[lastLocated.block.val]'lastLocated.block.isLt))
      (prepared.entry lastLocated.block).preparation.cell.models
      (prepared.entry lastLocated.block).preparation.query.requests (lastLocated.sourceInput lastInput))
    (lastStep : Variation.Point.Step lastOldObserved.retained.sample increment)
    (oldRepeat : NamedEquivalent oldObserved.retained.sample.certificate.value.name
      lastOldObserved.retained.sample.certificate.value.name)
    (newObserved : request.Observation sourceIndex input)
    (lastObserved : request.Observation lastIndex lastInput)
    (direct : PreparedEdge.Query
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge input inside)
    (lastDirect : PreparedEdge.Query
      ((request.shape.val.1 :: request.shape.val.2)[lastIndex.val]'lastIndex.isLt).edge lastInput lastInside)
    (samePoint :
      (⟨(request.attempt.2.1.entry sourceIndex).preparation.cell.models.coordinate.point input,
        ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.sheet⟩ : LiftedPoint 2) =
        ⟨(request.attempt.2.1.entry lastIndex).preparation.cell.models.coordinate.point lastInput,
          ((request.shape.val.1 :: request.shape.val.2)[lastIndex.val]'lastIndex.isLt).edge.sheet⟩) :
    NamedEquivalent newObserved.retained.sample.certificate.value.name
      lastObserved.retained.sample.certificate.value.name := by
  have oldKeys := (located.sourceKey_eq input).trans
    (samePoint.trans (lastLocated.sourceKey_eq lastInput).symm)
  let moved : NamedEquivalent step.root.value.name lastStep.root.value.name :=
    Variation.Point.Step.equivalent_of_source_eq
      (parameter := parameter) (increment := increment)
      (firstPoint := (prepared.entry located.block).preparation.cell.models.coordinate.point
        (located.sourceInput input))
      (lastPoint := (prepared.entry lastLocated.block).preparation.cell.models.coordinate.point
        (lastLocated.sourceInput lastInput))
      (firstCount := (prepared.entry located.block).preparation.cell.count)
      (lastCount := (prepared.entry lastLocated.block).preparation.cell.count)
      (firstPatch := (prepared.entry located.block).preparation.cell.patch)
      (lastPatch := (prepared.entry lastLocated.block).preparation.cell.patch)
      (firstSource := oldObserved.retained.sample) (lastSource := lastOldObserved.retained.sample)
      step lastStep (congrArg LiftedPoint.coordinate oldKeys) oldRepeat
  let firstCompared := located.queryEquivalent aligned input inside oldObserved step newObserved direct
  let lastCompared := lastLocated.queryEquivalent lastAligned lastInput lastInside
    lastOldObserved lastStep lastObserved lastDirect
  exact firstCompared.trans (moved.trans lastCompared.symm)

/-- Derive the new query's signed relation to the exact first matching shifted-bank owner from an actual old repeat.

Both old observation bundles and parameter Steps remain unchanged, with
their own admitted contour payments and seed refinements. Both target
observation bundles, direct child Queries and local RootPath Alignments
are retained inputs on the same global Request. The supplied bank Position
selects its actual original Found occurrence, including repeated keys.
The old signed repeat is at the two actual mapped physical fractions;
it is not inferred from the old endpoint bank or a closed RootChain.
-/
def queryEquivalentToFound
    (located : Occurrence blocks request sourceIndex)
    {point : LiftedPoint 2} {found : Vertex.Bank.Found request.attempt.2.2.1.val point}
    (position : Vertex.Bank.Position (.found found))
    (foundLocated : Occurrence blocks request (request.attempt.foundSourceIndex position))
    (aligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (foundAligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks foundLocated.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks foundLocated.block).comparison.firstReference)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (point_eq : (⟨((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.point input,
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.sheet⟩ :
        LiftedPoint 2) = point)
    (oldObserved : CellModels.Observations frame
      (PreparedParent.liftedCell ((firstParent :: remaining)[located.block.val]'located.block.isLt))
      (prepared.entry located.block).preparation.cell.models
      (prepared.entry located.block).preparation.query.requests (located.sourceInput input))
    (step : Variation.Point.Step oldObserved.retained.sample increment)
    (foundOldObserved : CellModels.Observations frame
      (PreparedParent.liftedCell ((firstParent :: remaining)[foundLocated.block.val]'foundLocated.block.isLt))
      (prepared.entry foundLocated.block).preparation.cell.models
      (prepared.entry foundLocated.block).preparation.query.requests (foundLocated.sourceInput 0))
    (foundStep : Variation.Point.Step foundOldObserved.retained.sample increment)
    (oldRepeat : NamedEquivalent oldObserved.retained.sample.certificate.value.name
      foundOldObserved.retained.sample.certificate.value.name)
    (newObserved : request.Observation sourceIndex input)
    (foundObserved : request.Observation (request.attempt.foundSourceIndex position) 0)
    (direct : PreparedEdge.Query
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge input inside)
    (foundDirect : PreparedEdge.Query
      (let selectedIndex := request.attempt.foundSourceIndex position
       (request.shape.val.1 :: request.shape.val.2)[selectedIndex.val]'selectedIndex.isLt).edge
      0 (by decide +kernel)) :
    NamedEquivalent
      (((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.rootName input inside)
      found.original.sample.certificate.value.name := by
  let current := request.attempt.2.1.entry sourceIndex
  let selected := request.attempt.2.1.entry (request.attempt.foundSourceIndex position)
  have currentKey :
      (⟨current.preparation.cell.models.coordinate.point input,
        ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.sheet⟩ : LiftedPoint 2) =
        point :=
    (congrArg (fun coordinate => (⟨coordinate,
        ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.sheet⟩ : LiftedPoint 2))
      (current.queryPoint_eq input)).trans point_eq
  have selectedKey :
      (⟨selected.preparation.cell.models.coordinate.point 0,
        ((request.shape.val.1 :: request.shape.val.2)[(request.attempt.foundSourceIndex position).val]'
          (request.attempt.foundSourceIndex position).isLt).edge.sheet⟩ : LiftedPoint 2) = point :=
    (congrArg (fun coordinate => (⟨coordinate,
        ((request.shape.val.1 :: request.shape.val.2)[(request.attempt.foundSourceIndex position).val]'
          (request.attempt.foundSourceIndex position).isLt).edge.sheet⟩ : LiftedPoint 2))
      ((selected.queryPoint_eq 0).trans
        ((request.shape.val.1 :: request.shape.val.2)[(request.attempt.foundSourceIndex position).val]'
          (request.attempt.foundSourceIndex position).isLt).edge.point_zero)).trans
      (request.attempt.found_source_point position)
  let compared := located.querySamplesEquivalent foundLocated aligned foundAligned
    input 0 inside (by decide +kernel) oldObserved step foundOldObserved foundStep oldRepeat
    newObserved foundObserved direct foundDirect (currentKey.trans selectedKey.symm)
  exact request.attempt.sampleEquivalentToFound sourceIndex input inside position
    newObserved foundObserved direct foundDirect compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
