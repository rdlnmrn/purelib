module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Comparison

/-! # Actual target-query agreement across retained shifted acquisitions

The two original source preparations may use different allocation stages.
Their actual shifted acquisition, Parents, trace and Alignment caches remain
separate inputs. Exact common physical-point incidence relates their original
parent fractions; original source and parameter-Step comparisons derive the
signed target query relation without another acquisition or advancement.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {strip : Norm.Basic.normSq increment ≤ range.stripBound} {firstWidth lastWidth : AccuracyRequest}
    {firstFloor lastFloor : Nat} {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstOriginal : LiftedPath 2 firstStart firstFinish} {lastOriginal : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets firstOriginal firstStage}
    {lastTargets : CellEndpoints.Targets lastOriginal lastStage}
    (first : PreparedParent patch count firstFloor covered firstTargets)
    (last : PreparedParent patch count lastFloor covered lastTargets)
    (firstLinked : Linked first range target admitted strip firstWidth)
    (lastLinked : Linked last range target admitted strip lastWidth)
    (firstAligned : Acquisition.Segment.RootComparisons.Alignment
      firstLinked.comparison.paths firstLinked.comparison.firstReference)
    (lastAligned : Acquisition.Segment.RootComparisons.Alignment
      lastLinked.comparison.paths lastLinked.comparison.firstReference)
    {firstChild lastChild : CenteredEdge (Fibre.frameCurve target) basis}
    {firstNewPatch : PreparedPatch firstChild} {lastNewPatch : PreparedPatch lastChild}
    {firstNewCount lastNewCount firstNewFloor lastNewFloor : Nat}
    {firstNewCovered : (firstNewPatch.neighborhood firstNewCount).box.Contains (firstChild.edge.point 1)}
    {lastNewCovered : (lastNewPatch.neighborhood lastNewCount).box.Contains (lastChild.edge.point 1)}
    {firstNewStart firstNewFinish lastNewStart lastNewFinish : LiftedPoint 2}
    {firstNewOriginal : LiftedPath 2 firstNewStart firstNewFinish}
    {lastNewOriginal : LiftedPath 2 lastNewStart lastNewFinish}
    {firstNewStage lastNewStage : Nat}
    {firstNewTargets : CellEndpoints.Targets firstNewOriginal firstNewStage}
    {lastNewTargets : CellEndpoints.Targets lastNewOriginal lastNewStage}
    (firstNew : PreparedParent firstNewPatch firstNewCount firstNewFloor firstNewCovered firstNewTargets)
    (lastNew : PreparedParent lastNewPatch lastNewCount lastNewFloor lastNewCovered lastNewTargets)
    (firstIndex : Fin firstLinked.shifted.parents.covered.parents.length)
    (lastIndex : Fin lastLinked.shifted.parents.covered.parents.length)
    (first_eq : firstChild = firstLinked.shifted.parents.covered.parents[firstIndex.val]'firstIndex.isLt)
    (last_eq : lastChild = lastLinked.shifted.parents.covered.parents[lastIndex.val]'lastIndex.isLt)
    (firstInput lastInput : Rational)
    (firstInside : 0 ≤ firstInput ∧ firstInput ≤ 1) (lastInside : 0 ≤ lastInput ∧ lastInput ≤ 1)
    {firstSource : ContinuedNeighborhood.Point first.preparation.cell.patch
      (first.preparation.cell.models.coordinate.point
        (PreparedSheetContinuation.parameterAt firstChild.edge.left firstChild.edge.request firstInput))}
    {lastSource : ContinuedNeighborhood.Point last.preparation.cell.patch
      (last.preparation.cell.models.coordinate.point
        (PreparedSheetContinuation.parameterAt lastChild.edge.left lastChild.edge.request lastInput))}
    (firstStep : Variation.Point.Step firstSource increment) (lastStep : Variation.Point.Step lastSource increment)
    (firstTarget : ContinuedNeighborhood.Point firstNew.preparation.cell.patch
      (firstNew.preparation.cell.models.coordinate.point firstInput))
    (lastTarget : ContinuedNeighborhood.Point lastNew.preparation.cell.patch
      (lastNew.preparation.cell.models.coordinate.point lastInput))

/-- Derive signed target agreement at an actual common physical point of two unchanged shifted child occurrences.

Both whole Linked acquisitions, their actual Alignments, original child
indices, source/target preparations, Point owners and parameter Steps stay
inputs. The three supplied direct Query caches retain their complete
original factories. Exact physical incidence alone supplies no root claim:
both original patch comparisons and both paid parameter Steps derive it.
-/
def queryEquivalent
    (samePoint : firstChild.edge.point firstInput = lastChild.edge.point lastInput)
    (parentQuery : PreparedEdge.Query parent.edge
      (PreparedSheetContinuation.parameterAt firstChild.edge.left firstChild.edge.request firstInput)
      (PreparedSheetContinuation.parameterAt_inside firstChild.edge.left firstChild.edge.request
        firstChild.edge.ordered firstInput firstInside))
    (firstQuery : PreparedEdge.Query firstChild.edge firstInput firstInside)
    (lastQuery : PreparedEdge.Query lastChild.edge lastInput lastInside) :
    NamedEquivalent firstTarget.certificate.value.name lastTarget.certificate.value.name := by
  have parentPoint : parent.edge.point
      (PreparedSheetContinuation.parameterAt firstChild.edge.left firstChild.edge.request firstInput) =
      parent.edge.point
        (PreparedSheetContinuation.parameterAt lastChild.edge.left lastChild.edge.request lastInput) :=
    (firstLinked.shifted.originalPoint_eq firstIndex first_eq firstInput).symm.trans
      (samePoint.trans (lastLinked.shifted.originalPoint_eq lastIndex last_eq lastInput))
  have steps := first.parameterStepsEquivalent last firstStep lastStep parentPoint
    (PreparedSheetContinuation.parameterAt_inside firstChild.edge.left firstChild.edge.request
      firstChild.edge.ordered firstInput firstInside) parentQuery
  have firstCompared := firstLinked.comparison.queryEquivalent firstAligned first firstNew firstInput firstInside
    firstStep firstTarget firstIndex first_eq firstQuery
  have lastCompared := lastLinked.comparison.queryEquivalent lastAligned last lastNew lastInput lastInside
    lastStep lastTarget lastIndex last_eq lastQuery
  exact firstCompared.trans (steps.trans lastCompared.symm)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
