module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Source

/-! # Original source agreement of actual zero-acquisition child queries

The original acquired trace, Alignment, child Query, Point samples and
zero-Step are supplied unchanged. Their existing comparison operations
derive the signed source relation without a Frame or whole-curve identity.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

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
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation

attribute [local irreducible] CertifiedSquareRoot.rawRoot

/-- An actual zero-acquisition query agrees with its unchanged original source Point.

The existing aligned query comparison keeps the literal acquired child,
original direct Query, two actual Point samples and stored zero-Step. The
same Step's source comparison closes the root relation without a Frame or
curve identity. The supplied acquisition, direct Query and Step are not
rebuilt; the existing source-root comparison performs its own finite
common-refinement/intersection work.
-/
def querySourceEquivalent
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + 0)}
    {admitted : Norm.Basic.normSq (0 : Canonical) ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample 0} {width : AccuracyRequest}
    {retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width}
    {strip : Norm.Basic.normSq (0 : Canonical) ≤ range.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
      (finishPoint parent).coordinate retained.acquired.traced.finishOwner}
    {actual_eq : actual = retained.acquired.traced.trace.get}
    (comparison : RootComparison retained strip actual actual_eq)
    (aligned : Acquisition.Segment.RootComparisons.Alignment comparison.paths comparison.firstReference)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    {oldFloor : Nat} {oldStart oldFinish : LiftedPoint 2} {oldPath : LiftedPath 2 oldStart oldFinish}
    {oldStage : Nat} {oldTargets : CellEndpoints.Targets oldPath oldStage}
    (oldPrepared : PreparedParent patch count oldFloor covered oldTargets)
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    {sourceSample : ContinuedNeighborhood.Point oldPrepared.preparation.cell.patch
      (oldPrepared.preparation.cell.models.coordinate.point
        (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input))}
    (step : Variation.Point.Step sourceSample 0)
    (targetSample : ContinuedNeighborhood.Point newPrepared.preparation.cell.patch
      (newPrepared.preparation.cell.models.coordinate.point input))
    (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (direct : Riemann.Integration.PreparedConstantModels.PreparedEdge.Query child.edge input inside) :
    NamedEquivalent targetSample.certificate.value.name sourceSample.certificate.value.name :=
  let toStep := comparison.queryEquivalent (parameter := parameter) (increment := 0) (frame := frame)
    (basis := basis) (parent := parent) (patch := patch) (count := count) (covered := covered)
    (range := range) (target := target) (admitted := admitted) (firstSample := firstSample)
    (firstStep := firstStep) (width := width) (retained := retained) (strip := strip)
    (actual := actual) (actual_eq := actual_eq) (child := child) aligned oldPrepared newPrepared input inside
    step targetSample index child_eq direct
  let toSource := Variation.Point.Step.sourceEquivalent (parameter := parameter)
    (point := oldPrepared.preparation.cell.models.coordinate.point
      (PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input))
    (count := oldPrepared.preparation.cell.count) (patch := oldPrepared.preparation.cell.patch)
    (source := sourceSample) step
  toStep.trans toSource

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

end
