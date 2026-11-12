module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Path
import Purelib.Riemann.Normalization.ContinuedInverseRoot

/-! # Signed agreement of independent parameter Steps on one original parent

Both source preparations retain their own patch, model, actual Point and
Step caches. One already retained original direct-edge Query compares both
source roots through their actual prepared seeds. Equal physical points
transport only indices; the original contour/refinement comparisons then
identify the unchanged target Steps without another query or advancement.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

/-- Compare two literal retained source Cells through their original model factories and the same direct Query.

Both complete Cell equalities retain their own selected Request and six-model
cache. The generic source comparisons and existing parameter-Step comparison
consume those same owners, without unfolding either enclosing preparation.
-/
private def cellParameterStepsEquivalent
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {firstPatch lastPatch : PreparedPatch parent} {firstCount lastCount : Nat}
    {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (parent.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (parent.edge.point 1)}
    {firstCache : Cache (firstPatch.neighborhood firstCount)}
    {lastCache : Cache (lastPatch.neighborhood lastCount)}
    {firstFloor lastFloor : Nat} {firstTarget lastTarget firstAllowance lastAllowance : Rational}
    (firstRequest : Request firstCache firstFloor firstTarget)
    (lastRequest : Request lastCache lastFloor lastTarget)
    (firstModels : CellModels firstRequest (startPoint parent).coordinate (finishPoint parent).coordinate
      firstAllowance)
    (lastModels : CellModels lastRequest (startPoint parent).coordinate (finishPoint parent).coordinate lastAllowance)
    (firstCell lastCell : Cell (parameter := parameter) (liftedCell parent))
    (first_eq : firstCell = Cell.ofModels firstRequest (liftedCell parent) firstModels
      (start_inside firstPatch firstCount) (finish_inside firstPatch firstCount firstCovered))
    (last_eq : lastCell = Cell.ofModels lastRequest (liftedCell parent) lastModels
      (start_inside lastPatch lastCount) (finish_inside lastPatch lastCount lastCovered))
    {firstInput lastInput : Rational}
    {firstSource : ContinuedNeighborhood.Point firstCell.patch (firstCell.models.coordinate.point firstInput)}
    {lastSource : ContinuedNeighborhood.Point lastCell.patch (lastCell.models.coordinate.point lastInput)}
    (firstStep : Variation.Point.Step firstSource increment)
    (lastStep : Variation.Point.Step lastSource increment)
    (samePoint : parent.edge.point firstInput = parent.edge.point lastInput)
    (inside : 0 ≤ firstInput ∧ firstInput ≤ 1)
    (direct : PreparedEdge.Query parent.edge firstInput inside) :
    NamedEquivalent firstStep.root.value.name lastStep.root.value.name := by
  have lastPoint : lastCell.models.coordinate.point firstInput = lastCell.models.coordinate.point lastInput :=
    (coordinate_point_eq lastCell.models.coordinate firstInput).trans
      (samePoint.trans (coordinate_point_eq lastCell.models.coordinate lastInput).symm)
  let transported := ContinuedNeighborhood.Point.castPoint lastPoint lastSource
  let firstAgrees := sampleEquivalent (parameter := parameter) (frame := frame) (basis := basis)
    (parent := parent) (patch := firstPatch) (count := firstCount) (covered := firstCovered)
    firstRequest firstModels firstCell first_eq firstInput inside firstSource direct
  let lastAgrees := sampleEquivalent (parameter := parameter) (frame := frame) (basis := basis)
    (parent := parent) (patch := lastPatch) (count := lastCount) (covered := lastCovered)
    lastRequest lastModels lastCell last_eq firstInput inside transported direct
  let sourceAgrees : NamedEquivalent firstSource.certificate.value.name lastSource.certificate.value.name :=
    firstAgrees.symm.trans
      (NamedEquivalent.transport
        (first := parent.edge.rootName firstInput inside)
        (second := transported.certificate.value.name)
        (left := parent.edge.rootName firstInput inside)
        (right := lastSource.certificate.value.name)
        rfl (ContinuedNeighborhood.Point.castPoint_name lastPoint lastSource) lastAgrees)
  have sourcePoint : firstCell.models.coordinate.point firstInput = lastCell.models.coordinate.point lastInput :=
    (coordinate_point_eq firstCell.models.coordinate firstInput).trans
      (samePoint.trans (coordinate_point_eq lastCell.models.coordinate lastInput).symm)
  exact Variation.Point.Step.equivalent_of_source_eq
    (parameter := parameter) (increment := increment)
    (firstPoint := firstCell.models.coordinate.point firstInput)
    (lastPoint := lastCell.models.coordinate.point lastInput)
    (firstCount := firstCell.count) (lastCount := lastCell.count)
    (firstPatch := firstCell.patch) (lastPatch := lastCell.patch)
    (firstSource := firstSource) (lastSource := lastSource)
    firstStep lastStep sourcePoint sourceAgrees

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {firstPatch lastPatch : PreparedPatch parent} {firstCount lastCount firstFloor lastFloor : Nat}
    {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (parent.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (parent.edge.point 1)}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstOriginal : LiftedPath 2 firstStart firstFinish} {lastOriginal : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets firstOriginal firstStage}
    {lastTargets : CellEndpoints.Targets lastOriginal lastStage}
    (first : PreparedParent firstPatch firstCount firstFloor firstCovered firstTargets)
    (last : PreparedParent lastPatch lastCount lastFloor lastCovered lastTargets)
    {firstInput lastInput : Rational}
    {firstSource : ContinuedNeighborhood.Point first.preparation.cell.patch
      (first.preparation.cell.models.coordinate.point firstInput)}
    {lastSource : ContinuedNeighborhood.Point last.preparation.cell.patch
      (last.preparation.cell.models.coordinate.point lastInput)}

/-- Compare two already retained parameter Steps at the same physical point of the original prepared parent.

The actual preparations may use different source stages, covering patches
and coefficient counts. Both source names are compared using the SAME
retained direct Query and their original complete Cell factory equations.
Point.castPoint changes only the second source's exact point index. The
existing Step comparison consumes both actual contour and refinement
payments; no desired source/target agreement is an input.
-/
def parameterStepsEquivalent
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {firstPatch lastPatch : PreparedPatch parent} {firstCount lastCount firstFloor lastFloor : Nat}
    {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (parent.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (parent.edge.point 1)}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstOriginal : LiftedPath 2 firstStart firstFinish} {lastOriginal : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets firstOriginal firstStage}
    {lastTargets : CellEndpoints.Targets lastOriginal lastStage}
    (first : PreparedParent firstPatch firstCount firstFloor firstCovered firstTargets)
    (last : PreparedParent lastPatch lastCount lastFloor lastCovered lastTargets)
    {firstInput lastInput : Rational}
    {firstSource : ContinuedNeighborhood.Point first.preparation.cell.patch
      (first.preparation.cell.models.coordinate.point firstInput)}
    {lastSource : ContinuedNeighborhood.Point last.preparation.cell.patch
      (last.preparation.cell.models.coordinate.point lastInput)}
    (firstStep : Variation.Point.Step firstSource increment)
    (lastStep : Variation.Point.Step lastSource increment)
    (samePoint : parent.edge.point firstInput = parent.edge.point lastInput)
    (inside : 0 ≤ firstInput ∧ firstInput ≤ 1)
    (direct : PreparedEdge.Query parent.edge firstInput inside) :
    NamedEquivalent firstStep.root.value.name lastStep.root.value.name := by
  let firstCell := first.preparation.cell
  let lastCell := last.preparation.cell
  exact cellParameterStepsEquivalent
    (parameter := parameter) (increment := increment) (frame := frame) (basis := basis) (parent := parent)
    (firstPatch := firstPatch) (lastPatch := lastPatch) (firstCount := firstCount) (lastCount := lastCount)
    (firstCovered := firstCovered) (lastCovered := lastCovered)
    (firstCache := first.cache) (lastCache := last.cache)
    first.preparation.attached.source last.preparation.attached.source
    first.preparation.models last.preparation.models firstCell lastCell
    first.preparation.cell_eq last.preparation.cell_eq
    (firstInput := firstInput) (lastInput := lastInput) (firstSource := firstSource) (lastSource := lastSource)
    firstStep lastStep samePoint inside direct

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
