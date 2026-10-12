module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.GluedPrimitives
public import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RegularFaceInverseModels

public section

/-!
# Face primitives on actual interior prepared edges

The public traced path retains the segment budgets needed to reach every
actual centered parent. Clear-face winding identifies its inherited owner
with the cell's continued occurrence. The uniform prepared patch therefore
has the same polynomial sign, with no prefix, sheet-agreement, or successful
search premise supplied by the caller. Auxiliary routes are proof-only.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PreparedComparison

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.RootContinuation.ClearBoxRootTransport

open Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached ParentReached)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (DensePrimitive PrimitiveOverlapBounds PrimitiveEdgeAccuracy)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition line_one line_zero)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels (primitiveOnBase)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {inner : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

/-- The actual owner reached inside the original clear face is aligned with the retained cell model at its cocycle
stage..

The trace retains the selected owner and its winding comparison.
Alignment uses the same containing cell and cocycle refinement index. -/
private theorem reached_aligned (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (differential : Differentials.Basic.Differential genus) {point : InverseRootPolynomial.Gaussian} {owner :
      SquareRootContinuationChain.Owner (curve.polynomial.eval point)}
    (pointInside : inner.Contains point) (reached : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners
      sheet) owner)
    (index : Nat) : InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) index) point
      (OwnerTraceReadings.ownerName owner) := by
  obtain ⟨ownerTrace, winding⟩ := reached
  let route := Route.build face.clearance face.cell.box.anchor point
    face.cell.box.contains_anchor (cell.geometry.refines.contains pointInside)
  let traced := TracedPath.build route.path route.within (models.frame.owners sheet)
  let frame := OwnerFrame.build owner.parameterNonzero
  have equivalent := TracedPath.equivalentOfOwnerPathSelections
    (BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop route.within traced ownerTrace frame
    (frame.select traced.finishOwner) (frame.select owner)
    ((Route.winding face.clearance (BranchIsolation.degreePositive curve) route face.cell.box.contains_anchor).trans
      winding.symm)
  intro count patch inside sample roots otherIndex
  exact ContinuedComparison.trace_aligned cell differential traced
    (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within face.cell.box.contains_anchor) frame
      pointInside index
    patch inside sample (equivalent.trans roots) otherIndex

/-- Every rational query of an actual retained parent is aligned with its containing face cell.

Reachability retains the inherited query owner and lineage witnesses.
The comparison is evaluated at the same point and cocycle index. -/
theorem prepared_query_aligned (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (differential : Differentials.Basic.Differential genus) (parent : PreparedSubdivisionModelCore.CenteredEdge curve
      differential)
    (reached : PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet) parent)
    (fraction : InverseRootPolynomial.Coordinate) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointInside : inner.Contains (parent.edge.point fraction)) (index : Nat) :
    InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) index) (parent.edge.point fraction)
      (parent.edge.rootName fraction fractionInside) := by
  have pointEq : parent.edge.point fraction = parent.edge.segment.pointAt
      (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request fraction) :=
    (PreparedSheetContinuation.pointAt_parameterAt parent.edge.segment parent.edge.within parent.edge.left
      parent.edge.request fraction).symm
  have initial : InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) index)
      (parent.edge.segment.pointAt (PreparedSheetContinuation.parameterAt parent.edge.left parent.edge.request
        fraction))
      (OwnerTraceReadings.ownerName (parent.edge.directQueryOwner fraction fractionInside)) :=
    reached_aligned cell differential (pointEq ▸
      pointInside) (reached.query_reached fraction fractionInside) index
  rw [pointEq, parent.edge.rootName_eq_directQueryOwnerRootName]
  intro count patch patchInside sample roots otherIndex
  exact initial patch patchInside sample roots otherIndex

/-- The actual uniform integration patch and the containing cell have the unflipped comparison.

The patch keeps its retained index, including zero or one. The cell
alone requires the fixed cocycle-accuracy floor. -/
theorem prepared_query_nearest (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (differential : Differentials.Basic.Differential genus) (parent : PreparedSubdivisionModelCore.CenteredEdge curve
      differential)
    (reached : PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet) parent)
    (fraction : InverseRootPolynomial.Coordinate) (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1)
    (pointInside : inner.Contains (parent.edge.point fraction)) (patch :
      UniformPrimitiveSheetCompatibility.PreparedPatch parent)
    (count leftIndex rightIndex : Nat) (patchInside : (patch.neighborhood count).box.Contains (parent.edge.point
      fraction)) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval (parent.edge.point
      fraction) -
      ((patch.neighborhood count).base.refine rightIndex).value.eval (parent.edge.point fraction)) ≤
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval (parent.edge.point
      fraction) +
      ((patch.neighborhood count).base.refine rightIndex).value.eval (parent.edge.point fraction)) := by
  let sample := ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (parent.edge.point fraction) patchInside
  have aligned : InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) leftIndex) (parent.edge.point
    fraction)
      (parent.edge.rootName fraction fractionInside) :=
    prepared_query_aligned cell differential parent
      reached fraction fractionInside pointInside leftIndex
  exact PreparedPolynomialSheetReadings.nearest_at_index aligned pointInside (patch.neighborhood count) patchInside
    sample
    (patch.point_equivalent count fraction fractionInside patchInside sample) rightIndex

/-- Compare a cell primitive directly with the primitive on an actual interior prepared parent's patch.

The two primitives retain their parent and endpoint containment certificates.
The estimate decays with the requested inverse residuals and squared edge
movement, without a Taylor error floor. -/
theorem prepared_subedge_primitive_increment_le
    (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet) inner)
    (differential : Differentials.Basic.Differential genus) (parent : PreparedSubdivisionModelCore.CenteredEdge curve
      differential)
    (reached : PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet) parent)
    (firstFraction lastFraction : InverseRootPolynomial.Coordinate)
    (firstInside : 0 ≤ firstFraction ∧ firstFraction ≤ 1)
    (pointInside : inner.Contains (parent.edge.point firstFraction)) (patch :
      UniformPrimitiveSheetCompatibility.PreparedPatch parent)
    (count leftIndex rightIndex : Nat) {numerator coefficient : InverseRootPolynomial.Polynomial}
    (first : PrimitiveEdgeComparison.DensePrimitive coefficient inner)
    (firstEq : ∀ query, coefficient.eval query = numerator.eval query * (cell.model.refine (leftIndex + 2)).value.eval
      query)
    (second : InverseRootPrimitive.PrimitiveModel (patch.neighborhood count) rightIndex numerator)
    (bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict cell.geometry.refines) numerator)
    (leftFinish : inner.Contains (parent.edge.point lastFraction))
    (rightStart : (patch.neighborhood count).box.Contains (parent.edge.point firstFraction))
    (rightFinish : (patch.neighborhood count).box.Contains (parent.edge.point lastFraction)) :
    Data.Gaussian.Norm.Basic.normSq ((first.value.eval (parent.edge.point lastFraction) - first.value.eval
      (parent.edge.point firstFraction)) -
      (second.primitive.value.eval (parent.edge.point lastFraction) - second.primitive.value.eval (parent.edge.point
        firstFraction))) ≤
      12 * ((cell.model.refine (leftIndex + 2)).bound + ((patch.neighborhood count).base.refine rightIndex).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * Data.Gaussian.Norm.Basic.normSq (parent.edge.point
          lastFraction - parent.edge.point firstFraction) := by
  let left := cell.model.refine (leftIndex + 2)
  let right := (patch.neighborhood count).base.refine rightIndex
  let edge : InverseModelEdgeTransition.EdgeTransition left right (parent.edge.point firstFraction) (parent.edge.point
    lastFraction) :=
    ⟨pointInside, leftFinish, (patch.neighborhood count).box_refines.contains rightStart,
      (patch.neighborhood count).box_refines.contains rightFinish,
      ⟨left.value.eval (parent.edge.point firstFraction), rfl, right.value.eval (parent.edge.point firstFraction), rfl,
        ⟨false, right.value.eval (parent.edge.point firstFraction), rfl,
          by
            have scalar := prepared_query_nearest cell
              differential parent reached firstFraction firstInside pointInside patch
              count leftIndex rightIndex rightStart
            simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩⟩
  have estimate := EdgeTransition.primitive_increment_le edge bounds first (FaceModels.primitiveOnBase second) firstEq
    second.coefficient_eq
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := rfl
  rw [sign, Data.Gaussian.Basic.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero]
    at estimate
  have unitDifference : (1 - 0 : InverseRootPolynomial.Coordinate) = 1 := by decide +kernel
  have scalar := estimate.trans_eq (by rw [unitDifference, one_pow, Fraction.Field.mul_one_direct])
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    FaceModels.primitiveOnBase] using scalar

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PreparedComparison
