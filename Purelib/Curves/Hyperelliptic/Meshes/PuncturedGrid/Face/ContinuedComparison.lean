module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
public import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Init.Prelude
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
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Polynomial.Winding

open Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.ClearBoxRootTransport

open Purelib.Riemann.RootContinuation.RootPathTransport

@[expose] public section

/-!
# Cell models at arbitrary occurrences of actual face paths

Join the retained source-to-cell owner path to its covered internal path.
The two pieces may have different original ambient boxes. Full-face winding
identifies the joined occurrence with every actual contained face trace.
For polynomial comparison, the auxiliary internal preparation is proof-only:
the executable edge reads just the supplied polynomial caches.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveEdgeAccuracy PrimitiveOverlapBounds DensePrimitive)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels (primitiveOnBase)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_one line_zero)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation (prepared_within)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.RootPathTransport.OwnerPath
open Purelib.Riemann.RootContinuation.ClearBoxRootTransport.TracedPath
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {inner ambient : Purelib.Riemann.Normalization.InverseRootPolynomial.Box} {point :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient face.cell.box.anchor point}

/-- Compare the actual two-piece continuation with a global face trace. Both original preparations and their owners are
retained. The winding equality is obtained by telescoping the face potential, not assumed. -/
def compareContinuedTrace (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet)
  inner)
    {localPath : Polynomial.Geometry.ClearPath curve.polynomial inner inner.anchor point}
    (prepared : PreparedClearPathModels.CoveredTracedPath localPath cell.traced.finishOwner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point)) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName prepared.traced.finishOwner)
      (OwnerTraceReadings.ownerName traced.finishOwner) := by
  let joined := cell.traced.trace.get.append prepared.traced.trace.get
  have localInside : localPath.InBox face.cell.box :=
    (Polynomial.Geometry.ClearPath.InBox.ofWithin localPath (PreparedPolynomialSheetPropagation.prepared_within
      prepared.traced.prepared)
      inner.contains_anchor).mono cell.geometry.refines
  have winding : ClearPath.rawWinding path = Polygon.Basic.chainRaw curve.polynomial face.cell.box.anchor
    joined.vertices := by
    rw [OwnerPath.append_winding,
      TracedPath.winding_original cell.traced,
      TracedPath.winding_original prepared.traced,
      Route.winding face.clearance
        (BranchIsolation.degreePositive curve) cell.route face.cell.box.contains_anchor,
      ClearPath.rawWinding_eq_potential face.clearance
        (BranchIsolation.degreePositive curve) localPath localInside,
      ClearPath.rawWinding_eq_potential face.clearance
        (BranchIsolation.degreePositive curve) path inside]
    omega
  exact (TracedPath.equivalentOfOwnerPathSelections
    (BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
    (PreparedPolynomialSheetPropagation.prepared_within traced.prepared) traced
    joined frame (frame.select traced.finishOwner) (frame.select prepared.traced.finishOwner) winding).symm

/-- The internal connector and its coverage are constructed inside the proof. At an arbitrary reached point, no local
path, coverage, root sign, or same-occurrence certificate is required by the caller. -/
theorem trace_aligned (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet)
  inner)
    (differential : Differentials.Basic.Differential genus) (traced : PreparedPathTrace.TracedPath path
      (models.frame.owners sheet))
    (inside : ClearPath.InBox face.cell.box path) (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) (index : Nat) :
    InverseRootPolynomial.RootAligned ((Model.overlapRefine cell.model) index) point (OwnerTraceReadings.ownerName
      traced.finishOwner) := by
  let route := Route.build (face.clearance.restrict cell.geometry.refines)
    inner.anchor point inner.contains_anchor pointInside
  let prepared := CoveredTracedPath.build route.path route.within cell.traced.finishOwner
  intro count patch patchInside sample roots otherIndex
  exact cell.continuedAligned differential prepared index patch patchInside sample
    ((compareContinuedTrace cell prepared traced
      inside frame).trans roots) otherIndex

/-- The fixed cell polynomial and the actual endpoint neighborhood agree at independently requested indices beyond the
fixed two-step cocycle floor. -/
theorem trace_nearest (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet)
  inner)
    (differential : Differentials.Basic.Differential genus) (traced : PreparedPathTrace.TracedPath path
      (models.frame.owners sheet))
    (inside : ClearPath.InBox face.cell.box path) (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced
      count)
    (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval point -
      (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point) ≤
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine (leftIndex + 2)).value.eval point +
      (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point) := by
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch point neighborhood.center_inside
  exact trace_aligned cell differential traced inside
    frame pointInside leftIndex neighborhood.patch
    neighborhood.center_inside sample (neighborhood.pointEquivalent sample) rightIndex

/-- A shared edge beginning anywhere in the cell has the actual unflipped transition. Generated caches use pointwise
semantic equations; no root transport, auxiliary preparation, or classification runs in this value. -/
def traceTransition (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet)
  inner)
    (differential : Differentials.Basic.Differential genus) (traced : PreparedPathTrace.TracedPath path
      (models.frame.owners sheet))
    (inside : ClearPath.InBox face.cell.box path) (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced
      count)
    (leftIndex rightIndex : Nat)
    (left : InverseRootPolynomial.Model curve.polynomial inner) (right : InverseRootPolynomial.Model curve.polynomial
      neighborhood.patch.base.box)
    (leftEq : left.value.eval point = (cell.model.refine (leftIndex + 2)).value.eval point)
    (rightEq : right.value.eval point = (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish) (rightFinish :
      neighborhood.patch.box.Contains finish) :
    InverseModelEdgeTransition.EdgeTransition left right point finish where
  leftStart := pointInside
  leftFinish := leftFinish
  rightStart := neighborhood.patch.box_refines.contains neighborhood.center_inside
  rightFinish := neighborhood.patch.box_refines.contains rightFinish
  sample :=
    let first := left.value.eval point
    let second := right.value.eval point
    ⟨first, rfl, second, rfl, ⟨false, second, rfl, by
      dsimp only [first, second]
      rw [leftEq, rightEq]
      have scalar := trace_nearest cell differential
        traced inside frame pointInside neighborhood leftIndex rightIndex
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩

/-- Compare the actual primitive increments on an edge starting anywhere in the cell. The complete residual budget is
paid without a Taylor floor or an additional operational sheet-identification premise. -/
theorem trace_primitive_increment_le (cell : TransportedFaceInverseModels.TransportedCell models.bounds
  (models.frame.owners sheet) inner)
    (differential : Differentials.Basic.Differential genus) (traced : PreparedPathTrace.TracedPath path
      (models.frame.owners sheet))
    (inside : ClearPath.InBox face.cell.box path) (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced
      count)
    (leftIndex rightIndex : Nat) {numerator coefficient : InverseRootPolynomial.Polynomial}
    (first : PrimitiveEdgeComparison.DensePrimitive coefficient inner)
    (firstEq : ∀ query, coefficient.eval query = numerator.eval query * (cell.model.refine (leftIndex + 2)).value.eval
      query)
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch (rightIndex + 2) numerator)
    (bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict cell.geometry.refines) numerator)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish) (rightFinish :
      neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((first.value.eval finish - first.value.eval point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) ≤
      12 * ((cell.model.refine (leftIndex + 2)).bound + (neighborhood.patch.base.refine (rightIndex + 2)).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * Data.Gaussian.Norm.Basic.normSq (finish - point) := by
  let edge := traceTransition cell differential
    traced inside frame pointInside neighborhood leftIndex rightIndex
    (cell.model.refine (leftIndex + 2)) (neighborhood.patch.base.refine (rightIndex + 2)) rfl rfl finish leftFinish
      rightFinish
  have estimate := EdgeTransition.primitive_increment_le
    edge bounds first (FaceModels.primitiveOnBase second) firstEq second.coefficient_eq
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := rfl
  rw [sign, Data.Gaussian.Basic.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero]
    at estimate
  have scalar := estimate.trans_eq (by rw [(show (1 : Fraction.Rational) - 0 = 1 from by decide), one_pow,
    Fraction.Field.mul_one_direct])
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    FaceModels.primitiveOnBase] using scalar

/-- The existing finite accuracy request pays this arbitrary-point comparison too. The fixed two extra Newton steps
ensure cocycle accuracy; their additional improvement only decreases the requested bound. -/
theorem trace_primitive_increment_lt (cell : TransportedFaceInverseModels.TransportedCell models.bounds
  (models.frame.owners sheet) inner)
    (differential : Differentials.Basic.Differential genus) (traced : PreparedPathTrace.TracedPath path
      (models.frame.owners sheet))
    (inside : ClearPath.InBox face.cell.box path) (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point))
    (pointInside : inner.Contains point) {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced
      count)
    {numerator coefficient : InverseRootPolynomial.Polynomial}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict cell.geometry.refines) numerator}
    {finish : InverseRootPolynomial.Gaussian} {target : InverseRootPolynomial.Coordinate}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds cell.model neighborhood.patch.base.model point
      finish target)
    (first : PrimitiveEdgeComparison.DensePrimitive coefficient inner)
    (firstEq : ∀ query, coefficient.eval query = numerator.eval query * (cell.model.refine (request.index +
      2)).value.eval query)
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch (request.index + 2) numerator)
    (leftFinish : inner.Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((first.value.eval finish - first.value.eval point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) < target := by
  have decrease (model : InverseRootPolynomial.Model curve.polynomial inner) :
      (model.refine (request.index + 2)).bound ≤ (model.refine request.index).bound := by
    rw [Model.refine_bound, Model.refine_bound]
    exact quarterRadius_antitone model.bound_nonnegative (Nat.le_add_right _ _)
  have rightDecrease : (neighborhood.patch.base.refine (request.index + 2)).bound ≤
      (neighborhood.patch.base.refine request.index).bound := by
    rw [SeededNeighborhood.refine, SeededNeighborhood.refine, Model.refine_bound, Model.refine_bound]
    exact quarterRadius_antitone neighborhood.patch.base.model.bound_nonnegative (Nat.le_add_right _ _)
  have bound := trace_primitive_increment_le cell
    differential traced inside frame pointInside neighborhood
    request.index request.index first firstEq second bounds finish leftFinish rightFinish
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, SeededNeighborhood.refine] at bound
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  apply bound.trans_lt
  apply lt_of_le_of_lt _ request.refined_scale_lt
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (decrease cell.model) rightDecrease) (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
    (Data.Gaussian.Basic.Canonical.normSq_nonneg (finish - point))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison
