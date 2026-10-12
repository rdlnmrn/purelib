module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
public import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RootComparison
public import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Coherent
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
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap

public section

/-!
# Primitive edge comparison with actual contained face traces

A cell's transported inverse model and a neighborhood of an alternative
actual trace agree at the cell anchor. This fixes the unflipped polynomial
transition on every shared straight edge, at independent Newton indices.
The primitive comparison consumes cached coefficients through semantic
equations. It does not yet assemble the whole exterior or the A/B sums.
-/

section

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings.PreparedObservationNeighborhoods

open Purelib.Riemann.RootContinuation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveEdgeAccuracy)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_one line_zero)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RootComparison (seedEquivalent compareCellTrace)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (DensePrimitive)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {inner : Purelib.Riemann.Normalization.InverseRootPolynomial.Box} {ambient :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient face.cell.box.anchor inner.anchor}

/-- The transported cell and a retained trace neighborhood agree nearest at the anchor.

Contained traces and their owner frame supply the root agreement. The two
Newton indices are independent and the polynomial values remain unflipped. -/
theorem anchor_nearest (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet)
  inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor -
      (neighborhood.patch.base.refine rightIndex).value.eval inner.anchor) ≤
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor +
      (neighborhood.patch.base.refine rightIndex).value.eval inner.anchor) := by
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch inner.anchor neighborhood.center_inside
  exact cell.anchor_nearest sample neighborhood.center_inside
    ((RootComparison.seedEquivalent cell).trans ((RootComparison.compareCellTrace cell traced inside frame).trans
      (neighborhood.pointEquivalent sample))) leftIndex rightIndex

/-- Build an unflipped edge transition from two retained polynomial caches.

The supplied cache equalities identify both values at the shared anchor.
The transition retains the endpoint containment witnesses and evaluates each
cache once; root agreement certifies nearestness. -/
@[expose] def anchorTransition (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (leftIndex rightIndex : Nat)
    (left : InverseRootPolynomial.Model curve.polynomial inner) (right : InverseRootPolynomial.Model curve.polynomial
      neighborhood.patch.base.box)
    (leftEq : left.value.eval inner.anchor = (cell.model.refine leftIndex).value.eval inner.anchor)
    (rightEq : right.value.eval inner.anchor = (neighborhood.patch.base.refine rightIndex).value.eval inner.anchor)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish) (rightFinish :
      neighborhood.patch.box.Contains finish) :
    InverseModelEdgeTransition.EdgeTransition left right inner.anchor finish where
  leftStart := inner.contains_anchor
  leftFinish := leftFinish
  rightStart := neighborhood.patch.box_refines.contains neighborhood.center_inside
  rightFinish := neighborhood.patch.box_refines.contains rightFinish
  sample :=
    let first := left.value.eval inner.anchor
    let second := right.value.eval inner.anchor
    ⟨first, rfl, second, rfl, ⟨false, second, rfl, by
      dsimp only [first, second]
      rw [leftEq, rightEq]
      have scalar := anchor_nearest cell
        traced inside frame neighborhood leftIndex rightIndex
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩

/-- Read a dense primitive on the retained inverse model's base box.

The primitive value and derivative identity are retained, and its Taylor
remainder bound certifies increments between contained points. -/
@[expose] def primitiveOnBase {polynomial numerator : InverseRootPolynomial.Polynomial} {count index : Nat}
    {patch : ContinuedInverseRoot.ContinuedNeighborhood polynomial count} (model : InverseRootPrimitive.PrimitiveModel
      patch index numerator) :
    PrimitiveEdgeComparison.DensePrimitive model.coefficient patch.base.box where
  value := model.primitive.value
  derivative_eq := model.primitive.derivative_eq
  remainderBound := Taylor.denseTaylorRemainderBound model.primitive.value patch.base.box
  remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
  increment_bound := by
    intro first last firstInside lastInside
    have estimate := Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      model.primitive.value lastInside firstInside
    rw [model.primitive.derivative_eq] at estimate
    exact estimate

/-- Bound the difference of two retained primitive increments by their residual budgets.

The supplied coefficient identity, contained trace and overlap bounds fix
the same unflipped edge. The bound retains both refinement indices and the
squared endpoint displacement. -/
theorem primitive_increment_le (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (leftIndex rightIndex : Nat)
    {numerator coefficient : InverseRootPolynomial.Polynomial} (first : PrimitiveEdgeComparison.DensePrimitive
      coefficient inner)
    (firstEq : ∀ point, coefficient.eval point = numerator.eval point * (cell.model.refine leftIndex).value.eval point)
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch rightIndex numerator)
    (bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict cell.geometry.refines) numerator)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish) (rightFinish :
      neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((first.value.eval finish - first.value.eval inner.anchor) -
      (second.primitive.value.eval finish - second.primitive.value.eval inner.anchor)) ≤
      12 * ((cell.model.refine leftIndex).bound + (neighborhood.patch.base.refine rightIndex).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * Data.Gaussian.Norm.Basic.normSq (finish - inner.anchor)
          := by
  let edge := anchorTransition cell traced
    inside frame neighborhood leftIndex rightIndex
    (cell.model.refine leftIndex) (neighborhood.patch.base.refine rightIndex) rfl rfl finish leftFinish rightFinish
  have estimate := EdgeTransition.primitive_increment_le edge bounds first
    (primitiveOnBase second) firstEq
    second.coefficient_eq
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = 1 := rfl
  rw [sign, Data.Gaussian.Basic.one_mul, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero]
    at estimate
  have unitDifference : (1 - 0 : Fraction.Rational) = 1 := by decide
  have scalar := estimate.trans_eq (by rw [unitDifference, one_pow, Fraction.Field.mul_one_direct])
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    primitiveOnBase] using scalar

/-- The retained edge accuracy request pays the difference of primitive increments.

Both primitives use the request index. Its certified residual scale bounds
their unflipped increments strictly below the requested target. -/
theorem primitive_increment_lt (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) {numerator coefficient :
      InverseRootPolynomial.Polynomial}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict cell.geometry.refines) numerator}
    {finish : InverseRootPolynomial.Gaussian} {target : InverseRootPolynomial.Coordinate}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds cell.model neighborhood.patch.base.model
      inner.anchor finish target)
    (first : PrimitiveEdgeComparison.DensePrimitive coefficient inner)
    (firstEq : ∀ point, coefficient.eval point = numerator.eval point * (cell.model.refine request.index).value.eval
      point)
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch request.index numerator)
    (leftFinish : inner.Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((first.value.eval finish - first.value.eval inner.anchor) -
      (second.primitive.value.eval finish - second.primitive.value.eval inner.anchor)) < target := by
  have paid := request.refined_scale_lt
  have paid : 12 * ((cell.model.refine request.index).bound + (neighborhood.patch.base.refine request.index).bound) *
      (bounds.numeratorUpper * bounds.inverseUpper) * Data.Gaussian.Norm.Basic.normSq (finish - inner.anchor) <
        target := by
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, SeededNeighborhood.refine] using paid
  exact (primitive_increment_le cell
    traced inside frame neighborhood request.index request.index
    first firstEq second bounds finish leftFinish rightFinish).trans_lt paid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

end
