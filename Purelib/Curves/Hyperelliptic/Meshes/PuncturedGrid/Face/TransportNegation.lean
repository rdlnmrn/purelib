module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.SquareRootNegation
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Integration.Algebraic.Primitive.TransportedPrimitiveNegation
public import Purelib.Riemann.RootContinuation.ClearBoxRootNegation
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RootComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
import Init.Prelude
import Mathlib.Algebra.Group.Basic
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
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Rat

open Purelib.Integration.Algebraic.Primitive

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.ClearPath

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.ClearBoxRootNegation

open Purelib.Riemann.RootContinuation.ClearBoxRootNegation.SquareRootTrace

@[expose] public section

/-!
# Opposite-sheet primitive comparison at transported cell anchors

Both paths start at the two occurrences of the same retained face frame.
Clearance supplies the endpoint sign, including for non-origin cells and
independently prepared traces. The primitive estimate consumes the existing
cell polynomial and the existing endpoint neighborhood of the other trace.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.TransportNegation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition line_one line_zero)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (DensePrimitive PrimitiveOverlapBounds PrimitiveEdgeAccuracy)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {inner ambient : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient face.cell.box.anchor inner.anchor}

/-- Retain both endpoint classifications and their certified negative-root comparison. The reference and winding proof
come from the face bank. -/
def compareOppositeCellTrace (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners (BranchCutLifts.otherSheet sheet)))
    (inside : ClearPath.InBox face.cell.box path) (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval
      inner.anchor)) :
    OwnerFrame.OppositeOwners frame cell.traced.finishOwner traced.finishOwner :=
  TracedPath.oppositeOfInBox
    face.clearance (BranchIsolation.degreePositive curve)
    (BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
    cell.route.within cell.traced traced
    (Polynomial.Geometry.ClearPath.InBox.ofWithin cell.route.path cell.route.within face.cell.box.contains_anchor)
      inside frame

/-- The negative sign follows from the retained opposite source occurrence; the caller supplies no root-equivalence or
winding premise. -/
theorem opposite_anchor_nearest (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners (BranchCutLifts.otherSheet sheet)))
    {frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)}
    (opposite : OwnerFrame.OppositeOwners frame cell.traced.finishOwner traced.finishOwner)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (leftIndex rightIndex : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor +
      (neighborhood.patch.base.refine rightIndex).value.eval inner.anchor) ≤
    Data.Gaussian.Norm.Basic.normSq ((cell.model.refine leftIndex).value.eval inner.anchor -
      (neighborhood.patch.base.refine rightIndex).value.eval inner.anchor) := by
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch inner.anchor neighborhood.center_inside
  have seeds := SquareRootNegation.neg_equivalent
    (cell.aligned.seed.owner.certificate cell.aligned.seed.owner.parameterNonzero).value
    (cell.traced.finishOwner.certificate cell.traced.finishOwner.parameterNonzero).value
    (RootComparison.seedEquivalent cell)
  exact TransportedPrimitiveNegation.opposite_point_nearest
    cell sample neighborhood.center_inside
    (seeds.trans (opposite.equivalent.trans (neighborhood.pointEquivalent sample))) leftIndex rightIndex

/-- Only the two retained polynomial evaluations are stored in the edge transition. Its sign proof reuses the cached
endpoint classifications. -/
def oppositeAnchorTransition (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners (BranchCutLifts.otherSheet sheet)))
    {frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)}
    (opposite : OwnerFrame.OppositeOwners frame cell.traced.finishOwner traced.finishOwner)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (leftIndex rightIndex : Nat)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish) (rightFinish :
      neighborhood.patch.box.Contains finish) :
    InverseModelEdgeTransition.EdgeTransition (cell.model.refine leftIndex) (neighborhood.patch.base.refine rightIndex)
      inner.anchor finish where
  leftStart := inner.contains_anchor
  leftFinish := leftFinish
  rightStart := neighborhood.patch.box_refines.contains neighborhood.center_inside
  rightFinish := neighborhood.patch.box_refines.contains rightFinish
  sample :=
    let first := (cell.model.refine leftIndex).value.eval inner.anchor
    let second := (neighborhood.patch.base.refine rightIndex).value.eval inner.anchor
    ⟨first, rfl, second, rfl, ⟨true, -second, rfl, by
      have difference : first - -second = first + second := by ring1
      rw [difference, ← Data.Gaussian.Basic.sub_eq_add_neg]
      dsimp only [first, second]
      have scalar := opposite_anchor_nearest cell
        traced opposite neighborhood leftIndex rightIndex
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩

/-- The same-oriented primitive increments sum to their residual error. Both primitive constants disappear by taking
actual endpoint differences. -/
theorem primitive_sum_le (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners sheet)
  inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners (BranchCutLifts.otherSheet sheet)))
    {frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)}
    (opposite : OwnerFrame.OppositeOwners frame cell.traced.finishOwner traced.finishOwner)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (leftIndex rightIndex : Nat)
    {numerator coefficient : InverseRootPolynomial.Polynomial} (first : PrimitiveEdgeComparison.DensePrimitive
      coefficient inner)
    (firstEq : ∀ point, coefficient.eval point = numerator.eval point * (cell.model.refine leftIndex).value.eval point)
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch rightIndex numerator)
    (bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict cell.geometry.refines) numerator)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : inner.Contains finish) (rightFinish :
      neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((first.value.eval finish - first.value.eval inner.anchor) +
      (second.primitive.value.eval finish - second.primitive.value.eval inner.anchor)) ≤
      12 * ((cell.model.refine leftIndex).bound + (neighborhood.patch.base.refine rightIndex).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * Data.Gaussian.Norm.Basic.normSq (finish - inner.anchor)
          := by
  let edge := oppositeAnchorTransition cell traced
    opposite neighborhood leftIndex rightIndex finish leftFinish rightFinish
  have estimate := EdgeTransition.primitive_increment_le
    edge bounds first (FaceModels.primitiveOnBase second) firstEq second.coefficient_eq
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = -1 := rfl
  rw [sign, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero] at estimate
  have same (a b : InverseRootPolynomial.Gaussian) : a - (-1) * b = a + b := by ring1
  rw [same] at estimate
  have scalar := estimate.trans_eq (by rw [(show (1 : Fraction.Rational) - 0 = 1 by decide +kernel), one_pow,
    Fraction.Field.mul_one_direct])
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    FaceModels.primitiveOnBase] using scalar

/-- One existing executable edge request pays the sum for every pair of later Newton indices, without rebuilding either
path or its endpoint data. -/
theorem primitive_sum_accurate (cell : TransportedFaceInverseModels.TransportedCell models.bounds (models.frame.owners
  sheet) inner)
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners (BranchCutLifts.otherSheet sheet)))
    {frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval inner.anchor)}
    (opposite : OwnerFrame.OppositeOwners frame cell.traced.finishOwner traced.finishOwner)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) {leftIndex rightIndex : Nat}
    {numerator coefficient : InverseRootPolynomial.Polynomial} {finish : InverseRootPolynomial.Gaussian} {target :
      InverseRootPolynomial.Coordinate}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict cell.geometry.refines) numerator}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds cell.model neighborhood.patch.base.model
      inner.anchor finish target)
    (first : PrimitiveEdgeComparison.DensePrimitive coefficient inner)
    (firstEq : ∀ point, coefficient.eval point = numerator.eval point * (cell.model.refine leftIndex).value.eval point)
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch rightIndex numerator)
    (leftFinish : inner.Contains finish) (rightFinish : neighborhood.patch.box.Contains finish)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq ((first.value.eval finish - first.value.eval inner.anchor) +
      (second.primitive.value.eval finish - second.primitive.value.eval inner.anchor)) < target := by
  have bound := primitive_sum_le cell traced opposite
    neighborhood leftIndex rightIndex
    first firstEq second bounds finish leftFinish rightFinish
  have leftBound := (cell.model.refine_bound leftIndex).trans_le
    ((quarterRadius_antitone cell.model.bound_nonnegative leftLater).trans_eq
      (cell.model.refine_bound request.index).symm)
  have rightBound := (neighborhood.patch.base.model.refine_bound rightIndex).trans_le
    ((quarterRadius_antitone neighborhood.patch.base.model.bound_nonnegative rightLater).trans_eq
      (neighborhood.patch.base.model.refine_bound request.index).symm)
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, SeededNeighborhood.refine] at bound
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  apply bound.trans_lt
  apply lt_of_le_of_lt _ request.refined_scale_lt
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftBound rightBound) (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
    (Data.Gaussian.Basic.Canonical.normSq_nonneg (finish - inner.anchor))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.TransportNegation

