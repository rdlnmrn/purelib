module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation

open Purelib.Data.Rat

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-!
# Opposite-sheet cancellation for the actual shared mesh readings

The primitive comparison pays the two retained meshes' ownership errors
before its local residual error. Both meshes and polynomial indices may
differ. The displayed global charges remain explicit for later aggregation.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds PrimitiveEdgeAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace bank}

/-- This bound is for the original shared vertex values, including their independently retained primitive offsets and
vertex owners on both sheets. -/
theorem shared_increment_sum_lt (domains : DomainBanks.FaceDomains frames face) (differential :
  Differentials.Basic.Differential genus)
    {globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    {leftTolerance rightTolerance : InverseRootPolynomial.Coordinate}
    (leftRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy globalBounds (domains.domain 0).steps
      leftTolerance)
    (rightRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy globalBounds (domains.domain 1).steps
      rightTolerance)
    (first : PrimitiveData.DomainPrimitives (domains.domain 0) differential leftRequest.index)
    (second : PrimitiveData.DomainPrimitives (domains.domain 1) differential rightRequest.index)
    {leftTriangles : List (RectangularOwnedTriangulation.ModelTriangle (domains.domain 0).geometry)}
    {rightTriangles : List (RectangularOwnedTriangulation.ModelTriangle (domains.domain 1).geometry)}
    {leftSurface : RectangularOwnedTriangulation.OwnedTriangulation leftTriangles} {rightSurface :
      RectangularOwnedTriangulation.OwnedTriangulation rightTriangles}
    (leftReadings : RectangularSharedPrimitives.SharedPrimitiveValues first.anchors first.offsets leftSurface)
    (rightReadings : RectangularSharedPrimitives.SharedPrimitiveValues second.anchors second.offsets rightSurface)
    (leftColumn leftRow : Fin ((domains.domain 0).steps + 1))
    (rightColumn rightRow : Fin ((domains.domain 1).steps + 1))
    (leftStart leftFinish : Fin leftSurface.mesh.vertices.length)
    (rightStart rightFinish : Fin rightSurface.mesh.vertices.length)
    (startEq : leftSurface.mesh.coordinate leftStart = rightSurface.mesh.coordinate rightStart)
    (finishEq : leftSurface.mesh.coordinate leftFinish = rightSurface.mesh.coordinate rightFinish)
    (leftStartInside : ((domains.domain 0).geometry.box leftColumn leftRow).Contains (leftSurface.mesh.coordinate
      leftStart))
    (leftFinishInside : ((domains.domain 0).geometry.box leftColumn leftRow).Contains (leftSurface.mesh.coordinate
      leftFinish))
    (rightStartInside : ((domains.domain 1).geometry.box rightColumn rightRow).Contains (rightSurface.mesh.coordinate
      rightStart))
    (rightFinishInside : ((domains.domain 1).geometry.box rightColumn rightRow).Contains (rightSurface.mesh.coordinate
      rightFinish))
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds
      (face.clearance.restrict ((domains.domain 0).patch.transported.cell leftColumn leftRow).geometry.refines)
      (PreparedPrimitiveSamples.differentialNumerator differential)} {target : InverseRootPolynomial.Coordinate}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds ((domains.domain 0).patch.models.ready leftColumn
      leftRow).model
      ((domains.domain 1).patch.models.ready rightColumn rightRow).model
      (leftSurface.mesh.coordinate leftStart) (leftSurface.mesh.coordinate leftFinish) target)
    (leftLater : request.index ≤ leftRequest.index) (rightLater : request.index ≤ rightRequest.index) :
    Data.Gaussian.Norm.Basic.normSq ((leftReadings.values leftFinish - leftReadings.values leftStart) +
      (rightReadings.values rightFinish - rightReadings.values rightStart)) <
      64 * (leftRequest.globalBound + rightRequest.globalBound) + 2 * target := by
  let leftIncrement := first.primitives.value leftColumn leftRow (leftSurface.mesh.coordinate leftFinish) -
    first.primitives.value leftColumn leftRow (leftSurface.mesh.coordinate leftStart)
  let rightIncrement := second.primitives.value rightColumn rightRow (rightSurface.mesh.coordinate rightFinish) -
    second.primitives.value rightColumn rightRow (rightSurface.mesh.coordinate rightStart)
  let leftError := (leftReadings.values leftFinish - leftReadings.values leftStart) - leftIncrement
  let rightError := (rightReadings.values rightFinish - rightReadings.values rightStart) - rightIncrement
  have leftOwnership : Data.Gaussian.Norm.Basic.normSq leftError ≤ 16 * leftRequest.globalBound := by
    have scalar := GridPrimitiveAccuracy.shared_local_increment_bound leftRequest leftReadings (domains.domain
      0).patch.cell_refines
      leftColumn leftRow leftStart leftFinish leftStartInside leftFinishInside
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have rightOwnership : Data.Gaussian.Norm.Basic.normSq rightError ≤ 16 * rightRequest.globalBound := by
    have scalar := GridPrimitiveAccuracy.shared_local_increment_bound rightRequest rightReadings (domains.domain
      1).patch.cell_refines
      rightColumn rightRow rightStart rightFinish rightStartInside rightFinishInside
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have ownership : Data.Gaussian.Norm.Basic.normSq (leftError + rightError) ≤ 32 * (leftRequest.globalBound +
    rightRequest.globalBound) :=
    (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftOwnership rightOwnership) (by decide)).trans_eq (by ring1))
  have analytic : Data.Gaussian.Norm.Basic.normSq (leftIncrement + rightIncrement) < target := by
    dsimp only [leftIncrement, rightIncrement]
    rw [← startEq, ← finishEq]
    exact FaceDomains.cell_primitive_sum_accurate domains leftColumn leftRow rightColumn rightRow request first second
      leftStartInside leftFinishInside (startEq.symm ▸ rightStartInside) (finishEq.symm ▸ rightFinishInside)
      leftLater rightLater
  have identity : (leftReadings.values leftFinish - leftReadings.values leftStart) +
      (rightReadings.values rightFinish - rightReadings.values rightStart) =
      (leftError + rightError) + (leftIncrement + rightIncrement) := by
    dsimp only [leftError, rightError]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((add_le_add ownership le_rfl).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct analytic
          (32 * (leftRequest.globalBound + rightRequest.globalBound))))).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains
