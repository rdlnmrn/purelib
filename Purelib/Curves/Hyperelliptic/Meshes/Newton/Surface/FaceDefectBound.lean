module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamRibbons
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Tactic.Ring
public import Purelib.Riemann.Integration.RectangularClippedConjugateSeams

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamRibbons

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Rectangle.Boundary

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open
  RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh.MatchedHorizontalSide

open
  Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh.MatchedVerticalSide

public section

/-! The requested complete-face defect bound includes every internal seam
and corner and is homogeneous for arbitrary coefficient vectors. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest (seamTarget)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
    {depth : Nat}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {position : Fin grid.faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Integration.Path.BoundaryRibbon (Ribbon)

variable {pieceError : Rational} {minimum : Nat}

variable {base : ExteriorRequest energy pieceError
  minimum} {traces : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides.SeamTraces energy position}
  {allowance : Rational} {stage : Nat} {cache :
    Numerics domains stage}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {assemblies :
    ExteriorRequest.Assemblies energy cache
    coefficients}
  {perimeters : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters assemblies}

/-- The original finite-sum allowance pays the squared norm of the actual sum with its retained nonnegative homogeneous
factor. -/
private theorem sum_paid {count : Nat} (values : Fin count → Data.Gaussian.Basic.Canonical) {factor target :
  Fraction.Rational}
    (nonnegative : 0 ≤ factor) (positive : 0 < target)
    (bounded : ∀ i, Data.Gaussian.Norm.Basic.normSq (values i) ≤ factor * Aggregate.perTerm target count) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin values) ≤ factor * target := by
  have bound := Indexed.normSq_sumFin_le values _ bounded
  have payment : (count : Fraction.Rational) ^ 2 * Aggregate.perTerm target count ≤ target :=
    (le_of_eq (by ring1)).trans (Aggregate.count_mul_perTerm_lt positive count).le
  apply bound.trans
  calc
    _ = factor * ((count : Fraction.Rational) ^ 2 * Aggregate.perTerm target count) := by ring1
    _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct payment nonnegative

/-- The two original nested seam allowances pay the complete retained row-and-column sum within one sixteenth of the
face allowance. -/
private theorem double_sum_paid {columns rows : Nat} (values : Fin columns → Fin rows → Data.Gaussian.Basic.Canonical)
    {factor allowance : Fraction.Rational} (nonnegative : 0 ≤ factor) (positive : 0 < allowance)
    (bounded : ∀ column row, Data.Gaussian.Norm.Basic.normSq (values column row) ≤ factor *
      FaceDefectRequest.seamTarget allowance columns rows) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (values column)))
      ≤ factor * (allowance / 16) := by
  apply sum_paid _ nonnegative
    (Fraction.Order.Field.div_pos_direct positive (by decide))
  intro column
  exact sum_paid _ nonnegative
    (Aggregate.perTerm_positive (Fraction.Order.Field.div_pos_direct positive (by decide)) _) (bounded column)

namespace FaceDefectRequest

/-- The original complete horizontal seam bank, with all vertical endpoint corrections, satisfies its retained
homogeneous allowance. -/
theorem horizontal_bound (request : FaceDefectRequest base traces allowance) (later : request.index ≤
  stage)
    (face : FaceAssembly perimeters position) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun column : Fin ((PieceIndices.columns
      (partitions.get position)) + 1) => FiniteSum.Fin.sumFin (fun row : Fin (PieceIndices.rows (partitions.get
      position)) =>
      Assembly.verticalSeam (Perimeters.faceSides perimeters position) column row -
        BilinearGridBoundary.verticalEndpoint face.corners column row))) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * (allowance /
        16) := by
  apply Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound.double_sum_paid _
    (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)) request.positive
  intro column row
  let trace := (traces.horizontal.get column).get row
  let ribbons := Data.Vector.Basic.vectorOfFn fun i : Fin genus =>
    Trace.energyRibbon trace (cache.atDomain position sheet i).anchors (cache.atDomain position sheet i).offsets
  exact FaceAssembly.horizontal_seam_bound face column row trace
    ((base.entries.get position).get (PieceIndices.pieceIndex (partitions.get position) column row.succ)).tolerance
    ((request.horizontal.get column).get row) ((request.horizontal_le column row).trans later)
    ribbons (fun i => Data.Vector.Basic.vectorOfFn_apply _ i)

/-- The original complete vertical seam bank, with all horizontal endpoint corrections, satisfies its retained
homogeneous allowance. -/
theorem vertical_bound (request : FaceDefectRequest base traces allowance) (later : request.index ≤
  stage)
    (face : FaceAssembly perimeters position) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun column : Fin (PieceIndices.columns
      (partitions.get position)) => FiniteSum.Fin.sumFin (fun row : Fin ((PieceIndices.rows (partitions.get position)) +
      1) =>
      Assembly.horizontalSeam (Perimeters.faceSides perimeters position) column row -
        BilinearGridBoundary.horizontalEndpoint face.corners column row))) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * (allowance /
        16) := by
  apply Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound.double_sum_paid _
    (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)) request.positive
  intro column row
  let trace := (traces.vertical.get column).get row
  let ribbons := Data.Vector.Basic.vectorOfFn fun i : Fin genus =>
    Trace.energyRibbon trace (cache.atDomain position sheet i).anchors (cache.atDomain position sheet i).offsets
  exact FaceAssembly.vertical_seam_bound face column row trace
    ((base.entries.get position).get (PieceIndices.pieceIndex (partitions.get position) column.castSucc row)).tolerance
    ((request.vertical.get column).get row) ((request.vertical_le column row).trans later)
    ribbons (fun i => Data.Vector.Basic.vectorOfFn_apply _ i)

/-- The original complete face request pays every internal seam and corner defect at the same retained stage.

The bound preserves the actual genus and squared coefficient-norm factors for an arbitrary coefficient vector. -/
theorem accurate (request : FaceDefectRequest base traces allowance) (later : request.index ≤ stage)
    (face : FaceAssembly perimeters position) :
    Data.Gaussian.Norm.Basic.normSq (face.seams + face.cornerTotal) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * allowance :=
        by
  have horizontal := horizontal_bound
    request later face
  have vertical := vertical_bound request
    later face
  have corners := FaceCornerRequest.accurate request.corners (request.corners_le.trans later) face
  have seams : Data.Gaussian.Norm.Basic.normSq face.seams ≤
      2 * ((genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        (allowance / 16) +
        (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * (allowance
          / 16)) := by
    rw [face.seams_eq, BilinearGridBoundary.correctedSeamSum]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add vertical horizontal) (by decide))
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two face.seams face.cornerTotal).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add seams corners) (by decide))
  have numeric : (8 : Fraction.Rational) * 16⁻¹ + 2 * 4⁻¹ = 1 := by decide
  apply estimate.trans_eq
  calc
    _ = ((genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * allowance)
      *
        (8 * 16⁻¹ + 2 * 4⁻¹) := by simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct]; ring1
    _ = _ := by rw [numeric, Fraction.Field.mul_one_direct]

end FaceDefectRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound
