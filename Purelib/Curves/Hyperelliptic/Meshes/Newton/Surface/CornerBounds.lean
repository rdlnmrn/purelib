module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.ClippedExteriorTolerance
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Tactic.Ring
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
import Purelib.Riemann.Periods.RectangularBilinearCorners

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerGeometry.SurfaceRequest.ExteriorRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Integration.Polynomial

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

public section

/-! Homogeneous bounds for the actual corner polygons between surface
pieces. All four readings refer to the same retained numerical bank and
physical junction; their model owners need not agree. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_mul_right)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg normSq_mul)
open Purelib.Data.Gaussian.Basic (conj_add conj_mul)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded Conjugate bounded_of_conjugate sub_conjugate)
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
  {partitions : SurfacePartitions observations grid} {coarse :
    SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions coarse fixed error} {stage :
    Nat} {cache : Numerics domains stage}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {assemblies :
    ExteriorRequest.Assemblies energy cache
    coefficients}
  {perimeters : Perimeters assemblies} {position : Fin
    grid.faces.regulars.length} {cap : Rational}

/-- Conjugating the finite original coefficient sum conjugates each coefficient and retained basis value. -/
private theorem conjugate_combination {count : Nat} (coefficients values : Fin count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun row => coefficients row * values row)) =
      FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Basic.conj (coefficients row) *
      Data.Gaussian.Basic.conj (values row)) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, Data.Gaussian.Basic.conj_add, Data.Gaussian.Basic.conj_mul, ih,
      FiniteSum.Fin.sumFin_succ]

/-- The actual aligned coefficient pair at an original model owner has conjugate components. -/
private theorem value_conjugate (column row : Fin (((domains.get position).domain sheet).steps + 1)) (point :
  Data.Gaussian.Basic.Canonical) :
    PrimitivePoint.Conjugate (SeamAreas.seamValues (sheet := sheet) cache coefficients position column row point) :=
  (conjugate_combination (fun row => coefficients row) _).symm

/-- Two original model owners at the same physical point have the retained homogeneous overlap bound on their actual
coefficient readings. -/
private theorem owner_difference_bound
    (request : EnergyPreflight.Request (fixed.get position).get cap) (later : request.index ≤ stage)
    (first last : RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry)
    (same : first.point = last.point) :
    PrimitivePoint.Bounded ((SeamAreas.seamValues (sheet := sheet) cache coefficients position first.column first.row
      first.point).sub
      (SeamAreas.seamValues (sheet := sheet) cache coefficients position last.column last.row last.point))
      (4 * (genus : Fraction.Rational) * Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients * cap) := by
  apply PrimitivePoint.bounded_of_conjugate (PrimitivePoint.sub_conjugate
    (value_conjugate _ _ _)
    (value_conjugate _ _ _))
  let gap := fun row => (cache.atDomain position sheet row).anchors.alignedValue
      (cache.atDomain position sheet row).offsets first.column first.row first.point -
    (cache.atDomain position sheet row).anchors.alignedValue
      (cache.atDomain position sheet row).offsets last.column last.row last.point
  have gaps (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq (gap row) ≤ 4 * cap := by
    let accuracy := request.rowAtStage stage later row
    dsimp only [gap]
    rw [same]
    have firstInside := first.contains
    rw [same] at firstInside
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (accuracy.overlap_bound (cache.atDomain position sheet row).anchors (cache.atDomain position sheet
      row).offsets
      ((domains.get position).domain sheet).patch.cell_refines _ _ _ _ firstInside last.contains).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accuracy.accurate.le (by decide))
  have readback : ((SeamAreas.seamValues (sheet := sheet) cache coefficients position first.column first.row
    first.point).sub
      (SeamAreas.seamValues (sheet := sheet) cache coefficients position last.column last.row last.point)).right =
      FiniteSum.Fin.sumFin (fun row => coefficients row * gap row) := by
    change FiniteSum.Fin.sumFin _ - FiniteSum.Fin.sumFin _ = _
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only [gap]
    ring1
  rw [readback]
  have bound := Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun row => coefficients row * gap row) (fun row => Data.Gaussian.Norm.Basic.normSq (coefficients row) * (4
      * cap)) (fun row => by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (gaps row)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _))
  rw [FiniteSum.Fin.sumFin_mul_right] at bound
  have coefficientReadback : FiniteSum.Fin.sumFin
      (fun row => Data.Gaussian.Norm.Basic.normSq (coefficients row)) =
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
    unfold PreparedObservationCoercivity.coefficientNormSq
    exact FiniteSum.Fin.sumFin_congr
      (fun row => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  rw [coefficientReadback, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  exact bound.trans_eq (by ring1)

/-- The actual four-owner interior corner polygon satisfies the original homogeneous squared overlap bound. -/
theorem FaceAssembly.corner_bound (face : FaceAssembly perimeters position)
    (request : EnergyPreflight.Request (fixed.get position).get cap) (later : request.index ≤ stage)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin (PieceIndices.rows (partitions.get
      position))) :
    Data.Gaussian.Norm.Basic.normSq (BilinearGridBoundary.interiorCorner face.corners column row) ≤
      256 * (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * cap ^ 2
        := by
  let value := fun right above =>
    let owner := SurfaceRequest.junctionOwner energy position column row right above
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point
  have bounded (right above : Bool) : PrimitivePoint.Bounded ((value right above).sub (value false false))
      (4 * (genus : Fraction.Rational) * PreparedObservationCoercivity.coefficientNormSq coefficients * cap) :=
    owner_difference_bound request later _ _
      ((SurfaceRequest.junctionOwner_point energy position column row right above).trans
        (SurfaceRequest.junctionOwner_point energy position column row false false).symm)
  have readback := FaceAssembly.corner_junction face column row
  rw [BilinearGridBoundary.interiorCorner, readback.1, readback.2.1, readback.2.2.1, readback.2.2.2]
  exact (BilinearGridBoundary.cornerArea_bound (bounded false true) (bounded true true) (bounded true false)).trans_eq
    (by ring1)

/-- The complete retained sum of interior corner polygons has the homogeneous column-count and row-count bound. -/
theorem FaceAssembly.cornerTotal_bound (face : FaceAssembly perimeters position)
    (request : EnergyPreflight.Request (fixed.get position).get cap) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq face.cornerTotal ≤ (genus : Fraction.Rational) ^ 2 *
      PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
      (256 * ((PieceIndices.columns (partitions.get position)) : Fraction.Rational) ^ 2 * ((PieceIndices.rows
        (partitions.get position)) : Fraction.Rational) ^ 2 * cap ^ 2) := by
  rw [face.cornerTotal_eq]
  have bound := Indexed.normSq_sumFin_le
    (fun column : Fin (PieceIndices.columns (partitions.get position)) => FiniteSum.Fin.sumFin
      (fun row : Fin (PieceIndices.rows (partitions.get position)) => BilinearGridBoundary.interiorCorner face.corners
        column row))
    (((PieceIndices.rows (partitions.get position)) : Fraction.Rational) ^ 2 *
      (256 * (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * cap ^
        2))
    (fun column => Indexed.normSq_sumFin_le _ _
      (Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds.FaceAssembly.corner_bound face request later column))
  exact bound.trans_eq (by ring1)

set_option genInjectivity false in
/-- A numerical request for all interior observation-cut corners in one whole face. The existing finite corner budget is
reused with zero seam slope; no coefficient vector is needed to select the stage. -/
structure FaceCornerRequest (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid)
    (fixed : NewtonRequestedObservationEnergy.Preflights domains sheet) (position : Fin grid.faces.regulars.length)
      (allowance : Fraction.Rational) where
  /-- The retained finite corner budget on the original partition dimensions with zero seam slope. -/ budget :
    Rectangle.ClippedExteriorTolerance
    (PieceIndices.columns (partitions.get position)) (PieceIndices.rows (partitions.get position)) 0 allowance
  /-- The original basis model accuracy request at that exact retained corner budget cap. -/ models :
    EnergyPreflight.Request (fixed.get position).get budget.cap

constructive_injectivity FaceCornerRequest

namespace FaceCornerRequest

/-- Reuse the original finite corner budget to prepare coefficient-independent model accuracy on the retained face. -/
@[expose] def build (partitions : NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid) (fixed :
  NewtonRequestedObservationEnergy.Preflights domains sheet)
    (position : Fin grid.faces.regulars.length) (allowance : Fraction.Rational) (positive : 0 < allowance) :
    Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds.FaceCornerRequest partitions fixed position allowance :=
  let budget := ClippedExteriorTolerance.build
    (PieceIndices.columns (partitions.get position)) (PieceIndices.rows (partitions.get position)) 0 allowance (by
      decide) positive
  ⟨budget, EnergyPreflight.Request.build (fixed.get position).get budget.cap budget.positive⟩

/-- Every later actual face corner sum satisfies the requested homogeneous corner allowance. -/
theorem accurate {allowance : Fraction.Rational} (request :
  Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds.FaceCornerRequest partitions fixed position allowance)
    (later : request.models.index ≤ stage) (face : FaceAssembly perimeters position) :
    Data.Gaussian.Norm.Basic.normSq face.cornerTotal ≤ (genus : Fraction.Rational) ^ 2 *
      PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * allowance := by
  have paid := request.budget.pair_bound
    (firstError := request.budget.cap) (secondError := request.budget.cap) (firstSlope := 0) (secondSlope := 0)
    request.budget.positive.le le_rfl le_rfl (by decide) le_rfl le_rfl
  simp only [-eq_self, -iff_self, Fraction.Order.Basic.max_self, mul_zero, zero_add, add_zero] at paid
  let amount := 256 * ((PieceIndices.columns (partitions.get position)) : Fraction.Rational) ^ 2 *
    ((PieceIndices.rows (partitions.get position)) : Fraction.Rational) ^ 2 * request.budget.cap ^ 2
  have nonnegative : 0 ≤ amount := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have bound : amount ≤ allowance :=
    (le_add_of_nonneg_right nonnegative).trans ((le_of_eq (by dsimp only [amount]; ring1)).trans paid)
  exact (Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds.FaceAssembly.cornerTotal_bound face request.models
    later).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)))

end FaceCornerRequest

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds
