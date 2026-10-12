module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamRibbons
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.EnergyRibbonCombination
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Polynomial.Rectangle.ClippedExteriorTolerance
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy

open Purelib.Data.Rat

open Purelib.Data.Vector

public section

/-! A coefficient-independent numerical request pays every internal seam
and corner of a complete regular face at one common later index. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data

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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CornerBounds (FaceCornerRequest)

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
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Basic (conj_add conj_mul)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Integration.Path.BoundaryRibbon (Ribbon)

variable {pieceError : Rational} {minimum : Nat}

namespace FaceDefectRequest

/-- Two finite-sum allowances pay every row and column count. -/
@[expose] def seamTarget (allowance : Fraction.Rational) (columns rows : Nat) : Fraction.Rational :=
  Aggregate.perTerm (Aggregate.perTerm (allowance / 16) columns) rows

/-- A positive face allowance yields positive tolerance for every retained row-and-column seam count.

The two original finite per-term allowances divide the same positive input across the supplied column and row counts. -/
theorem seamTarget_positive {allowance : Fraction.Rational} (positive : 0 < allowance) (columns rows : Nat) :
    0 < seamTarget allowance columns rows :=
  Aggregate.perTerm_positive
    (Aggregate.perTerm_positive (Fraction.Order.Field.div_pos_direct positive (by decide)) _) _

/-- The dependent original horizontal seam energy request bank on the exact retained column and internal-row indices. -/
@[expose] def HorizontalRequests (base : ExteriorRequest energy pieceError minimum)
    (traces : MatchedSides.SeamTraces energy position) (allowance : Fraction.Rational) :=
  Data.Vector.DependentVector (fun column : Fin ((PieceIndices.columns (partitions.get position)) + 1) =>
    Data.Vector.DependentVector (fun row : Fin (PieceIndices.rows (partitions.get position)) =>
    DomainMatchedEnergy.MatchedEnergyRequest (fixed.get position).get
      (((base.entries.get position).get (PieceIndices.pieceIndex (partitions.get position) column
        row.succ)).tolerance.slope)
      ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column
        row.succ)).boundaryColumns
      ((traces.horizontal.get column).get row).vertices.rest.length
      (seamTarget allowance ((PieceIndices.columns
        (partitions.get position)) + 1) (PieceIndices.rows (partitions.get position)))))

/-- The dependent original vertical seam energy request bank on the exact retained internal-column and row indices. -/
@[expose] def VerticalRequests (base : ExteriorRequest energy pieceError minimum)
    (traces : MatchedSides.SeamTraces energy position) (allowance : Fraction.Rational) :=
  Data.Vector.DependentVector (fun column : Fin (PieceIndices.columns (partitions.get position)) =>
    Data.Vector.DependentVector (fun row : Fin ((PieceIndices.rows (partitions.get position)) + 1) =>
    DomainMatchedEnergy.MatchedEnergyRequest (fixed.get position).get
      (((base.entries.get position).get (PieceIndices.pieceIndex (partitions.get position) column.castSucc
        row)).tolerance.slope)
      ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column.castSucc
        row)).boundaryRows
      ((traces.vertical.get column).get row).vertices.rest.length
      (seamTarget allowance (PieceIndices.columns
        (partitions.get position)) ((PieceIndices.rows (partitions.get position)) + 1))))

end FaceDefectRequest

namespace FaceDefectRequest.HorizontalRequests

/-- Every actual original horizontal seam model is available at the supplied common stage. -/
@[expose] def IndexBound {base : ExteriorRequest energy pieceError minimum}
    {traces : MatchedSides.SeamTraces energy position} {allowance : Fraction.Rational}
    (entries : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest.HorizontalRequests base traces allowance)
      (index : Nat) : Prop :=
  ∀ column row, ((entries.get column).get row).models.index ≤ index

end FaceDefectRequest.HorizontalRequests

namespace FaceDefectRequest.VerticalRequests

/-- Every actual original vertical seam model is available at the supplied common stage. -/
@[expose] def IndexBound {base : ExteriorRequest energy pieceError minimum}
    {traces : MatchedSides.SeamTraces energy position} {allowance : Fraction.Rational}
    (entries : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest.VerticalRequests base traces allowance)
      (index : Nat) : Prop :=
  ∀ column row, ((entries.get column).get row).models.index ≤ index

end FaceDefectRequest.VerticalRequests

set_option genInjectivity false in
/-- One original numerical request paying every internal seam and corner of a complete regular face.

The retained stage covers the original exterior request and both actual seam banks independently of the eventual
coefficient vector. -/
structure FaceDefectRequest (base : ExteriorRequest energy pieceError minimum)
    (traces : MatchedSides.SeamTraces energy position) (allowance : Fraction.Rational) where
  /-- The original complete face defect allowance is strictly positive. -/ positive : 0 < allowance
  /-- The actual original horizontal seam request bank with the retained row and column budgets. -/ horizontal :
    Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest.HorizontalRequests base traces allowance
  /-- The actual original vertical seam request bank with the retained row and column budgets. -/ vertical :
    Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest.VerticalRequests base traces allowance
  /-- The original complete face corner request at one quarter of the retained allowance. -/ corners :
    CornerBounds.FaceCornerRequest partitions fixed position (allowance / 4)
  /-- The cached common stage paying the original exterior, seam and corner requests. -/ index : Nat
  /-- The common stage pays the retained original exterior request. -/ base_le : base.index ≤ index
  /-- The common stage pays every actual retained horizontal seam model. -/ horizontal_le : horizontal.IndexBound index
  /-- The common stage pays every actual retained vertical seam model. -/ vertical_le : vertical.IndexBound index
  /-- The common stage pays the original retained corner model. -/ corners_le : corners.models.index ≤ index

constructive_injectivity FaceDefectRequest

namespace FaceDefectRequest

/-- Prepare the original complete face seam and corner requests and cache a common paid stage.

Each request keeps its actual piece tolerance, retained mesh indices and original slope bound. -/
@[expose] def build (base : ExteriorRequest energy pieceError minimum)
    (traces : MatchedSides.SeamTraces energy position) (allowance : Fraction.Rational) (positive : 0 < allowance) :
    FaceDefectRequest base traces allowance := by
  let horizontal : HorizontalRequests base traces allowance
    :=
    DependentVector.ofFn fun column => DependentVector.ofFn fun row =>
      let tolerance := ((base.entries.get position).get (PieceIndices.pieceIndex (partitions.get position) column
        row.succ)).tolerance
      MatchedEnergyRequest.build (fixed.get position).get tolerance.slope
        ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column
          row.succ)).boundaryColumns
        ((traces.horizontal.get column).get row).vertices.rest.length
        (seamTarget allowance ((PieceIndices.columns
          (partitions.get position)) + 1) (PieceIndices.rows (partitions.get position))) tolerance.nonnegative
          (seamTarget_positive positive _ _)
  let horizontalIndex := horizontal.maximum fun _ entries => entries.maximum fun _ request => request.models.index
  let vertical : VerticalRequests base traces allowance :=
    DependentVector.ofFn fun column => DependentVector.ofFn fun row =>
      let tolerance := ((base.entries.get position).get (PieceIndices.pieceIndex (partitions.get position)
        column.castSucc row)).tolerance
      MatchedEnergyRequest.build (fixed.get position).get tolerance.slope
        ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column.castSucc
          row)).boundaryRows
        ((traces.vertical.get column).get row).vertices.rest.length
        (seamTarget allowance (PieceIndices.columns
          (partitions.get position)) ((PieceIndices.rows (partitions.get position)) + 1)) tolerance.nonnegative
          (seamTarget_positive positive _ _)
  let verticalIndex := vertical.maximum fun _ entries => entries.maximum fun _ request => request.models.index
  let corners := FaceCornerRequest.build partitions fixed position (allowance / 4)
    (Fraction.Order.Field.div_pos_direct positive (by decide))
  let index := max (max base.index corners.models.index) (max horizontalIndex verticalIndex)
  refine ⟨positive, horizontal, vertical, corners, index,
    (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _), ?_, ?_,
    (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_left _ _)⟩
  · dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest.HorizontalRequests.IndexBound]
    intro column row
    exact (((horizontal.get column).get_le_maximum (fun _ request => request.models.index) row).trans
      (horizontal.get_le_maximum (fun _ entries => entries.maximum fun _ request => request.models.index) column)).trans
        ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _))
  · dsimp only [Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest.VerticalRequests.IndexBound]
    intro column row
    exact (((vertical.get column).get_le_maximum (fun _ request => request.models.index) row).trans
      (vertical.get_le_maximum (fun _ entries => entries.maximum fun _ request => request.models.index) column)).trans
        ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _))

end FaceDefectRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
