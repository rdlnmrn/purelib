module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetRefinement
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest

@[expose] public section

/-! Read the unchanged coarse intervals from a refined two-sheet surface. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetSpatialRefinement

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List
    (RegularFace bank)}
  {domains : FaceDomainBank frames faces}

namespace TwoSheetRequest

variable {coarse : (sheet : Fin 2) → RegularMeshes
  domains sheet}
  {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}

/-- Side capacities depend on the retained coarse intervals, not on depth. -/
theorem mesh_x_intervals (request : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target)
    (sheet : Fin 2) (position : Fin faces.length) :
    ((request.entries.get sheet).meshes.entries.get position).partition.x.intervals =
      ((coarse sheet).entries.get position).partition.x.intervals := by
  rw [RegularMeshes.Request.mesh_eq, EnergyRequest.mesh_eq]
  rfl

/-- Refining the retained two-sheet depth preserves each actual original coarse horizontal interval list. -/
theorem atDepth_mesh_x_intervals (request : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target) (depth : Nat)
    (later : request.depth ≤ depth) (sheet : Fin 2) (position : Fin faces.length) :
    (((TwoSheetRequest.atDepth request depth later).entries.get sheet).meshes.entries.get
      position).partition.x.intervals =
      ((request.entries.get sheet).meshes.entries.get position).partition.x.intervals :=
  (mesh_x_intervals
    (TwoSheetRequest.atDepth request depth later) sheet position).trans
    (mesh_x_intervals request sheet
    position).symm

/-- Each actual two-sheet requested mesh retains its original coarse vertical interval list. -/
theorem mesh_y_intervals (request : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target)
    (sheet : Fin 2) (position : Fin faces.length) :
    ((request.entries.get sheet).meshes.entries.get position).partition.y.intervals =
      ((coarse sheet).entries.get position).partition.y.intervals := by
  rw [RegularMeshes.Request.mesh_eq, EnergyRequest.mesh_eq]
  rfl

/-- Refining the retained two-sheet depth preserves each actual original coarse vertical interval list. -/
theorem atDepth_mesh_y_intervals (request : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target) (depth : Nat)
    (later : request.depth ≤ depth) (sheet : Fin 2) (position : Fin faces.length) :
    (((TwoSheetRequest.atDepth request depth later).entries.get sheet).meshes.entries.get
      position).partition.y.intervals =
      ((request.entries.get sheet).meshes.entries.get position).partition.y.intervals :=
  (mesh_y_intervals
    (TwoSheetRequest.atDepth request depth later) sheet position).trans
    (mesh_y_intervals request sheet
    position).symm

end TwoSheetRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetSpatialRefinement
