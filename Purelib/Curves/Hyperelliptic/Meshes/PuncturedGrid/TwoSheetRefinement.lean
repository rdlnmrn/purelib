module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh

public section

/-! Refine both complete regular sheets to a later exterior-request depth,
retaining the coarse partitions and their paid surface tolerances. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Data.Vector
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List
    (Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace bank)}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
    domains sheet}
  {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {target : Purelib.Data.Rat.Fraction.Rational}

/-- Refine both retained regular-sheet energy requests to the supplied later depth, preserving their original coarse
partitions and numerical stage floor. -/
@[expose] def atDepth (request : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target) (depth : Nat) (later :
  request.depth ≤ depth) :
    TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target := by
  have faceLater (sheet : Fin 2) (position : Fin faces.length) :
      ((request.entries.get sheet).entries.get position).depth ≤ depth :=
    (request.depth_eq sheet position).trans_le later
  let entries := DependentVector.ofFn fun sheet =>
    (request.entries.get sheet).atDepth depth (faceLater sheet)
  refine ⟨entries, depth, ?_, max request.index (entries.maximum fun _ entry => entry.index), ?_⟩
  · intro sheet position
    dsimp only [entries]
    rw [DependentVector.ofFn_get]
    exact (request.entries.get sheet).atDepth_entry_depth depth (faceLater sheet) position
  · intro sheet
    exact (entries.get_le_maximum (fun _ entry => entry.index) sheet).trans (Purelib.Data.Nat.Order.le_max_right _ _)

/-- The original numerical lower bound remains part of the refined request.

The refined request retains the original request index as one argument of its displayed maximum. The comparison does not
alter any selected sheet or entry. -/
theorem atDepth_index_ge (request : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target) (depth : Nat)
    (later : request.depth ≤ depth) : request.index ≤ (request.atDepth depth later).index :=
  Purelib.Data.Nat.Order.le_max_left _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest

end
