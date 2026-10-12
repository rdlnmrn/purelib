module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

@[expose] public section

/-! Unpaired regular sides retain their actual hole or ambient boundary. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces (SideNeighbor)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {face :
    RegularFace bank} {side :
    GridSide}

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

set_option genInjectivity false in
/-- An original regular face side belonging to a retained hole or the actual ambient exterior. -/
inductive PhysicalSide
    (faces : PuncturedGridFaces.PuncturedFaces bank) (face : PuncturedGridFaces.RegularFace bank) (side :
      GridLiftedDualSteps.GridSide) where
  /-- Retain the exact original hole index and its physical side matching certificate. -/ | hole (position : Fin
    faces.holes.length)
      (matching : side.Matches face.cell.box faces.holes[position.val].cell.box)
  /-- Retain the original side's equality with the actual ambient boundary. -/ | exterior (equal : side.Exterior
    face.cell.box (Cuts.Ambient curve))

constructive_injectivity Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.PhysicalSide

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor

/-- Read the actual hole or ambient boundary from an original side neighbor with no regular destination. -/
def physical
    (neighbor : PuncturedFaces.SideNeighbor faces face side)
    (absent : ∀ position, ¬ neighbor.RegularAt position) :
    Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.PhysicalSide faces face side := by
  cases neighbor with
  | neighbor cell member matching location =>
      cases location with
      | regular found equal => exact (absent found rfl).elim
      | hole found equal =>
          exact .hole found (by rw [equal]; exact matching)
  | exterior equal => exact .exterior equal

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.SideNeighbor

end

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.UnmatchedPhysicalSides.TwoSheetRequest.CrossingBank

/-- An unmatched original top crossing retains its actual hole or ambient physical side. -/
def horizontal_physical (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (firstPosition : Fin faces.regulars.length) (sheet : Fin 2)
    (absent : ∀ nextPosition, ¬ ∃ joined,
      ((retained.horizontal.get firstPosition).get sheet).get nextPosition = .matched joined) :
    Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.PhysicalSide faces faces.regulars[firstPosition.val] .top :=
  (neighbors.entries.get firstPosition).top.physical (fun nextPosition regular =>
    absent nextPosition ((CrossingBank.horizontal_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mp regular))

/-- An unmatched original bottom crossing retains its actual hole or ambient physical side. -/
def horizontal_reverse_physical (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (nextPosition : Fin faces.regulars.length) (sheet : Fin 2)
    (absent : ∀ firstPosition, ¬ ∃ joined,
      ((retained.horizontal.get firstPosition).get sheet).get nextPosition = .matched joined) :
    Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.PhysicalSide faces faces.regulars[nextPosition.val] .bottom :=
  (neighbors.entries.get nextPosition).bottom.physical (fun firstPosition regular =>
    absent firstPosition ((CrossingBank.horizontal_reverse_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mp regular))

/-- An unmatched original right crossing retains its actual hole or ambient physical side. -/
def vertical_physical (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (firstPosition : Fin faces.regulars.length) (sheet : Fin 2)
    (absent : ∀ nextPosition, ¬ ∃ joined,
      ((retained.vertical.get firstPosition).get sheet).get nextPosition = .matched joined) :
    Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.PhysicalSide faces faces.regulars[firstPosition.val] .right :=
  (neighbors.entries.get firstPosition).right.physical (fun nextPosition regular =>
    absent nextPosition ((CrossingBank.vertical_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mp regular))

/-- An unmatched original left crossing retains its actual hole or ambient physical side. -/
def vertical_reverse_physical (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (nextPosition : Fin faces.regulars.length) (sheet : Fin 2)
    (absent : ∀ firstPosition, ¬ ∃ joined,
      ((retained.vertical.get firstPosition).get sheet).get nextPosition = .matched joined) :
    Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.PhysicalSide faces faces.regulars[nextPosition.val] .left :=
  (neighbors.entries.get nextPosition).left.physical (fun firstPosition regular =>
    absent firstPosition ((CrossingBank.vertical_reverse_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mp regular))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.UnmatchedPhysicalSides.TwoSheetRequest.CrossingBank

end
