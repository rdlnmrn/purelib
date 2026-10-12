module
import Purelib.Data.List.GetD
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Init.Data.Fin.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

public section

/-! Executable lookup in the retained regular/hole split, with indexed cell
identity certificates and no reconstruction of clearance data. -/
section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (FaceSplit PuncturedFaces RegularFace BranchHole)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations

/-- Decide equality of two original grid cells from their lower-left coordinates and retained grid memberships. -/
@[expose] def sameCell (first second : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))
    (firstMember : first ∈ bank.grid.cells) (secondMember : second ∈ bank.grid.cells) : Decidable (first = second) :=
  if horizontal : first.box.xLower = second.box.xLower then
    if vertical : first.box.yLower = second.box.yLower then
      .isTrue (Cell.eq_of_lower firstMember secondMember horizontal vertical)
    else .isFalse (fun equal => vertical (congrArg (fun cell => cell.box.yLower) equal))
  else .isFalse (fun equal => horizontal (congrArg (fun cell => cell.box.xLower) equal))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations

section

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.FaceSplit

set_option genInjectivity false in
/-- The retained regular-face or branch-hole position of an original cell, with exact indexed readback. -/
inductive Location {cells : List (ClearGrid.Cell
  curve.polynomial (Cuts.Ambient curve))}
    (split : PuncturedGridFaces.FaceSplit bank cells) (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))
      where
  /-- Retain the original regular-face position and equality of its indexed cell with the requested cell. -/ | regular
    (position : Fin split.regulars.length) (equal : (split.regulars[position.val]'position.isLt).cell = cell)
  /-- Retain the original branch-hole position and equality of its indexed cell with the requested cell. -/ | hole
    (position : Fin split.holes.length) (equal : (split.holes[position.val]'position.isLt).cell = cell)

constructive_injectivity Purelib.Riemann.Meshes.PuncturedGridFaces.FaceSplit.Location

open Purelib.Riemann.Meshes.PuncturedGridFaces.FaceSplit (Location)

/-- Locate the original cell in its retained regular/hole classification, preserving exact list positions and cell
readback. -/
@[expose] def locate (cell : ClearGrid.Cell curve.polynomial
  (Cuts.Ambient curve)) (cellMember : cell ∈ bank.grid.cells) :
    {cells : List (ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))} → (split : PuncturedGridFaces.FaceSplit bank
      cells) →
      cell ∈ cells → Location split cell
  | _, .nil, member => (List.not_mem_nil member).elim
  | _, FaceSplit.regular face tail, member =>
      match Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations.sameCell face.cell cell face.member
        cellMember
        with
      | .isTrue equal => Location.regular ⟨0, Nat.succ_pos _⟩ equal
      | .isFalse different =>
          match FaceSplit.locate cell cellMember tail
            (Data.List.Membership.tail_member member different) with
          | Location.regular position equal =>
            Location.regular position.succ equal
          | Location.hole position equal =>
            Location.hole position equal
  | _, FaceSplit.hole head tail, member =>
      match Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitLocations.sameCell head.cell cell head.member
        cellMember
        with
      | .isTrue equal => Location.hole ⟨0, Nat.succ_pos _⟩ equal
      | .isFalse different =>
          match FaceSplit.locate cell cellMember tail
            (Data.List.Membership.tail_member member different) with
          | Location.regular position equal =>
            Location.regular position equal
          | Location.hole position equal =>
            Location.hole position.succ equal

end Purelib.Riemann.Meshes.PuncturedGridFaces.FaceSplit

end

section

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

set_option genInjectivity false in
/-- The retained regular-face or branch-hole position of an original cell, with exact indexed readback. -/
inductive Location (faces :
  PuncturedGridFaces.PuncturedFaces bank) (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) where
  /-- Retain the original regular-face position and equality of its indexed cell with the requested cell. -/ | regular
    (position : Fin faces.regulars.length) (equal : (faces.regulars[position.val]'position.isLt).cell = cell)
  /-- Retain the original branch-hole position and equality of its indexed cell with the requested cell. -/ | hole
    (position : Fin faces.holes.length) (equal : (faces.holes[position.val]'position.isLt).cell = cell)

constructive_injectivity Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.Location

open Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces (Location)

/-- Locate the original cell in its retained regular/hole classification, preserving exact list positions and cell
readback. -/
@[expose] def locate (faces :
  PuncturedGridFaces.PuncturedFaces bank) (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))
    (member : cell ∈ bank.grid.cells) : Location faces cell :=
  match faces.split.locate cell member member with
  | .regular position equal => .regular (Fin.cast (congrArg List.length faces.regulars_eq.symm) position)
      ((congrArg RegularFace.cell (Data.List.at_cast faces.regulars_eq.symm position)).trans equal)
  | .hole position equal => .hole (Fin.cast (congrArg List.length faces.holes_eq.symm) position)
      ((congrArg BranchHole.cell (Data.List.at_cast faces.holes_eq.symm position)).trans equal)

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.Location

/-- A location of an original regular face must retain its exact original regular-list position. -/
theorem regular_position {faces :
  PuncturedGridFaces.PuncturedFaces bank} (position : Fin faces.regulars.length)
    (location : Location faces (faces.regulars[position.val]'position.isLt).cell) :
    match location with
    | .regular found _ => found = position
    | .hole _ _ => False := by
  cases location with
  | regular found equal => exact faces.position_eq_of_cell found position equal
  | hole found equal =>
      exact (faces.regulars[position.val]'position.isLt).unassigned (faces.holes[found.val]'found.isLt).index
        (equal.symm.trans (faces.holes[found.val]'found.isLt).cell_eq)

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces.Location

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

/-- Looking up an original regular face returns its exact retained regular-list position. -/
theorem locate_regular (faces :
  PuncturedGridFaces.PuncturedFaces bank) (position : Fin faces.regulars.length) :
    match faces.locate (faces.regulars[position.val]'position.isLt).cell
      (faces.regulars[position.val]'position.isLt).member with
    | .regular found _ => found = position
    | .hole _ _ => False :=
  Location.regular_position position _

end Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces

end
end
