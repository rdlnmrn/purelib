module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.VertexStar
public import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Exact lookup into the retained regular/hole partition

Compare only the rational anchor of an actual grid cell. Adjacent-axis
uniqueness proves that this identifies its full original cell, without
comparing proof-bearing clearance functions. Results retain both the payload
and its exact position in the already materialized regular or hole bank.
-/

namespace Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces
  (RegularFace BranchHole FaceSplit PuncturedFaces)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

set_option genInjectivity false in
open Purelib.Curves in
open Purelib.Polynomial in
/-- A regular-face payload with its exact position in the retained regular list.

The indexed readback identifies that payload and its cell with the original queried grid cell. -/
structure RegularLocation (regulars : List (RegularFace bank)) (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve)) where
  /-- The finite position in the retained regular-face list. -/ index : Fin regulars.length
  /-- The retained regular-face payload. -/ face : RegularFace bank
  /-- The original list entry at this position is the retained face. -/ indexed : regulars[index.val] = face
  /-- The retained face has the exact queried grid cell. -/ cell_eq : face.cell = cell

constructive_injectivity RegularLocation

set_option genInjectivity false in
open Purelib.Curves in
open Purelib.Polynomial in
/-- A branch-hole payload with its exact position in the retained hole list.

The indexed readback retains the original hole and proves its actual cell equals the queried cell. -/
structure HoleLocation (holes : List (BranchHole bank)) (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve)) where
  /-- The finite position in the retained hole list. -/ index : Fin holes.length
  /-- The retained branch-hole payload and its root-state evidence. -/ hole : BranchHole bank
  /-- The original hole-list entry at this position is the retained payload. -/ indexed : holes[index.val] = hole
  /-- The retained hole has the exact queried grid cell. -/ cell_eq : hole.cell = cell

constructive_injectivity HoleLocation

set_option genInjectivity false in
open Purelib.Curves in
open Purelib.Polynomial in
/-- A complete regular-face or branch-hole lookup result for the actual queried cell.

Both cases retain the original cached payload, its finite position and exact cell identity. -/
inductive LocatedCell (regulars : List (RegularFace bank)) (holes : List (BranchHole bank))
    (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) where
  /-- Return the exact position and payload of the matching regular face. -/ | regular (located : RegularLocation
    regulars cell)
  /-- Return the exact position and payload of the matching branch hole. -/ | hole (located : HoleLocation holes cell)

constructive_injectivity LocatedCell

namespace FaceSplit

open Purelib.Data.List

open Purelib.Curves
open Purelib.Polynomial
/-- A cell with a different anchor from the list head belongs to the tail.

The head occurrence would identify the two anchors. Its excluded equality
leaves the retained occurrence in the original tail list. -/
theorem tail_member {cell head : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
  curve)} {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))}
    (member : cell ∈ head :: cells) (different : head.box.anchor ≠ cell.box.anchor) : cell ∈ cells := by
  rcases Membership.mem_cons.mp member with same | member
  · exact (different (congrArg (fun cell => cell.box.anchor) same.symm)).elim
  · exact member

/-- Locate an actual grid cell through the retained ordered classification spine.

Compare executable rational anchors, then use grid-cell uniqueness to preserve the complete original cell and cached
payload. Recursive tail results retain their finite positions. -/
@[expose] def locateCell (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
  curve)) (onGrid : cell ∈ bank.grid.cells) :
    {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))} → (split
      : FaceSplit bank cells) → cell ∈ cells →
      LocatedCell split.regulars split.holes cell
  | _, .nil, member => (List.not_mem_nil member).elim
  | _, .regular face tail, member =>
      if same : face.cell.box.anchor = cell.box.anchor then
        .regular ⟨⟨0, Nat.zero_lt_succ _⟩, face, rfl, Polynomial.Geometry.Grid.ClearGrid.cell_eq_of_anchor face.member
          onGrid
          same⟩
      else
        match locateCell cell onGrid tail (tail_member member same) with
        | .regular found => .regular ⟨found.index.succ, found.face, found.indexed, found.cell_eq⟩
        | .hole found => .hole found
  | _, .hole branchHole tail, member =>
      if same : branchHole.cell.box.anchor = cell.box.anchor then
        .hole ⟨⟨0, Nat.zero_lt_succ _⟩, branchHole, rfl, Polynomial.Geometry.Grid.ClearGrid.cell_eq_of_anchor
          branchHole.member onGrid same⟩
      else
        match locateCell cell onGrid tail (tail_member member same) with
        | .regular found => .regular found
        | .hole found => .hole ⟨found.index.succ, found.hole, found.indexed, found.cell_eq⟩

end FaceSplit

open Purelib.Curves in
open Purelib.Polynomial in
/-- Locate the actual grid cell in the materialized regular-or-hole caches.

Transport the spine lookup through the retained cache equalities, preserving the original payload, list position and
cell identity. -/
@[expose] def PuncturedFaces.locateCell (faces : PuncturedFaces bank) (cell : Geometry.Grid.ClearGrid.Cell
  curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
    (member : cell ∈ bank.grid.cells) : LocatedCell faces.regulars faces.holes cell :=
  match faces.split.locateCell cell member member with
  | .regular found => .regular
      ⟨⟨found.index.val, by rw [faces.regulars_eq]; exact found.index.isLt⟩, found.face,
        by simpa only [faces.regulars_eq] using found.indexed, found.cell_eq⟩
  | .hole found => .hole
      ⟨⟨found.index.val, by rw [faces.holes_eq]; exact found.index.isLt⟩, found.hole,
        by simpa only [faces.holes_eq] using found.indexed, found.cell_eq⟩

end Purelib.Riemann.Meshes.PuncturedGridFaces
