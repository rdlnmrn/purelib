module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Map
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.VertexStar
public import Purelib.Riemann.Meshes.PuncturedFaceLookup
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Polynomial.Geometry.Grid.FramedVertexStar
import Purelib.Data.List.Attach
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Classified vertex stars of the framed punctured grid

Each of at most four incident cells is looked up in the existing partition.
The retained classification distinguishes regular faces from winding-one holes
and carries exact indices into those banks. Positive separation allows at
most one hole in a vertex star, and strict hole interiority rules out holes
at an outer-frame vertex. No classification or root preparation is repeated.
-/

namespace Purelib.Riemann.Integration.PuncturedVertexStars

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (LocatedCell RegularLocation HoleLocation)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- An incident grid cell with its retained regular-or-hole classification.

The cell contains the displayed point, and the classification preserves its exact position in the existing regular or
hole bank. -/
structure StarEntry (base : FramedPuncturedGrid curve branches higher) (point : Gaussian.Basic.Canonical) where
  /-- The retained grid cell incident to the point. -/ cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve)
  /-- The cell's retained classification in the regular and hole banks. -/ classified : LocatedCell base.faces.regulars
    base.faces.holes cell
  /-- The displayed point lies in this cell's box. -/ contains : cell.box.Contains point

constructive_injectivity StarEntry

namespace StarEntry

variable {point : Purelib.Data.Gaussian.Basic.Canonical}

/-- Two classified holes incident to the same point have the same cell.

Distinct retained hole indices have positively separated boxes, excluding a common point. -/
theorem hole_cells_equal (first second : StarEntry base point)
    (firstHole : HoleLocation base.faces.holes first.cell) (secondHole : HoleLocation base.faces.holes second.cell) :
    first.cell = second.cell := by
  by_cases same : firstHole.hole.index = secondHole.hole.index
  · exact firstHole.cell_eq.symm.trans
      (firstHole.hole.cell_eq.trans ((congrArg base.bank.toBranchCellBank.cell same).trans
        (secondHole.hole.cell_eq.symm.trans secondHole.cell_eq)))
  · have firstContains : firstHole.hole.cell.box.Contains point := by rw [firstHole.cell_eq]; exact first.contains
    have secondContains : secondHole.hole.cell.box.Contains point := by rw [secondHole.cell_eq]; exact second.contains
    exact ((base.holes_separated firstHole.hole secondHole.hole same).points_ne firstContains secondContains rfl).elim

open Purelib.Curves in
/-- A hole entry cannot contain a point on the ambient frame.

Every retained hole lies strictly inside the frame, contradicting any boundary-coordinate equality. -/
theorem no_hole_on_frame (entry : StarEntry base point) (hole : HoleLocation base.faces.holes entry.cell)
    (boundary : point.re = (Hyperelliptic.Branches.Cuts.Ambient curve).xLower ∨ point.re =
      (Hyperelliptic.Branches.Cuts.Ambient curve).xUpper ∨
      point.im = (Hyperelliptic.Branches.Cuts.Ambient curve).yLower ∨ point.im = (Hyperelliptic.Branches.Cuts.Ambient
        curve).yUpper) : False := by
  have inside : hole.hole.cell.box.Contains point := by rw [hole.cell_eq]; exact entry.contains
  have strict := base.hole_interior hole.hole
  rcases boundary with left | right | bottom | top
  · exact (lt_irrefl _) (strict.left.trans_le (inside.1.trans_eq left))
  · exact (lt_irrefl _) ((right.symm.trans_le inside.2.1).trans_lt strict.right)
  · exact (lt_irrefl _) (strict.bottom.trans_le (inside.2.2.1.trans_eq bottom))
  · exact (lt_irrefl _) ((top.symm.trans_le inside.2.2.2).trans_lt strict.top)

/-- The stored classification selects a regular face. -/
@[expose] def IsRegular (entry : StarEntry base point) : Prop :=
  match entry.classified with
  | .regular _ => True
  | .hole _ => False

/-- Count hole tags in the retained list of incident entries. -/
@[expose] def countHoles : List (StarEntry base point) → Nat
  | [] => 0
  | entry :: entries =>
      match entry.classified with
      | .regular _ => countHoles entries
      | .hole _ => countHoles entries + 1

/-- A list of regular entries has zero counted holes.

Every original list occurrence has a retained regular tag. Structural induction keeps the unchanged tail and reads the
head classification directly, so no hole contributes to the count. -/
theorem countHoles_zero : ∀ (entries : List (StarEntry base point)),
    (∀ entry ∈ entries, entry.IsRegular) → countHoles entries = 0
  | [], _ => rfl
  | head :: tail, regular => by
      have headRegular := regular head List.mem_cons_self
      have tailZero := countHoles_zero tail (fun entry member => regular entry (List.mem_cons_of_mem _ member))
      cases classified : head.classified with
      | regular located => rw [countHoles, classified, tailZero]
      | hole located => simp only [IsRegular, classified] at headRegular

open Purelib.Data in
/-- A list of distinct cells incident to one point has at most one hole.

Any two hole entries would have equal cells by separation, contradicting the retained no-duplicates condition. -/
theorem countHoles_le_one : ∀ (entries : List (StarEntry base point)),
    (entries.map StarEntry.cell).Nodup → countHoles entries ≤ 1
  | [], _ => Nat.zero_le _
  | head :: tail, unique => by
      have parts := List.pairwise_cons.mp unique
      cases classified : head.classified with
      | regular located =>
          simp only [countHoles, classified]
          exact countHoles_le_one tail parts.2
      | hole located =>
          have tailZero := countHoles_zero tail (by
            intro other member
            cases otherClassified : other.classified with
            | regular found => simp only [IsRegular, otherClassified]
            | hole found =>
                exact (parts.1 other.cell (List.Map.mem_map_of_mem member)
                  (head.hole_cells_equal other located found)).elim)
          simp only [countHoles, classified, tailZero]
          exact Nat.le_refl _

set_option genInjectivity false in
/-- A selected regular row of an incident-entry list.

Retain its list membership, exact regular-bank location and equality to the stored classification tag. -/
structure RegularIn (entries : List (StarEntry base point)) where
  /-- The selected incident entry. -/ entry : StarEntry base point
  /-- The selected entry belongs to the retained list. -/ member : entry ∈ entries
  /-- The selected cell's exact regular-bank location. -/ located : RegularLocation base.faces.regulars entry.cell
  /-- The location agrees with the entry's stored regular tag. -/ classified_eq : entry.classified = .regular located

constructive_injectivity RegularIn

/-- Scan retained tags to select a regular entry.

The strict inequality between hole count and list length proves the finite scan succeeds and preserves the selected
row's original membership and classification. -/
@[expose] def selectRegular : (entries : List (StarEntry base point)) →
    countHoles entries < entries.length → RegularIn entries
  | [], strict => (Nat.not_lt_zero _ strict).elim
  | head :: tail, strict =>
      match classified : head.classified with
      | .regular located => ⟨head, List.mem_cons_self, located, classified⟩
      | .hole _ =>
          let next := selectRegular tail (by
            simp only [countHoles, classified, List.length_cons] at strict
            exact Nat.lt_of_succ_lt_succ strict)
          ⟨next.entry, List.mem_cons_of_mem _ next.member, next.located, next.classified_eq⟩

end StarEntry

open Purelib.Data in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A classified finite vertex star with an exact cached hole count.

The retained entries project to the geometric star's ordered cells, tying every classification to the original framed
grid. -/
structure VertexStar (base : FramedPuncturedGrid curve branches higher) (point : Gaussian.Basic.Canonical) where
  /-- The retained geometric vertex star. -/ geometry : Polynomial.Geometry.Grid.ClearGrid.VertexStar base.bank.grid
    point
  /-- The ordered list of classified incident cells. -/ entries : List (StarEntry base point)
  /-- The classified entries project exactly to the geometric star's cells. -/ entries_eq : entries.map StarEntry.cell =
    geometry.cells
  /-- The cached number of incident hole tags. -/ holeCount : Nat
  /-- The cache equals the actual hole count of the retained entries. -/ holeCount_eq : holeCount = StarEntry.countHoles
    entries

constructive_injectivity VertexStar

namespace VertexStar

variable {point : Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Data in
open Purelib.Polynomial in
/-- Classify the geometric vertex star using the existing face partition.

At a certified grid vertex, retain each incident cell's location and containment proof, then compute its hole count
once. -/
@[expose] def build (base : FramedPuncturedGrid curve branches higher) (point : Gaussian.Basic.Canonical)
    (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point) : VertexStar base point :=
  let geometry := Polynomial.Geometry.Grid.ClearGrid.VertexStar.build base.bank.grid point onGrid
  let entries := geometry.cells.attach.map fun cell =>
    (⟨cell.val, base.faces.locateCell cell.val (geometry.member cell.property), geometry.contains cell.property⟩ :
      StarEntry base point)
  { geometry := geometry
    entries := entries
    entries_eq := by
      dsimp only [entries]
      rw [Purelib.Data.List.Map.map_map]
      exact Purelib.Data.List.attach_map_subtype_val _
    holeCount := StarEntry.countHoles entries
    holeCount_eq := rfl }

/-- The classified and geometric stars contain the same number of cells.

Applying list length to the retained projection equation preserves its exact classified entries. Structural map length
gives the same count for the original geometric-cell cache. -/
theorem length_eq_geometry (star : VertexStar base point) : star.entries.length = star.geometry.cells.length := by
  have lengths := congrArg List.length star.entries_eq
  rw [Purelib.Data.List.Map.length_map] at lengths
  exact lengths

/-- A classified vertex star has at most four incident entries. -/
theorem length_le_four (star : VertexStar base point) : star.entries.length ≤ 4 := by
  exact star.length_eq_geometry.trans_le star.geometry.length_le_four

/-- The classified star contains no repeated cells. -/
theorem unique_cells (star : VertexStar base point) : (star.entries.map StarEntry.cell).Nodup := by
  rw [star.entries_eq]
  exact star.geometry.nodup

/-- A retained vertex star has at most one incident hole. -/
theorem holeCount_le_one (star : VertexStar base point) : star.holeCount ≤ 1 := by
  rw [star.holeCount_eq]
  exact StarEntry.countHoles_le_one star.entries star.unique_cells

open Purelib.Curves in
/-- The cached hole count is zero at an ambient-frame point. -/
theorem holeCount_eq_zero_on_frame (star : VertexStar base point)
    (boundary : point.re = (Hyperelliptic.Branches.Cuts.Ambient curve).xLower ∨ point.re =
      (Hyperelliptic.Branches.Cuts.Ambient curve).xUpper ∨
      point.im = (Hyperelliptic.Branches.Cuts.Ambient curve).yLower ∨ point.im = (Hyperelliptic.Branches.Cuts.Ambient
        curve).yUpper) : star.holeCount = 0 := by
  rw [star.holeCount_eq]
  apply StarEntry.countHoles_zero
  intro entry _
  cases classified : entry.classified with
  | regular found => simp only [StarEntry.IsRegular, classified]
  | hole found => exact (entry.no_hole_on_frame found boundary).elim

open Purelib.Polynomial in
/-- The number of holes is strictly smaller than the number of incident entries.

Frame vertices have no holes; an interior star has four cells and at most one hole. -/
theorem holeCount_lt_length (star : VertexStar base point) : star.holeCount < star.entries.length := by
  have proper := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper curve.polynomial
  rw [star.length_eq_geometry]
  rcases Geometry.Grid.FramedVertexStar.framed_size_cases
    star.geometry base.bank.frame proper with ⟨one | two, boundary⟩ | four
  · rw [star.holeCount_eq_zero_on_frame boundary, one]
    decide
  · rw [star.holeCount_eq_zero_on_frame boundary, two]
    decide
  · have atMostOne := star.holeCount_le_one
    omega

/-- Select a regular incident face from the retained vertex star.

The cached hole count proves a regular entry exists even at frame corners or vertices touching a removed branch cell. -/
@[expose] def regularFace (star : VertexStar base point) : StarEntry.RegularIn star.entries :=
  StarEntry.selectRegular star.entries (star.holeCount_eq ▸ star.holeCount_lt_length)

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Every actual grid cell containing the vertex has a classified entry in the star. -/
theorem covers (star : VertexStar base point) {cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve)}
    (member : cell ∈ base.bank.grid.cells) (inside : cell.box.Contains point) : ∃ entry ∈ star.entries, entry.cell =
      cell := by
  have inGeometry := star.geometry.covers member inside
  rw [← star.entries_eq] at inGeometry
  exact List.Map.mem_map.mp inGeometry

end VertexStar

end Purelib.Riemann.Integration.PuncturedVertexStars
