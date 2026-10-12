module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Pairwise
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.VertexStar
public import Purelib.Riemann.Integration.PuncturedVertexStars
public import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.Riemann.Meshes.GridLiftedEdgeUniqueness
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Constructed regular-cell routes around every retained vertex

Use the two rectangles obtained by mixing the endpoint cells' axis intervals.
They lie in the same cached star. If the first intermediate is a branch hole,
the other is regular: two such holes would coincide by positive separation,
forcing an endpoint regular cell to be a branch hole. The result contains at
most two genuine side steps, with coincidence steps allowed. No graph-search
success or caller-supplied connectivity certificate is assumed.
-/

namespace Purelib.Riemann.Integration

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (LocatedCell RegularLocation)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Integration.PuncturedVertexStars (StarEntry VertexStar)
open Purelib.Polynomial.Geometry.Grid.VertexCellSteps (IncidentCell)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {point : Purelib.Data.Gaussian.Basic.Canonical}

namespace PuncturedVertexStars.StarEntry

/-- The classified star entry retains membership of its exact original grid cell.

The retained classification is either a regular face or a hole location. Its original cell equality supplies membership
in the same cached grid without selecting a replacement cell. -/
theorem onGrid (entry : StarEntry base point) : entry.cell ∈ base.bank.grid.cells := by
  cases classified : entry.classified with
  | regular located => rw [← located.cell_eq]; exact located.face.member
  | hole located => rw [← located.cell_eq]; exact located.hole.member

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- An actual star entry whose retained cell is the specified original cell.

The entry and its list membership are stored with an exact cell equality, preserving the original classification owner.
-/
structure LocatedIn (entries : List (StarEntry base point)) (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Cuts.Ambient curve)) where
  /-- The actual retained star entry for the specified cell. -/ entry : StarEntry base point
  /-- The entry belongs to the original star-entry list. -/ member : entry ∈ entries
  /-- The retained entry has exactly the specified original cell. -/ cell_eq : entry.cell = cell

constructive_injectivity LocatedIn

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial in
/-- Find the actual entry for an original grid cell using its anchor identity.

The finite search retains the selected entry and its original list membership; grid anchor uniqueness supplies the exact
cell readback. -/
@[expose] def locate (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) (onGrid : cell ∈
  base.bank.grid.cells) :
    (entries : List (StarEntry base point)) → (∃ entry ∈ entries, entry.cell = cell) → StarEntry.LocatedIn entries cell
  | [], covered => (by obtain ⟨_, member, _⟩ := covered; exact List.not_mem_nil member : False).elim
  | head :: tail, covered =>
      if same : head.cell.box.anchor = cell.box.anchor then
        ⟨head, List.mem_cons_self, Polynomial.Geometry.Grid.ClearGrid.cell_eq_of_anchor head.onGrid onGrid same⟩
      else
        let found := locate cell onGrid tail (by
          obtain ⟨entry, member, equal⟩ := covered
          rcases Data.List.Membership.mem_cons.mp member with atHead | inTail
          · subst entry
            exact (same (congrArg (fun cell => cell.box.anchor) equal)).elim
          · exact ⟨entry, inTail, equal⟩)
        ⟨found.entry, List.mem_cons_of_mem _ found.member, found.cell_eq⟩

end PuncturedVertexStars.StarEntry

namespace PuncturedVertexStars.VertexStar

open Purelib.Polynomial in
/-- Classify an original incident cell using its actual retained star entry.

Anchor lookup returns an entry from the original star list. Its exact cell equality transports that retained
classification to the supplied incident cell. -/
@[expose] def classify (star : VertexStar base point) (cell : Geometry.Grid.VertexCellSteps.IncidentCell base.bank.grid
  point) :
    LocatedCell base.faces.regulars base.faces.holes cell.cell :=
  let found := StarEntry.locate cell.cell cell.member star.entries (star.covers cell.member cell.corner.contains)
  found.cell_eq ▸ found.entry.classified

end PuncturedVertexStars.VertexStar

namespace PuncturedVertexConnections

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- An original incident cell with its exact regular-grid location.

The retained corner and regular-list index refer to the same original cell at the specified vertex. -/
structure RegularIncident (base : FramedPuncturedGrid curve branches higher) (point : Basic.Canonical) where
  /-- The original cell and corner incident at this vertex. -/ incident : Geometry.Grid.VertexCellSteps.IncidentCell
    base.bank.grid point
  /-- The retained regular-list location of that exact incident cell. -/ located : RegularLocation base.faces.regulars
    incident.cell

constructive_injectivity RegularIncident

end PuncturedVertexConnections

namespace PuncturedVertexStars.VertexStar

open Purelib.Polynomial in
/-- Read the original star's selected regular incident cell with its retained location.

The original star selection supplies its regular face and bounded location. The retained grid membership and corner
certificate keep that selected entry and its original cell unchanged. -/
@[expose] def regularIncident (star : VertexStar base point) : PuncturedVertexConnections.RegularIncident base point :=
  let selected := star.regularFace
  ⟨⟨selected.entry.cell, selected.entry.onGrid,
      Polynomial.Geometry.Grid.ClearGrid.corner_of_contains selected.entry.onGrid star.geometry.onGrid
        selected.entry.contains⟩,
    selected.located⟩

end PuncturedVertexStars.VertexStar

namespace PuncturedVertexConnections.RegularIncident

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Construct a regular incident from an original bounded regular-list position.

The retained position supplies the actual cell, while the point and containment evidence certify its original corner
incidence. -/
@[expose] def ofPosition (base : FramedPuncturedGrid curve branches higher)
    (position : Fin base.faces.regulars.length) (point : Basic.Canonical) (onGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point)
    (inside : base.faces.regulars[position.val].cell.box.Contains point) : RegularIncident base point :=
  let face := base.faces.regulars[position.val]
  ⟨⟨face.cell, face.member, Polynomial.Geometry.Grid.ClearGrid.corner_of_contains face.member onGrid inside⟩,
    ⟨position, face,
    rfl, rfl⟩⟩

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.List in
open Purelib.Polynomial in
/-- Equal original regular cells have equal retained regular-list indices. -/
private theorem regular_index_eq (first last : RegularIncident base point)
    (equal : first.incident.cell = last.incident.cell) : first.located.index = last.located.index := by
  have cellsEqual : base.faces.regulars[first.located.index.val].cell = base.faces.regulars[last.located.index.val].cell
    := by
    rw [first.located.indexed, last.located.indexed, first.located.cell_eq, last.located.cell_eq, equal]
  have noSeparation (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) (apart :
    cell.box.InteriorSeparated cell.box) : False := by
    rcases apart with left | right | below | above
    · exact not_lt_of_ge left cell.box_proper.1
    · exact not_lt_of_ge right cell.box_proper.1
    · exact not_lt_of_ge below cell.box_proper.2
    · exact not_lt_of_ge above cell.box_proper.2
  apply Fin.ext
  rcases Nat.lt_trichotomy first.located.index.val last.located.index.val with before | same | after
  · have apart := Pairwise.pairwise_getElem base.faces.regulars_pairwise _ _
      first.located.index.isLt last.located.index.isLt before
    rw [cellsEqual] at apart
    exact (noSeparation _ apart).elim
  · exact same
  · have apart := Pairwise.pairwise_getElem base.faces.regulars_pairwise _ _
      last.located.index.isLt first.located.index.isLt after
    rw [cellsEqual] at apart
    exact (noSeparation _ apart).elim

/-- Regular incidents with the same original cell are equal as retained records. -/
theorem eq_of_cell (first last : RegularIncident base point)
    (equal : first.incident.cell = last.incident.cell) : first = last := by
  have indices := regular_index_eq first last equal
  rcases first with ⟨⟨firstCell, firstMember, firstCorner⟩, ⟨firstIndex, firstFace, firstIndexed, firstEq⟩⟩
  rcases last with ⟨⟨lastCell, lastMember, lastCorner⟩, ⟨lastIndex, lastFace, lastIndexed, lastEq⟩⟩
  dsimp only at equal indices
  cases equal
  cases indices
  have facesEqual := firstIndexed.symm.trans lastIndexed
  cases facesEqual
  rfl

open Purelib.Polynomial in
set_option genInjectivity false in
/-- Two original incident steps connected through a retained regular middle cell.

Both ordered steps use the actual incident-cell owners at the same vertex. -/
structure Connection (first last : RegularIncident base point) where
  /-- The retained regular middle incident of the connection. -/ middle : RegularIncident base point
  /-- The original ordered incident step to the middle cell. -/ firstStep :
    Geometry.Grid.VertexCellSteps.IncidentCell.Step first.incident middle.incident
  /-- The original ordered incident step from the middle cell. -/ lastStep :
    Geometry.Grid.VertexCellSteps.IncidentCell.Step middle.incident last.incident

constructive_injectivity Connection

open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
/-- The two mixed cells of distinct regular incidents cannot both be retained holes.

Star uniqueness would identify those holes and force an original regular cell into the hole classification. -/
theorem mixed_holes_impossible (first last : RegularIncident base point)
    (firstHole : PuncturedGridFaces.HoleLocation base.faces.holes (first.incident.mix last.incident).cell)
    (lastHole : PuncturedGridFaces.HoleLocation base.faces.holes (last.incident.mix first.incident).cell) : False := by
  let firstMix := first.incident.mix last.incident
  let lastMix := last.incident.mix first.incident
  have equal := StarEntry.hole_cells_equal
    (⟨firstMix.cell, .hole firstHole, firstMix.corner.contains⟩ : StarEntry base point)
    (⟨lastMix.cell, .hole lastHole, lastMix.corner.contains⟩ : StarEntry base point) firstHole lastHole
  have horizontal := congrArg Geometry.Grid.ClearGrid.Cell.horizontal equal
  have mixedEq : firstMix.cell = last.incident.cell := congrArg₂ Geometry.Grid.ClearGrid.Cell.mk horizontal rfl
  exact last.located.face.unassigned firstHole.hole.index
    (last.located.cell_eq.trans (mixedEq.symm.trans (firstHole.cell_eq.symm.trans firstHole.hole.cell_eq)))

open Purelib.Polynomial in
/-- Connect two original regular incidents through a classified regular mixed cell.

The finite classification first tries the column-then-row route, then the row-then-column route; the retained hole
exclusion proves these original alternatives cover the construction. -/
@[expose] def connect (star : VertexStar base point) (first last : RegularIncident base point) : Connection first last
  :=
  let firstMix := first.incident.mix last.incident
  match star.classify firstMix with
  | .regular located =>
      ⟨⟨firstMix, located⟩, Geometry.Grid.VertexCellSteps.IncidentCell.alongColumn first.incident firstMix rfl,
        Geometry.Grid.VertexCellSteps.IncidentCell.alongRow firstMix last.incident rfl⟩
  | .hole firstHole =>
      let lastMix := last.incident.mix first.incident
      match star.classify lastMix with
      | .regular located =>
          ⟨⟨lastMix, located⟩, Geometry.Grid.VertexCellSteps.IncidentCell.alongRow first.incident lastMix rfl,
            Geometry.Grid.VertexCellSteps.IncidentCell.alongColumn lastMix last.incident rfl⟩
      | .hole lastHole => (mixed_holes_impossible first last firstHole lastHole).elim

end PuncturedVertexConnections.RegularIncident

end Purelib.Riemann.Integration
