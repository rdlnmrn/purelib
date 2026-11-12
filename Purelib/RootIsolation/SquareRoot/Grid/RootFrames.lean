module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-!
# A retained root frame at every common grid vertex

The canonical producer visits the finite Cartesian product of the two axes
once.  Edge queries look up stored owners by exact coordinates; they do not
run root isolation again.  Generated banks may provide different checked
owners and a different enumeration, subject to the same finite coverage law.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.RootContinuation
open Purelib.Data.Gaussian

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.List

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

namespace RootFrames

set_option genInjectivity false in
/-- One retained pair of actual root occurrences at its displayed point.

The displayed coordinate determines the exact polynomial value indexing the stored frame. Both root occurrences remain
owned by that retained base value. -/
public structure RootFrameEntry (polynomial : Geometry.ClearPath.GaussianPolynomial) where
  /-- The exact grid coordinate at which the root frame is retained. -/ point : Gaussian.Basic.Canonical
  /-- The retained pair of root occurrences over the polynomial value at this point. -/ frame :
    RootOwnerFrames.OwnerFrame (polynomial.eval point)

constructive_injectivity RootFrameEntry

end RootFrames

namespace RootFrames.RootFrameEntry

/-- Prepare a root frame at the intersection of two retained clear grid lines.

The original line clearance proves nonzeroness at that exact coordinate. -/
@[expose] public def ofLines (vertical : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (horizontal :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) :
    RootFrameEntry polynomial :=
  let segment : Geometry.ClearPath.ClearSegment polynomial ambient (Components.Basic.point vertical.coordinate
    horizontal.coordinate)
      (Components.Basic.point vertical.coordinate horizontal.coordinate) :=
    .horizontal vertical.coordinate vertical.coordinate horizontal.coordinate
      vertical.inside.1 vertical.inside.2 vertical.inside.1 vertical.inside.2 horizontal.clearance
  ⟨Components.Basic.point vertical.coordinate horizontal.coordinate,
    RootOwnerFrames.OwnerFrame.build segment.start_eval_ne_zero⟩

/-- Transport the stored root frame along equality of its displayed base coordinate. -/
@[expose] public def frameAt (entry : RootFrameEntry polynomial) (base :
  Gaussian.Basic.Canonical) (equal : entry.point = base) :
    RootOwnerFrames.OwnerFrame (polynomial.eval base) := equal ▸ entry.frame

/-- Look up the actual stored frame at a displayed coordinate.

The first matching entry is returned after exact coordinate comparisons. The original finite bank, retained frames and
recursive tails are reused without root isolation or frame reconstruction. -/
@[expose] public def lookup (base : Gaussian.Basic.Canonical) : (entries : List
  (RootFrameEntry polynomial)) →
    base ∈ entries.map point →
      RootOwnerFrames.OwnerFrame (polynomial.eval base)
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member =>
      if equal : base = head.point then head.frameAt base equal.symm
      else
        RootFrameEntry.lookup base tail (by
          rcases Membership.mem_cons.mp member with same | remaining
          · exact (equal same).elim
          · exact remaining)

/-- Appending further entries preserves the SAME original first matching frame.

The supplied original occurrence is already present in the left bank.
The lookup follows its unchanged first-match branches and never prepares
or selects another root frame.
-/
public theorem lookup_append (base : Gaussian.Basic.Canonical) (entries added : List (RootFrameEntry polynomial))
    (original : base ∈ entries.map point) (combined : base ∈ (entries ++ added).map point) :
    lookup base (entries ++ added) combined = lookup base entries original := by
  revert original combined
  induction entries with
  | nil =>
      intro original _
      exact (List.not_mem_nil original).elim
  | cons head tail retained =>
      intro original combined
      by_cases same : base = head.point
      · simp only [List.cons_append, lookup, dif_pos same, -eq_self, -iff_self]
        rfl
      · have inTail : base ∈ tail.map point := by
          rcases Membership.mem_cons.mp original with equal | remaining
          · exact (same equal).elim
          · exact remaining
        have inCombined : base ∈ (tail ++ added).map point := by
          rcases Membership.mem_cons.mp combined with equal | remaining
          · exact (same equal).elim
          · exact remaining
        simp only [List.cons_append, lookup, dif_neg same, -eq_self, -iff_self]
        exact retained inTail inCombined

/-- The first appended occurrence wins when the complete earlier key prefix rejects this point.

The result is the whole retained frame, not a reconstructed pair of owners.
Only coordinate decisions occur; no selector or root isolation is run.
-/
public theorem lookup_appended_first (base : Gaussian.Basic.Canonical)
    (before after : List (RootFrameEntry polynomial))
    (frame : RootOwnerFrames.OwnerFrame (polynomial.eval base))
    (absent : base ∉ before.map point)
    (member : base ∈ (before ++ (⟨base, frame⟩ :: after)).map point) :
    lookup base (before ++ (⟨base, frame⟩ :: after)) member = frame := by
  revert absent member
  induction before with
  | nil =>
      intro _ member
      simp only [-eq_self, -iff_self, List.nil_append, lookup, dif_pos rfl, frameAt]
      rfl
  | cons head tail retained =>
      intro absent member
      have different : base ≠ head.point := by
        intro same
        exact absent (Membership.mem_cons.mpr (Or.inl same))
      have remaining : base ∉ tail.map point := by
        intro found
        exact absent (Membership.mem_cons.mpr (Or.inr found))
      have memberTail : base ∈ (tail ++ (⟨base, frame⟩ :: after)).map point := by
        rcases Membership.mem_cons.mp member with same | found
        · exact (different same).elim
        · exact found
      simp only [List.cons_append, lookup, dif_neg different]
      exact retained remaining memberTail

end RootFrames.RootFrameEntry

set_option genInjectivity false in
/-- A finite bank of retained root frames covering every original grid vertex.

The coverage witness indexes the actual stored entries, so queries reuse their owners. -/
public structure RootFrames (grid : Geometry.Grid.ClearGrid polynomial ambient) where
  /-- The retained finite list of actual root-frame entries. -/ entries : List
    (RootFrames.RootFrameEntry polynomial)
  /-- Every original grid vertex occurs among the stored entry coordinates. -/ covers : ∀ base,
    FromStates.ContainsVertex grid base →
    base ∈ entries.map RootFrames.RootFrameEntry.point

constructive_injectivity RootFrames

namespace RootFrames

section

variable {grid : Geometry.Grid.ClearGrid polynomial ambient}

/-- Materialize all endpoint frames once from the original grid lines.

The finite Cartesian traversal retains the original axis order and line-clearance certificates. Nonzeroness at each
displayed vertex follows from those exact lines, and the coverage proof indexes the stored frame bank. -/
@[expose] public def build (grid : Geometry.Grid.ClearGrid polynomial ambient) :
  RootFrames grid := by
  let entries := grid.vertical.flatMap fun vertical =>
    grid.horizontal.map fun horizontal => RootFrameEntry.ofLines vertical horizontal
  refine ⟨entries, ?_⟩
  intro base member
  rcases Map.mem_map.mp member.1 with ⟨vertical, verticalMember, verticalEq⟩
  rcases Map.mem_map.mp member.2 with ⟨horizontal, horizontalMember, horizontalEq⟩
  apply Map.mem_map.mpr
  refine ⟨RootFrameEntry.ofLines vertical horizontal, ?_, ?_⟩
  · exact Flatten.mem_flatMap.mpr ⟨vertical, verticalMember,
      Map.mem_map.mpr ⟨horizontal, horizontalMember, rfl⟩⟩
  · exact Gaussian.Basic.ext verticalEq horizontalEq

/-- Look up the stored frame at a certified original grid vertex. -/
@[expose] public def frameAt (frames : RootFrames grid) (base : Gaussian.Basic.Canonical)
    (member : FromStates.ContainsVertex grid base) :
    RootOwnerFrames.OwnerFrame (polynomial.eval base) :=
  RootFrameEntry.lookup base frames.entries (frames.covers base member)

/-- Append actual already prepared frame entries, keeping the complete original bank first.

This performs only finite list work. The new entries may be strict cut
frames already retained by Point preparation; no frame isolation, Point
or frame selection is executed here. Original first-match lookup wins.
-/
public def appendEntries (frames : RootFrames grid) (added : List (RootFrameEntry polynomial)) :
    RootFrames grid :=
  ⟨frames.entries ++ added, fun base member => Map.mem_map.mpr (by
    obtain ⟨entry, listed, same⟩ := Map.mem_map.mp (frames.covers base member)
    exact ⟨entry, Membership.mem_append.mpr (Or.inl listed), same⟩)⟩

/-- Appending prepared frames retains the whole original ordered entry prefix. -/
public theorem appendEntries_entries (frames : RootFrames grid) (added : List (RootFrameEntry polynomial)) :
    (frames.appendEntries added).entries = frames.entries ++ added := by rfl

/-- An old vertex still reads its whole SAME original frame after actual prepared entries are appended. -/
public theorem appendEntries_frameAt (frames : RootFrames grid) (added : List (RootFrameEntry polynomial))
    (base : Gaussian.Basic.Canonical) (member : FromStates.ContainsVertex grid base) :
    (frames.appendEntries added).frameAt base member = frames.frameAt base member :=
  RootFrameEntry.lookup_append base frames.entries added (frames.covers base member)
    ((frames.appendEntries added).covers base member)

/-- Materialize only grid frames whose displayed points are absent from the original key bank. -/
private def missingEntries {small : Box} (keys : List Gaussian.Basic.Canonical)
    (fine : Geometry.Grid.ClearGrid polynomial small) : List (RootFrameEntry polynomial) :=
  fine.vertical.flatMap fun vertical => fine.horizontal.flatMap fun horizontal =>
    let base := Components.Basic.point vertical.coordinate horizontal.coordinate
    if base ∈ keys then [] else [RootFrameEntry.ofLines vertical horizontal]

/-- Extend a retained frame bank to an actual new grid, retaining every old occurrence first.

The old key list is materialized before the finite traversal. Existing
points acquire no root frame. Every genuinely new Cartesian vertex gets
one original ofLines result, and the original entry prefix is unchanged.
The two grids may have different ambient boxes.
-/
public def extend {small : Box} (frames : RootFrames grid) (fine : Geometry.Grid.ClearGrid polynomial small) :
    RootFrames fine := by
  let keys := frames.entries.map RootFrameEntry.point
  let added := missingEntries keys fine
  refine ⟨frames.entries ++ added, ?_⟩
  intro base member
  by_cases present : base ∈ keys
  · exact Map.mem_map.mpr (by
      obtain ⟨entry, oldMember, equal⟩ := Map.mem_map.mp present
      exact ⟨entry, Membership.mem_append.mpr (Or.inl oldMember), equal⟩)
  · obtain ⟨vertical, verticalMember, xEq⟩ := Map.mem_map.mp member.1
    obtain ⟨horizontal, horizontalMember, yEq⟩ := Map.mem_map.mp member.2
    let entry := RootFrameEntry.ofLines vertical horizontal
    have pointEq : entry.point = base := Gaussian.Basic.ext xEq yEq
    have absent : Components.Basic.point vertical.coordinate horizontal.coordinate ∉ keys := by
      intro found
      exact present (Eq.mp (congrArg (fun point : Gaussian.Basic.Canonical => point ∈ keys) pointEq) found)
    apply Map.mem_map.mpr
    refine ⟨entry, Membership.mem_append.mpr (Or.inr ?_), pointEq⟩
    apply Flatten.mem_flatMap.mpr
    refine ⟨vertical, verticalMember, Flatten.mem_flatMap.mpr ⟨horizontal, horizontalMember, ?_⟩⟩
    change entry ∈ (if Components.Basic.point vertical.coordinate horizontal.coordinate ∈ keys
      then [] else [RootFrameEntry.ofLines vertical horizontal])
    rewrite [if_neg absent]
    exact Membership.mem_cons.mpr (Or.inl rfl)

/-- Taking the complete original entry count after extension returns those SAME retained frame entries.

The original ordered prefix includes every actual owner pair and selection
operation. The proof reads the existing append factory; it exposes neither
private missing-entry code nor a newly prepared replacement frame.
-/
public theorem extend_take_entries {small : Box} (frames : RootFrames grid)
    (fine : Geometry.Grid.ClearGrid polynomial small) :
    (frames.extend fine).entries.take frames.entries.length = frames.entries := by
  unfold extend
  exact Append.take_length_append _ _

/-- Every old point still reads the whole SAME original frame after adding the genuinely new grid entries. -/
public theorem extend_frameAt {small : Box} (frames : RootFrames grid)
    (fine : Geometry.Grid.ClearGrid polynomial small) (base : Gaussian.Basic.Canonical)
    (newMember : FromStates.ContainsVertex fine base)
    (oldMember : FromStates.ContainsVertex grid base) :
    (frames.extend fine).frameAt base newMember = frames.frameAt base oldMember :=
  RootFrameEntry.lookup_append base frames.entries
    (missingEntries (frames.entries.map RootFrameEntry.point) fine) (frames.covers base oldMember)
    ((frames.extend fine).covers base newMember)

/-- A retained prepared head frame is reused after extension when the earlier old bank rejects its point.

Appending and extending preserve this exact first occurrence, including
its whole selection operation. New Cartesian frames cannot shadow it.
-/
public theorem extend_frameAt_appended_first {small : Box} (frames : RootFrames grid)
    (fine : Geometry.Grid.ClearGrid polynomial small) (base : Gaussian.Basic.Canonical)
    (frame : RootOwnerFrames.OwnerFrame (polynomial.eval base))
    (after : List (RootFrameEntry polynomial))
    (member : FromStates.ContainsVertex fine base)
    (absent : base ∉ frames.entries.map RootFrameEntry.point) :
    ((frames.appendEntries (⟨base, frame⟩ :: after)).extend fine).frameAt base member = frame := by
  have present : base ∈ (frames.entries ++ (⟨base, frame⟩ :: after)).map RootFrameEntry.point :=
    Map.mem_map.mpr ⟨⟨base, frame⟩,
      Membership.mem_append.mpr (Or.inr (Membership.mem_cons.mpr (Or.inl rfl))), rfl⟩
  exact (RootFrameEntry.lookup_append base (frames.entries ++ (⟨base, frame⟩ :: after))
    (missingEntries ((frames.entries ++ (⟨base, frame⟩ :: after)).map RootFrameEntry.point) fine)
    present (((frames.appendEntries (⟨base, frame⟩ :: after)).extend fine).covers base member)).trans
      (RootFrameEntry.lookup_appended_first base frames.entries after frame absent present)

/-- An actual prepared middle frame wins precisely after rejection by its complete old and earlier-provider prefix.

The same old entries, preceding provider entries and later entries remain
in order. The conclusion identifies the whole retained frame, including
its original selection operation, without running that operation.
-/
public theorem extend_frameAt_appended_middle {small : Box} (frames : RootFrames grid)
    (fine : Geometry.Grid.ClearGrid polynomial small) (base : Gaussian.Basic.Canonical)
    (frame : RootOwnerFrames.OwnerFrame (polynomial.eval base))
    (before after : List (RootFrameEntry polynomial))
    (member : FromStates.ContainsVertex fine base)
    (absent : base ∉ (frames.entries ++ before).map RootFrameEntry.point) :
    ((frames.appendEntries (before ++ (⟨base, frame⟩ :: after))).extend fine).frameAt base member = frame := by
  have same : frames.appendEntries (before ++ (⟨base, frame⟩ :: after)) =
      (frames.appendEntries before).appendEntries (⟨base, frame⟩ :: after) := by
    have records {first last : List (RootFrameEntry polynomial)} (equal : first = last)
        (left : ∀ point, FromStates.ContainsVertex grid point → point ∈ first.map RootFrameEntry.point)
        (right : ∀ point, FromStates.ContainsVertex grid point → point ∈ last.map RootFrameEntry.point) :
        (RootFrames.mk first left : RootFrames grid) = RootFrames.mk last right := by
      cases equal
      rfl
    unfold appendEntries
    exact records (List.append_assoc frames.entries before (⟨base, frame⟩ :: after)).symm _ _
  exact (congrArg (fun value : RootFrames grid => (value.extend fine).frameAt base member) same).trans
    ((frames.appendEntries before).extend_frameAt_appended_first fine base frame after member absent)

/-- Restrict the SAME retained root-frame entries to a grid whose vertices are original occurrences.

The polynomial is unchanged, while the new grid may have a different
ambient box. Only its erased coverage proof changes; the complete original
entry list and each cached frame are reused.
-/
public def restrict {small : Box} (frames : RootFrames grid) (smallGrid : Geometry.Grid.ClearGrid polynomial small)
    (onGrid : ∀ point, FromStates.ContainsVertex smallGrid point →
      FromStates.ContainsVertex grid point) : RootFrames smallGrid :=
  ⟨frames.entries, fun point member => frames.covers point (onGrid point member)⟩

/-- Frame restriction retains the complete original entry list, including its original ordering and repeats. -/
public theorem restrict_entries {small : Box} (frames : RootFrames grid)
    (smallGrid : Geometry.Grid.ClearGrid polynomial small)
    (onGrid : ∀ point, FromStates.ContainsVertex smallGrid point →
      FromStates.ContainsVertex grid point) :
    (frames.restrict smallGrid onGrid).entries = frames.entries := by rfl

/-- Looking up a restricted vertex returns the whole SAME original cached frame. -/
public theorem restrict_frameAt {small : Box} (frames : RootFrames grid)
    (smallGrid : Geometry.Grid.ClearGrid polynomial small)
    (onGrid : ∀ point, FromStates.ContainsVertex smallGrid point →
      FromStates.ContainsVertex grid point)
    (point : Gaussian.Basic.Canonical) (member : FromStates.ContainsVertex smallGrid point) :
    (frames.restrict smallGrid onGrid).frameAt point member = frames.frameAt point (onGrid point member) := by rfl

/-- The local four-side grid and its SAME old root-frame entries are retained with complete original factory laws. -/
public abbrev CellRestriction (frames : RootFrames grid) (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient)
    (listed : cell ∈ grid.cells) :=
  Σ smallGrid : {value : Geometry.Grid.ClearGrid polynomial cell.box // value = cell.grid},
  Σ _selected : {value : {entry : Geometry.Grid.ClearGrid.Cell polynomial cell.box //
      entry ∈ smallGrid.val.cells ∧ entry.box = cell.box} // value = cell.cachedCell smallGrid.val smallGrid.property},
  {value : RootFrames smallGrid.val // value = frames.restrict smallGrid.val
    (fun _ member => cell.grid_vertex_of_eq listed smallGrid.property member)}

/-- Restrict the four line certificates and retain the SAME original frame entries at their corners. -/
public def restrictCell (frames : RootFrames grid) (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient)
    (listed : cell ∈ grid.cells) : frames.CellRestriction cell listed :=
  let smallGrid := cell.grid
  let selected := cell.cachedCell smallGrid rfl
  let restricted := frames.restrict smallGrid (fun _ member => cell.grid_vertex listed member)
  ⟨⟨smallGrid, rfl⟩, ⟨selected, rfl⟩, ⟨restricted, rfl⟩⟩

end

namespace CellRestriction

variable {baseGrid : Geometry.Grid.ClearGrid polynomial ambient}
variable {original : RootFrames baseGrid} {sourceCell : Geometry.Grid.ClearGrid.Cell polynomial ambient}
variable {listed : sourceCell ∈ baseGrid.cells} (restricted : original.CellRestriction sourceCell listed)

/-- Read the actual once-built cell grid with the SAME four restricted line payloads. -/
public def grid : Geometry.Grid.ClearGrid polynomial sourceCell.box := restricted.1.val

/-- Read the complete retained frame list on the actual cached local grid. -/
public def frames : RootFrames restricted.grid := restricted.2.2.val

/-- Read the sole actual local cell, retaining its exact cached-grid membership and original box identity. -/
public def cell : {value : Geometry.Grid.ClearGrid.Cell polynomial sourceCell.box //
    value ∈ restricted.grid.cells ∧ value.box = sourceCell.box} := restricted.2.1.val

/-- The retained local grid is its complete original cell-restriction factory. -/
public theorem grid_eq : restricted.grid = sourceCell.grid := restricted.1.property

/-- The retained local frame owner is its complete original list-restriction factory on that SAME cached grid. -/
public theorem frames_eq : restricted.frames = original.restrict restricted.grid
    (fun _ member => sourceCell.grid_vertex_of_eq listed restricted.grid_eq member) := restricted.2.2.property

/-- The actual local cell is the whole cached selection from the SAME retained grid. -/
public theorem cell_eq : restricted.cell = sourceCell.cachedCell restricted.grid restricted.grid_eq :=
  restricted.2.1.property

/-- The restricted result keeps every original cached frame entry without root preparation. -/
public theorem entries_eq : restricted.frames.entries = original.entries :=
  (congrArg (fun value : RootFrames restricted.grid => value.entries) restricted.frames_eq).trans
    (original.restrict_entries restricted.grid (fun _ member =>
      sourceCell.grid_vertex_of_eq listed restricted.grid_eq member))

/-- Each actual local corner lookup is the whole original frame at the derived original occurrence. -/
public theorem frameAt_eq (point : Gaussian.Basic.Canonical)
    (member : FromStates.ContainsVertex restricted.grid point) :
    restricted.frames.frameAt point member = original.frameAt point
      (sourceCell.grid_vertex_of_eq listed restricted.grid_eq member) :=
  (congrArg (fun value : RootFrames restricted.grid => value.frameAt point member) restricted.frames_eq).trans
    (original.restrict_frameAt restricted.grid (fun _ member =>
      sourceCell.grid_vertex_of_eq listed restricted.grid_eq member) point member)

end CellRestriction

end RootFrames

end Purelib.RootIsolation.SquareRoot.Grid
