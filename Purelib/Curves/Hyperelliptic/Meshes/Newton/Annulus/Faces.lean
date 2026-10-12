module
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Geometry.Grid.Incidence
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Components.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

section

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.CellBoundary

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.ClearGridCoverage

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank

public section

/-!
# The regular cells between a Newton band and its actual grid hole

Filter the cached face classification, without recomputing any clearance.
Every contained cell other than the selected hole is represented, and finite
cell sums split into this regular region plus exactly that one hole. Exact
edge cancellation identifies its boundary with a cached subdivided band walk
minus the actual hole boundary, retaining every intermediate grid cut.
The analytic period transport across these cells remains a separate step.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (EdgeValues sumValues sumValues_congr sumValues_zero)
open Purelib.Polynomial.Geometry.Grid.CellBoundary.Cell (boundaryWalk_value)
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (sumValues_filter)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Polynomial.Geometry.Grid.Incidence.Interval (coordinate_side)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (spanned_of_keys)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid (punctured)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Polynomial.Geometry.Grid.Incidence.Interval in
/-- An adjacent grid interval containing a strict interior point cannot cross either retained endpoint coordinate. -/
private theorem interval_contains_point {Alpha : Type} {key : Alpha → Fraction.Rational} (entries : List Alpha)
    (ordered : entries.Pairwise (fun left right => key left < key right)) {interval : ClearGrid.Interval key}
    (member : interval ∈ Interval.adjacent entries ordered) {lower upper point : Fraction.Rational}
    (lowerMember : lower ∈ entries.map key) (upperMember : upper ∈ entries.map key)
    (strict : lower < point ∧ point < upper) (inside : key interval.lower ≤ point ∧ point ≤ key interval.upper) :
    lower ≤ key interval.lower ∧ key interval.upper ≤ upper := by
  constructor
  · rcases coordinate_side entries ordered member lowerMember with before | after
    · exact before
    · exact (not_lt_of_ge (inside.2.trans after) strict.1).elim
  · rcases coordinate_side entries ordered member upperMember with before | after
    · exact (not_lt_of_ge (before.trans inside.1) strict.2).elim
    · exact after

/-- Even a point on an internal grid line is assigned to a cell contained in the band: an adjacent interval cannot cross
a retained band coordinate. -/
private theorem cell_refines_at_point (grid : BranchCellBank.NewtonGrid preparation target radius) (index : Data.Index
  branches)
    (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) (member : cell ∈ grid.punctured.bank.grid.cells)
      {point : Data.Gaussian.Basic.Canonical}
    (strict : (grid.bands.box index).StrictContains point) (inside : cell.box.Contains point) :
    cell.box.Refines (grid.bands.box index) := by
  rcases Flatten.mem_flatMap.mp member with ⟨horizontal, horizontalMember, member⟩
  rcases Map.mem_map.mp member with ⟨vertical, verticalMember, equal⟩
  subst cell
  have x := interval_contains_point _
    grid.punctured.bank.grid.vertical_ordered horizontalMember
    (grid.band_x_lines index).1 (grid.band_x_lines index).2 ⟨strict.1, strict.2.1⟩ ⟨inside.1, inside.2.1⟩
  have y := interval_contains_point _
    grid.punctured.bank.grid.horizontal_ordered verticalMember
    (grid.band_y_lines index).1 (grid.band_y_lines index).2 strict.2.2 inside.2.2
  exact ⟨x.1, x.2, y.1, y.2⟩

/-- A finite list with distinct retained keys has exactly the selected keyed contribution in its conditional sum. -/
private theorem sum_unique {Alpha : Type} {count : Nat} (key : Alpha → Fin count) (index : Fin count) (value :
  Data.Gaussian.Basic.Canonical) :
    ∀ (entries : List Alpha), entries.Pairwise (fun first second => key first ≠ key second) →
      (∃ entry ∈ entries, key entry = index) →
      CellBoundary.sumValues (fun entry => if key entry = index then value else 0) entries = value
  | [], _, found => by obtain ⟨_, member, _⟩ := found; cases member
  | head :: tail, unique, found => by
      by_cases same : key head = index
      · rw [CellBoundary.sumValues, if_pos same]
        have tailZero : CellBoundary.sumValues (fun entry => if key entry = index then value else 0) tail = 0 := by
          rw [CellBoundary.sumValues_congr _ (fun _ => 0) tail (by
            intro entry member
            have different : key entry ≠ index := fun equal =>
              (List.pairwise_cons.mp unique).1 entry member (same.trans equal.symm)
            rw [if_neg different]), CellBoundary.sumValues_zero]
        rw [tailZero, add_zero]
      · rw [CellBoundary.sumValues, if_neg same, zero_add]
        apply sum_unique key index value tail
          (List.pairwise_cons.mp unique).2
        obtain ⟨entry, member, equal⟩ := found
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact (same equal).elim
        · exact ⟨entry, member, equal⟩

set_option genInjectivity false in
/-- The retained regular grid faces between one original Newton band and its selected hole.

The exact filtered classification list and window retain the original grid and branch occurrence. -/
structure AnnularFaces (grid : BranchCellBank.NewtonGrid preparation target radius) (index : Data.Index branches) where
  /-- The cached original regular faces contained in the selected Newton band. -/ faces : List
    (PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank)
  /-- The cached face list is exactly the original regular classification filtered by containment in this band. -/
    faces_eq : faces = grid.faces.regulars.filter (fun face => decide (face.cell.box.Refines (grid.bands.box index)))
  /-- The retained grid window with the exact original Newton band boundary. -/ window :
    Polynomial.Geometry.Grid.WindowBoundary.Window
    grid.shrunk.prepared.grid (grid.bands.box index)

constructive_injectivity AnnularFaces

namespace AnnularFaces

variable {grid : NewtonGrid preparation target
  radius} {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

/-- Cache the band's regular faces and its window from the original grid classification and retained axis coordinates.
-/
@[expose] def build (grid : BranchCellBank.NewtonGrid preparation target radius) (index : Data.Index branches) :
  Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index :=
  ⟨grid.faces.regulars.filter (fun face => decide (face.cell.box.Refines (grid.bands.box index))), rfl,
    Window.build _ _ (grid.band_x_lines index).1 (grid.band_x_lines index).2
      (grid.band_y_lines index).1 (grid.band_y_lines index).2⟩

/-- Read the complete original grid-cell list retained by the band window. -/
@[expose] def cells (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) : List
  (ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) := annulus.window.cells

/-- The retained window cells are exactly the original grid cells contained in the selected band. -/
theorem cells_eq (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) :
    annulus.cells = grid.punctured.bank.grid.cells.filter (fun cell => decide (cell.box.Refines (grid.bands.box index)))
      :=
  annulus.window.cells_eq

/-- Opposite sides reuse the same retained axis spine. No band extraction, axis search or cell classification is
repeated when reading this walk. -/
@[expose] def boundary (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) :
    Walks.Walk grid.shrunk.prepared.grid
      (Components.Basic.point (grid.bands.box index).xLower (grid.bands.box index).yLower)
      (Components.Basic.point (grid.bands.box index).xLower (grid.bands.box index).yLower) := annulus.window.boundary

/-- The retained subdivided outer band boundary has raw winding four. -/
theorem boundary_winding (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) :
    ClearPath.rawWinding annulus.boundary.path = 4 := by
  rw [boundary, annulus.window.boundary_winding, ←
    grid.bands.state_box index]
  exact (grid.bands.neighborhoods.states index).rawWindingFour

/-- Every retained annular face lies within its original selected Newton band. -/
theorem face_inside (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) {face :
  PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank}
    (member : face ∈ annulus.faces) : face.cell.box.Refines (grid.bands.box index) := by
  rw [annulus.faces_eq] at member
  exact of_decide_eq_true (Data.List.Filter.mem_filter.mp member).2

/-- Coverage is proved from the retained classification spine and the exclusion of every other branch hole, not assumed
by the annulus cache. -/
theorem covers (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) {cell :
  ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)}
    (member : cell ∈ grid.punctured.bank.grid.cells) (inside : cell.box.Refines (grid.bands.box index))
    (different : cell ≠ grid.punctured.bank.toBranchCellBank.cell index) :
    ∃ face ∈ annulus.faces, face.cell = cell := by
  rcases grid.faces.split.covers member with ⟨face, belongs, equal⟩ | ⟨hole, _, equal⟩
  · refine ⟨face, ?_, equal⟩
    rw [annulus.faces_eq, grid.faces.regulars_eq]
    exact Data.List.Filter.mem_filter.mpr ⟨belongs, decide_eq_true (by rw [equal]; exact inside)⟩
  · have label := grid.hole_index hole index (by rw [equal]; exact inside)
    exact (different (equal.symm.trans (hole.cell_eq.trans (congrArg (grid.punctured.bank.toBranchCellBank.cell)
      label)))).elim

/-- Every rational point in the open band but outside the closed hole is covered by a retained regular face, including
points on internal grid seams. -/
theorem point_covered (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) {point :
  Data.Gaussian.Basic.Canonical}
    (inside : (grid.bands.box index).StrictContains point)
    (outsideHole : ¬(grid.punctured.bank.toBranchCellBank.cell index).box.Contains point) :
    ∃ face ∈ annulus.faces, face.cell.box.Contains point := by
  have proper := (grid.bands.entries.get index).selection.sample.output.proper
  let found := Polynomial.Geometry.Grid.ClearGridCoverage.locate grid.punctured.bank.grid point
    (Polynomial.Geometry.Grid.FromStates.spanned_of_keys _ _ (grid.band_x_lines index).1 (grid.band_x_lines index).2
      proper.1 ⟨inside.1.le,
      inside.2.1.le⟩)
    (Polynomial.Geometry.Grid.FromStates.spanned_of_keys _ _ (grid.band_y_lines index).1 (grid.band_y_lines index).2
      proper.2 ⟨inside.2.2.1.le,
      inside.2.2.2.le⟩)
  have included := Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.cell_refines_at_point grid index found.cell
    found.member inside found.contains
  have different : found.cell ≠ grid.punctured.bank.toBranchCellBank.cell index := by
    intro equal
    exact outsideHole (equal ▸ found.contains)
  obtain ⟨face, member, equal⟩ := annulus.covers found.member included different
  exact ⟨face, member, by rw [equal]; exact found.contains⟩

set_option genInjectivity false in
/-- A retained original regular face containing the displayed point in the same annulus. -/
structure Located (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (point :
  Data.Gaussian.Basic.Canonical) where
  /-- The retained original regular face containing the displayed point. -/ face : PuncturedGridFaces.RegularFace
    grid.shrunk.prepared.toBranchCellBank
  /-- The retained face belongs to this exact annulus's cached list. -/ member : face ∈ annulus.faces
  /-- The retained face box contains the displayed point. -/ contains : face.cell.box.Contains point

constructive_injectivity Located

/-- Search the finite face list for the first containing box using its coverage witness.

The rational containment decision examines each retained face in list order. Coverage
certifies a successful result without changing that first-occurrence selection. -/
@[expose] def findFace (point : Data.Gaussian.Basic.Canonical) :
    ∀ (faces : List (PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank)),
      (∃ face ∈ faces, face.cell.box.Contains point) →
      { face : PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank // face ∈ faces ∧
        face.cell.box.Contains point }
  | [], found => False.elim (by obtain ⟨_, member, _⟩ := found; cases member)
  | face :: tail, found =>
      if inside : face.cell.box.Contains point then ⟨face, List.mem_cons_self, inside⟩
      else
        let rest := findFace point tail (by
          obtain ⟨other, member, contains⟩ := found
          rcases Data.List.Membership.mem_cons.mp member with rfl | member
          · exact (inside contains).elim
          · exact ⟨other, member, contains⟩)
        ⟨rest.val, List.mem_cons_of_mem _ rest.property.1, rest.property.2⟩

/-- An executable witness from the cached face list. The lookup checks only finite rational containment and never
reacquires analytic clearance. -/
@[expose] def locate (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (point :
  Data.Gaussian.Basic.Canonical)
    (inside : (grid.bands.box index).StrictContains point)
    (outsideHole : ¬(grid.punctured.bank.toBranchCellBank.cell index).box.Contains point) :
      Located annulus point :=
  let found := findFace point annulus.faces
    (annulus.point_covered inside outsideHole)
  ⟨found.val, found.property.1, found.property.2⟩

/-- The filtered hole contribution in one Newton band is exactly its original selected branch hole. -/
private theorem hole_sum (grid : BranchCellBank.NewtonGrid preparation target radius) (index : Data.Index branches)
    (value : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun hole => if hole.cell.box.Refines (grid.bands.box index) then value hole.cell else 0)
      grid.faces.holes =
      value (grid.punctured.bank.toBranchCellBank.cell index) := by
  rw [CellBoundary.sumValues_congr _ (fun hole => if hole.index = index then value
    (grid.punctured.bank.toBranchCellBank.cell index) else 0)
    grid.faces.holes (by
      intro hole _
      by_cases same : hole.index = index
      · have inside : hole.cell.box.Refines (grid.bands.box index) := by rw [← same]; exact grid.hole_refines_band hole
        rw [if_pos inside, if_pos same, hole.cell_eq, same]
        rfl
      · have outside : ¬hole.cell.box.Refines (grid.bands.box index) := fun inside => same (grid.hole_index hole index
          inside)
        rw [if_neg outside, if_neg same])]
  exact Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.sum_unique (fun hole => hole.index) index _ grid.faces.holes
    grid.faces.holes_pairwise (grid.faces.hole_complete index)

/-- Exact cellwise decomposition of the actual band region. In particular, the only removed contribution is the actual
selected grid hole. -/
theorem sum_balance (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (value :
  ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun face => value face.cell) annulus.faces + value
      (grid.punctured.bank.toBranchCellBank.cell index) =
      CellBoundary.sumValues value annulus.cells := by
  simp only [NewtonGrid.punctured]
  rw [annulus.faces_eq, annulus.cells_eq, WindowBoundary.sumValues_filter, WindowBoundary.sumValues_filter]
  have balance := grid.faces.split.sum_eq (fun cell => if cell.box.Refines (grid.bands.box index) then value cell else
    0)
  rw [← grid.faces.regulars_eq, ← grid.faces.holes_eq,
    hole_sum] at balance
  exact balance

/-- Exact annular incidence on the actual subdivided outer walk and actual inner cell. Arbitrary shared edge readings
are allowed; this is not yet a claim identifying independently prepared integration programs. -/
theorem boundary_balance (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (values :
  CellBoundary.EdgeValues) :
    CellBoundary.sumValues (fun face => values.walk face.boundary) annulus.faces +
      values.cellBoundary (grid.shrunk.prepared.toBranchCellBank.cell index) = values.walk annulus.boundary := by
  have regular := CellBoundary.sumValues_congr
    (fun face : PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank => values.walk face.boundary)
    (fun face => values.cellBoundary face.cell) annulus.faces
    (fun face _ => Cell.boundaryWalk_value face.cell face.member values)
  exact (congrArg (fun total => total + values.cellBoundary (grid.shrunk.prepared.toBranchCellBank.cell index))
    regular).trans
    ((annulus.sum_balance values.cellBoundary).trans (annulus.window.sum_cells_eq_boundary values))

/-- The sum over retained annular face boundaries is the retained outer boundary value minus the original selected hole
boundary value. -/
theorem boundary_eq_outer_sub_hole (annulus : Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index)
  (values : CellBoundary.EdgeValues) :
    CellBoundary.sumValues (fun face => values.walk face.boundary) annulus.faces = values.walk annulus.boundary -
      values.walk (Cell.boundaryWalk
        (grid.shrunk.prepared.toBranchCellBank.cell index)
        (grid.shrunk.prepared.toBranchCellBank.cell_mem index)) := by
  rw [Cell.boundaryWalk_value
      (grid.shrunk.prepared.toBranchCellBank.cell index)
      (grid.shrunk.prepared.toBranchCellBank.cell_mem index) values,
    ← annulus.boundary_balance values]
  ring1

end AnnularFaces

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces

end
