module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.SingleHole
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Membership
import Purelib.Data.List.Pairwise
import Purelib.Data.List.Nodup
import Purelib.Data.List.Map
import Purelib.Data.Vector.Dependent.Subtype
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CellPolygon
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Mesh.RetracingWords

/-! # Rooted old-hole windows with actual inner holes and signed face corrections

The original bank and its lifted edge prefix remain given. On the same
related fine mesh, the original circuit compiler supplies every regular
correction and its arriving sheet. Literal singleton extraction supplies
the actual inner-hole connector. Three genuine owner traces are retained;
no branch boundary is declared root-closed or assigned a zero period.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window (OrderedBranches prepareBranches)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank (ChainComparison)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    (retained : ClearanceRefinement original prepared)

/-- The actual new selected cell lies strictly inside its SAME original branch hole. -/
theorem inner_cell_inside (index : Data.Index branches) :
    (retained.fineBase.bank.toBranchCellBank.cell index).box.StrictInterior
      (base.bank.toBranchCellBank.cell index).box := by
  have bankEq : retained.fineBase.bank = retained.1.val.fine :=
    congrArg (fun value : FramedPuncturedGrid curve branches higher => value.bank) retained.2.1.property
  exact Eq.mpr (congrArg (fun bank : FramedBranchCellBank curve branches higher =>
    (bank.toBranchCellBank.cell index).box.StrictInterior (base.bank.toBranchCellBank.cell index).box) bankEq)
    (retained.1.val.cell_inside_original index)

/-- An old-hole window contains precisely its SAME branch's new selected hole.

Actual strict nesting supplies the matching occurrence. Distinct old holes
have a positive gap; a hypothetical different new hole inside this window
would place its displayed anchor in those two separated old boxes.
-/
theorem inner_cell_refines_iff (index other : Data.Index branches) :
    (retained.fineBase.bank.toBranchCellBank.cell other).box.Refines
      (base.bank.toBranchCellBank.cell index).box ↔ other = index := by
  constructor
  · intro inside
    by_cases same : other = index
    · exact same
    · have anchor := (retained.fineBase.bank.toBranchCellBank.cell other).box.contains_anchor
      exact ((base.bank.toBranchCellBank.cells_separated other index same).points_ne
        ((Box.Refinement.StrictInterior.refines (retained.inner_cell_inside other)).contains anchor)
        (inside.contains anchor) rfl).elim
  · intro same
    cases same
    exact Box.Refinement.StrictInterior.refines (retained.inner_cell_inside index)

/-- Build the old-hole window from the SAME retained fine grid and original endpoint line certificates.

All four memberships are transported by the actual old-grid inclusion.
The original Window builder caches its axes, lookups and selected cells;
no ambient enlargement or new clear line is requested.
-/
def holeWindow (index : Data.Index branches) :
    Window retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box :=
  let cell := base.bank.toBranchCellBank.cell index
  let intervals := CellBoundary.Cell.intervals_mem cell (base.bank.toBranchCellBank.cell_mem index)
  let x := ClearGrid.Interval.endpoints_mem _ base.bank.grid.vertical_ordered intervals.1
  let y := ClearGrid.Interval.endpoints_mem _ base.bank.grid.horizontal_ordered intervals.2
  Window.build retained.fineBase.bank.grid cell.box
    (retained.included.vertical _ (Map.mem_map_of_mem x.1))
    (retained.included.vertical _ (Map.mem_map_of_mem x.2))
    (retained.included.horizontal _ (Map.mem_map_of_mem y.1))
    (retained.included.horizontal _ (Map.mem_map_of_mem y.2))

/-- The retained original window classification has exactly the matching new branch label. -/
theorem labels_singleton (index : Data.Index branches)
    (window : Window retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box)
    (sheet : Fin 2)
    (ordered : OrderedBranches retained.fineBase.faces window retained.fine.edges retained.fine.vertices sheet) :
    ordered.labels = [index] := by
  have member : index ∈ ordered.labels :=
    (ordered.selected index).mpr (Box.Refinement.StrictInterior.refines (retained.inner_cell_inside index))
  have only : ∀ other, other ∈ ordered.labels → other = index := fun other member =>
    (retained.inner_cell_refines_iff index other).mp ((ordered.selected other).mp member)
  cases labelsEq : ordered.labels with
  | nil => exact (List.not_mem_nil (Eq.mp (congrArg (fun values => index ∈ values) labelsEq) member)).elim
  | cons head tail =>
      have headEq := only head (Eq.mpr (congrArg (fun values => head ∈ values) labelsEq) List.mem_cons_self)
      have tailEmpty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest =>
            have nextMember : next ∈ ordered.labels := Eq.mpr
              (congrArg (fun values => next ∈ values) labelsEq) (List.mem_cons_of_mem _ List.mem_cons_self)
            have nextEq := only next nextMember
            have unique := Eq.mp (congrArg List.Nodup labelsEq) ordered.unique
            exact ((List.pairwise_cons.mp unique).1 next List.mem_cons_self (headEq.trans nextEq.symm)).elim
      exact congrArg₂ List.cons headEq tailEmpty

/-- The fine old-anchor frame is its SAME whole original cached frame, including its actual owners. -/
theorem source_frame (index : Data.Index branches) : retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))) =
    original.frames.frameAt _ (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)) :=
  (congrArg (fun frames : RootFrames retained.fineBase.bank.grid => frames.frameAt _
    (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))))
    retained.fine_frames).trans
    (retained.frameAt _ (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))

/-- Both fine traces start at exactly the original retained source owner on their given sheet. -/
theorem source_owner (index : Data.Index branches) (sheet : Fin 2) :
    (retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners sheet =
    (original.frames.frameAt _
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners sheet :=
  congrArg (fun frame : OwnerFrame _ => frame.owners sheet) (retained.source_frame index)

/-- Exact existing-mesh locations for the original regular occurrences of a GIVEN compilation and its actual sheets. -/
@[expose] def CorrectionLocations {point : Canonical}
    {tree : CellCircuits retained.fineBase.bank.grid point}
    {partition : CircuitPartition retained.fineBase.faces tree} {sheet : Fin 2}
    (compiled : CircuitPartition.Compiled partition retained.fine.edges retained.fine.vertices sheet) : Type _ :=
  DependentVector (fun position : Fin compiled.regulars.length =>
    {value : retained.fine.mesh.LocatedFace
        (compiled.regulars[position.val]'position.isLt).location.index
        (compiled.regulars[position.val]'position.isLt).sheet //
      value = retained.fine.mesh.locateFace
        (compiled.regulars[position.val]'position.isLt).location.index
        (compiled.regulars[position.val]'position.isLt).sheet})

/-- Locate every GIVEN compiled correction on the SAME retained fine mesh without rebuilding a lift.

The actual original regular location and arriving sheet select the existing
quadrilateral and two bounded triangulation positions. Each occurrence runs
one original lookup; the compiler, its roots and its classification remain
unchanged. A window and a whole based/append word use this same operation.
-/
def correctionLocations {point : Canonical} {tree : CellCircuits retained.fineBase.bank.grid point}
    {partition : CircuitPartition retained.fineBase.faces tree} {sheet : Fin 2}
    (compiled : CircuitPartition.Compiled partition retained.fine.edges retained.fine.vertices sheet) :
    retained.CorrectionLocations compiled :=
  DependentVector.ofFnWithEq (fun position : Fin compiled.regulars.length =>
    retained.fine.mesh.locateFace (compiled.regulars[position.val]'position.isLt).location.index
      (compiled.regulars[position.val]'position.isLt).sheet)

namespace CorrectionLocations

variable {retained} {point : Canonical} {tree : CellCircuits retained.fineBase.bank.grid point}
    {partition : CircuitPartition retained.fineBase.faces tree} {sheet : Fin 2}
    {compiled : CircuitPartition.Compiled partition retained.fine.edges retained.fine.vertices sheet}
    (locations : retained.CorrectionLocations compiled)

/-- Read the actual cached quadrilateral and its bounded two-triangle incidence for one original signed correction. -/
@[expose] def correction (position : Fin compiled.regulars.length) : retained.fine.mesh.LocatedFace
    (compiled.regulars[position.val]'position.isLt).location.index
    (compiled.regulars[position.val]'position.isLt).sheet :=
  (locations.get position).val

/-- The actual correction is exactly its one retained original-mesh lookup on the true arriving sheet. -/
theorem correction_eq (position : Fin compiled.regulars.length) :
    locations.correction (retained := retained) (compiled := compiled) position = retained.fine.mesh.locateFace
      (compiled.regulars[position.val]'position.isLt).location.index
      (compiled.regulars[position.val]'position.isLt).sheet :=
  (locations.get position).property

/-- The actual mesh quadrilateral has exactly the original signed correction boundary word.

The original face-list and cell readbacks identify the retained lookup.
Its two triangle positions remain those of the SAME mesh triangulation;
no fresh LiftedFace construction or zero-boundary assertion is used.
-/
theorem correction_boundary (position : Fin compiled.regulars.length) :
    (locations.correction (retained := retained) (compiled := compiled) position).lifted.quad.boundary =
      (compiled.regulars[position.val]'position.isLt).word := by
  let occurrence := compiled.regulars[position.val]'position.isLt
  have sameFace := congrArg (fun face : PuncturedGridFaces.RegularFace retained.fineBase.bank.toBranchCellBank =>
    retained.fine.edges.indexedEdges retained.fine.vertices face.boundary occurrence.sheet)
    occurrence.location.indexed
  have sameCell : ∀ (left right : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))
      (leftMember : left ∈ retained.fineBase.bank.grid.cells)
      (rightMember : right ∈ retained.fineBase.bank.grid.cells), left = right →
      retained.fine.edges.indexedEdges retained.fine.vertices
        (CellBoundary.Cell.boundaryWalk left leftMember) occurrence.sheet =
      retained.fine.edges.indexedEdges retained.fine.vertices
        (CellBoundary.Cell.boundaryWalk right rightMember) occurrence.sheet := by
    intro left right leftMember rightMember same
    cases same
    rfl
  exact (locations.correction (retained := retained) (compiled := compiled) position).lifted.boundary_eq.trans
    (sameFace.trans ((sameCell occurrence.location.face.cell occurrence.cell occurrence.location.face.member
      occurrence.member occurrence.location.cell_eq).trans occurrence.word_eq.symm))

end CorrectionLocations

/-- Actual window, classification, singleton connector, three walks and three owner traces with complete factories.

The trace caches are new genuine work on the given edge banks. Each starts
at its actual retained frame and ends at its actual transported sheet;
none is forced to close. The original bank and all fine caches stay distinct.
-/
@[expose] def Annulus (index : Data.Index branches) (sheet : Fin 2) : Type _ :=
  (window : {value : Window retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box //
    value = retained.holeWindow index}) ×
  (ordered : {value : OrderedBranches retained.fineBase.faces window.val
      retained.fine.edges retained.fine.vertices sheet //
    value = prepareBranches retained.fineBase.faces window.val retained.fine.edges retained.fine.vertices sheet}) ×
  (selected : {value : ordered.val.partition.SingleHole index //
    value = ordered.val.partition.singleHole index (ordered.val.labels_eq.symm.trans
      (retained.labels_singleton index window.val sheet ordered.val))}) ×
  (oldWalk : {value : Walk base.bank.grid (base.bank.toBranchCellBank.cell index).box.anchor
      (base.bank.toBranchCellBank.cell index).box.anchor //
    value = CellBoundary.Cell.boundaryWalk (base.bank.toBranchCellBank.cell index)
      (base.bank.toBranchCellBank.cell_mem index)}) ×
  (outerWalk : {value : Walk retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box.anchor
      (base.bank.toBranchCellBank.cell index).box.anchor //
    value = retained.included.resplit oldWalk.val
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))}) ×
  (innerWalk : {value : Walk retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box.anchor
      (base.bank.toBranchCellBank.cell index).box.anchor //
    value = selected.val.val.based (CellBoundary.Cell.boundaryWalk
      (retained.fineBase.bank.toBranchCellBank.cell index) (retained.fineBase.bank.toBranchCellBank.cell_mem index))}) ×
  (_oldTrace : {value : OwnerPath curve.polynomial (base.bank.toBranchCellBank.cell index).box.anchor
      ((original.frames.frameAt _
        (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners sheet)
      (base.bank.toBranchCellBank.cell index).box.anchor
      ((original.frames.frameAt _ (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners
        (RootEdgeBank.target original.edges oldWalk.val sheet)) //
    value = RootEdgeBank.trace original.edges oldWalk.val
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)) sheet}) ×
  (_outerTrace : {value : OwnerPath curve.polynomial (base.bank.toBranchCellBank.cell index).box.anchor
      ((retained.fine.frames.frameAt _ (retained.included.vertex
        (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners sheet)
      (base.bank.toBranchCellBank.cell index).box.anchor
      ((retained.fine.frames.frameAt _ (retained.included.vertex
        (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
        (RootEdgeBank.target retained.fine.edges outerWalk.val sheet)) //
    value = RootEdgeBank.trace retained.fine.edges outerWalk.val
      (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))
      (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))) sheet}) ×
  (_innerTrace : {value : OwnerPath curve.polynomial (base.bank.toBranchCellBank.cell index).box.anchor
      ((retained.fine.frames.frameAt _ (retained.included.vertex
        (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners sheet)
      (base.bank.toBranchCellBank.cell index).box.anchor
      ((retained.fine.frames.frameAt _ (retained.included.vertex
        (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
        (RootEdgeBank.target retained.fine.edges innerWalk.val sheet)) //
    value = RootEdgeBank.trace retained.fine.edges innerWalk.val
      (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))
      (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))) sheet}) ×
  {value : retained.CorrectionLocations ordered.val.compiled //
    value = retained.correctionLocations ordered.val.compiled}

/-- Construct one rooted annular relation with actual old, resplit and connector-based inner traces.

The original circuit compiler classifies the cached window once, retaining
every regular face correction. Singleton extraction only reads that cache.
The three trace operations each consume their given edge bank once; their
joins and any later numerical comparison payments are genuine separate work.
-/
def annulus (index : Data.Index branches) (sheet : Fin 2) : retained.Annulus index sheet :=
  let window := retained.holeWindow index
  let ordered := prepareBranches retained.fineBase.faces window retained.fine.edges retained.fine.vertices sheet
  let selected := ordered.partition.singleHole index
    (ordered.labels_eq.symm.trans (retained.labels_singleton index window sheet ordered))
  let oldWalk := CellBoundary.Cell.boundaryWalk (base.bank.toBranchCellBank.cell index)
    (base.bank.toBranchCellBank.cell_mem index)
  let member := ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)
  let onFine := retained.included.vertex member
  let outerWalk := retained.included.resplit oldWalk member
  let innerWalk := selected.val.based (CellBoundary.Cell.boundaryWalk
    (retained.fineBase.bank.toBranchCellBank.cell index) (retained.fineBase.bank.toBranchCellBank.cell_mem index))
  let oldTrace := RootEdgeBank.trace original.edges oldWalk member member sheet
  let outerTrace := RootEdgeBank.trace retained.fine.edges outerWalk onFine onFine sheet
  let innerTrace := RootEdgeBank.trace retained.fine.edges innerWalk onFine onFine sheet
  let corrections := retained.correctionLocations ordered.compiled
  ⟨⟨window, rfl⟩, ⟨ordered, rfl⟩, ⟨selected, rfl⟩, ⟨oldWalk, rfl⟩, ⟨outerWalk, rfl⟩,
    ⟨innerWalk, rfl⟩, ⟨oldTrace, rfl⟩, ⟨outerTrace, rfl⟩, ⟨innerTrace, rfl⟩, ⟨corrections, rfl⟩⟩

/-- Retain one complete rooted annular construction per original finite branch occurrence.

The original branch-index order is unchanged. Each requested occurrence
executes the annulus worker once inside this one finite materialization;
separate calls of this function are independent constructions, not memoized.
-/
def annuli (sheet : Fin 2) : DependentVector (fun index : Data.Index branches =>
    {value : retained.Annulus index sheet // value = retained.annulus index sheet}) :=
  DependentVector.ofFnWithEq (fun index => retained.annulus index sheet)

namespace Annulus

variable {retained} {index : Data.Index branches} {sheet : Fin 2} (annular : retained.Annulus index sheet)

/-- Read the actual once-built old-hole window. -/
@[expose] def window : Window retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box :=
  annular.1.val

/-- Read the original complete circuit order, classification and signed correction cache. -/
@[expose] def ordered : OrderedBranches retained.fineBase.faces annular.window
    retained.fine.edges retained.fine.vertices sheet := annular.2.1.val

/-- Read the original hole leaf's actual connector and its literal empty-node reduction proof. -/
@[expose] def selected : annular.ordered.partition.SingleHole index := annular.2.2.1.val

/-- Read the actual retained old four-side boundary. -/
@[expose] def oldWalk : Walk base.bank.grid (base.bank.toBranchCellBank.cell index).box.anchor
    (base.bank.toBranchCellBank.cell index).box.anchor := annular.2.2.2.1.val

/-- Read the once-resplit old boundary on the SAME fine grid. -/
@[expose] def outerWalk : Walk retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box.anchor
    (base.bank.toBranchCellBank.cell index).box.anchor := annular.2.2.2.2.1.val

/-- Read the actual connector-based inner boundary on the SAME fine grid. -/
@[expose] def innerWalk : Walk retained.fineBase.bank.grid (base.bank.toBranchCellBank.cell index).box.anchor
    (base.bank.toBranchCellBank.cell index).box.anchor := annular.2.2.2.2.2.1.val

/-- Read the whole actual old boundary trace, including its original root-edge connections and joins. -/
@[expose] def oldTrace : OwnerPath curve.polynomial (base.bank.toBranchCellBank.cell index).box.anchor
    ((original.frames.frameAt _ (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners sheet)
    (base.bank.toBranchCellBank.cell index).box.anchor
    ((original.frames.frameAt _ (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners
      (RootEdgeBank.target original.edges annular.oldWalk sheet)) := annular.2.2.2.2.2.2.1.val

/-- Read the whole actual fine resplit trace, preserving its independently retained connections and joins. -/
@[expose] def outerTrace : OwnerPath curve.polynomial (base.bank.toBranchCellBank.cell index).box.anchor
    ((retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners sheet)
    (base.bank.toBranchCellBank.cell index).box.anchor
    ((retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
      (RootEdgeBank.target retained.fine.edges annular.outerWalk sheet)) := annular.2.2.2.2.2.2.2.1.val

/-- Read the whole actual connector-based inner trace, preserving its outgoing and returning sheet roles. -/
@[expose] def innerTrace : OwnerPath curve.polynomial (base.bank.toBranchCellBank.cell index).box.anchor
    ((retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners sheet)
    (base.bank.toBranchCellBank.cell index).box.anchor
    ((retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
      (RootEdgeBank.target retained.fine.edges annular.innerWalk sheet)) := annular.2.2.2.2.2.2.2.2.1.val

/-- The whole old owner trace is exactly its original one-run trace factory. -/
theorem oldTrace_eq : annular.oldTrace = RootEdgeBank.trace original.edges annular.oldWalk
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)) sheet :=
  annular.2.2.2.2.2.2.1.property

/-- The whole outer owner trace is exactly its original one-run fine-bank trace factory. -/
theorem outerTrace_eq : annular.outerTrace = RootEdgeBank.trace retained.fine.edges annular.outerWalk
    (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))
    (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))) sheet :=
  annular.2.2.2.2.2.2.2.1.property

/-- The whole inner owner trace is exactly its original one-run connector trace factory. -/
theorem innerTrace_eq : annular.innerTrace = RootEdgeBank.trace retained.fine.edges annular.innerWalk
    (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))
    (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))) sheet :=
  annular.2.2.2.2.2.2.2.2.1.property

/-- Read the SAME finite correction-location cache on the actual fine mesh. -/
@[expose] def corrections : retained.CorrectionLocations annular.ordered.compiled :=
  annular.2.2.2.2.2.2.2.2.2.val

/-- Read the original mesh quadrilateral and two triangle positions of one signed correction occurrence. -/
@[expose] def correction (position : Fin annular.ordered.compiled.regulars.length) :
    retained.fine.mesh.LocatedFace
      (annular.ordered.compiled.regulars[position.val]'position.isLt).location.index
      (annular.ordered.compiled.regulars[position.val]'position.isLt).sheet :=
  annular.corrections.correction (retained := retained) (compiled := annular.ordered.compiled) position

/-- Each correction location is exactly the original lookup on the SAME mesh and actual arriving sheet. -/
theorem correction_eq (position : Fin annular.ordered.compiled.regulars.length) :
    annular.correction position = retained.fine.mesh.locateFace
      (annular.ordered.compiled.regulars[position.val]'position.isLt).location.index
      (annular.ordered.compiled.regulars[position.val]'position.isLt).sheet :=
  annular.corrections.correction_eq (retained := retained) (compiled := annular.ordered.compiled) position

/-- The actual mesh quadrilateral has exactly the original signed correction boundary word.

The original face-list and cell readbacks identify the retained lookup.
Its two triangle positions remain those of the SAME mesh triangulation;
no fresh LiftedFace construction or zero-boundary assertion is used.
-/
theorem correction_boundary (position : Fin annular.ordered.compiled.regulars.length) :
    (annular.correction position).lifted.quad.boundary =
      (annular.ordered.compiled.regulars[position.val]'position.isLt).word :=
  annular.corrections.correction_boundary (retained := retained) (compiled := annular.ordered.compiled) position

/-- The resplit old boundary and cached window retain their actual sheet maps and retracing-word comparison. -/
theorem outer_comparison : ChainComparison retained.fine.edges retained.fine.vertices
    annular.outerWalk annular.window.boundary := by
  have oldEq := congrArg (fun walk => retained.included.resplit walk
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))) annular.2.2.2.1.property
  have outerEq := annular.2.2.2.2.1.property.trans oldEq
  exact (RootEdgeBank.ChainComparison.of_eq outerEq).trans
    (retained.included.cell_boundary_comparison_anchored (base.bank.toBranchCellBank.cell index)
      (base.bank.toBranchCellBank.cell_mem index) annular.window retained.fine.edges retained.fine.vertices
      (LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
        (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).toLoop
      (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))))

/-- Literal nil-node removal identifies the kept product with this SAME actual inner connector route. -/
theorem kept_inner_eq : annular.ordered.kept.product = annular.innerWalk :=
  (congrArg RowCircuitOrder.CellCircuits.product annular.ordered.kept_eq).trans
    (annular.selected.property.trans annular.2.2.2.2.2.1.property.symm)

/-- The kept product and inner connector route retain their complete actual chain comparison. -/
theorem inner_comparison : ChainComparison retained.fine.edges retained.fine.vertices
    annular.ordered.kept.product annular.innerWalk :=
  RootEdgeBank.ChainComparison.of_eq annular.kept_inner_eq

/-- The actual outer and inner paths reach the SAME terminal sheet, without requiring either path to close. -/
theorem target_eq : RootEdgeBank.target retained.fine.edges annular.outerWalk sheet =
    RootEdgeBank.target retained.fine.edges annular.innerWalk sheet :=
  (annular.outer_comparison.targets sheet).trans
    (annular.ordered.target.trans (annular.ordered.kept_target.symm.trans
      (annular.inner_comparison.targets sheet)))

/-- The inner trace keeps its actual connector arrival, hole transition and reverse-connector return maps.

The inner branch boundary may change the connector's arriving sheet. The
return map therefore consumes that changed sheet, never an assumed closed
root occurrence or the original source-sheet label.
-/
theorem inner_target_factors : RootEdgeBank.target retained.fine.edges annular.innerWalk sheet =
    RootEdgeBank.target retained.fine.edges annular.selected.val.reverse
      (RootEdgeBank.target retained.fine.edges
        (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
          (retained.fineBase.bank.toBranchCellBank.cell_mem index))
        (RootEdgeBank.target retained.fine.edges annular.selected.val sheet)) :=
  (congrArg (fun walk => RootEdgeBank.target retained.fine.edges walk sheet)
    annular.2.2.2.2.2.1.property).trans
    ((RootEdgeBank.target_append retained.fine.edges annular.selected.val _ sheet).trans
      (RootEdgeBank.target_append retained.fine.edges _ annular.selected.val.reverse
        (RootEdgeBank.target retained.fine.edges annular.selected.val sheet)))

/-- The original boundary has its actual winding-one raw winding. -/
theorem old_winding : rawWinding annular.oldWalk.path = 4 :=
  (congrArg (fun walk => rawWinding walk.path)
    annular.2.2.2.1.property).trans
    ((CellBoundary.Cell.boundaryWalk_winding _ (base.bank.toBranchCellBank.cell_mem index)).trans
      (BranchCellWinding.selected_winding_four base.bank.toBranchCellBank index))

/-- The old actual trace changes the retained source sheet. -/
theorem old_target : RootEdgeBank.target original.edges annular.oldWalk sheet =
    BranchCutLifts.otherSheet sheet :=
  RootEdgeBank.target_odd original.edges annular.oldWalk
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)) 0 annular.old_winding sheet

/-- The actual resplit boundary has the SAME winding-one raw winding. -/
theorem outer_winding : rawWinding annular.outerWalk.path = 4 :=
  (congrArg (fun walk => rawWinding walk.path)
    annular.2.2.2.2.1.property).trans
    ((retained.included.resplit_winding annular.oldWalk
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).trans annular.old_winding)

/-- The fine actual outer trace changes the retained source sheet. -/
theorem outer_target : RootEdgeBank.target retained.fine.edges annular.outerWalk sheet =
    BranchCutLifts.otherSheet sheet :=
  RootEdgeBank.target_odd retained.fine.edges annular.outerWalk
    (retained.included.vertex (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))
    0 annular.outer_winding sheet

/-- The actual connector, inner boundary and reverse connector end on the opposite old-anchor sheet. -/
theorem inner_target : RootEdgeBank.target retained.fine.edges annular.innerWalk sheet =
    BranchCutLifts.otherSheet sheet := annular.target_eq.symm.trans annular.outer_target

/-- The actual old and fine outer trace endpoints are the SAME retained opposite-sheet Owner. -/
theorem old_outer_owner :
    (original.frames.frameAt _ (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners
      (RootEdgeBank.target original.edges annular.oldWalk sheet) =
    (retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
      (RootEdgeBank.target retained.fine.edges annular.outerWalk sheet) :=
  (congrArg (fun value => (original.frames.frameAt _
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners value) annular.old_target).trans
    ((congrArg (fun frame : OwnerFrame _ => frame.owners (BranchCutLifts.otherSheet sheet))
      (retained.source_frame index)).symm.trans
      (congrArg (fun value => (retained.fine.frames.frameAt _ (retained.included.vertex
        (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners value)
        annular.outer_target).symm)

/-- The actual fine outer and inner trace endpoints are the SAME retained terminal Owner. -/
theorem outer_inner_owner :
    (retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
      (RootEdgeBank.target retained.fine.edges annular.outerWalk sheet) =
    (retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
      (RootEdgeBank.target retained.fine.edges annular.innerWalk sheet) :=
  congrArg (fun value => (retained.fine.frames.frameAt _ (retained.included.vertex
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners value) annular.target_eq

/-- The old and fine outer endpoint names compare through their SAME retained actual Owner. -/
def old_outer_equivalent : Approximation.Gaussian.Equivalence.NamedEquivalent
    (ownerName ((original.frames.frameAt _
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))).owners
      (RootEdgeBank.target original.edges annular.oldWalk sheet)))
    (ownerName ((retained.fine.frames.frameAt _ (retained.included.vertex
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)))).owners
      (RootEdgeBank.target retained.fine.edges annular.outerWalk sheet))) :=
  Approximation.Gaussian.Equivalence.NamedEquivalent.transport rfl
    (congrArg ownerName annular.old_outer_owner)
    (Approximation.Gaussian.Equivalence.NamedEquivalent.refl _)

/-- The actual outer edge value equals the inner edge value plus every retained signed regular-face correction. -/
theorem values (value : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    retained.fine.edges.chainValue retained.fine.vertices value annular.outerWalk sheet =
      retained.fine.edges.chainValue retained.fine.vertices value annular.innerWalk sheet +
        CellBoundary.sumValues (fun occurrence => wordValue value occurrence.word)
          annular.ordered.compiled.regulars := by
  have kept := congrArg (fun walk => retained.fine.edges.chainValue retained.fine.vertices value walk sheet)
    (congrArg RowCircuitOrder.CellCircuits.product annular.ordered.kept_eq)
  have word := (congrArg (wordValue value) annular.ordered.compiled.word_eq).trans kept.symm
  have inner := word.trans (annular.inner_comparison.values value anti sheet)
  exact (annular.outer_comparison.values value anti sheet).trans
    ((annular.ordered.values value anti).trans (congrArg (fun total => total +
      CellBoundary.sumValues (fun occurrence => wordValue value occurrence.word)
        annular.ordered.compiled.regulars) inner))

/-- The actual outer polygon retains the inner polygon and all signed local face/connector area terms. -/
theorem areas (value : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    retained.fine.edges.chainArea retained.fine.vertices value annular.outerWalk sheet =
      retained.fine.edges.chainArea retained.fine.vertices value annular.innerWalk sheet +
        AreaTerm.total value annular.ordered.compiled.areaTerms := by
  have kept := congrArg (fun walk => retained.fine.edges.chainArea retained.fine.vertices value walk sheet)
    (congrArg RowCircuitOrder.CellCircuits.product annular.ordered.kept_eq)
  have word := (congrArg (wordArea value) annular.ordered.compiled.word_eq).trans kept.symm
  have inner := word.trans (annular.inner_comparison.areas value anti sheet)
  exact (annular.outer_comparison.areas value anti sheet).trans
    ((annular.ordered.areas value anti).trans (congrArg (fun total => total +
      AreaTerm.total value annular.ordered.compiled.areaTerms) inner))

end Annulus

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

end
