module
import Purelib.Data.List.Filter
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Roots.Walk

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
public import Purelib.Riemann.Meshes.PuncturedFaceLookup
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding
import Purelib.Data.List.Permutation
import Purelib.Data.Gaussian.Components.Basic
import Init.Data.List.Basic
import Init.Data.List.Sublist
import Init.Data.List.Pairwise
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
public import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Tactic.Ring
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.CellBoundary

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder

open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-!
# Ordered branch circuits with retained regular-face corrections

Classify each leaf against the existing face partition once. Removing a
regular circuit preserves the actual arriving sheet, but its lifted boundary
value is retained as a correction on the sheet reached by its connector.
Branch circuits keep their original connectors, labels and order.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm wordArea wordArea_append)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace RegularLocation HoleLocation)
open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification (FaceKind)
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

set_option genInjectivity false in
/-- The classification is indexed by the original circuit expression. Every leaf retains its exact location in the
cached regular or hole list. -/
inductive CircuitPartition (faces : PuncturedFaces bank) {base : Basic.Canonical} :
  CellCircuits bank.grid base → Type
  /-- The original empty circuit tree has no classified face occurrences. -/ | nil :
    CircuitPartition faces (.nil
    base)
  /-- Retain the original circuit leaf's exact location in the regular-face bank. -/ | regular {cell : ClearGrid.Cell
    curve.polynomial (Cuts.Ambient curve)} {member : cell ∈ bank.grid.cells}
      {stem : Walks.Walk bank.grid base cell.box.anchor} (location : RegularLocation faces.regulars
        cell) :
      CircuitPartition faces
        (.cell cell member stem)
  /-- Retain the original circuit leaf's exact location in the branch-hole bank. -/ | hole {cell : ClearGrid.Cell
    curve.polynomial (Cuts.Ambient curve)} {member : cell ∈ bank.grid.cells}
      {stem : Walks.Walk bank.grid base cell.box.anchor} (location : HoleLocation faces.holes cell) :
      CircuitPartition faces
        (.cell cell member stem)
  /-- Retain the two original classified subtrees in their original circuit concatenation order. -/ | append {first last
    : CellCircuits bank.grid base}
      (firstPartition :
        CircuitPartition faces
        first) (lastPartition :
        CircuitPartition faces
        last) :
      CircuitPartition faces
        (.append first last)

constructive_injectivity CircuitPartition

namespace CircuitPartition

variable {faces : PuncturedFaces bank} {base :
  Basic.Canonical}

/-- Classify every original circuit leaf using the retained regular/hole face bank. -/
@[expose] def build (faces : PuncturedFaces bank) : (tree : CellCircuits bank.grid
  base) → CircuitPartition faces tree
  | .nil _ => .nil
  | .cell cell member _ => match faces.locateCell cell member with
      | .regular found => .regular found
      | .hole found => .hole found
  | .append first last => .append
    (build faces
    first)
    (build faces
    last)
termination_by structural tree => tree

/-- Keep the original hole circuits and their exact stems in order, replacing regular leaves by empty circuits. -/
@[expose] def kept : {tree : CellCircuits bank.grid base} →
  CircuitPartition faces tree →
  CellCircuits bank.grid base
  | _, .nil => .nil base
  | _, .regular _ => .nil base
  | .cell cell member stem, .hole _ => .cell cell member stem
  | _, .append first last => .append first.kept last.kept
termination_by structural _ partition => partition

/-- Read the original branch labels from the retained hole leaves in their exact circuit order. -/
@[expose] def labels : {tree : CellCircuits bank.grid base} →
  CircuitPartition faces tree → List
  (Data.Index branches)
  | _, .nil => []
  | _, .regular _ => []
  | _, .hole found => [found.hole.index]
  | _, .append first last => first.labels ++ last.labels
termination_by structural _ partition => partition

/-- Transport the SAME original face classification along a given connector prefix.

Every regular/hole location and original cell membership is retained.
Only the actual circuit connector is prefixed; no face lookup, isolation,
root selection or numerical observation is replayed.
-/
@[expose] def based {first last : Basic.Canonical} (stem : Walks.Walk bank.grid first last) :
    {tree : CellCircuits bank.grid last} → CircuitPartition faces tree →
      CircuitPartition faces (tree.based stem)
  | _, .nil => .nil
  | _, .regular location => .regular location
  | _, .hole location => .hole location
  | _, .append initial final => .append (initial.based stem) (final.based stem)
termination_by structural _ partition => partition

/-- Basing a classification preserves its whole kept circuit tree with that SAME connector prefix. -/
theorem based_kept {first last : Basic.Canonical} (stem : Walks.Walk bank.grid first last)
    {tree : CellCircuits bank.grid last} (partition : CircuitPartition faces tree) :
    (partition.based stem).kept = partition.kept.based stem := by
  induction partition with
  | nil => rfl
  | regular => rfl
  | hole => rfl
  | append initial final ihInitial ihFinal => exact congrArg₂ CellCircuits.append ihInitial ihFinal

/-- Basing a classification preserves every original signed branch label occurrence and its order. -/
theorem based_labels {first last : Basic.Canonical} (stem : Walks.Walk bank.grid first last)
    {tree : CellCircuits bank.grid last} (partition : CircuitPartition faces tree) :
    (partition.based stem).labels = partition.labels := by
  induction partition with
  | nil => rfl
  | regular => rfl
  | hole => rfl
  | append initial final ihInitial ihFinal => exact congrArg₂ List.append ihInitial ihFinal

/-- The original hole location identifies exactly the branch bank cell of its retained label. -/
private theorem hole_cell {cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)} (location :
  HoleLocation faces.holes cell) :
    cell = bank.cell location.hole.index := location.cell_eq.symm.trans location.hole.cell_eq

/-- Completeness is about the original branch labels, independently of their enumeration order in the isolator or the
retained hole list. -/
theorem labels_exact {tree : CellCircuits bank.grid base} (partition :
  CircuitPartition faces tree)
    (index : Data.Index branches) : index ∈ partition.labels ↔ bank.cell index ∈ tree.cells := by
  induction partition with
  | nil => constructor <;> intro impossible <;> nomatch impossible
  | @regular cell member stem location =>
      constructor
      · intro impossible
        exact (List.not_mem_nil impossible).elim
      · intro belongs
        have equal := Membership.mem_singleton.mp belongs
        exact (location.face.unassigned index (location.cell_eq.trans equal.symm)).elim
  | @hole cell member stem location =>
      change index ∈ [location.hole.index] ↔ bank.cell index ∈ [cell]
      constructor
      · intro member
        have equal := Membership.mem_singleton.mp member
        exact Membership.mem_singleton.mpr
          ((congrArg bank.cell equal).trans
            (hole_cell
              location).symm)
      · intro member
        have equal := Membership.mem_singleton.mp member
        exact Membership.mem_singleton.mpr
          (FaceKind.branch_unique equal.symm
            (hole_cell
              location))
  | append first last ihFirst ihLast =>
      change index ∈ first.labels ++ last.labels ↔ bank.cell index ∈ _ ++ _
      constructor
      · intro member
        rcases Membership.mem_append.mp member with member | member
        · exact Membership.mem_append.mpr (Or.inl (ihFirst.mp member))
        · exact Membership.mem_append.mpr (Or.inr (ihLast.mp member))
      · intro member
        rcases Membership.mem_append.mp member with member | member
        · exact Membership.mem_append.mpr (Or.inl (ihFirst.mpr member))
        · exact Membership.mem_append.mpr (Or.inr (ihLast.mpr member))

/-- The original ordered branch labels select the same cells as an order-preserving sublist of the retained tree.

Each hole occurrence uses its existing location's whole cell equality.
Regular occurrences are omitted; append nodes preserve both original
suborders. No face classification or cell producer is evaluated again.
-/
theorem labels_cells_sublist {tree : CellCircuits bank.grid base} (partition : CircuitPartition faces tree) :
    List.Sublist (partition.labels.map bank.cell) tree.cells := by
  induction partition with
  | nil => exact .slnil
  | regular => exact List.Sublist.cons _ .slnil
  | @hole cell member stem location =>
      change List.Sublist [bank.cell location.hole.index] [cell]
      exact Eq.mpr
        (congrArg (fun target => List.Sublist [bank.cell location.hole.index] [target]) (hole_cell location))
        (List.Sublist.cons_cons _ .slnil)
  | append first last ihFirst ihLast =>
      change List.Sublist ((first.labels ++ last.labels).map bank.cell) (_ ++ _)
      rewrite [Map.map_append]
      exact List.Sublist.append ihFirst ihLast

/-- Every retained cell-order relation passes to the actual branch labels without changing an occurrence.

The original labels are read through their exact bank cells. This uses
the retained sublist certificate, so equal label sets cannot substitute
for the actual classified circuit order.
-/
theorem labels_pairwise {tree : CellCircuits bank.grid base} (partition : CircuitPartition faces tree)
    {relation : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) →
      ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) → Prop}
    (ordered : tree.cells.Pairwise relation) :
    partition.labels.Pairwise (fun first last => relation (bank.cell first) (bank.cell last)) :=
  Pairwise.pairwise_map.mp (List.Pairwise.sublist partition.labels_cells_sublist ordered)

/-- An original circuit tree with no repeated cells has no repeated retained branch labels. -/
theorem labels_unique {tree : CellCircuits bank.grid base} (partition :
  CircuitPartition faces tree)
    (unique : tree.cells.Nodup) : partition.labels.Nodup := by
  exact List.Pairwise.imp (fun different equal => different (congrArg bank.cell equal))
    (partition.labels_pairwise unique)

variable {frames : RootFrames bank.grid} {vertices :
  LiftedVertices.VertexBank bank.grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

/-- The original regular-cell boundary preserves its incoming retained root sheet. -/
private theorem regular_identity (face : RegularFace bank) (cell : ClearGrid.Cell curve.polynomial
  (Cuts.Ambient curve))
    (member : cell ∈ bank.grid.cells) (equal : face.cell = cell) (sheet : Fin 2) :
    RootEdgeBank.target edges (Cell.boundaryWalk cell member) sheet = sheet := by
  cases equal
  exact Riemann.RootContinuation.GridRootWalks.BranchCellBank.RegularFace.sharedTransport_identity
    face edges sheet

/-- A retained stem, original regular-cell circuit and exact return preserve the initial root sheet.

The located regular face leaves its arriving sheet fixed; the original reverse connector cancels the same retained stem
transport. -/
theorem regular_based_target {cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)} (member : cell ∈
  bank.grid.cells)
    (location : RegularLocation faces.regulars cell) (stem : Walks.Walk bank.grid base
      cell.box.anchor) (sheet : Fin 2) :
    RootEdgeBank.target edges (stem.based (Cell.boundaryWalk cell member)) sheet = sheet := by
  rw [Walk.based, RootEdgeBank.target_append edges, RootEdgeBank.target_append edges,
    regular_identity
      location.face cell member location.cell_eq,
    edges.target_reverse (fun point member => (BranchCellBank.referenceAt bank point member).toLoop)]

/-- After exact stem-return cancellation, the original based regular circuit retains its boundary value on the sheet
actually reached. -/
private theorem regular_based_value {cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)} (member : cell ∈
  bank.grid.cells)
    (location : RegularLocation faces.regulars cell) (stem : Walks.Walk bank.grid base
      cell.box.anchor)
    (value : OrientedEdge vertices.count → Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) (sheet : Fin 2) :
    edges.chainValue vertices value (stem.based (Cell.boundaryWalk cell member)) sheet =
      edges.chainValue vertices value (Cell.boundaryWalk cell member) (RootEdgeBank.target edges stem sheet) := by
  rw [Walk.based, RootEdgeBank.chainValue_append, RootEdgeBank.chainValue_append,
    regular_identity
      location.face cell member location.cell_eq]
  have cancelled := (ChainComparison.retrace (edges := edges) (vertices := vertices)
    (fun point member => (BranchCellBank.referenceAt bank point member).toLoop) stem).values value anti sheet
  rw [RootEdgeBank.chainValue_append] at cancelled
  change edges.chainValue vertices value stem sheet +
    edges.chainValue vertices value stem.reverse (RootEdgeBank.target edges stem sheet) = 0 at cancelled
  calc
    _ = edges.chainValue vertices value (Cell.boundaryWalk cell member) (RootEdgeBank.target edges stem sheet) +
        (edges.chainValue vertices value stem sheet +
          edges.chainValue vertices value stem.reverse (RootEdgeBank.target edges stem sheet)) := by ring1
    _ = _ := by rw [cancelled, add_zero]

/-- The original based regular circuit retains its actual local boundary area and the exact connector cross term. -/
private theorem regular_based_area {cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)} (member : cell ∈
  bank.grid.cells)
    (location : RegularLocation faces.regulars cell) (stem : Walks.Walk bank.grid base
      cell.box.anchor)
    (value : OrientedEdge vertices.count → Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) (sheet : Fin 2) :
    edges.chainArea vertices value (stem.based (Cell.boundaryWalk cell member)) sheet =
      edges.chainArea vertices value (Cell.boundaryWalk cell member) (RootEdgeBank.target edges stem sheet) +
        2 * BoundaryRibbon.area (edges.chainValue vertices value stem sheet)
          (edges.chainValue vertices value (Cell.boundaryWalk cell member) (RootEdgeBank.target edges stem sheet)) := by
  rw [Walk.based, RootEdgeBank.chainArea, edges.indexedEdges_append, edges.indexedEdges_append,
    regular_identity
      location.face cell member location.cell_eq,
    edges.indexedEdges_reverse vertices (fun point member => (BranchCellBank.referenceAt bank point member).toLoop)]
  exact RetracingWords.wordArea_conjugate value anti _ _

set_option genInjectivity false in
/-- One actual regular-face occurrence, on the sheet reached by its connector. The original face location and indexed
boundary are cached. -/
structure RegularOccurrence (faces : PuncturedFaces bank) (vertices : LiftedVertices.VertexBank
  bank.grid)
    (edges : RootEdgeBank frames) where
  /-- The retained original regular cell occurrence. -/ cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)
  /-- The original retained cell belongs to the grid. -/ member : cell ∈ bank.grid.cells
  /-- The exact original regular-face location of this retained circuit occurrence. -/ location :
    RegularLocation faces.regulars cell
  /-- The original sheet reached by this occurrence's retained connector. -/ sheet : Fin 2
  /-- The cached indexed boundary word of this original regular occurrence on its actual arriving sheet. -/ word : List
    (OrientedEdge vertices.count)
  /-- The cached word is exactly the original cell boundary lifted on its retained arriving sheet. -/ word_eq : word =
    edges.indexedEdges vertices (Cell.boundaryWalk cell member) sheet

constructive_injectivity RegularOccurrence

set_option genInjectivity false in

/-- The finite reduction keeps every regular correction and both actual terminal-sheet equations. No regular boundary is
assigned value zero. -/
structure Compiled {tree : CellCircuits bank.grid base} (partition :
  CircuitPartition faces tree)
    (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank bank.grid) (sheet : Fin 2) where
  /-- The cached final root sheet of the original circuit product. -/ finish : Fin 2
  /-- The original full circuit product reaches exactly the retained final sheet. -/ target_eq : RootEdgeBank.target
    edges tree.product sheet = finish
  /-- The retained hole-only circuit product reaches that same original final sheet. -/ kept_target_eq :
    RootEdgeBank.target edges partition.kept.product sheet = finish
  /-- The cached indexed word of the original retained hole-only circuit product. -/ word : List (OrientedEdge
    vertices.count)
  /-- The cached retained word is exactly the classified hole-only product lifted from the original starting sheet. -/
    word_eq : word = edges.indexedEdges vertices partition.kept.product sheet
  /-- The retained original regular-face correction occurrences in circuit order. -/ regulars : List
    (RegularOccurrence
    faces vertices edges)
  /-- The cached concatenation of the exact original regular correction boundary words. -/ regularWord : List
    (OrientedEdge vertices.count)
  /-- The cached correction word is exactly the retained regular occurrence words concatenated in order. -/
    regularWord_eq : regularWord = regulars.flatMap
    RegularOccurrence.word
  /-- The retained signed local polygon and connector cross terms of the original circuit reduction. -/ areaTerms : List
    (AreaTerm vertices.count)
  /-- The original full circuit value equals the retained branch word plus the exact regular boundary correction values.
  -/
  values : ∀ (value : OrientedEdge vertices.count → Basic.Canonical), (∀ edge, value
    edge.reverse = -value edge) →
    edges.chainValue vertices value tree.product sheet =
      SewingRetraction.wordValue value word + CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value
        occurrence.word) regulars
  /-- The original full circuit area equals the retained branch word area plus all cached signed correction terms. -/
    areas : ∀ (value : OrientedEdge vertices.count → Basic.Canonical), (∀ edge, value edge.reverse
    = -value edge) →
    edges.chainArea vertices value tree.product sheet = RetracingWords.wordArea value word + AreaTerm.total value
      areaTerms

constructive_injectivity Compiled

/-- The cached regular correction word value equals the original finite sum of its retained occurrence values. -/
theorem Compiled.regularWord_values {tree : CellCircuits bank.grid base} {partition :
  CircuitPartition faces tree}
    {sheet : Fin 2} (compiled :
      Compiled partition
      edges vertices sheet) (value : OrientedEdge vertices.count → Basic.Canonical) :
    SewingRetraction.wordValue value compiled.regularWord = CellBoundary.sumValues (fun occurrence =>
      SewingRetraction.wordValue value occurrence.word) compiled.regulars := by
  rw [compiled.regularWord_eq]
  induction compiled.regulars with
  | nil => rfl
  | cons occurrence rest ih =>
      simp only [Flatten.flatMap_cons, SewingRetraction.wordValue_append, CellBoundary.sumValues, ih,
        -eq_self, -iff_self]
      rfl

/-- Compile the original classified circuit tree into retained hole circuits and exact regular corrections.

The starting and finishing sheets, original face occurrences, indexed words and every signed area cross term remain
attached to the same root edge bank. -/
@[expose] def compile (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank bank.grid) :
    {tree : CellCircuits bank.grid base} → (partition :
      CircuitPartition faces tree) →
      (sheet : Fin 2) →
      Compiled partition
        edges vertices sheet
  | _, .nil, sheet => ⟨sheet, rfl, rfl, [], rfl, [], [], rfl, [],
      fun _ _ => (add_zero _).symm, fun _ _ => (add_zero _).symm⟩
  | .cell cell member stem, .regular location, sheet =>
      let localSheet := RootEdgeBank.target edges stem sheet
      let word := edges.indexedEdges vertices (Cell.boundaryWalk cell member) localSheet
      let stemWord := edges.indexedEdges vertices stem sheet
      let occurrence :
        RegularOccurrence
        faces vertices edges := ⟨cell, member, location, localSheet, word, rfl⟩
      ⟨sheet,
        regular_based_target
        member location stem sheet, rfl, [], rfl, [occurrence], word,
        (Append.append_nil word).symm, [.polygon word, .cross 2 stemWord word], by
        intro value anti
        change edges.chainValue vertices value (stem.based (Cell.boundaryWalk cell member)) sheet =
          0 + (edges.chainValue vertices value (Cell.boundaryWalk cell member) localSheet + 0)
        rw [zero_add, add_zero]
        exact
          regular_based_value
          member location stem value anti sheet, by
        intro value anti
        change edges.chainArea vertices value (stem.based (Cell.boundaryWalk cell member)) sheet =
          0 + (RetracingWords.wordArea value word + (2 * BoundaryRibbon.area (SewingRetraction.wordValue value stemWord)
            (SewingRetraction.wordValue value word) + 0))
        rw [zero_add, add_zero]
        exact
          regular_based_area
          member location stem value anti sheet⟩
  | .cell cell member stem, .hole _, sheet =>
      let walk := stem.based (Cell.boundaryWalk cell member)
      ⟨RootEdgeBank.target edges walk sheet, rfl, rfl, edges.indexedEdges vertices walk sheet, rfl, [], [], rfl, [],
        fun _ _ => (add_zero _).symm, fun _ _ => (add_zero _).symm⟩
  | _, .append first last, sheet => by
      let initial :=
        compile
        edges vertices first sheet
      let final :=
        compile
        edges vertices last initial.finish
      refine ⟨final.finish, ?_, ?_, initial.word ++ final.word, ?_, initial.regulars ++ final.regulars,
        initial.regularWord ++ final.regularWord, ?_, initial.areaTerms ++ final.areaTerms ++
          [.cross 1 initial.word final.regularWord, .cross 1 initial.regularWord final.word,
            .cross 1 initial.regularWord final.regularWord], ?_, ?_⟩
      · rw [CellCircuits.product, RootEdgeBank.target_append edges, initial.target_eq, final.target_eq]
      · rw [kept,
          CellCircuits.product, RootEdgeBank.target_append edges, initial.kept_target_eq, final.kept_target_eq]
      · rw [kept,
          CellCircuits.product, edges.indexedEdges_append, initial.kept_target_eq,
          ← initial.word_eq, ← final.word_eq]
      · rw [initial.regularWord_eq, final.regularWord_eq, Flatten.flatMap_append]
      · intro value anti
        rw [CellCircuits.product, RootEdgeBank.chainValue_append, initial.target_eq,
          initial.values value anti, final.values value anti, SewingRetraction.wordValue_append,
            CellBoundary.sumValues_append]
        ring1
      · intro value anti
        rw [CellCircuits.product, RootEdgeBank.chainArea_append, initial.target_eq,
          initial.areas value anti, final.areas value anti, initial.values value anti, final.values value anti,
          ← initial.regularWord_values value, ← final.regularWord_values value,
          RetracingWords.wordArea_append, AreaTerm.total_append, AreaTerm.total_append]
        simp only [AreaTerm.total, AreaTerm.evaluate, Int.cast_one, one_mul, add_zero,
          IncrementArea.area_add_left, IncrementArea.area_add_right, -eq_self, -iff_self]
        ring1
termination_by structural _ partition _ => partition

end CircuitPartition

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces BranchHole)
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder (CircuitOrder)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window (BranchCount)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {box :
    Geometry.Rational.Box} {window : WindowBoundary.Window
    bank.grid box}
  {frames : RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

set_option genInjectivity false in
/-- A window's actual branch order, with complete label selection and cached finite corrections for the requested
initial sheet. -/
structure OrderedBranches (faces : PuncturedFaces bank) (window :
  WindowBoundary.Window bank.grid box)
    (edges : RootEdgeBank frames) (vertices : VertexBank bank.grid) (sheet : Fin 2) where
  /-- The retained original window circuit order with its exact boundary comparison. -/ ordered :
    CircuitOrder window edges vertices
  /-- The regular/hole classification of that exact original ordered circuit tree. -/ partition : CircuitPartition faces
    ordered.tree
  /-- The cached original hole-only circuit tree in the retained window order. -/ kept : CellCircuits
    bank.grid (Components.Basic.point box.xLower box.yLower)
  /-- The cached retained circuit tree is exactly the hole-only tree from the original classification. -/ kept_eq : kept
    = partition.kept
  /-- The cached original branch labels in their retained geometric circuit order. -/ labels : List (Data.Index
    branches)
  /-- The cached label list is exactly the original classified circuit label list. -/ labels_eq : labels =
    partition.labels
  /-- The retained original branch labels have no repetitions. -/ unique : labels.Nodup
  /-- The retained labels identify exactly the original branch cells contained in the window. -/ selected : ∀ index,
    index ∈ labels ↔ (bank.cell index).box.Refines box
  /-- The cached circuit compilation for the original starting sheet and shared vertex bank. -/ compiled :
    CircuitPartition.Compiled partition edges vertices sheet

constructive_injectivity OrderedBranches

/-- Retain the original window circuit order, classify its leaves and cache the ordered branch circuits with exact
regular corrections. -/
@[expose] def prepareBranches (faces : PuncturedFaces bank) (window :
  WindowBoundary.Window bank.grid box)
    (edges : RootEdgeBank frames) (vertices : VertexBank bank.grid) (sheet : Fin 2) :
    OrderedBranches faces window edges vertices
      sheet := by
  let ordered := WindowCircuitOrder.prepareCircuits window edges vertices
    (fun point member => (BranchCellBank.referenceAt bank point member).toLoop)
  let partition := CircuitPartition.build faces ordered.tree
  refine ⟨ordered, partition, partition.kept, rfl, partition.labels, rfl, ?_, ?_, partition.compile edges vertices
    sheet⟩
  · apply partition.labels_unique
    rw [ordered.tree_eq]
    exact window.circuits_unique
  · intro index
    constructor
    · intro member
      have belongs := (partition.labels_exact index).mp member
      rw [ordered.tree_eq] at belongs
      exact (window.circuits_member.mp belongs).2
    · intro inside
      apply (partition.labels_exact index).mpr
      rw [ordered.tree_eq]
      exact window.circuits_member.mpr ⟨bank.cell_mem index, inside⟩

namespace OrderedBranches

variable {sheet : Fin 2} (prepared :
  OrderedBranches faces window edges
  vertices sheet)

/-- The original window boundary reaches the retained compilation's final root sheet. -/
theorem target : RootEdgeBank.target edges window.boundary sheet = prepared.compiled.finish := by
  have same := prepared.ordered.comparison.targets sheet
  rw [prepared.ordered.product_eq] at same
  exact same.symm.trans prepared.compiled.target_eq

/-- The retained branch-only circuit tree reaches the same original final sheet. -/
theorem kept_target : RootEdgeBank.target edges prepared.kept.product sheet = prepared.compiled.finish := by
  rw [prepared.kept_eq]
  exact prepared.compiled.kept_target_eq

/-- The retained final sheet equals the actual window's cached branch-parity action. -/
theorem finish_action (count : BranchCount faces window) : prepared.compiled.finish = count.action sheet :=
  prepared.target.symm.trans (count.target edges sheet)

/-- The original ordered branch label count equals the retained geometric window hole count. -/
theorem labels_count (count : BranchCount faces window) : prepared.labels.length = count.count := by
  let indices := count.holes.map BranchHole.index
  have unique : indices.Nodup := by
    apply Pairwise.pairwise_map.mpr
    rw [count.holes_eq]
    exact Filter.pairwise_filter _ faces.holes_pairwise
  have same (index : Data.Index branches) : index ∈ prepared.labels ↔ index ∈ indices := by
    constructor
    · intro member
      rcases (count.selected_iff index).mpr ((prepared.selected index).mp member) with ⟨hole, member, equal⟩
      exact Map.mem_map.mpr ⟨hole, member, equal⟩
    · intro member
      exact (prepared.selected index).mpr ((count.selected_iff index).mp (Map.mem_map.mp member))
  have lengths := Nat.le_antisymm
    (Nodup.nodup_length_le_of_mem prepared.unique unique (fun index member => (same index).mp member))
    (Nodup.nodup_length_le_of_mem unique prepared.unique (fun index member => (same index).mpr member))
  exact lengths.trans ((Map.length_map BranchHole.index count.holes).trans count.count_eq.symm)

/-- The original exterior word equals the ordered branch word plus actual regular boundaries, on the shared lifted
vertices and without face-zero assumptions. -/
theorem values (value : OrientedEdge vertices.count → Basic.Canonical) (anti : ∀ edge, value
  edge.reverse = -value edge) :
    edges.chainValue vertices value window.boundary sheet = SewingRetraction.wordValue value prepared.compiled.word +
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value occurrence.word)
        prepared.compiled.regulars := by
  have same := prepared.ordered.comparison.values value anti sheet
  rw [prepared.ordered.product_eq] at same
  exact same.symm.trans (prepared.compiled.values value anti)

/-- The complete increment polygon is preserved, including all internal regular-face areas and every cross term stored
by the finite compiler. -/
theorem areas (value : OrientedEdge vertices.count → Basic.Canonical) (anti : ∀ edge, value
  edge.reverse = -value edge) :
    edges.chainArea vertices value window.boundary sheet = RetracingWords.wordArea value prepared.compiled.word +
      AreaTerm.total value prepared.compiled.areaTerms := by
  have same := prepared.ordered.comparison.areas value anti sheet
  rw [prepared.ordered.product_eq] at same
  exact same.symm.trans (prepared.compiled.areas value anti)

end OrderedBranches
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window

end
