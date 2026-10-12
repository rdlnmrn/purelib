module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.RegularArea
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.WindowOrder
import Init.Data.List.Basic
import Init.Data.List.Lemmas
public import Init.Data.List.Sublist
import Init.Prelude
import Init.SimpLemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Tactic.Ring
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts

public section

/-! The original ordered cell decomposition on the enlarged grid. Cached
regular occurrences retain their original locations, subdivided words and
actual arriving sheets; their polygon and connector areas are not erased. -/

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Topology.Mesh
open Purelib.Topology.Mesh.RetracingWords
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm wordArea wordArea_append)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {grid :
    Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Ambient
    curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Purelib.Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
  {start : Purelib.Data.Gaussian.Basic.Canonical} (member :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

set_option genInjectivity false in
/-- One actual original regular-face boundary occurrence lifted on the enlarged grid.

Its retained cell location and arriving sheet identify the exact subdivided indexed word. -/
structure ResplitRegularOccurrence where
  /-- The original regular cell whose actual boundary is retained. -/ cell : ClearGrid.Cell curve.polynomial
    (Cuts.Ambient curve)
  /-- The retained original cell belongs to the original grid. -/ member : cell ∈ bank.grid.cells
  /-- The actual original regular-face location of this retained cell. -/ location : PuncturedGridFaces.RegularLocation
    faces.regulars cell
  /-- The actual arriving sheet of this boundary occurrence on the enlarged grid. -/ sheet : Fin 2
  /-- The cached exact lifted indexed word on the enlarged grid. -/ word : List (Stokes.OrientedEdge vertices.count)
  /-- The cached word is exactly the retained original boundary or kept product after resplitting on its actual sheet.
  -/
  word_eq : word = edges.indexedEdges vertices
    (included.resplit (CellBoundary.Cell.boundaryWalk cell member)
      (ClearGrid.Cell.anchor_mem cell member)) sheet

constructive_injectivity ResplitRegularOccurrence

/-- Connector corrections contain no retained polygon area. -/
@[expose] def IsConnectorTerm : RetracingWords.AreaTerm count → Prop
  | .polygon _ => False
  | .cross _ _ _ => True

/-- One factor is a subsequence of the retained regular boundaries, with their original sheets and order. The
subsequence bounds its multiplicity. -/
@[expose] def RegularFactor (regulars : List
  (ResplitRegularOccurrence
  (faces := faces) included edges vertices))
    (word : List (Stokes.OrientedEdge vertices.count)) : Prop :=
  ∃ selected : List
    (ResplitRegularOccurrence
    (faces := faces) included edges vertices),
    selected.Sublist regulars ∧ word = selected.flatMap
      ResplitRegularOccurrence.word

/-- A retained cross-area correction with at least one factor drawn from an ordered sublist of actual regular boundary
occurrences. -/
@[expose] def RegularConnector (regulars : List
  (ResplitRegularOccurrence
  (faces := faces) included edges vertices)) :
    RetracingWords.AreaTerm vertices.count → Prop
  | .polygon _ => False
  | .cross _ first last =>
    RegularFactor
    included edges vertices regulars first ∨
    RegularFactor
    included edges vertices regulars last

/-- An ordered extension of the retained regular-occurrence list preserves its actual connector-factor certificate. -/
theorem regularConnector_mono
    {first last : List
      (ResplitRegularOccurrence
      (faces := faces) included edges vertices)}
    (sublist : first.Sublist last) {term : RetracingWords.AreaTerm vertices.count}
    (regular :
      RegularConnector
      included edges vertices first term) :
    RegularConnector
      included edges vertices last term := by
  cases term with
  | polygon => exact regular.elim
  | cross coefficient left right =>
      rcases regular with ⟨selected, present, equal⟩ | ⟨selected, present, equal⟩
      · exact Or.inl ⟨selected, present.trans sublist, equal⟩
      · exact Or.inr ⟨selected, present.trans sublist, equal⟩

 set_option genInjectivity false in
/-- The original ordered circuit partition evaluated on an enlarged grid with all regular areas and connector terms
retained.

Exact final-sheet, word, value and area readbacks preserve original occurrences and bound each connector's regular
factor by an actual ordered sublist. -/
structure ResplitCompiled {tree : RowCircuitOrder.CellCircuits bank.grid start} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (sheet : Fin 2) where
  /-- The actual final sheet after the retained resplit circuit product. -/ finish : Fin 2
  /-- The original full circuit product reaches this exact retained final sheet. -/ target_eq : RootEdgeBank.target
    edges (included.resplit tree.product member) sheet = finish
  /-- The retained kept circuit product reaches the same actual final sheet. -/ kept_target_eq : RootEdgeBank.target
    edges (included.resplit partition.kept.product member) sheet = finish
  /-- The cached exact lifted indexed word on the enlarged grid. -/ word : List (Stokes.OrientedEdge vertices.count)
  /-- The cached word is exactly the retained original boundary or kept product after resplitting on its actual sheet.
  -/
  word_eq : word = edges.indexedEdges vertices (included.resplit partition.kept.product member) sheet
  /-- The original ordered regular boundary occurrences with their actual enlarged-grid words and sheets. -/ regulars :
    List
    (ResplitRegularOccurrence
    (faces := faces) included edges vertices)
  /-- The cached concatenation of all actual retained regular boundary words. -/ regularWord : List (Stokes.OrientedEdge
    vertices.count)
  /-- The regular-word cache is exactly the retained occurrence-list flattening. -/ regularWord_eq : regularWord =
    regulars.flatMap
    ResplitRegularOccurrence.word
  /-- The complete retained polygon and connector area corrections. -/ areaTerms : List (RetracingWords.AreaTerm
    vertices.count)
  /-- The retained cross terms remaining after actual regular polygon areas are separated. -/ connectorTerms : List
    (RetracingWords.AreaTerm vertices.count)
  /-- The original full circuit value is the kept word value plus all actual regular boundary values. -/ values : ∀
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical), (∀ edge, value edge.reverse = -value
    edge) →
    edges.chainValue vertices value (included.resplit tree.product member) sheet =
      SewingRetraction.wordValue value word + CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value
        occurrence.word) regulars
  /-- The original full circuit area is the kept word area plus every retained area correction. -/ areas : ∀ (value :
    Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical), (∀ edge, value edge.reverse = -value edge) →
    edges.chainArea vertices value (included.resplit tree.product member) sheet = RetracingWords.wordArea value word +
      AreaTerm.total value areaTerms
  /-- The complete retained correction separates into actual regular polygon areas and exact connector terms. -/
    area_split : ∀ value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical,
    AreaTerm.total value areaTerms = CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea value
      occurrence.word) regulars +
      AreaTerm.total value connectorTerms
  /-- Every retained connector has an actual regular factor with certified ordered-sublist multiplicity. -/
    connector_factors : ∀ term ∈ connectorTerms,
    RegularConnector
    included edges vertices regulars term

constructive_injectivity ResplitCompiled

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
namespace ResplitCompiled

variable {included edges vertices member} {tree : Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits
  bank.grid start}
  {partition : CircuitPartition
    faces tree} {sheet : Fin 2}

/-- Every retained connector correction is a cross term and carries no independent polygon area. -/
theorem connector_only (compiled :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
  included edges vertices member partition sheet)
    (term : RetracingWords.AreaTerm vertices.count) (present : term ∈ compiled.connectorTerms) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.IsConnectorTerm
      term := by
  have regular := compiled.connector_factors term present
  cases term with
  | polygon => exact regular.elim
  | cross => trivial

/-- The cached regular-word value is exactly the finite sum of its actual ordered occurrence values. -/
theorem regularWord_values (compiled :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
  included edges vertices member partition sheet)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue value compiled.regularWord = CellBoundary.sumValues (fun occurrence =>
      SewingRetraction.wordValue value occurrence.word) compiled.regulars := by
  rw [compiled.regularWord_eq]
  induction compiled.regulars with
  | nil => rfl
  | cons occurrence rest ih =>
      simp only [Flatten.flatMap_cons, SewingRetraction.wordValue_append, CellBoundary.sumValues, ih, -eq_self,
        -iff_self]
      rfl

/-- Retain one original regular circuit's arriving sheet, subdivided boundary polygon and exact stem cross correction.
-/
@[expose] def ofRegular {cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)} {onGrid : cell ∈ bank.grid.cells}
    {stem : Walks.Walk bank.grid start cell.box.anchor} (location : PuncturedGridFaces.RegularLocation faces.regulars
      cell) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices member (.regular (member := onGrid) (stem := stem) location) sheet := by
  rcases location with ⟨index, face, indexed, equal⟩
  cases equal
  let localSheet := RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member)) sheet
  let word := edges.indexedEdges vertices (included.resplit face.boundary (face.cell.anchor_mem face.member)) localSheet
  let stemWord := edges.indexedEdges vertices (included.resplit stem (face.cell.anchor_mem face.member)) sheet
  let occurrence :
    ResplitRegularOccurrence
    (faces := faces) included edges vertices :=
    ⟨face.cell, face.member, ⟨index, face, indexed, rfl⟩, localSheet, word, rfl⟩
  refine ⟨sheet, face.resplit_based_target included edges vertices reference stem member sheet, rfl, [], rfl,
    [occurrence], word, (Append.append_nil word).symm, [.polygon word, .cross 2 stemWord word],
    [.cross 2 stemWord word], ?_, ?_, ?_, ?_⟩
  · intro value anti
    change edges.chainValue vertices value (included.resplit (stem.based face.boundary) member) sheet =
      0 + (edges.chainValue vertices value (included.resplit face.boundary (face.cell.anchor_mem face.member))
        localSheet + 0)
    rw [zero_add, add_zero]
    exact face.resplit_based_value included edges vertices reference stem member value anti sheet
  · intro value anti
    change edges.chainArea vertices value (included.resplit (stem.based face.boundary) member) sheet =
      0 + (RetracingWords.wordArea value word + (2 * BoundaryRibbon.area (SewingRetraction.wordValue value stemWord)
        (SewingRetraction.wordValue value word) + 0))
    rw [zero_add, add_zero]
    exact face.resplit_based_area included edges vertices reference stem member value anti sheet
  · intro value
    change RetracingWords.wordArea value word + (2 * BoundaryRibbon.area (SewingRetraction.wordValue value stemWord)
      (SewingRetraction.wordValue value word) + 0) =
      (RetracingWords.wordArea value word + 0) + (2 * BoundaryRibbon.area (SewingRetraction.wordValue value stemWord)
        (SewingRetraction.wordValue value word) + 0)
    simp only [add_zero, -eq_self, -iff_self]
    rfl
  · intro term belongs
    have same := Membership.mem_singleton.mp belongs
    cases same
    exact Or.inr ⟨[occurrence], List.Sublist.refl _, (Append.append_nil word).symm⟩

/-- Compose two retained circuit partitions on their actual successive sheets, preserving every regular polygon and all
resulting cross terms. -/
@[expose] def append {first last : RowCircuitOrder.CellCircuits bank.grid start}
    {firstPartition : BranchCellBank.CircuitPartition faces first} {lastPartition : BranchCellBank.CircuitPartition
      faces last}
    (initial :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices member firstPartition sheet)
    (final :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices member lastPartition initial.finish) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices member (.append firstPartition lastPartition) sheet := by
  refine ⟨final.finish, ?_, ?_, initial.word ++ final.word, ?_, initial.regulars ++ final.regulars,
    initial.regularWord ++ final.regularWord, ?_, initial.areaTerms ++ final.areaTerms ++
      [.cross 1 initial.word final.regularWord, .cross 1 initial.regularWord final.word,
        .cross 1 initial.regularWord final.regularWord],
    initial.connectorTerms ++ final.connectorTerms ++
      [.cross 1 initial.word final.regularWord, .cross 1 initial.regularWord final.word,
        .cross 1 initial.regularWord final.regularWord], ?_, ?_, ?_, ?_⟩
  · rw [CellCircuits.product, included.resplit_append _ _ member member, RootEdgeBank.target_append edges,
      initial.target_eq, final.target_eq]
  · rw [CircuitPartition.kept, CellCircuits.product, included.resplit_append _ _ member member,
      RootEdgeBank.target_append edges,
      initial.kept_target_eq, final.kept_target_eq]
  · rw [CircuitPartition.kept, CellCircuits.product, included.resplit_append _ _ member member,
      edges.indexedEdges_append,
      initial.kept_target_eq, ← initial.word_eq, ← final.word_eq]
  · rw [initial.regularWord_eq, final.regularWord_eq, Flatten.flatMap_append]
  · intro value anti
    rw [CellCircuits.product, included.resplit_append _ _ member member, RootEdgeBank.chainValue_append,
      initial.target_eq, initial.values value anti, final.values value anti, SewingRetraction.wordValue_append,
        CellBoundary.sumValues_append]
    ring1

  · intro value anti
    rw [CellCircuits.product, included.resplit_append _ _ member member, RootEdgeBank.chainArea_append,
      initial.target_eq, initial.areas value anti, final.areas value anti, initial.values value anti, final.values value
        anti,
      ← initial.regularWord_values value, ← final.regularWord_values value,
      RetracingWords.wordArea_append, AreaTerm.total_append, AreaTerm.total_append]
    simp only [AreaTerm.total, AreaTerm.evaluate, Int.cast_one, one_mul, add_zero,
      IncrementArea.area_add_left, IncrementArea.area_add_right, -eq_self, -iff_self]
    ring1
  · intro value
    rw [AreaTerm.total_append, AreaTerm.total_append, initial.area_split, final.area_split,
      CellBoundary.sumValues_append, AreaTerm.total_append, AreaTerm.total_append]
    ring1
  · intro term belongs
    rcases Membership.mem_append.mp belongs with belongs | belongs
    · rcases Membership.mem_append.mp belongs with belongs | belongs
      · exact
          regularConnector_mono
          included edges vertices (List.sublist_append_left _ _) (initial.connector_factors term belongs)
      · exact
          regularConnector_mono
          included edges vertices (List.sublist_append_right _ _) (final.connector_factors term belongs)
    · have choices : term = .cross 1 initial.word final.regularWord ∨
          term = .cross 1 initial.regularWord final.word ∨
          term = .cross 1 initial.regularWord final.regularWord := by
        cases Membership.mem_cons.mp belongs with
        | inl first => exact Or.inl first
        | inr tail =>
            cases Membership.mem_cons.mp tail with
            | inl second => exact Or.inr (Or.inl second)
            | inr last => exact Or.inr (Or.inr (Membership.mem_singleton.mp last))
      rcases choices with rfl | rfl | rfl
      · exact Or.inr ⟨final.regulars, List.sublist_append_right _ _, final.regularWord_eq⟩
      · exact Or.inl ⟨initial.regulars, List.sublist_append_left _ _, initial.regularWord_eq⟩
      · exact Or.inl ⟨initial.regulars, List.sublist_append_left _ _, initial.regularWord_eq⟩

end ResplitCompiled
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
/-- Reuse the original classification and branch order. No new cell classification, connector selection or branch
enumeration is performed. -/
@[expose] def compileResplit : {tree : RowCircuitOrder.CellCircuits bank.grid start} → (partition :
  BranchCellBank.CircuitPartition faces tree) → (sheet : Fin 2) →
    ResplitCompiled
      included edges vertices member partition sheet
  | _, .nil, sheet => ⟨sheet, rfl, rfl, [], rfl, [], [], rfl, [], [],
      fun _ _ => (add_zero _).symm, fun _ _ => (add_zero _).symm, fun _ => (add_zero _).symm,
      fun _ belongs => (List.not_mem_nil belongs).elim⟩
  | _, .regular location, _ =>
    ResplitCompiled.ofRegular
    reference location
  | .cell cell onGrid stem, .hole _, sheet =>
      let walk := included.resplit
        (stem.based (CellBoundary.Cell.boundaryWalk cell onGrid)) member
      ⟨RootEdgeBank.target edges walk sheet, rfl, rfl, edges.indexedEdges vertices walk sheet, rfl, [], [], rfl, [], [],
        fun _ _ => (add_zero _).symm, fun _ _ => (add_zero _).symm, fun _ => (add_zero _).symm,
        fun _ belongs => (List.not_mem_nil belongs).elim⟩
  | _, .append first last, sheet =>
      let initial :=
        compileResplit
        first sheet
      let final :=
        compileResplit
        last initial.finish
      initial.append final
termination_by structural _ partition _ => partition

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Topology.Mesh
open Purelib.Topology.Mesh.RetracingWords
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  (ordered :
    Ordered bank
    sheet) {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Purelib.Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
  {newSheet : Fin 2}
  (compiled :
    OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
    included edges vertices
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
    ordered.prepared.partition newSheet)

include reference

/-- The original physical exterior now consumes the original ordered classification on the enlarged mesh, retaining
every regular area term. -/
theorem resplit_exterior_areas (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    edges.chainArea vertices value (included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank))
      newSheet =
      RetracingWords.wordArea value compiled.word + AreaTerm.total value compiled.areaTerms := by
  have same := ordered.window.resplit_circuits_comparison included edges vertices reference
    (FramedBranchCellBank.baseMember base.bank)
  rw [← ordered.prepared.ordered.tree_eq, ordered.exterior_eq] at same
  exact (same.areas value anti newSheet).symm.trans (compiled.areas value anti)

/-- The period correction uses exactly the same retained regular words as the area comparison, with no separate ordering
or resampling. -/
theorem resplit_exterior_values (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    edges.chainValue vertices value (included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank))
      newSheet =
      SewingRetraction.wordValue value compiled.word + CellBoundary.sumValues (fun occurrence =>
        SewingRetraction.wordValue value occurrence.word) compiled.regulars := by
  have same := ordered.window.resplit_circuits_comparison included edges vertices reference
    (FramedBranchCellBank.baseMember base.bank)
  rw [← ordered.prepared.ordered.tree_eq, ordered.exterior_eq] at same
  exact (same.values value anti newSheet).symm.trans (compiled.values value anti)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
