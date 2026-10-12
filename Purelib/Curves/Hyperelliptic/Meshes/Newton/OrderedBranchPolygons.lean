module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

public section

/-! Incoming sheets of the original ordered branch excursions, including
the one- or two-branch ending. No branch polygon is dropped. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons in
/-- Determine a branch's incoming sheet from its position in the original ordered label list, alternating after each
preceding label. -/
@[expose] def incoming {count : Nat} : List (Fin count) → Fin 2 → Fin count → Fin 2
  | [], sheet, _ => sheet
  | head :: tail, sheet, index => if index = head then sheet else incoming tail
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) index

/-- Sum the original branch polygon values with alternating incoming sheets in retained label order. -/
private def alternatingArea {count : Nat} (value : Fin count → Fin 2 → Gaussian.Basic.Canonical) : List (Fin count) →
  Fin 2 → Gaussian.Basic.Canonical
  | [], _ => 0
  | head :: tail, sheet => value head sheet +
    Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea value tail
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons in
/-- For distinct retained branch labels, selecting each branch's incoming sheet equals the original alternating ordered
area sum. -/
private theorem incoming_sum {count : Nat} (value : Fin count → Fin 2 → Gaussian.Basic.Canonical)
    (labels : List (Fin count)) (unique : labels.Nodup) (sheet : Fin 2) :
    Geometry.Grid.CellBoundary.sumValues (fun index => value index (incoming labels sheet index)) labels =
      Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea value labels sheet := by
  induction labels generalizing sheet with
  | nil => rfl
  | cons head tail ih =>
      rw [Geometry.Grid.CellBoundary.sumValues, incoming, if_pos rfl,
        Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea]
      apply congrArg (value head sheet + ·)
      have read : Geometry.Grid.CellBoundary.sumValues (fun index => value index (incoming (head :: tail) sheet index))
        tail =
          Geometry.Grid.CellBoundary.sumValues (fun index => value index (incoming tail
            (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) index)) tail := by
        apply Geometry.Grid.CellBoundary.sumValues_congr
        intro index member
        have different : index ≠ head := fun equal => (List.pairwise_cons.mp unique).1 index member equal.symm
        rw [incoming, if_neg different]
      exact read.trans (ih (List.pairwise_cons.mp unique).2 _)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons in
/-- The actual position in the retained geometric order determines the
incoming sheet. The default outside that complete order is never consumed. -/
@[expose] def branchSheet (ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet) (newSheet
  : Fin 2) (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) : Fin 2 :=
  incoming ordered.prepared.labels newSheet index

variable {fine : Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid fine)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames fine} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank fine)

/-- The even ending has a genuine cross area between its two excursions;
the odd ending has only one excursion. -/
@[expose] def terminalCross (bank :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (newSheet : Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
      (Hyperelliptic.Branches.BranchIsolation.Data.Index branches) → Gaussian.Basic.Canonical
  | .odd _ => 0
  | .even first last => Path.BoundaryRibbon.area
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get first).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet))
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get last).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
          (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet)))

section
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
/-- The original terminal loop-product area is its alternating excursion sum plus the retained terminal cross area. -/
private theorem terminal_area (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical)
    (ending : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
      (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)) :
    Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices (included.resplit (bank.loopProduct
      ending.labels) (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      newSheet) =
      Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea (fun index incoming =>
        Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get index).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) incoming))
          ending.labels newSheet +
      Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminalCross included edges vertices bank newSheet value ending
        := by
  have empty (incoming : Fin 2) : edges.indexedEdges vertices
      (included.resplit (bank.loopProduct [])
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) incoming = []
        := rfl
  cases ending with
  | odd index =>
      rw [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.labels,
        Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.resplit_product_cons
        bank included edges vertices, empty, Data.List.Append.append_nil]
      simp only [Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea,
        Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminalCross, add_zero, -eq_self, -iff_self]
      rfl
  | even first last =>
      rw [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.labels,
        Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.resplit_product_pair
        bank included edges vertices, empty, Data.List.Append.append_nil, Topology.Mesh.RetracingWords.wordArea_append]
      simp only [Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea,
        Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminalCross, add_zero, -eq_self, -iff_self]
      rfl

/-- The original alternating branch sum splits into its paired internal polygons and the retained ending sum. -/
private theorem pairs_area (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical)
    (pairs : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches))
    (ending : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)) :
    Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea (fun index incoming =>
      Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
      (included.resplit (bank.rows.get index).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) incoming))
      (pairs.flatMap (fun pair => [pair.1, pair.2]) ++ ending) newSheet =
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea included edges vertices bank newSheet
      value pairs +
      Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea (fun index incoming =>
        Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get index).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) incoming))
          ending newSheet := by
  induction pairs with
  | nil => exact (zero_add _).symm
  | cons pair tail ih =>
      simp only [Data.List.Flatten.flatMap_cons, List.cons_append, List.nil_append,
        Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea,
        Hyperelliptic.Branches.BranchCutLifts.otherSheet_other]
      rw [ih]
      simp only [Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea, List.map_cons,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      ring1

/-- The original branch-sheet area sum equals the paired internal area plus the actual terminal loop area minus its
retained cross term.

The identity uses the original geometric order and keeps both ending cases and their incoming sheets. -/
theorem branch_area_sum {ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet} (paired :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered)
    (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun index => Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges
      vertices
      (included.resplit (bank.rows.get index).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
        (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet index)))
      ordered.prepared.labels =
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea included edges vertices bank newSheet
      value paired.split.pairs +
      Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices (included.resplit (bank.loopProduct
        paired.split.ending.labels)
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) -
          Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminalCross included edges vertices bank newSheet value
          paired.split.ending := by
  let entryArea := fun index incoming => Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
    (included.resplit (bank.rows.get index).reference.walk
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) incoming)
  have read := Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.incoming_sum entryArea ordered.prepared.labels
    ordered.prepared.unique newSheet
  have labels := congrArg (fun labels => Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea entryArea
    labels newSheet) paired.split.labels_eq
  have split := read.trans (labels.trans (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.pairs_area included edges
    vertices newSheet value paired.split.pairs paired.split.ending.labels))
  have terminal := Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminal_area included edges vertices (bank :=
    bank) newSheet value paired.split.ending
  calc
    _ = Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea included edges vertices bank
      newSheet value paired.split.pairs +
        Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.alternatingArea entryArea paired.split.ending.labels newSheet
          := split
    _ = _ := by rw [terminal]; ring1

end

variable {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation
  base.bank.toBranchCellBank} {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- Read the already cached branch polygons in the exact paired-area
formula, retaining the terminal cross term and both incoming sheets. -/
theorem branch_polygons_eq {ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet} (paired :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered) (newSheet : Fin 2)
    (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current) {fixed :
      Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {error :
      Fraction.Rational} {floor : Nat}
    {requests : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank
      (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branchSheet ordered newSheet) fixed error floor
      excision.entries}
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} {readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh}
    {surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values}
      (samples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface
      requests) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
    samples.polygons = Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea grid.shrunk.included
      current.edges current.vertices bank newSheet value paired.split.pairs +
      Topology.Mesh.RetracingWords.wordArea value (current.edges.indexedEdges current.vertices
        (grid.shrunk.included.resplit
        (bank.loopProduct paired.split.ending.labels)
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) -
      Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminalCross grid.shrunk.included current.edges
        current.vertices bank newSheet value paired.split.ending := by
  intro value
  exact samples.polygons_eq.trans ((Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.Ordered.branch_entries_sum
    ordered excision _).symm.trans
    (Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.branch_area_sum grid.shrunk.included current.edges
      current.vertices paired newSheet value))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
