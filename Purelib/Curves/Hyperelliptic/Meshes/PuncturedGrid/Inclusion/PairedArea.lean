module
import Purelib.Data.List.Flatten
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts

open Purelib.Topology

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation hiding Gaussian

open Purelib.Topology.Surface.Sewing

public section

/-! Read the corrected ordered pairing on an enlarged grid, without
replacing the original cycles or identifying old and new root frames. -/

section

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Data.List

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_congr)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {grid : Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

/-- Transporting the original vertex endpoints preserves the exact subdivided lifted-word reading. -/
private theorem cast_read {first last nextFirst nextLast : Fin lifted.vertices.count}
    (walk : SquareRoot.Grid.Walk.Vertex.VertexWalk lifted.vertices lifted.edges first last)
    (firstEq : first = nextFirst) (lastEq : last = nextLast) (newSheet : Fin 2) :
    edges.indexedEdges vertices (included.resplit (walk.castVertices firstEq lastEq).walk
      (lifted.vertices.coordinate_onGrid _)) newSheet =
    edges.indexedEdges vertices (included.resplit walk.walk (lifted.vertices.coordinate_onGrid _)) newSheet := by
  cases firstEq
  cases lastEq
  rfl

/-- The transported original lifted branch loop reads as its retained reference loop on the enlarged grid. -/
private theorem loop_read (index : Data.Index branches) (oldSheet newSheet : Fin
  2) :
    edges.indexedEdges vertices (included.resplit (bank.liftedLoop index oldSheet).walk
      (lifted.vertices.coordinate_onGrid _)) newSheet =
      edges.indexedEdges vertices (included.resplit (bank.rows.get index).reference.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet := by
  change edges.indexedEdges vertices (included.resplit
    ((bank.rows.get index).reference.walk.castEndpoints _ _) _) newSheet = _
  rw [included.resplit_castEndpoints, edges.indexedEdges_castEndpoints]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair

/-- The original subdivided branch pair is the concatenation of its two actual reference loops on opposite incoming
sheets. -/
theorem resplit_indexed {first last : Data.Index branches}
    (pair : Pair bank first last
      sheet) (newSheet : Fin 2) :
    edges.indexedEdges vertices (included.resplit pair.closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet =
      edges.indexedEdges vertices (included.resplit (bank.rows.get first).reference.walk
        (FramedBranchCellBank.baseMember base.bank)) newSheet ++
      edges.indexedEdges vertices (included.resplit (bank.rows.get last).reference.walk
        (FramedBranchCellBank.baseMember base.bank))
        (Branches.BranchCutLifts.otherSheet newSheet) := by
  rw [pair.closed_eq]
  change edges.indexedEdges vertices (included.resplit (pair.outward.walk.append pair.returning.walk) _) _ = _
  rw [included.resplit_append _ _ (lifted.vertices.coordinate_onGrid _) _, edges.indexedEdges_append]
  have target : RootEdgeBank.target edges (included.resplit pair.outward.walk
    (lifted.vertices.coordinate_onGrid _)) newSheet =
      Branches.BranchCutLifts.otherSheet newSheet := by
    rw [pair.outward_eq]
    change RootEdgeBank.target edges (included.resplit ((bank.rows.get
      first).reference.walk.castEndpoints _ _) _) _ = _
    rw [included.resplit_castEndpoints, edges.target_castEndpoints]
    exact bank.resplit_branch_target included edges first newSheet
  rw [target, pair.outward_eq, pair.returning_eq, Inclusion.PairedArea.cast_read,
    Inclusion.PairedArea.loop_read,
    Inclusion.PairedArea.loop_read]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

/-- The two increments per label pair use opposite incoming sheets on the
new grid. These are readings of the original branch loops, not new tours. -/
@[expose] def resplitReadings (bank :
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (newSheet : Fin 2)
    (value : Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (labels : List (Data.Index branches ×
      Data.Index branches)) : List (Gaussian.Basic.Canonical ×
      Gaussian.Basic.Canonical) :=
  labels.map (fun pair =>
    (SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
      (bank.rows.get pair.1).reference.walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet),
     SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
       (bank.rows.get pair.2).reference.walk
       (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
       (Branches.BranchCutLifts.otherSheet newSheet))))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows

/-- The original ordered A/B pairing on the enlarged grid equals its corrected paired-increment area with the actual
reference and prior readings. -/
theorem resplit_pairing {reference : Data.Index branches}
    {labels : List (Data.Index branches ×
      Data.Index branches)}
    {prior : CommonLoop lifted sheet} (rows :
      PairedRows bank reference sheet labels prior)
    (newSheet : Fin 2) (value : Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    RootEdgeBank.target edges (included.resplit prior.walk (lifted.vertices.coordinate_onGrid
      _)) newSheet = newSheet →
    sumFin (fun index : Fin labels.length =>
      Path.BoundaryRibbon.area
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (rows.get index).row.a.closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (rows.get index).row.corrected.walk (lifted.vertices.coordinate_onGrid _)) newSheet))) =
      Path.Paired.Increments.correctedArea
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (bank.rows.get reference).reference.walk
            (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
            (Branches.BranchCutLifts.otherSheet newSheet)))
        (SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
          prior.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
        (Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet
          value labels) := by
  induction rows with
  | nil => intro _; rfl
  | @cons label rest earlier row tail ih =>
      intro closed
      have nextClosed : RootEdgeBank.target edges
          (included.resplit (earlier.append row.a.closed).walk (lifted.vertices.coordinate_onGrid _)) newSheet =
            newSheet := by
        change RootEdgeBank.target edges (included.resplit (earlier.walk.append
          row.a.closed.walk) _) _ = _
        rw [included.resplit_append _ _ (lifted.vertices.coordinate_onGrid _) _,
          RootEdgeBank.target_append edges,
          closed,
            BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.resplit_target
            included edges]
      rw [FiniteSum.Fin.sumFin_succ]
      change Path.BoundaryRibbon.area
        (SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
          row.a.closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
        (SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
          row.corrected.walk (lifted.vertices.coordinate_onGrid _)) newSheet)) +
        (sumFin fun index : Fin rest.length => Path.BoundaryRibbon.area
          (SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
            (tail.get index).row.a.closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
          (SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
            (tail.get index).row.corrected.walk (lifted.vertices.coordinate_onGrid _)) newSheet))) = _
      rw [ih nextClosed]
      have corrected : edges.indexedEdges vertices
          (included.resplit row.corrected.walk (lifted.vertices.coordinate_onGrid _)) newSheet =
          edges.indexedEdges vertices (included.resplit row.b.closed.walk (lifted.vertices.coordinate_onGrid _))
            newSheet ++
          edges.indexedEdges vertices (included.resplit earlier.walk (lifted.vertices.coordinate_onGrid _)) newSheet :=
            by
        rw [row.corrected_eq]
        change edges.indexedEdges vertices (included.resplit (row.b.closed.walk.append earlier.walk) _) _ = _
        rw [included.resplit_append _ _ (lifted.vertices.coordinate_onGrid _) _, edges.indexedEdges_append,
          BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.resplit_target
            included edges]
      have priorValue : SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (earlier.append row.a.closed).walk (lifted.vertices.coordinate_onGrid _)) newSheet) =
          SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
            earlier.walk (lifted.vertices.coordinate_onGrid _)) newSheet) +
          SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
            row.a.closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet) := by
        change SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
          (earlier.walk.append row.a.closed.walk) _) _) = _
        rw [included.resplit_append _ _ (lifted.vertices.coordinate_onGrid _) _, edges.indexedEdges_append]
        rw [closed, SewingRetraction.wordValue_append]
      rw [corrected, SewingRetraction.wordValue_append, priorValue,
        BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.resplit_indexed
        included edges vertices,
        BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Pair.resplit_indexed
          included edges vertices, SewingRetraction.wordValue_append,
          SewingRetraction.wordValue_append]
      rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

/-- Keep the area of every original single-branch excursion. -/
@[expose] def resplitInternalArea (bank :
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (newSheet : Fin 2)
    (value : Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (labels : List (Data.Index branches ×
      Data.Index branches)) : Gaussian :=
  Gaussian.Norm.Sum.Basic.gaussianSum (labels.map (fun pair =>
    Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices (included.resplit (bank.rows.get
      pair.1).reference.walk (BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank)) newSheet) +
    Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices (included.resplit (bank.rows.get
      pair.2).reference.walk (BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank))
      (Branches.BranchCutLifts.otherSheet newSheet))))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- The subdivided original loop product reads as the total of the retained paired increments. -/
theorem resplit_pairs_value (bank :
  BasedBranchBank lifted) (newSheet : Fin 2)
    (value : Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (labels : List (Data.Index branches ×
      Data.Index branches)) :
    SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.loopProduct (labels.flatMap (fun pair => [pair.1, pair.2])))
        (FramedBranchCellBank.baseMember base.bank)) newSheet) =
      Path.Paired.Increments.total (Inclusion.PairedArea.resplitReadings included
        edges vertices bank newSheet value labels) := by
  induction labels with
  | nil => rfl
  | cons pair rest ih =>
      simp only [Flatten.flatMap_cons, List.cons_append, List.nil_append, -eq_self, -iff_self]
      rw [bank.resplit_product_pair included edges vertices, SewingRetraction.wordValue_append,
        SewingRetraction.wordValue_append, ih]
      change _ = (_ + _) + _
      exact (add_assoc _ _ _).symm

/-- The original subdivided loop-product area is the sum of its retained excursion areas and paired-increment polygon
area. -/
theorem resplit_pairs_area (bank :
  BasedBranchBank lifted) (newSheet : Fin 2)
    (value : Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (labels : List (Data.Index branches ×
      Data.Index branches)) :
    Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
      (included.resplit (bank.loopProduct (labels.flatMap (fun pair => [pair.1, pair.2])))
        (FramedBranchCellBank.baseMember base.bank)) newSheet) =
      Inclusion.PairedArea.resplitInternalArea included edges vertices bank newSheet
        value labels +
        Path.IncrementArea.pathArea (Path.Paired.Increments.values
          (Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet
          value labels)) := by
  induction labels with
  | nil => exact (add_zero _).symm
  | cons pair rest ih =>
      simp only [Flatten.flatMap_cons, List.cons_append, List.nil_append, -eq_self, -iff_self]
      rw [bank.resplit_product_pair included edges vertices, Mesh.RetracingWords.wordArea_append,
        Mesh.RetracingWords.wordArea_append,
        SewingRetraction.wordValue_append, ih, bank.resplit_pairs_value included edges vertices]
      simp only [Inclusion.PairedArea.resplitInternalArea,
        Inclusion.PairedArea.resplitReadings, List.map_cons,
        Gaussian.Norm.Sum.Basic.gaussianSum,
        Path.Paired.Increments.values, Path.IncrementArea.pathArea_cons, Path.Paired.Increments.values_total,
        Path.IncrementArea.area_add_right, -eq_self, -iff_self]
      ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

/-- Transporting the retained finite index preserves the exact original Gaussian sum. -/
private theorem sum_cast {first last : Nat} (equal : first = last) (value : Fin first → Gaussian.Basic.Canonical) :
    sumFin value = sumFin (fun index : Fin last => value (Fin.cast equal.symm index)) := by
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea

variable {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet} {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

/-- The actual prepared A/B walks obey the corrected paired-increment
formula on the enlarged grid, with no assumption equating root frames. -/
theorem resplit_pairing (newSheet : Fin 2) (value : Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical) :
    sumFin (fun index : Fin genus =>
      Path.BoundaryRibbon.area
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))) =
      Path.Paired.Increments.correctedArea
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
            (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
          (Branches.BranchCutLifts.otherSheet newSheet))) 0
        (Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet
          value paired.split.pairs) := by
  have actual := paired.rows.resplit_pairing included edges vertices newSheet value rfl
  rw [Inclusion.PairedArea.sum_cast paired.split.count_eq] at actual
  refine (FiniteSum.Fin.sumFin_congr (fun index => ?_)).trans actual
  rw [prepared.a_walk_eq, prepared.b_walk_eq]
  rfl

/-- Exact transported ordered-cycle area accounting. The terminal word
and the reference return remain explicit until their physical comparisons
are paid; no sheet cancellation or zero-area hypothesis is assumed. -/
theorem resplit_area_formula (newSheet : Fin 2) (value : Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical)
    (ending : List (Polygon.Stokes.OrientedEdge vertices.count)) :
    Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
      (included.resplit (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      newSheet ++ ending) +
      sumFin (fun index : Fin genus => Path.BoundaryRibbon.area
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))) =
      Inclusion.PairedArea.resplitInternalArea included edges vertices bank newSheet
        value paired.split.pairs + Mesh.RetracingWords.wordArea value ending +
        Path.BoundaryRibbon.area (Path.Paired.Increments.total
          (Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet
          value paired.split.pairs))
          (SewingRetraction.wordValue value ending +
            SewingRetraction.wordValue value (edges.indexedEdges vertices
            (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
              (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
            (Branches.BranchCutLifts.otherSheet newSheet))) := by
  rw [Mesh.RetracingWords.wordArea_append, bank.resplit_pairs_area included edges vertices,
    bank.resplit_pairs_value included edges vertices, prepared.resplit_pairing included edges vertices]
  have formula := Path.Paired.Increments.formula
    (SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      (Branches.BranchCutLifts.otherSheet newSheet))) 0
    (Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet value
      paired.split.pairs)
  rw [add_zero] at formula
  rw [Path.IncrementArea.area_add_right]
  rw [← formula]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

end
