module

import Purelib.Algebra.Group.Basic
import Purelib.Data.List.Flatten
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Tactic.Ring

open Purelib.Topology.Surface.Sewing

public section

/-! Match the even terminal cross to the actual original exterior, with
the original compiler's regular integral residual retained exactly. -/

section

open Purelib.Curves
open Purelib.Data
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Data.List
open Purelib.Algebra

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {fine : Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid fine)
  {frames : SquareRoot.Grid.RootFrames fine} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank fine)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal

/-- The resplit ordered branch-product value splits into the actual paired-prefix total and retained ending value. -/
private theorem product_pairs_value (pairs : List (Branches.BranchIsolation.Data.Index branches ×
  Branches.BranchIsolation.Data.Index branches))
    (ending : List (Branches.BranchIsolation.Data.Index branches)) (newSheet : Fin 2) (value :
      Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.loopProduct (pairs.flatMap (fun pair => [pair.1, pair.2]) ++ ending))
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) =
    Path.Paired.Increments.total (PairedArea.resplitReadings included edges
      vertices bank newSheet value pairs) +
      SewingRetraction.wordValue value (edges.indexedEdges vertices (included.resplit
        (bank.loopProduct ending) (BasedBranchTours.FramedBranchCellBank.baseMember
        base.bank)) newSheet) := by
  induction pairs with
  | nil => exact (zero_add _).symm
  | cons pair tail ih =>
      simp only [Flatten.flatMap_cons, List.cons_append, List.nil_append, -eq_self, -iff_self]
      rw [BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.resplit_product_pair
        bank included edges vertices, SewingRetraction.wordValue_append,
        SewingRetraction.wordValue_append, ih]
      simp only [PairedArea.resplitReadings, List.map_cons,
        Path.Paired.Increments.total, -eq_self, -iff_self]
      ring1

/-- The original ordered branch-product value equals its retained paired-prefix total plus the actual ending word value.
-/
theorem resplit_total_value (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.loopProduct ordered.prepared.labels)
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) =
    Path.Paired.Increments.total (PairedArea.resplitReadings included edges
      vertices bank newSheet value paired.split.pairs) +
      SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.loopProduct paired.split.ending.labels)
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) :=
  (congrArg (fun labels => SewingRetraction.wordValue value (edges.indexedEdges vertices
    (included.resplit (bank.loopProduct labels)
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet))
      paired.split.labels_eq).trans
    (ExteriorTotal.product_pairs_value included edges vertices
      paired.split.pairs paired.split.ending.labels newSheet value)

/-- The original factor multiplying the terminal exterior total, zero for an odd ending and the retained
outward-plus-prefix value for an even ending. -/
@[expose] def resplitExteriorFactor (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical) : Gaussian :=
  match paired.split.ending with
  | .odd _ => 0
  | .even first _ => SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.rows.get first).reference.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) +
      Path.Paired.Increments.total (PairedArea.resplitReadings included
        edges vertices bank newSheet value paired.split.pairs)

/-- This uses the literal original exterior walk, not the ordered branch
product. No smallness of that fixed physical boundary is asserted. -/
@[expose] def resplitPhysicalExteriorCorrection (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge
  vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  Path.BoundaryRibbon.area (ExteriorTotal.resplitExteriorFactor (paired :=
    paired) included edges vertices newSheet value)
    (edges.chainValue vertices value (included.resplit base.bank.exterior
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet)

/-- The terminal exterior correction pairs its retained factor with the complete original ordered branch-product value.
-/
theorem resplitExteriorCorrection_total (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count
  → Gaussian.Basic.Canonical) :
    TerminalCorrection.resplitExteriorCorrection (paired := paired)
      included edges vertices newSheet value =
      Path.BoundaryRibbon.area (ExteriorTotal.resplitExteriorFactor (paired
        := paired) included edges vertices newSheet value)
        (SewingRetraction.wordValue value (edges.indexedEdges vertices
          (included.resplit (bank.loopProduct ordered.prepared.labels)
            (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet))
            := by
  rw [ExteriorTotal.resplit_total_value (paired := paired) included edges
    vertices]
  unfold TerminalCorrection.resplitExteriorCorrection
    ExteriorTotal.resplitExteriorFactor
  cases endingEq : paired.split.ending with
  | odd index => exact (Path.IncrementArea.area_zero_left _).symm
  | even first last => rfl

/-- The literal resplit physical exterior value is the original ordered branch-product value plus all retained
regular-loop integrals. -/
theorem resplit_exterior_integral_partition
    (reference : ∀ point, Geometry.Grid.FromStates.ContainsVertex fine point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    {newSheet : Fin 2}
    (compiled : OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices (BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank)
      ordered.prepared.partition newSheet)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    edges.chainValue vertices value (included.resplit base.bank.exterior
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet =
      SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.loopProduct ordered.prepared.labels)
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) +
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value
        occurrence.word) compiled.regulars := by
  have formula :=
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered.resplit_exterior_values
    ordered included edges vertices reference compiled value anti
  have word := congrArg (SewingRetraction.wordValue value) compiled.word_eq
  have comparison := (OrderedBoundary.Ordered.resplit_comparison included
    edges vertices reference ordered).values value anti newSheet
  exact formula.trans (congrArg (fun total => total + Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
    SewingRetraction.wordValue value occurrence.word) compiled.regulars)
    (word.trans comparison))

/-- The only discrepancy in replacing the terminal exterior total by the
physical boundary is the already requested sum of original regular-loop
integrals, multiplied by the retained even-ending factor. -/
theorem resplit_physical_exterior_difference
    (reference : ∀ point, Geometry.Grid.FromStates.ContainsVertex fine point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    {newSheet : Fin 2}
    (compiled : OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices (BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank)
      ordered.prepared.partition newSheet)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      included edges vertices newSheet value -
      TerminalCorrection.resplitExteriorCorrection (paired := paired)
        included edges vertices newSheet value =
    Path.BoundaryRibbon.area (ExteriorTotal.resplitExteriorFactor (paired
      := paired) included edges vertices newSheet value)
      (Geometry.Grid.CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value
        occurrence.word) compiled.regulars) := by
  have physical := ExteriorTotal.resplit_exterior_integral_partition
    included edges vertices reference compiled value anti
  rw [ExteriorTotal.resplitPhysicalExteriorCorrection,
    ExteriorTotal.resplitExteriorCorrection_total, physical,
    Path.IncrementArea.area_add_right,
    Group.add_sub_cancel_left]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal

end
