module
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-! Separate the original terminal correction into the reference two-sheet
sum and the even-degree physical exterior total. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {fine : Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid fine)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames fine} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank fine)

/-- The retained resplit reference-loop correction summed over both original sheets.

Its ribbon pairs the preceding original paired total with the actual two-sheet reference word values. -/
@[expose] def resplitReferenceCorrection (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count
  → Gaussian.Basic.Canonical) : Gaussian :=
  Path.BoundaryRibbon.area (Path.Paired.Increments.total
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet value
    paired.split.pairs))
    (Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
      (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) +
      Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
        (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet)))

/-- The odd ending has no exterior-total cross. In even degree the full
ending increment is retained, not replaced by a refinement-small term. -/
@[expose] def resplitExteriorCorrection (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count
  → Gaussian.Basic.Canonical) : Gaussian :=
  let total := Path.Paired.Increments.total (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitReadings
    included edges vertices bank newSheet value paired.split.pairs)
  match paired.split.ending with
  | .odd _ => 0
  | .even first last =>
      let outward := Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get first).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet)
      let ending := Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.loopProduct [first, last])
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet)
      Path.BoundaryRibbon.area (outward + total) (total + ending)

/-- The original terminal correction splits into its two-sheet reference correction and retained even-ending exterior
correction. -/
theorem resplitEndCorrection_split (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included edges vertices
      newSheet value =
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection (paired := paired)
        included edges vertices newSheet value +
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
        included edges vertices newSheet value := by
  have empty (incoming : Fin 2) : edges.indexedEdges vertices
      (included.resplit (bank.loopProduct [])
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) incoming = []
        := rfl
  unfold Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection
  cases endingEq : paired.split.ending with
  | odd index =>
      rw [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.labels,
        Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.resplit_product_cons
        bank included edges vertices, empty, Purelib.Data.List.Append.append_nil]
      rfl
  | even first last =>
      dsimp only [-eq_self, -iff_self, Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.reference,
        Hyperelliptic.Meshes.Newton.OrderedBranchPolygons.terminalCross]
      rw [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.labels,
        Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.resplit_product_pair
        bank included edges vertices, empty, Purelib.Data.List.Append.append_nil,
        Topology.Surface.Sewing.SewingRetraction.wordValue_append]
      have scalar (total outward returning referenceReturn : Gaussian.Basic.Canonical) :
          Path.BoundaryRibbon.area total (outward + returning + referenceReturn) + Path.BoundaryRibbon.area outward
            returning =
            Path.BoundaryRibbon.area total (outward + referenceReturn) + Path.BoundaryRibbon.area (outward + total)
              (total + (outward + returning)) := by
        unfold Path.BoundaryRibbon.area
        simp only [-eq_self, -iff_self, Gaussian.Basic.conj_add]
        ring1
      exact scalar _ _ _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
