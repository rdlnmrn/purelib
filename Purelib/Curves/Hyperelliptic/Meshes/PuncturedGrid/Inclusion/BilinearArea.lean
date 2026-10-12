module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! The corrected ordered two-differential identity on the enlarged mesh.
The same finite area formula serves both energy and the first relation;
all branch, terminal and reference contributions remain in its residual. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) {grid :
    Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (newSheet : Fin 2)

/-- This is the full transported residual, not a zero-area assertion. -/
def resplitResidual (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (ending : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)) : Gaussian :=
  Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea included edges vertices bank newSheet
    value paired.split.pairs + Topology.Mesh.RetracingWords.wordArea value ending +
    Path.BoundaryRibbon.area (Path.Paired.Increments.total
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet
      value paired.split.pairs))
      (Topology.Surface.Sewing.SewingRetraction.wordValue value ending +
        Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
        (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet))) -
    Topology.Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices
      (included.resplit (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      newSheet ++ ending)

/-- The actual resplit A/B pairing equals the full transported residual, retaining internal, terminal and reference
contributions. -/
theorem resplit_pairing_eq_residual (value : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical)
    (ending : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)) :
    FiniteSum.Fin.sumFin (fun index : Fin genus => Path.BoundaryRibbon.area
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (edges.indexedEdges vertices
        (included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet))) =
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea.resplitResidual (paired := paired) included edges
        vertices newSheet value ending := by
  have formula := prepared.resplit_area_formula included edges vertices newSheet value ending
  unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea.resplitResidual
  rw [← formula]
  ring1

/-- Polarization on the same actual resplit A/B walks preserves every
physical residual. No intersection tag, change of basis or second mesh is
substituted for the corrected period programs. -/
theorem resplit_bilinear_formula (first second : Topology.Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical)
    (ending : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)) :
    FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Topology.Surface.Sewing.SewingRetraction.wordValue first (edges.indexedEdges vertices
        (included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet) *
      Topology.Surface.Sewing.SewingRetraction.wordValue second (edges.indexedEdges vertices
        (included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet) -
      Topology.Surface.Sewing.SewingRetraction.wordValue first (edges.indexedEdges vertices
        (included.resplit (prepared.bWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet) *
      Topology.Surface.Sewing.SewingRetraction.wordValue second (edges.indexedEdges vertices
        (included.resplit (prepared.aWalk index).closed.walk (lifted.vertices.coordinate_onGrid _)) newSheet)) =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea.resplitResidual (paired := paired) included edges
          vertices newSheet (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first
          second coefficient) ending) := by
  have polarized := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient =>
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea.resplit_pairing_eq_residual prepared included edges
      vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        ending)
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_sum] at polarized
  refine Eq.trans (FiniteSum.Fin.sumFin_congr (fun index => ?_)) polarized
  symm
  exact (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun coefficient
    => by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix])).trans
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_area _ _ _ _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea
