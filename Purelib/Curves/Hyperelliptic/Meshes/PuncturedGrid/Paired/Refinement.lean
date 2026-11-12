module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.Anchor
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Periods
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.Anchor
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Transport
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Topology.Polygon.Stokes

/-! # Same original paired periods on a retained clearance-refined grid

The original A and full corrected-B periods select their refined frames
through actual whole-frame prefix preservation. Joint coordinate/Owner
transport to the ambient anchor retains the whole closed preparation and
therefore its exact ordered indexed word, including the earlier-A B prefix.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (ClearanceRefinement)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement (PeriodFaces)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
variable {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
variable (prepared : PeriodPrograms.Prepared paired)
variable {patches : List (ContinuedNeighborhood curve.polynomial count)}
variable {clearance : ClearancePreparation base.bank.toBranchCellBank patches}
variable (retained : ClearanceRefinement lifted clearance)

/-- Select one real fine-grid frame and face cache from the GIVEN original prepared A period. -/
def aPeriodFaces (index : Fin genus) :
    PeriodFaces retained (anchor lifted sheet) (prepared.aWalk index) :=
  retained.periodFaces (anchor lifted sheet) (prepared.aWalk index)

/-- Select one real fine-grid frame and face cache from the GIVEN full corrected-B period. -/
def bPeriodFaces (index : Fin genus) :
    PeriodFaces retained (anchor lifted sheet) (prepared.bWalk index) :=
  retained.periodFaces (anchor lifted sheet) (prepared.bWalk index)

/-- The original A face cache reads the exact resplit two-label word at the ambient anchor.

The whole original closed preparation is jointly transported through the
actual anchor coordinate and Owner HEq. Scalar endpoint transport only
then preserves the original indexed word. No root relation follows from a
coordinate or label comparison.
-/
theorem a_refined_word (index : Fin genus)
    (kept : PeriodFaces retained (anchor lifted sheet) (prepared.aWalk index)) :
    kept.view.geometry.indexed = retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit (bank.loopProduct (paired.aLabels index))
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet := by
  have actual := kept.indexed_castBase (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet) (prepared.aAtAnchor index) (prepared.aAtAnchor_heq index)
  have walk := congrArg (fun walk => retained.fine.edges.indexedEdges retained.fine.vertices
    (retained.included.resplit walk (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      (lifted.vertices.sheet (anchor lifted sheet))) (prepared.aAtAnchor_walk index)
  have selected : lifted.vertices.sheet (anchor lifted sheet) = sheet :=
    lifted.vertices.sheet_index _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank) sheet
  exact (actual.trans walk).trans (congrArg (retained.fine.edges.indexedEdges retained.fine.vertices
    (retained.included.resplit (bank.loopProduct (paired.aLabels index))
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))) selected)

/-- The original B face cache reads its full original B pair and every earlier-A pair, in their retained order.

The complete corrected preparation and operational root return are retained
by the original bAtAnchor whole transport. This does not replace corrected B
by its reference bridge or infer any independent homology realization.
-/
theorem b_refined_word (index : Fin genus)
    (kept : PeriodFaces retained (anchor lifted sheet) (prepared.bWalk index)) :
    kept.view.geometry.indexed = retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit (bank.loopProduct (paired.bLabels index))
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet := by
  have actual := kept.indexed_castBase (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet) (prepared.bAtAnchor index) (prepared.bAtAnchor_heq index)
  have walk := congrArg (fun walk => retained.fine.edges.indexedEdges retained.fine.vertices
    (retained.included.resplit walk (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      (lifted.vertices.sheet (anchor lifted sheet))) (prepared.bAtAnchor_walk index)
  have selected : lifted.vertices.sheet (anchor lifted sheet) = sheet :=
    lifted.vertices.sheet_index _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank) sheet
  exact (actual.trans walk).trans (congrArg (retained.fine.edges.indexedEdges retained.fine.vertices
    (retained.included.resplit (bank.loopProduct (paired.bLabels index))
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))) selected)

/-- Reading any actual supplied cochain preserves the same transported original A word. -/
theorem a_refined_value (index : Fin genus)
    (kept : PeriodFaces retained (anchor lifted sheet) (prepared.aWalk index))
    (valuation : Topology.Polygon.Stokes.OrientedEdge retained.fine.vertices.count → Data.Gaussian.Basic.Canonical) :
    wordValue valuation kept.view.geometry.indexed = wordValue valuation
      (retained.fine.edges.indexedEdges retained.fine.vertices
        (retained.included.resplit (bank.loopProduct (paired.aLabels index))
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet) :=
  congrArg (wordValue valuation) (prepared.a_refined_word retained index kept)

/-- Reading any actual supplied cochain preserves the full corrected-B ordered word. -/
theorem b_refined_value (index : Fin genus)
    (kept : PeriodFaces retained (anchor lifted sheet) (prepared.bWalk index))
    (valuation : Topology.Polygon.Stokes.OrientedEdge retained.fine.vertices.count → Data.Gaussian.Basic.Canonical) :
    wordValue valuation kept.view.geometry.indexed = wordValue valuation
      (retained.fine.edges.indexedEdges retained.fine.vertices
        (retained.included.resplit (bank.loopProduct (paired.bLabels index))
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet) :=
  congrArg (wordValue valuation) (prepared.b_refined_word retained index kept)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
