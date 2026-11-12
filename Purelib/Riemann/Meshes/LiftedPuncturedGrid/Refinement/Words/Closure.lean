module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Paired
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.Anchor
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Data.List.Flatten
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingConnected

/-! # Actual closure and cut support of the retained excursion replacement

Two original branch references exchange sheets twice. The literal earlier-A
prefix therefore returns without a supplied parity or root-closure premise.
The all-sheet comparisons of the retained compiler transfer that actual
return to its cached replacement. Existing indexed-edge and mesh support
laws give the precise closed supported word used by cut retraction.
-/

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.Topology.Chain
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing.SewingConnected

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} (bank : BasedBranchBank lifted)
    {grid : ClearGrid curve.polynomial (Cuts.Ambient curve)}
    (included : Extension.CoordinateInclusion base.bank.grid grid) {frames : RootFrames grid}
    (edges : RootEdgeBank frames)

/-- The two actual original branch references return before the actual remaining resplit word begins. -/
theorem resplit_product_pair_target (first last : Data.Index branches)
    (labels : List (Data.Index branches)) (sheet : Fin 2) :
    RootEdgeBank.target edges (included.resplit (bank.loopProduct (first :: last :: labels))
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet =
      RootEdgeBank.target edges (included.resplit (bank.loopProduct labels)
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet := by
  let member := BasedBranchTours.FramedBranchCellBank.baseMember base.bank
  change RootEdgeBank.target edges (included.resplit ((bank.rows.get first).reference.walk.append
    ((bank.rows.get last).reference.walk.append (bank.loopProduct labels))) member) sheet = _
  rewrite [included.resplit_append _ _ member member, RootEdgeBank.target_append,
    bank.resplit_branch_target included edges first sheet,
    included.resplit_append _ _ member member, RootEdgeBank.target_append,
    bank.resplit_branch_target included edges last (BranchCutLifts.otherSheet sheet),
    BranchCutLifts.otherSheet_other]
  rfl

/-- Any actual ordered list of the original branch pairs returns on its true incoming sheet after resplitting. -/
theorem resplit_paired_target (pairs : List (Data.Index branches × Data.Index branches)) (sheet : Fin 2) :
    RootEdgeBank.target edges (included.resplit
      (bank.loopProduct (pairs.flatMap (fun pair => [pair.1, pair.2])))
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet = sheet := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      change RootEdgeBank.target edges (included.resplit
        (bank.loopProduct (pair.1 :: pair.2 :: rest.flatMap (fun pair => [pair.1, pair.2]))) _) sheet = sheet
      exact (bank.resplit_product_pair_target included edges pair.1 pair.2 _ sheet).trans ih

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCompilation

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original prepared}
    {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {oldSheet annulusSheet stripSheet : Fin 2} {ordered : BasedBranchBank.Ordered oldBank oldSheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} {periods : Paired.PeriodPrograms.Prepared paired}
    {annuli : DependentVector (fun index : Data.Index branches =>
      {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet})}
    {strips : DependentVector (fun index : Data.Index branches =>
      {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
        value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet})}
    {index : Fin genus} (value : retained.PairCompilation oldBank newBank periods annuli strips index)

/-- The retained A replacement has actual fine-edge sheet return, derived from its two original branch references. -/
theorem a_return : RootEdgeBank.target retained.fine.edges value.a.word.replacement oldSheet = oldSheet := by
  let labels := paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'
    (Fin.cast paired.split.count_eq.symm index).isLt
  have source : RootEdgeBank.target retained.fine.edges
      (retained.included.resplit (oldBank.loopProduct (paired.aLabels index))
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet = oldSheet :=
    (oldBank.resplit_product_pair_target retained.included retained.fine.edges labels.1 labels.2 [] oldSheet).trans
      (show RootEdgeBank.target retained.fine.edges (Walk.nil (Cuts.Ambient curve).anchor) oldSheet = oldSheet from rfl)
  exact value.a.replacement_target.trans (value.a.source_target.symm.trans source)

/-- The corrected-B replacement returns after its real reference pair and complete original earlier-A prefix. -/
theorem b_return : RootEdgeBank.target retained.fine.edges value.b.word.replacement oldSheet = oldSheet := by
  let labels := paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'
    (Fin.cast paired.split.count_eq.symm index).isLt
  have source : RootEdgeBank.target retained.fine.edges
      (retained.included.resplit (oldBank.loopProduct (paired.bLabels index))
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet = oldSheet :=
    (oldBank.resplit_product_pair_target retained.included retained.fine.edges labels.1
      paired.split.ending.reference _ oldSheet).trans
      (oldBank.resplit_paired_target retained.included retained.fine.edges
        (paired.split.pairs.take index.val) oldSheet)
  exact value.b.replacement_target.trans (value.b.source_target.symm.trans source)

/-- The SAME cached A replacement indexes a genuine closed fine-mesh word at its actual source sheet. -/
theorem a_closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish
    (retained.fine.edges.indexedEdges retained.fine.vertices value.a.word.replacement oldSheet)
    (BasedBranchBank.anchor retained.fine oldSheet) (BasedBranchBank.anchor retained.fine oldSheet) :=
  retained.fine.edges.indexedEdges_closed retained.fine.vertices value.a.word.replacement
    (BasedBranchTours.FramedBranchCellBank.baseMember retained.fineBase.bank) oldSheet value.a_return

/-- The SAME cached corrected-B replacement indexes a genuine closed word with its entire earlier-A prefix. -/
theorem b_closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish
    (retained.fine.edges.indexedEdges retained.fine.vertices value.b.word.replacement oldSheet)
    (BasedBranchBank.anchor retained.fine oldSheet) (BasedBranchBank.anchor retained.fine oldSheet) :=
  retained.fine.edges.indexedEdges_closed retained.fine.vertices value.b.word.replacement
    (BasedBranchTours.FramedBranchCellBank.baseMember retained.fineBase.bank) oldSheet value.b_return

/-- Every actual A replacement edge belongs to the SAME retained fresh cut patch, up to its original reversal. -/
theorem a_supported : CutPath.Supported (SewnPatch.originalEdges retained.fine.cutPolygon.patch)
    (retained.fine.edges.indexedEdges retained.fine.vertices value.a.word.replacement oldSheet) :=
  CutPath.supported_mono (SkeletonFaceAssignments.indexedWalk_supported retained.fine.mesh
    value.a.word.replacement oldSheet)
    (fun _ member => Standard.TourRetraction.originalEdge_on_cutPatch retained.fine member)

/-- Every actual full corrected-B replacement edge belongs to the SAME retained fresh cut patch. -/
theorem b_supported : CutPath.Supported (SewnPatch.originalEdges retained.fine.cutPolygon.patch)
    (retained.fine.edges.indexedEdges retained.fine.vertices value.b.word.replacement oldSheet) :=
  CutPath.supported_mono (SkeletonFaceAssignments.indexedWalk_supported retained.fine.mesh
    value.b.word.replacement oldSheet)
    (fun _ member => Standard.TourRetraction.originalEdge_on_cutPatch retained.fine member)

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCompilation

end
