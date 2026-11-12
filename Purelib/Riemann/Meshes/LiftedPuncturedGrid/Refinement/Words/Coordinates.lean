module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Closure
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ClosedReduction
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Paired
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Data.Vector.Dependent.Subtype
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

/-! # Computed fresh-basis coordinates of the actual retained old corrected words

Both original paired owners remain GIVEN on the same retained fine mesh.
The source's395 words and the fresh geometric cut are fixed before this
finite construction. Actual closure/support constructs the new retraction
and intersection coordinates; no word, basis, sign or period agreement is
an input. Every physical loop, face residual and annular regular correction
remains in the final value identity.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (ClosedCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates (Reduction)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Topology.Chain
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

section Inputs

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original prepared}
    {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {oldSheet annulusSheet stripSheet freshSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered oldBank oldSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {periods : Paired.PeriodPrograms.Prepared paired}
    {annuli : DependentVector (fun index : Data.Index branches =>
      {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet})}
    {strips : DependentVector (fun index : Data.Index branches =>
      {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
        value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet})}
    {index : Fin genus} (source : retained.PairCompilation oldBank newBank periods annuli strips index)
    {freshOrdered : BasedBranchBank.Ordered newBank freshSheet}
    {freshPaired : OrderedBranchPairs.Ordered.Paired freshOrdered}
    {fresh : Paired.PeriodPrograms.Prepared freshPaired} (basis : fresh.GeometricBasis)
    (boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences retained.fine.mesh.triangulation.faces))
    (factory : boundary = retained.fine.boundaryComponents)

/-- The actual old A/full corrected-B indexed word caches, true incidence certificates and computed fresh reductions. -/
@[expose] def PairCoordinates : Type _ :=
  (aWord : {word : List (OrientedEdge retained.fine.vertices.count) //
    word = retained.fine.edges.indexedEdges retained.fine.vertices source.a.word.replacement oldSheet ∧
    CutPath.Supported (SewingConnected.SewnPatch.originalEdges retained.fine.cutPolygon.patch) word ∧
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
      (BasedBranchBank.anchor retained.fine oldSheet) (BasedBranchBank.anchor retained.fine oldSheet)}) ×
  (bWord : {word : List (OrientedEdge retained.fine.vertices.count) //
    word = retained.fine.edges.indexedEdges retained.fine.vertices source.b.word.replacement oldSheet ∧
    CutPath.Supported (SewingConnected.SewnPatch.originalEdges retained.fine.cutPolygon.patch) word ∧
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
      (BasedBranchBank.anchor retained.fine oldSheet) (BasedBranchBank.anchor retained.fine oldSheet)}) ×
  (_a : {value : Reduction basis aWord.val oldSheet aWord.property.2.1 aWord.property.2.2 boundary factory //
    value = ClosedCoordinates.reduce basis aWord.val oldSheet aWord.property.2.1 aWord.property.2.2 boundary factory}) ×
  {value : Reduction basis bWord.val oldSheet bWord.property.2.1 bWord.property.2.2 boundary factory //
    value = ClosedCoordinates.reduce basis bWord.val oldSheet bWord.property.2.1 bWord.property.2.2 boundary factory}

/-- Materialize each retained source word once and run the ORIGINAL coordinate and physical-loop constructors once.

The original395 source result, fresh geometric basis and whole boundary
cache stay separate. The fresh basis sheet is independent of oldSheet;
no Frame or Owner identification is inferred from their common coordinate.
-/
def pairCoordinates : PairCoordinates source basis boundary factory :=
  let aWord := retained.fine.edges.indexedEdges retained.fine.vertices source.a.word.replacement oldSheet
  let bWord := retained.fine.edges.indexedEdges retained.fine.vertices source.b.word.replacement oldSheet
  let a : {word : List (OrientedEdge retained.fine.vertices.count) //
      word = retained.fine.edges.indexedEdges retained.fine.vertices source.a.word.replacement oldSheet ∧
      CutPath.Supported (SewingConnected.SewnPatch.originalEdges retained.fine.cutPolygon.patch) word ∧
      PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
        (BasedBranchBank.anchor retained.fine oldSheet) (BasedBranchBank.anchor retained.fine oldSheet)} :=
    ⟨aWord, rfl, source.a_supported, source.a_closed⟩
  let b : {word : List (OrientedEdge retained.fine.vertices.count) //
      word = retained.fine.edges.indexedEdges retained.fine.vertices source.b.word.replacement oldSheet ∧
      CutPath.Supported (SewingConnected.SewnPatch.originalEdges retained.fine.cutPolygon.patch) word ∧
      PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
        (BasedBranchBank.anchor retained.fine oldSheet) (BasedBranchBank.anchor retained.fine oldSheet)} :=
    ⟨bWord, rfl, source.b_supported, source.b_closed⟩
  let aReduction := ClosedCoordinates.reduce basis a.val oldSheet a.property.2.1 a.property.2.2 boundary factory
  let bReduction := ClosedCoordinates.reduce basis b.val oldSheet b.property.2.1 b.property.2.2 boundary factory
  ⟨a, b, ⟨aReduction, rfl⟩, ⟨bReduction, rfl⟩⟩

namespace PairCoordinates

variable {source basis boundary factory} (value : PairCoordinates source basis boundary factory)

/-- The actual once-materialized old A replacement word on its original source sheet. -/
@[expose] def aWord : List (OrientedEdge retained.fine.vertices.count) := value.1.val

/-- The actual once-materialized full corrected-B replacement word, including its whole earlier-A prefix. -/
@[expose] def bWord : List (OrientedEdge retained.fine.vertices.count) := value.2.1.val

/-- The SAME original A source-word indexing factory. -/
theorem aWord_eq : value.aWord = retained.fine.edges.indexedEdges retained.fine.vertices
    source.a.word.replacement oldSheet := value.1.property.1

/-- The SAME original full corrected-B source-word indexing factory. -/
theorem bWord_eq : value.bWord = retained.fine.edges.indexedEdges retained.fine.vertices
    source.b.word.replacement oldSheet := value.2.1.property.1

/-- The complete actual A cut retraction, fresh intersection coefficients and physical loop cache. -/
@[expose] def a : Reduction basis value.aWord oldSheet value.1.property.2.1 value.1.property.2.2 boundary factory :=
  value.2.2.1.val

/-- The complete actual corrected-B cut retraction, fresh coefficients and physical loop cache. -/
@[expose] def b : Reduction basis value.bWord oldSheet value.2.1.property.2.1 value.2.1.property.2.2 boundary factory :=
  value.2.2.2.val

/-- The whole A reduction is exactly its single original coordinate/loop construction on this SAME cached word. -/
theorem a_eq : value.a = ClosedCoordinates.reduce basis value.aWord oldSheet
    value.1.property.2.1 value.1.property.2.2 boundary factory := value.2.2.1.property

/-- The whole corrected-B reduction is exactly its single original construction on this SAME cached full word. -/
theorem b_eq : value.b = ClosedCoordinates.reduce basis value.bWord oldSheet
    value.2.1.property.2.1 value.2.1.property.2.2 boundary factory := value.2.2.2.property

/-- The old A value is its computed fresh corrected-basis combination plus every physical and face remainder. -/
theorem a_values (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainValue retained.fine.vertices reading
      (retained.included.resplit source.aClosed.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet =
      value.a.coordinates.periodValue reading +
        gaussianSum (value.a.loops.rows.map (fun entry => (entry.1 : Canonical) *
          SewingRetraction.wordValue reading entry.2)) + value.a.coordinates.faceResidual reading +
        CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue reading occurrence.word)
          source.a.compiled.regulars := by
  have indexed : retained.fine.edges.chainValue retained.fine.vertices reading source.a.word.replacement oldSheet =
      SewingRetraction.wordValue reading value.aWord :=
    (congrArg (SewingRetraction.wordValue reading) value.aWord_eq).symm
  exact (PairCompilation.a_values source reading anti).trans
    (congrArg (fun amount => amount + CellBoundary.sumValues
      (fun occurrence => SewingRetraction.wordValue reading occurrence.word) source.a.compiled.regulars)
        (indexed.trans (value.a.value_eq reading anti)))

/-- Full corrected B reduces against the GIVEN fresh basis with actual computed coefficients and all remainders. -/
theorem b_values (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainValue retained.fine.vertices reading
      (retained.included.resplit source.bClosed.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet =
      value.b.coordinates.periodValue reading +
        gaussianSum (value.b.loops.rows.map (fun entry => (entry.1 : Canonical) *
          SewingRetraction.wordValue reading entry.2)) + value.b.coordinates.faceResidual reading +
        CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue reading occurrence.word)
          source.b.compiled.regulars := by
  have indexed : retained.fine.edges.chainValue retained.fine.vertices reading source.b.word.replacement oldSheet =
      SewingRetraction.wordValue reading value.bWord :=
    (congrArg (SewingRetraction.wordValue reading) value.bWord_eq).symm
  exact (PairCompilation.b_values source reading anti).trans
    (congrArg (fun amount => amount + CellBoundary.sumValues
      (fun occurrence => SewingRetraction.wordValue reading occurrence.word) source.b.compiled.regulars)
        (indexed.trans (value.b.value_eq reading anti)))

end PairCoordinates

end Inputs

section Family

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original prepared}
    {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {oldSheet annulusSheet stripSheet freshSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered oldBank oldSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {periods : Paired.PeriodPrograms.Prepared paired}
    (sourceRows : retained.PairedWords oldBank newBank periods annulusSheet stripSheet)
    {freshOrdered : BasedBranchBank.Ordered newBank freshSheet}
    {freshPaired : OrderedBranchPairs.Ordered.Paired freshOrdered}
    {fresh : Paired.PeriodPrograms.Prepared freshPaired} (basis : fresh.GeometricBasis)

/-- One actual boundary cache and all computed old-A/full-B coordinate rows on the GIVEN fresh corrected basis. -/
@[expose] def Coordinates : Type _ :=
  (boundary : {value : BoundaryCycleDecomposition
    (triangleEdgeOccurrences retained.fine.mesh.triangulation.faces) //
    value = retained.fine.boundaryComponents}) ×
  DependentVector (fun index : Fin genus =>
    {value : PairCoordinates (PairedWords.row sourceRows index) basis boundary.val boundary.property //
      value = pairCoordinates (PairedWords.row sourceRows index) basis boundary.val boundary.property})

/-- Construct the actual boundary decomposition once and each original source-row reduction once.

The GIVEN395 source rows and fresh prepared/basis owners remain fixed.
Every bounded row computes its A/B intersections with that same fresh cut;
independent invocations are independent finite runs, not memoized queries.
-/
def coordinates : Coordinates sourceRows basis :=
  let boundary := retained.fine.boundaryComponents
  let rows := DependentVector.ofFnWithEq (fun index : Fin genus =>
    pairCoordinates (PairedWords.row sourceRows index) basis boundary rfl)
  ⟨⟨boundary, rfl⟩, rows⟩

namespace Coordinates

variable {sourceRows basis} (value : Coordinates sourceRows basis)

/-- The SAME whole physical boundary decomposition shared by every old-A/full-B reduction. -/
@[expose] def boundary : BoundaryCycleDecomposition
    (triangleEdgeOccurrences retained.fine.mesh.triangulation.faces) := value.1.val

/-- The boundary is exactly one original construction on the SAME fine mesh, not a guessed collection of loops. -/
theorem boundary_eq : value.boundary = retained.fine.boundaryComponents := value.1.property

/-- Read the SAME retained old-A/full-B row with its coefficient vectors, loop multiples and face residuals. -/
@[expose] def row (index : Fin genus) :
    PairCoordinates (PairedWords.row sourceRows index) basis value.boundary value.boundary_eq := (value.2.get index).val

/-- Every row is its single actual construction on the GIVEN source row, fresh basis and SAME boundary cache. -/
theorem row_eq (index : Fin genus) : value.row index =
    pairCoordinates (PairedWords.row sourceRows index) basis value.boundary value.boundary_eq :=
  (value.2.get index).property

end Coordinates

end Family

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

end
