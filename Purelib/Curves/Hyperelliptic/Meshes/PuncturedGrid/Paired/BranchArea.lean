module
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations
public import Purelib.Integration.Path.Paired.Increments
import Purelib.Approximation.Gaussian.Equivalence
import Init.Data.Fin.Basic
import Init.Data.Fin.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Closure
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid

open Purelib.Integration.Path

open Purelib.Integration.Path.Paired

open Purelib.Riemann

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedGridPeriodPrograms

open Purelib.RootIsolation.SquareRoot.Grid.Walk

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-!
# Corrected paired branch walks and their complete increment areas

Each A walk uses two consecutive retained branches. Each corrected B walk
is the actual reference pair followed by the already constructed A prefix.
The finite area identity reads these very root-closed words and retains all
internal one-branch excursions and physical terminal terms.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Mesh.RetracingWords (wordArea wordArea_append)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Pair
  anchor)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Integration.Path.IncrementArea hiding Gaussian
open Purelib.Integration.Path.BoundaryRibbon (area)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}

/-- An actual lifted vertex walk closed at the retained branch bank's original common anchor and sheet. -/
abbrev CommonLoop (lifted : Meshes.LiftedPuncturedGrid base) (sheet : Fin 2) :=
  Vertex.VertexWalk lifted.vertices lifted.edges (BasedBranchBank.anchor lifted sheet) (BasedBranchBank.anchor lifted
    sheet)

set_option genInjectivity false in
/-- The actual consecutive-branch A pair and reference B pair with its retained earlier-A prefix.

The corrected B walk is exactly the original reference pair followed by that supplied prefix. -/
structure PairedRow (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (reference : BranchIsolation.Data.Index
  branches) (sheet : Fin 2)
    (labels : BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches) (prior :
      CommonLoop lifted sheet) where
  /-- The retained original A pair, preparation or face assignments. -/ a : BasedBranchBank.Pair bank labels.1 labels.2
    sheet
  /-- The retained original B pair, prepared walk or face assignments. -/ b : BasedBranchBank.Pair bank labels.1
    reference sheet
  /-- The actual root-closed B walk with the retained earlier-A prefix. -/ corrected :
    CommonLoop lifted sheet
  /-- The corrected walk is exactly the original B pair followed by the retained prior walk. -/ corrected_eq : corrected
    = b.closed.append prior

constructive_injectivity PairedRow

namespace PairedRow

variable {bank : BasedBranchBank
  lifted} {reference : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}
  {labels : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {prior :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet}

/-- Cache the actual consecutive-branch and reference pairs, appending the supplied original prior A prefix to the
corrected B walk. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (reference : BranchIsolation.Data.Index
  branches) (sheet : Fin 2)
    (labels : BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches) (prior :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet labels prior :=
  let a := bank.pair labels.1 labels.2 sheet
  let b := bank.pair labels.1 reference sheet
  ⟨a, b, b.closed.append prior, rfl⟩

/-- Read the actual outward and returning leg values of the retained A pair. -/
@[expose] def reading (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet
  labels prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    Gaussian × Gaussian := (SewingRetraction.wordValue value row.a.outward.indexed, SewingRetraction.wordValue value
      row.a.returning.indexed)

/-- The retained A-pair value is the sum of its exact outward and returning leg values. -/
theorem a_value (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet labels
  prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    SewingRetraction.wordValue value row.a.closed.indexed = (row.reading value).1 + (row.reading value).2 := by
  rw [row.a.closed_eq]
  exact SewingRetraction.wordValue_append value _ _

/-- The corrected B value retains the first actual branch leg, reference leg on the exchanged sheet and complete prior A
prefix. -/
theorem b_value (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet labels
  prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    SewingRetraction.wordValue value row.corrected.indexed = (row.reading value).1 +
      SewingRetraction.wordValue value (lifted.edges.indexedEdges lifted.vertices (bank.rows.get
        reference).reference.walk (BranchCutLifts.otherSheet sheet)) +
      SewingRetraction.wordValue value prior.indexed := by
  rw [row.corrected_eq]
  change SewingRetraction.wordValue value (row.b.closed.indexed ++ prior.indexed) = _
  rw [SewingRetraction.wordValue_append, row.b.indexed, SewingRetraction.wordValue_append]
  change _ = SewingRetraction.wordValue value row.a.outward.indexed + _ + _
  rw [row.a.outward_eq, BasedBranchBank.liftedLoop_indexed]

/-- The actual A-pair area retains both original leg areas and their exact cross term. -/
theorem a_area (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet labels
  prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    RetracingWords.wordArea value row.a.closed.indexed = RetracingWords.wordArea value row.a.outward.indexed +
      RetracingWords.wordArea value row.a.returning.indexed +
      BoundaryRibbon.area (row.reading value).1 (row.reading value).2 := by
  rw [row.a.closed_eq]
  exact RetracingWords.wordArea_append value _ _

set_option genInjectivity false in
/-- The A and corrected B programs both consume their original certified root-closed walks. No new branch isolation or
sheet choice is performed. -/
structure Prepared (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet
  labels prior) (source : Differentials.Basic.Differential genus) where
  /-- The retained original A pair, preparation or face assignments. -/ a : row.a.Prepared source
  /-- The retained original B pair, prepared walk or face assignments. -/ b : PreparedGridPeriodPrograms.PeriodWalk
    base.bank.grid (lifted.vertices.coordinate (BasedBranchBank.anchor lifted sheet))
    (lifted.vertices.owner lifted.frames (BasedBranchBank.anchor lifted sheet)) source
  /-- The prepared B program consumes exactly the original corrected root-closed walk. -/ b_walk_eq : b.closed.walk =
    row.corrected.walk

constructive_injectivity Prepared

/-- Prepare the actual A and corrected B walks on their original retained root owners. -/
@[expose] def prepare (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet
  labels prior) (source : Differentials.Basic.Differential genus) :
  Prepared row source :=
  let reference := (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (lifted.vertices.coordinate_onGrid
    (BasedBranchBank.anchor lifted sheet))).toLoop
  ⟨row.a.prepare source, PeriodWalk.ofClosed (row.corrected.rootClosed reference) source, rfl⟩

namespace Prepared

variable {row : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet
  labels prior} {source : Differential genus}

set_option genInjectivity false in
/-- The actual A and corrected-B face assignments with the original B segment cache and indexed-word readback. -/
structure Faces (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow.Prepared row source)
  where
  /-- The retained original A pair, preparation or face assignments. -/ a : prepared.a.Faces
  /-- The cached actual covered-segment bank of the original corrected B program. -/ bSegments :
    PeriodSegmentBanks.SegmentBank prepared.b
  /-- The retained original B pair, prepared walk or face assignments. -/ b : FramedPuncturedGrid.OwnerWalkFaces
    lifted.mesh prepared.b.closed.walk
    (lifted.vertices.owner lifted.frames (BasedBranchBank.anchor lifted sheet))
  /-- The retained B face assignments have exactly the corrected walk's original indexed edge word. -/ b_indexed :
    b.geometry.indexed = row.corrected.indexed

constructive_injectivity Faces

/-- Cache the original corrected-B covered segments and attach face geometry on its retained starting owner. -/
@[expose] def faces (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow.Prepared row
  source) : Faces prepared :=
  let segments := SegmentBank.build prepared.b
  let geometry := OwnerWalkFaces.ofSheet lifted.mesh prepared.b.closed.walk
    (lifted.vertices.coordinate_onGrid (BasedBranchBank.anchor lifted sheet)) (lifted.vertices.sheet
      (BasedBranchBank.anchor lifted sheet))
    ⟨NamedEquivalent.refl _⟩
  ⟨prepared.a.faces, segments, geometry, geometry.indexed_eq.trans
    ((congrArg (fun walk => lifted.edges.indexedEdges lifted.vertices walk (lifted.vertices.sheet
      (BasedBranchBank.anchor lifted sheet)))
      prepared.b_walk_eq).trans row.corrected.indexed_eq.symm)⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow.Prepared
/-- Build face-domain comparisons using the exact original corrected-B segment and parent caches. -/
@[expose] def Faces.bComparisons {prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow.Prepared row source} (faces :
  Faces prepared)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (differential :
      Differentials.Basic.Differential genus) :=
  faces.b.comparisons faces.bSegments.pieces domains differential 0 (faces.bSegments.parentCaches differential)

/-- The retained B comparisons use exactly the original prepared program's ordered parent list recast to the supplied
differential. -/
theorem Faces.b_parents {prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow.Prepared row
  source} (faces : Faces prepared)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (differential :
      Differentials.Basic.Differential genus) :
    Comparisons.parents differential 0
      (faces.b.assign faces.bSegments.pieces) (faces.bComparisons domains differential) =
      prepared.b.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential) :=
  (faces.b.comparisons_parents faces.bSegments.pieces domains differential 0 (faces.bSegments.parentCaches
    differential)).trans
    (faces.bSegments.parentCaches_parents differential)

end Prepared

end PairedRow

set_option genInjectivity false in
/-- Prefixes are indexed by the actual concatenation of earlier A walks. The recursive row cache therefore carries every
B shear certificate. -/
inductive PairedRows (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (reference : BranchIsolation.Data.Index
  branches) (sheet : Fin 2) :
    List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches) →
      CommonLoop lifted sheet → Type
  /-- An empty paired-row bank retains its actual prior A prefix. -/ | nil (prior) :
    PairedRows bank reference sheet [] prior
  /-- Retain one actual paired row and the tail indexed by the prior prefix extended with that row's original A walk. -/
    | cons {labels rest prior} (row : PairedRow bank
    reference sheet labels prior)
      (tail : PairedRows bank reference sheet rest
        (prior.append row.a.closed)) :
      PairedRows bank reference sheet (labels ::
        rest) prior

constructive_injectivity PairedRows

namespace PairedRows

variable {bank : BasedBranchBank
  lifted} {reference : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}
  {labels : List (Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} {prior :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet}

set_option genInjectivity false in
/-- An indexed retained paired row together with its exact earlier-A prefix. -/
structure Entry (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (reference : BranchIsolation.Data.Index branches)
  (sheet : Fin 2)
    (labels : BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches) where
  /-- The actual retained concatenation of all earlier A walks. -/ prior :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet
  /-- The original paired row indexed by this exact retained prefix. -/ row :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet labels prior

constructive_injectivity Entry

/-- Read the actual paired row and its retained earlier-A prefix at the supplied bounded label index. -/
@[expose] def get : {labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)} →
    {prior : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior →
    (index : Fin labels.length) → Entry bank
      reference sheet labels[index.val]
  | _, _, .nil _, index => Fin.elim0 index
  | first :: rest, prior, .cons row tail, index =>
      Purelib.Data.Fin.casesDependent
        (motive := fun position : Fin ((first :: rest).length) =>
          Entry bank reference sheet
            ((first :: rest)[position.val]'position.isLt))
        ⟨prior, row⟩
        (fun position => get tail
          position) index

/-- Construct the ordered paired-row bank while retaining the exact cumulative original A prefix at each row. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (reference : BranchIsolation.Data.Index
  branches) (sheet : Fin 2) :
    (labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)) →
    (prior : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior
  | [], prior => .nil prior
  | labels :: rest, prior =>
      let row := Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow.build bank reference sheet labels
        prior
      .cons row (build bank reference
        sheet rest (prior.append row.a.closed))
termination_by structural labels _ => labels

/-- Read the ordered actual outward and returning leg values of every retained paired row. -/
@[expose] def readings (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    {labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)} → {prior :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior → List
      (Gaussian × Gaussian)
  | _, _, .nil _ => []
  | _, _, .cons row tail => row.reading value ::
    readings value tail

/-- Concatenate the actual original closed A words in retained row order. -/
@[expose] def word : {labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)} →
    {prior : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior → List
      (Stokes.OrientedEdge lifted.vertices.count)
  | _, _, .nil _ => []
  | _, _, .cons row tail => row.a.closed.indexed ++
    word tail

/-- Sum both actual one-branch leg areas in every retained A row. -/
@[expose] def internalArea (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    {labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)} → {prior :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior → Gaussian
  | _, _, .nil _ => 0
  | _, _, .cons row tail => RetracingWords.wordArea value row.a.outward.indexed + RetracingWords.wordArea value
    row.a.returning.indexed +
    internalArea value tail

/-- Sum the actual bilinear areas of each original A value with its corrected B value. -/
@[expose] def correctedArea (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    {labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)} → {prior :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior → Gaussian
  | _, _, .nil _ => 0
  | _, _, .cons row tail => BoundaryRibbon.area (SewingRetraction.wordValue value row.a.closed.indexed)
    (SewingRetraction.wordValue value row.corrected.indexed) +
    correctedArea value tail

/-- The complete retained A-word value equals the total of its actual paired leg readings. -/
theorem word_value (rows : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet
  labels prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    SewingRetraction.wordValue value rows.word = Increments.total (rows.readings value) := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
    rw [word, SewingRetraction.wordValue_append,
      row.a_value value, ih]; rfl

/-- The actual corrected-pair area reads back the finite paired-increment formula with the retained reference and
prior-prefix values. -/
theorem correctedArea_eq (rows : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference
  sheet labels prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    rows.correctedArea value = Increments.correctedArea
      (SewingRetraction.wordValue value (lifted.edges.indexedEdges lifted.vertices (bank.rows.get
        reference).reference.walk (BranchCutLifts.otherSheet sheet)))
      (SewingRetraction.wordValue value prior.indexed) (rows.readings value) := by
  induction rows with
  | nil => rfl
  | @cons label rest earlier row tail ih =>
      rw [correctedArea, row.a_value value,
        row.b_value value, ih]
      change _ + Increments.correctedArea _ (SewingRetraction.wordValue value (earlier.indexed ++ row.a.closed.indexed))
        _ = _
      rw [SewingRetraction.wordValue_append, row.a_value value]
      rfl

/-- The retained corrected-pair area equals the complete finite indexed sum over its actual rows. -/
theorem correctedArea_sum (rows : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference
  sheet labels prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    rows.correctedArea value = FiniteSum.Fin.sumFin (fun index : Fin labels.length =>
      BoundaryRibbon.area (SewingRetraction.wordValue value (rows.get index).row.a.closed.indexed)
        (SewingRetraction.wordValue value (rows.get index).row.corrected.indexed)) := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
      rw [correctedArea,
        FiniteSum.Fin.sumFin_succ]
      exact congrArg (BoundaryRibbon.area (SewingRetraction.wordValue value row.a.closed.indexed)
        (SewingRetraction.wordValue value row.corrected.indexed) + ·) ih

/-- The original complete A-word area splits into actual internal leg areas and the polygon area of their ordered
totals. -/
theorem word_area (rows : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet
  labels prior) (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) :
    RetracingWords.wordArea value rows.word = rows.internalArea value + IncrementArea.pathArea (Increments.values
      (rows.readings value)) := by
  induction rows with
  | nil => exact (add_zero _).symm
  | cons row tail ih =>
      rw [word, RetracingWords.wordArea_append,
        row.a_area value, ih, row.a_value value, tail.word_value value]
      simp only [internalArea,
        readings, Increments.values,
        IncrementArea.pathArea_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Increments.values_total,
        IncrementArea.area_add_left, IncrementArea.area_add_right, -eq_self, -iff_self]
      ring1

/-- The concatenated retained A words are exactly the original ordered branch-loop product on its actual sheet. -/
theorem word_eq (rows : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet
  labels prior) :
    rows.word = lifted.edges.indexedEdges lifted.vertices (bank.loopProduct (labels.flatMap (fun pair => [pair.1,
      pair.2]))) sheet := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
      simp only [Purelib.Data.List.Flatten.flatMap_cons, List.cons_append, List.nil_append, -eq_self, -iff_self]
      rw [bank.loopProduct_pair_indexed _ _ _ sheet row.a]
      exact congrArg (row.a.closed.indexed ++ ·) ih

/-- Appending remaining original branch labels preserves the exact retained A prefix word and arriving sheet. -/
theorem word_eq_append (rows : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference
  sheet labels prior) (ending : List (BranchIsolation.Data.Index branches)) :
    lifted.edges.indexedEdges lifted.vertices (bank.loopProduct (labels.flatMap (fun pair => [pair.1, pair.2]) ++
      ending)) sheet =
      rows.word ++ lifted.edges.indexedEdges lifted.vertices (bank.loopProduct ending) sheet := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
      simp only [Purelib.Data.List.Flatten.flatMap_cons, List.cons_append, List.nil_append, -eq_self, -iff_self]
      rw [bank.loopProduct_pair_indexed _ _ _ sheet row.a, ih,
        word,
        Purelib.Data.List.Append.append_assoc]

variable (rows : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet
  labels (Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk.nil lifted.vertices lifted.edges
  (BasedBranchBank.anchor lifted
  sheet)))

/-- The odd-ending complete word and corrected pairing retain every internal branch area and the exact terminal cross
term. -/
theorem odd_area (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian) (ending : List (Stokes.OrientedEdge
  lifted.vertices.count)) :
    RetracingWords.wordArea value (rows.word ++ ending) + rows.correctedArea value = rows.internalArea value +
      RetracingWords.wordArea value ending +
      BoundaryRibbon.area (Increments.total (rows.readings value)) (SewingRetraction.wordValue value ending +
        SewingRetraction.wordValue value (lifted.edges.indexedEdges lifted.vertices (bank.rows.get
          reference).reference.walk (BranchCutLifts.otherSheet sheet))) := by
  have polygon := (congrArg (IncrementArea.pathArea (Increments.values (rows.readings value) ++
    [SewingRetraction.wordValue value ending]) + ·)
    (rows.correctedArea_eq value)).trans (Increments.odd _ _ _)
  rw [IncrementArea.pathArea_append, Increments.values_total] at polygon
  simp only [IncrementArea.pathArea_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, show IncrementArea.pathArea []
    = 0 from rfl, IncrementArea.area_zero_right, add_zero, -eq_self, -iff_self] at polygon
  rw [RetracingWords.wordArea_append, rows.word_area value, rows.word_value value]
  calc
    _ = rows.internalArea value + RetracingWords.wordArea value ending +
        (IncrementArea.pathArea (Increments.values (rows.readings value)) + BoundaryRibbon.area (Increments.total
          (rows.readings value)) (SewingRetraction.wordValue value ending) +
          rows.correctedArea value) := by ring1
    _ = _ := by rw [polygon]

/-- The two-leg ending and corrected pairing retain all original internal, terminal and cross-area terms. -/
theorem even_area (value : Stokes.OrientedEdge lifted.vertices.count → Gaussian)
    (forward returning : List (Stokes.OrientedEdge lifted.vertices.count)) :
    RetracingWords.wordArea value (rows.word ++ (forward ++ returning)) + rows.correctedArea value =
      rows.internalArea value + RetracingWords.wordArea value forward + RetracingWords.wordArea value returning +
        BoundaryRibbon.area (Increments.total (rows.readings value)) (SewingRetraction.wordValue value forward +
          SewingRetraction.wordValue value (lifted.edges.indexedEdges lifted.vertices (bank.rows.get
            reference).reference.walk (BranchCutLifts.otherSheet sheet))) +
        BoundaryRibbon.area (SewingRetraction.wordValue value forward + Increments.total (rows.readings value))
          (Increments.total (rows.readings value) + (SewingRetraction.wordValue value forward +
            SewingRetraction.wordValue value returning)) := by
  have polygon := (congrArg (IncrementArea.pathArea (Increments.values (rows.readings value) ++
    [SewingRetraction.wordValue value forward, SewingRetraction.wordValue value returning]) + ·)
    (rows.correctedArea_eq value)).trans (Increments.even _ _ _ _)
  rw [IncrementArea.pathArea_append, Increments.values_total] at polygon
  simp only [IncrementArea.pathArea_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, show IncrementArea.pathArea []
    = 0 from rfl, IncrementArea.area_zero_right, add_zero, zero_add, -eq_self, -iff_self] at polygon
  rw [RetracingWords.wordArea_append, RetracingWords.wordArea_append, SewingRetraction.wordValue_append, rows.word_area
    value, rows.word_value value]
  calc
    _ = rows.internalArea value + RetracingWords.wordArea value forward + RetracingWords.wordArea value returning +
        (IncrementArea.pathArea (Increments.values (rows.readings value)) + BoundaryRibbon.area
          (SewingRetraction.wordValue value forward) (SewingRetraction.wordValue value returning) +
          BoundaryRibbon.area (Increments.total (rows.readings value)) (SewingRetraction.wordValue value forward +
            SewingRetraction.wordValue value returning) +
          rows.correctedArea value) := by ring1
    _ = _ := by rw [polygon]; ring1

end PairedRows
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea

end
