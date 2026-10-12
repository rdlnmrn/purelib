module
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Nodup
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea

open Purelib.Data.List

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-!
# Genus-many pairs from the certified geometric branch order

Split the retained list without sorting it again or changing a branch
label. The final one or two branches are kept as physical data. Every
corrected A/B row is an actual common-root walk with its earlier A prefix.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Mesh.RetracingWords (wordArea wordArea_append AreaTerm)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Pair anchor
  Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea (PairedRows)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts (nodup_ofFn_injective)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Integration.Path.BoundaryRibbon (area)

set_option genInjectivity false in
/-- The one or two original terminal branch labels left after retaining the ordered genus-many pairs. -/
inductive PairEnding (Alpha : Type) where
  /-- Retain the original single terminal reference label or its actual branch tour. -/ | odd (reference : Alpha)
  /-- Retain the original reference and last terminal labels or their actual branch tours. -/ | even (reference last :
    Alpha)

constructive_injectivity PairEnding

namespace PairEnding

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
/-- Read the original retained reference label from either ending shape. -/
@[expose] def reference {Alpha : Type} : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding Alpha →
  Alpha
  | .odd reference => reference
  | .even reference _ => reference

/-- Read the original one- or two-label terminal list in its retained order. -/
@[expose] def labels {Alpha : Type} : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding Alpha →
  List Alpha
  | .odd reference => [reference]
  | .even reference last => [reference, last]

end PairEnding

set_option genInjectivity false in
/-- The original ordered label list split into exactly the requested number of consecutive pairs and its retained
terminal labels. -/
structure LabelPairs {Alpha : Type} (count : Nat) (labels : List Alpha) where
  /-- The actual consecutive label pairs in their original order. -/ pairs : List (Alpha × Alpha)
  /-- The retained pair count is exactly the supplied genus count. -/ count_eq : pairs.length = count
  /-- The retained one- or two-branch terminal data with its actual tour owners. -/ ending :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding Alpha
  /-- The original ordered labels are exactly the retained pair flattening followed by the actual terminal labels. -/
    labels_eq : labels = pairs.flatMap (fun pair => [pair.1, pair.2]) ++ ending.labels

constructive_injectivity LabelPairs

namespace LabelPairs

/-- Split the actual ordered labels structurally into consecutive pairs while retaining the certified one- or two-label
ending. -/
@[expose] def build {Alpha : Type} : (count : Nat) → (labels : List Alpha) →
    (labels.length = 2 * count + 1 ∨ labels.length = 2 * count + 2) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.LabelPairs count labels
  | 0, [], shape => (by simp only [List.length_nil, -eq_self, -iff_self] at shape; omega : False).elim
  | 0, [reference], _ => ⟨[], rfl, .odd reference, rfl⟩
  | 0, [reference, last], _ => ⟨[], rfl, .even reference last, rfl⟩
  | 0, _ :: _ :: _ :: _, shape => (by simp only [List.length_cons, -eq_self, -iff_self] at shape; omega : False).elim
  | _ + 1, [], shape => (by simp only [List.length_nil, -eq_self, -iff_self] at shape; omega : False).elim
  | _ + 1, [_], shape => (by
      simp only [List.length_cons, List.length_nil, -eq_self, -iff_self] at shape;
      omega : False).elim
  | count + 1, first :: last :: rest, shape =>
      let tail := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.LabelPairs.build count rest (by
        simp only [List.length_cons, -eq_self, -iff_self] at shape; omega)
      ⟨(first, last) :: tail.pairs, congrArg Nat.succ tail.count_eq, tail.ending,
        congrArg (fun suffix => first :: last :: suffix) tail.labels_eq⟩
termination_by structural count _ _ => count

end LabelPairs

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}

set_option genInjectivity false in
/-- The actual reference and terminal branch tours indexed by the original ending labels and starting sheet. -/
inductive EndingTours (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (sheet : Fin 2) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding (BranchIsolation.Data.Index branches) → Type
  /-- Retain the original single terminal reference label or its actual branch tour. -/ | odd (index) (reference :
    BasedBranchBank.Pair bank index index sheet) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet (.odd index)
  /-- Retain the original reference and last terminal labels or their actual branch tours. -/ | even (index last)
    (reference : BasedBranchBank.Pair bank index index sheet) (terminal : BasedBranchBank.Pair bank index last sheet) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet (.even index last)

constructive_injectivity EndingTours

namespace EndingTours

variable {ending : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
  (Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}

/-- Construct the actual reference and terminal tours on the original retained branch bank and starting sheet. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (sheet : Fin 2) : (ending :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding (BranchIsolation.Data.Index branches)) →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending
  | .odd index => .odd index (bank.pair index index sheet)
  | .even index last => .even index last (bank.pair index index sheet) (bank.pair index last sheet)

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours
/-- Read the original repeated-reference pair retained by either terminal shape. -/
@[expose] def reference : {ending : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
  (BranchIsolation.Data.Index branches)} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending → BasedBranchBank.Pair
      bank ending.reference ending.reference sheet
  | _, .odd _ reference => reference
  | _, .even _ _ reference _ => reference

/-- Read the actual outward indexed word of the retained terminal branch tour. -/
@[expose] def forward : {ending : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
  (BranchIsolation.Data.Index branches)} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending → List
      (Stokes.OrientedEdge lifted.vertices.count)
  | _, .odd _ reference => reference.outward.indexed
  | _, .even _ _ _ terminal => terminal.outward.indexed

/-- Read the complete actual terminal indexed word: one outward leg for odd endings or both terminal legs for even
endings. -/
@[expose] def word : {ending : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
  (BranchIsolation.Data.Index branches)} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending → List
      (Stokes.OrientedEdge lifted.vertices.count)
  | _, .odd _ reference => reference.outward.indexed
  | _, .even _ _ _ terminal => terminal.closed.indexed

/-- Sum the original internal areas of the retained terminal branch legs. -/
@[expose] def internalArea (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    {ending : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding (BranchIsolation.Data.Index
      branches)} → Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending →
      Data.Gaussian.Basic.Canonical
  | _, .odd _ reference => RetracingWords.wordArea value reference.outward.indexed
  | _, .even _ _ _ terminal => RetracingWords.wordArea value terminal.outward.indexed + RetracingWords.wordArea value
    terminal.returning.indexed

end

/-- Read the exact retained exterior cross term of an even ending, with zero contribution for an odd ending. -/
@[expose] def exteriorArea (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (total :
  Data.Gaussian.Basic.Canonical) :
    {ending : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding (BranchIsolation.Data.Index
      branches)} → Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending →
      Data.Gaussian.Basic.Canonical
  | _, .odd _ _ => 0
  | _, .even _ _ _ terminal => BoundaryRibbon.area (SewingRetraction.wordValue value terminal.outward.indexed + total)
    (total + SewingRetraction.wordValue value terminal.closed.indexed)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours
/-- The retained terminal word is exactly the original branch-loop product on its actual starting sheet. -/
theorem word_eq (tours : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending) :
    tours.word = lifted.edges.indexedEdges lifted.vertices (bank.loopProduct ending.labels) sheet := by
  cases tours with
  | odd index reference =>
      change reference.outward.indexed = lifted.edges.indexedEdges lifted.vertices (bank.loopProduct [index]) sheet
      rw [reference.outward_eq, BasedBranchBank.liftedLoop_indexed, BasedBranchBank.loopProduct,
        lifted.edges.indexedEdges_append]
      exact (Purelib.Data.List.Append.append_nil _).symm
  | even index last reference terminal =>
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.labels, bank.loopProduct_pair_indexed
        _ _ [] sheet terminal]
      exact (Purelib.Data.List.Append.append_nil _).symm

/-- The actual repeated-reference value splits into its retained forward leg and original reference return on the
exchanged sheet. -/
theorem reference_value (tours : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet
  ending) (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue value tours.reference.closed.indexed = SewingRetraction.wordValue value tours.forward +
      SewingRetraction.wordValue value (lifted.edges.indexedEdges lifted.vertices (bank.rows.get
        ending.reference).reference.walk (BranchCutLifts.otherSheet sheet)) := by
  cases tours with
  | odd index reference =>
      rw [show (odd index reference).reference = reference from rfl, reference.indexed,
        SewingRetraction.wordValue_append]
      change _ = SewingRetraction.wordValue value reference.outward.indexed + _
      rw [reference.outward_eq, BasedBranchBank.liftedLoop_indexed]
      rfl
  | even index last reference terminal =>
      rw [show (even index last reference terminal).reference = reference from rfl, reference.indexed,
        SewingRetraction.wordValue_append]
      change _ = SewingRetraction.wordValue value terminal.outward.indexed + _
      rw [terminal.outward_eq, BasedBranchBank.liftedLoop_indexed]
      rfl

/-- The complete paired and terminal word area retains every internal leg area, corrected pair area and exact reference
and exterior cross term. -/
theorem area_formula (tours : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet
  ending)
    {labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)}
    (rows : BranchArea.PairedRows bank ending.reference sheet labels (VertexWalk.nil lifted.vertices lifted.edges
      (BasedBranchBank.anchor lifted sheet)))
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    RetracingWords.wordArea value (rows.word ++ tours.word) + rows.correctedArea value = rows.internalArea value +
      tours.internalArea value +
      BoundaryRibbon.area (SewingRetraction.wordValue value rows.word) (SewingRetraction.wordValue value
        tours.reference.closed.indexed) + tours.exteriorArea value (SewingRetraction.wordValue value rows.word) := by
  rw [tours.reference_value value, rows.word_value value]
  cases tours with
  | odd index reference =>
      change _ = _ + _ + _ + 0
      rw [add_zero]
      exact rows.odd_area value reference.outward.indexed
  | even index last reference terminal =>
      have joined : terminal.closed.indexed = terminal.outward.indexed ++ terminal.returning.indexed := by
        rw [terminal.closed_eq]
        rfl
      change RetracingWords.wordArea value (rows.word ++ terminal.closed.indexed) + _ = _
      rw [joined]
      change _ = rows.internalArea value + (RetracingWords.wordArea value terminal.outward.indexed +
        RetracingWords.wordArea value terminal.returning.indexed) +
        BoundaryRibbon.area _ (SewingRetraction.wordValue value terminal.outward.indexed + _) +
        BoundaryRibbon.area (SewingRetraction.wordValue value terminal.outward.indexed + _) (_ +
          SewingRetraction.wordValue value terminal.closed.indexed)
      rw [joined, SewingRetraction.wordValue_append]
      exact (rows.even_area value terminal.outward.indexed terminal.returning.indexed).trans (by ring1)

end EndingTours

namespace Ordered

/-- The complete unique original ordered branch labels have exactly the retained branch bank's site count. -/
theorem labels_length (ordered : BasedBranchBank.Ordered bank sheet) : ordered.prepared.labels.length =
  branches.siteCount := by
  let all := List.ofFn (fun index : BranchIsolation.Data.Index branches => index)
  have unique : all.Nodup := BoundaryCounts.nodup_ofFn_injective _ (fun _ _ same => same)
  have equal : ordered.prepared.labels.length = all.length := Nat.le_antisymm
    (Nodup.nodup_length_le_of_mem ordered.prepared.unique unique
      (fun index _ => OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩))
    (Nodup.nodup_length_le_of_mem unique ordered.prepared.unique (fun index _ => ordered.complete index))
  exact equal.trans OfFn.Basic.length_ofFn

/-- Split the original certified geometric branch order into genus-many consecutive pairs and its actual terminal
labels. -/
@[expose] def labelPairs (ordered : BasedBranchBank.Ordered bank sheet) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.LabelPairs genus ordered.prepared.labels :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.LabelPairs.build genus ordered.prepared.labels (by
    have degree := (Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.labels_length ordered).trans
      branches.count_eq
    cases curve.degreeShape with
    | odd equal => exact Or.inl (degree.trans equal)
    | even equal => exact Or.inr (degree.trans equal))

set_option genInjectivity false in
/-- The actual genus-many paired branch walks with retained terminal tours and physical reference-hole ownership.

The original ordered labels, cumulative A prefixes and actual starting sheet remain unchanged. -/
structure Paired (ordered : BasedBranchBank.Ordered bank sheet) where
  /-- The cached exact split of the original ordered branch labels. -/ split :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.LabelPairs genus ordered.prepared.labels
  /-- The actual retained paired A and corrected B walks beginning at the original common anchor with an empty prior
    prefix. -/ rows : BranchArea.PairedRows bank split.ending.reference sheet split.pairs (VertexWalk.nil
    lifted.vertices lifted.edges (BasedBranchBank.anchor lifted sheet))
  /-- The retained one- or two-branch terminal data with its actual tour owners. -/ ending :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet split.ending
  /-- The actual physical hole location of the original retained terminal reference branch. -/ reference :
    PuncturedGridFaces.HoleLocation base.faces.holes (base.bank.cell split.ending.reference)
  /-- The physical reference hole carries exactly the retained terminal reference branch label. -/ reference_eq :
    reference.hole.index = split.ending.reference

constructive_injectivity Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered in
/-- Cache the exact ordered label split and paired walks, then locate the original physical reference hole. -/
@[expose] def paired (ordered : BasedBranchBank.Ordered bank sheet) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered := by
  let split := Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.labelPairs ordered
  let rows := PairedRows.build bank split.ending.reference sheet split.pairs (VertexWalk.nil lifted.vertices
    lifted.edges (BasedBranchBank.anchor lifted sheet))
  let ending := Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours.build bank sheet split.ending
  match base.faces.locateCell (base.bank.cell split.ending.reference) (base.bank.cell_mem split.ending.reference) with
  | .regular found => exact (found.face.unassigned split.ending.reference found.cell_eq).elim
  | .hole found => exact ⟨split, rows, ending, found, FaceKind.branch_unique found.hole.cell_eq found.cell_eq⟩

namespace Paired

variable {ordered :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet} (paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered)

/-- Read the actual retained paired row at a genus index, transporting only its original count equality. -/
@[expose] def row (index : Fin genus) := paired.rows.get (Fin.cast paired.split.count_eq.symm index)

/-- Transporting a finite index along equality of its original size preserves the exact Gaussian sum. -/
private theorem sum_cast {first last : Nat} (equal : first = last) (value : Fin first → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin value =
      FiniteSum.Fin.sumFin (fun index : Fin last => value (Fin.cast equal.symm index)) := by
  cases equal
  rfl

/-- The retained corrected-pair area is exactly the finite sum of the actual genus-indexed A and corrected B readings.
-/
theorem correctedArea_sum (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    paired.rows.correctedArea value = FiniteSum.Fin.sumFin (fun index : Fin genus =>
      BoundaryRibbon.area (SewingRetraction.wordValue value (paired.row index).row.a.closed.indexed)
        (SewingRetraction.wordValue value (paired.row index).row.corrected.indexed)) :=
  (paired.rows.correctedArea_sum value).trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired.sum_cast paired.split.count_eq _)

/-- The original complete ordered branch word is exactly the retained paired A prefix followed by its actual terminal
word. -/
theorem branch_word : ordered.word = paired.rows.word ++ paired.ending.word := by
  rw [ordered.word_eq, ordered.walk_eq]
  exact (congrArg (fun labels => lifted.edges.indexedEdges lifted.vertices (bank.loopProduct labels) sheet)
    paired.split.labels_eq).trans
    ((paired.rows.word_eq_append paired.split.ending.labels).trans (congrArg (paired.rows.word ++ ·)
      paired.ending.word_eq.symm))

/-- For an antisymmetric valuation, the actual repeated-reference tour reads the negative original physical
reference-hole boundary value. -/
theorem reference_value (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value paired.ending.reference.closed.indexed =
      -SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary lifted.vertices lifted.edges) := by
  have move (index : BranchIsolation.Data.Index branches) (equal : paired.reference.hole.index = index)
      (tour : BasedBranchBank.Pair bank index index sheet) : SewingRetraction.wordValue value tour.closed.indexed =
        -SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary lifted.vertices lifted.edges) := by
    cases equal
    exact Pair.repeated_hole_value paired.reference.hole tour value anti
  exact move _ paired.reference_eq paired.ending.reference

/-- The corrected genus-many actual A/B words satisfy the complete area formula. Regular-face excursions, the reference
hole and the finite exterior term are all retained; no physical boundary is assumed negligible. -/
theorem area_formula (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    lifted.edges.chainArea lifted.vertices value base.bank.exterior sheet + paired.rows.correctedArea value =
      paired.rows.internalArea value + paired.ending.internalArea value +
        BoundaryRibbon.area (SewingRetraction.wordValue value paired.rows.word) (-SewingRetraction.wordValue value
          (paired.reference.hole.liftedBoundary lifted.vertices lifted.edges)) +
        paired.ending.exteriorArea value (SewingRetraction.wordValue value paired.rows.word) + AreaTerm.total value
          ordered.prepared.compiled.areaTerms := by
  have formula := paired.ending.area_formula paired.rows value
  rw [← paired.branch_word, paired.reference_value value anti] at formula
  rw [ordered.exterior_areas value anti]
  calc
    _ = (RetracingWords.wordArea value ordered.word + paired.rows.correctedArea value) + AreaTerm.total value
      ordered.prepared.compiled.areaTerms := by
      ring1
    _ = _ := by rw [formula]

end Paired

end Ordered
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs

end
