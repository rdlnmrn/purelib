module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Integration.PreparedCoveredParentLists.Entries
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Data.List.OfFn.Basic

/-! # Global shifted geometry on the same original finite signed parent spine

The retained per-parent shifted acquisitions are inputs, not callbacks that
acquire them. Their same covered lists and actual center chains are joined
once. The original geometric and root spines derive each shifted handoff
and the final return through the retained original endpoint Steps. Local
shifted source allocations play no part in this construction.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint finishPoint)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition (Linked)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}

/-- The joined actual shifted parent list, original covering spine and two exact geometric/signed endpoint chains. -/
@[expose] def ShiftedGeometry (start finish : LiftedPoint 2) (first last : Named) :=
  (parents : List (CenteredEdge (Fibre.frameCurve target) basis)) ×
  CoveredParents count parents × CenteredPathChain parents (start := start) (finish := finish) ×
    RootChain parents first last

namespace ShiftedGeometry

/-- Read the cached concatenation of the exact actual shifted-acquisition parent lists. -/
@[expose] def parents {start finish : LiftedPoint 2} {first last : Named}
    (geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) start finish first last) :=
  geometry.1

/-- Read the same original patches and endpoint witnesses on those actual concatenated parents. -/
@[expose] def covered {start finish : LiftedPoint 2} {first last : Named}
    (geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) start finish first last) :
    CoveredParents count geometry.parents := geometry.2.1

/-- Read the cached joined centered chain, preserving the original physical endpoints and sheet occurrences. -/
@[expose] def chain {start finish : LiftedPoint 2} {first last : Named}
    (geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) start finish first last) :
    CenteredPathChain geometry.parents (start := start) (finish := finish) := geometry.2.2.1

/-- Read the derived global signed root chain on the exact same cached parent list. -/
@[expose] def roots {start finish : LiftedPoint 2} {first last : Named}
    (geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) start finish first last) :
    RootChain geometry.parents first last := geometry.2.2.2

section Joining

variable {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {returnPoint : LiftedPoint 2} {returnPatch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (returnSample : ContinuedNeighborhood.Point returnPatch returnPoint.coordinate)
    (returnStep : Variation.Point.Step returnSample increment)
    {oldRoot : Named}

/-- Join only the stored shifted blocks while deriving their signed endpoint handoffs from the old original spine.

The incoming sample/Step is an actual original endpoint from the preceding
block. Its old-query comparison and the old RootChain derive the next
source comparison before the existing paid Step congruence is used. At the
empty tail that same construction derives the return to the original first
Step. No shifted handoff or returning relation is supplied as an input.
-/
private def join (returning : NamedEquivalent oldRoot returnSample.certificate.value.name) :
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    (patchAt : (index : Fin parents.length) → PreparedPatch (parents[index.val]'index.isLt)) →
    (finishAt : (index : Fin parents.length) →
      ((patchAt index).neighborhood count).box.Contains ((parents[index.val]'index.isLt).edge.point 1)) →
    (sourceAt : (index : Fin parents.length) → PreparedParent (patchAt index) count floor (finishAt index) targets) →
    (rangeAt : (index : Fin parents.length) → Variation.Point.Range ((patchAt index).neighborhood count)) →
    (admittedAt : (index : Fin parents.length) → Norm.Basic.normSq increment ≤ (rangeAt index).shiftedBound) →
    (stripAt : (index : Fin parents.length) → Norm.Basic.normSq increment ≤ (rangeAt index).stripBound) →
    (widthAt : Fin parents.length → AccuracyRequest) →
    (linkedAt : (index : Fin parents.length) →
      Linked (sourceAt index) (rangeAt index) target (admittedAt index) (stripAt index) (widthAt index)) →
    {left : LiftedPoint 2} →
    CenteredPathChain parents (start := left) (finish := returnPoint) →
    {incoming : Named} → RootChain parents incoming oldRoot →
    {incomingPatch : ContinuedNeighborhood (Paths.polynomial parameter) count} →
    (sample : ContinuedNeighborhood.Point incomingPatch left.coordinate) →
    (step : Variation.Point.Step sample increment) → NamedEquivalent incoming sample.certificate.value.name →
    ShiftedGeometry (target := target) (basis := basis) (count := count) left returnPoint
      step.root.value.name returnStep.root.value.name
  | [], _, _, _, _, _, _, _, _, _, geometry, _, roots, _, sample, step, incoming => by
      have incidence := geometry.empty_eq
      cases roots with
      | nil oldReturn =>
          let sources := incoming.symm.trans (oldReturn.trans returning)
          let equivalent := step.equivalent_of_source_eq returnStep
            (congrArg (fun point : LiftedPoint 2 => point.coordinate) incidence) sources
          let empty := (CenteredPathChain.nil (curve := Fibre.frameCurve target) (differential := basis) _).castFinish
            incidence
          exact ⟨[], CoveredParents.nil, empty, RootChain.nil equivalent⟩
  | parent :: remaining, patchAt, finishAt, sourceAt, rangeAt, admittedAt, stripAt, widthAt, linkedAt,
      _, geometry, _, roots, _, sample, step, incoming => by
      let linked := linkedAt 0
      have incidence : startPoint parent = _ := geometry.start_eq
      let sources := incoming.symm.trans (roots.firstEquivalent.trans (sourceAt 0).firstQueryEquivalent)
      let entry := step.equivalent_of_source_eq linked.first
        (congrArg (fun point : LiftedPoint 2 => point.coordinate) incidence.symm) sources
      let tail := join returning remaining
        (fun index => patchAt index.succ) (fun index => finishAt index.succ)
        (fun index => sourceAt index.succ) (fun index => rangeAt index.succ)
        (fun index => admittedAt index.succ) (fun index => stripAt index.succ)
        (fun index => widthAt index.succ) (fun index => linkedAt index.succ)
        geometry.remaining roots.remaining (sourceAt 0).lastSample linked.last (sourceAt 0).lastQueryEquivalent
      let head := linked.endpointRoots.changeStart entry
      let parents := linked.shifted.parents.covered.parents ++ tail.parents
      let covered := PreparedCoveredParentLists.CoveredParents.append
        linked.shifted.parents.coveredParents tail.covered
      let chain := (linked.geometry.append tail.chain).castStart incidence
      let roots := head.append tail.roots
      exact ⟨parents, covered, chain, roots⟩
termination_by structural parents _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => parents

/-- The actual join's retained parent list is the ordered flattening of its SAME original block occurrences. -/
private theorem join_parents (returning : NamedEquivalent oldRoot returnSample.certificate.value.name) :
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    (patchAt : (index : Fin parents.length) → PreparedPatch (parents[index.val]'index.isLt)) →
    (finishAt : (index : Fin parents.length) →
      ((patchAt index).neighborhood count).box.Contains ((parents[index.val]'index.isLt).edge.point 1)) →
    (sourceAt : (index : Fin parents.length) → PreparedParent (patchAt index) count floor (finishAt index) targets) →
    (rangeAt : (index : Fin parents.length) → Variation.Point.Range ((patchAt index).neighborhood count)) →
    (admittedAt : (index : Fin parents.length) → Norm.Basic.normSq increment ≤ (rangeAt index).shiftedBound) →
    (stripAt : (index : Fin parents.length) → Norm.Basic.normSq increment ≤ (rangeAt index).stripBound) →
    (widthAt : Fin parents.length → AccuracyRequest) →
    (linkedAt : (index : Fin parents.length) →
      Linked (sourceAt index) (rangeAt index) target (admittedAt index) (stripAt index) (widthAt index)) →
    {left : LiftedPoint 2} →
    (geometry : CenteredPathChain parents (start := left) (finish := returnPoint)) →
    {incoming : Named} → (roots : RootChain parents incoming oldRoot) →
    {incomingPatch : ContinuedNeighborhood (Paths.polynomial parameter) count} →
    (sample : ContinuedNeighborhood.Point incomingPatch left.coordinate) →
    (step : Variation.Point.Step sample increment) →
    (agrees : NamedEquivalent incoming sample.certificate.value.name) →
    (join (target := target) returnSample returnStep returning parents patchAt finishAt sourceAt rangeAt
      admittedAt stripAt widthAt linkedAt geometry roots sample step agrees).parents =
      (List.ofFn (fun index => (linkedAt index).shifted.parents.covered.parents)).flatten
  | [], _, _, _, _, _, _, _, _, _, _, _, roots, _, _, _, _ => by
      cases roots
      rfl
  | parent :: remaining, patchAt, finishAt, sourceAt, rangeAt, admittedAt, stripAt, widthAt, linkedAt,
      _, geometry, _, roots, _, sample, step, agrees => by
      have tail := join_parents returning remaining
        (fun index => patchAt index.succ) (fun index => finishAt index.succ)
        (fun index => sourceAt index.succ) (fun index => rangeAt index.succ)
        (fun index => admittedAt index.succ) (fun index => stripAt index.succ)
        (fun index => widthAt index.succ) (fun index => linkedAt index.succ)
        geometry.remaining roots.remaining (sourceAt 0).lastSample (linkedAt 0).last (sourceAt 0).lastQueryEquivalent
      change (linkedAt 0).shifted.parents.covered.parents ++ _ = _
      rewrite [Data.List.OfFn.Basic.ofFn_succ]
      change (linkedAt 0).shifted.parents.covered.parents ++ _ =
        (linkedAt 0).shifted.parents.covered.parents ++
          (List.ofFn (fun index => (linkedAt index.succ).shifted.parents.covered.parents)).flatten
      exact congrArg (List.append (linkedAt 0).shifted.parents.covered.parents) tail
termination_by structural parents _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => parents

/-- The actual ordered join retains the SAME original block's complete covering entry at its exact prefix offset. -/
private theorem join_entry_heq (returning : NamedEquivalent oldRoot returnSample.certificate.value.name) :
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) →
    (patchAt : (index : Fin parents.length) → PreparedPatch (parents[index.val]'index.isLt)) →
    (finishAt : (index : Fin parents.length) →
      ((patchAt index).neighborhood count).box.Contains ((parents[index.val]'index.isLt).edge.point 1)) →
    (sourceAt : (index : Fin parents.length) → PreparedParent (patchAt index) count floor (finishAt index) targets) →
    (rangeAt : (index : Fin parents.length) → Variation.Point.Range ((patchAt index).neighborhood count)) →
    (admittedAt : (index : Fin parents.length) → Norm.Basic.normSq increment ≤ (rangeAt index).shiftedBound) →
    (stripAt : (index : Fin parents.length) → Norm.Basic.normSq increment ≤ (rangeAt index).stripBound) →
    (widthAt : Fin parents.length → AccuracyRequest) →
    (linkedAt : (index : Fin parents.length) →
      Linked (sourceAt index) (rangeAt index) target (admittedAt index) (stripAt index) (widthAt index)) →
    {left : LiftedPoint 2} →
    (geometry : CenteredPathChain parents (start := left) (finish := returnPoint)) →
    {incoming : Named} → (roots : RootChain parents incoming oldRoot) →
    {incomingPatch : ContinuedNeighborhood (Paths.polynomial parameter) count} →
    (sample : ContinuedNeighborhood.Point incomingPatch left.coordinate) →
    (step : Variation.Point.Step sample increment) →
    (agrees : NamedEquivalent incoming sample.certificate.value.name) →
    let joined := join (target := target) returnSample returnStep returning parents patchAt finishAt sourceAt rangeAt
      admittedAt stripAt widthAt linkedAt geometry roots sample step agrees
    (outer : Fin parents.length) →
    (inner : Fin (linkedAt outer).shifted.parents.covered.parents.length) →
    (globalIndex : Fin joined.parents.length) →
    globalIndex.val = ((List.ofFn (fun index => (linkedAt index).shifted.parents.covered.parents)).take
      outer.val).flatten.length + inner.val →
    HEq (joined.covered.entry globalIndex) ((linkedAt outer).shifted.parents.coveredParents.entry inner)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, outer, _, _, _ => Fin.elim0 outer
  | parent :: remaining, patchAt, finishAt, sourceAt, rangeAt, admittedAt, stripAt, widthAt, linkedAt,
      _, geometry, _, roots, _, sample, step, agrees, ⟨0, _⟩, inner, globalIndex, offset => by
      let linked := linkedAt 0
      let tail := join returnSample returnStep returning remaining
        (fun index => patchAt index.succ) (fun index => finishAt index.succ)
        (fun index => sourceAt index.succ) (fun index => rangeAt index.succ)
        (fun index => admittedAt index.succ) (fun index => stripAt index.succ)
        (fun index => widthAt index.succ) (fun index => linkedAt index.succ)
        geometry.remaining roots.remaining (sourceAt 0).lastSample linked.last (sourceAt 0).lastQueryEquivalent
      have scalar : globalIndex.val = inner.val := offset.trans (Nat.zero_add inner.val)
      have bound : inner.val < (linked.shifted.parents.covered.parents ++ tail.parents).length :=
        Eq.mp (congrArg (fun value => value < (linked.shifted.parents.covered.parents ++ tail.parents).length)
          scalar) globalIndex.isLt
      have indices : globalIndex = (⟨inner.val, bound⟩ :
          Fin (linked.shifted.parents.covered.parents ++ tail.parents).length) := Fin.ext scalar
      let covered := PreparedCoveredParentLists.CoveredParents.append linked.shifted.parents.coveredParents tail.covered
      exact (covered.entry_congr indices).trans
        (PreparedCoveredParentLists.CoveredParents.entry_append_left
          linked.shifted.parents.coveredParents tail.covered inner bound)
  | parent :: remaining, patchAt, finishAt, sourceAt, rangeAt, admittedAt, stripAt, widthAt, linkedAt,
      _, geometry, _, roots, _, sample, step, agrees, ⟨outer + 1, bounded⟩, inner, globalIndex, offset => by
      let linked := linkedAt 0
      let tail := join returnSample returnStep returning remaining
        (fun index => patchAt index.succ) (fun index => finishAt index.succ)
        (fun index => sourceAt index.succ) (fun index => rangeAt index.succ)
        (fun index => admittedAt index.succ) (fun index => stripAt index.succ)
        (fun index => widthAt index.succ) (fun index => linkedAt index.succ)
        geometry.remaining roots.remaining (sourceAt 0).lastSample linked.last (sourceAt 0).lastQueryEquivalent
      let tailWords := List.ofFn (fun index : Fin remaining.length =>
        (linkedAt index.succ).shifted.parents.covered.parents)
      have prefixLength : ((List.ofFn (fun index => (linkedAt index).shifted.parents.covered.parents)).take
          (outer + 1)).flatten.length =
          linked.shifted.parents.covered.parents.length + (tailWords.take outer).flatten.length := by
        rewrite [Data.List.OfFn.Basic.ofFn_succ]
        change (linked.shifted.parents.covered.parents ++ (tailWords.take outer).flatten).length = _
        exact Data.List.Append.length_append _ _
      let tailValue := (tailWords.take outer).flatten.length + inner.val
      have scalar : globalIndex.val = linked.shifted.parents.covered.parents.length + tailValue :=
        (offset.trans (congrArg (fun value => value + inner.val) prefixLength)).trans (Nat.add_assoc _ _ _)
      have fullBound : globalIndex.val < linked.shifted.parents.covered.parents.length + tail.parents.length :=
        Eq.mp (congrArg (fun length => globalIndex.val < length)
          (Data.List.Append.length_append linked.shifted.parents.covered.parents tail.parents)) globalIndex.isLt
      have tailBound : tailValue < tail.parents.length := Nat.lt_of_add_lt_add_left
        (Eq.mp (congrArg (fun value => value < linked.shifted.parents.covered.parents.length + tail.parents.length)
          scalar) fullBound)
      let tailIndex : Fin tail.parents.length := ⟨tailValue, tailBound⟩
      have bound : linked.shifted.parents.covered.parents.length + tailIndex.val <
          (linked.shifted.parents.covered.parents ++ tail.parents).length :=
        Eq.mp (congrArg (fun value => value < (linked.shifted.parents.covered.parents ++ tail.parents).length)
          scalar) globalIndex.isLt
      have indices : globalIndex = (⟨linked.shifted.parents.covered.parents.length + tailIndex.val, bound⟩ :
          Fin (linked.shifted.parents.covered.parents ++ tail.parents).length) := Fin.ext scalar
      let covered := PreparedCoveredParentLists.CoveredParents.append linked.shifted.parents.coveredParents tail.covered
      have inTail := PreparedCoveredParentLists.CoveredParents.entry_append_right
        linked.shifted.parents.coveredParents tail.covered tailIndex bound
      have original := join_entry_heq returning remaining
        (fun index => patchAt index.succ) (fun index => finishAt index.succ)
        (fun index => sourceAt index.succ) (fun index => rangeAt index.succ)
        (fun index => admittedAt index.succ) (fun index => stripAt index.succ)
        (fun index => widthAt index.succ) (fun index => linkedAt index.succ)
        geometry.remaining roots.remaining (sourceAt 0).lastSample linked.last (sourceAt 0).lastQueryEquivalent
        ⟨outer, Nat.lt_of_succ_lt_succ bounded⟩ inner tailIndex rfl
      exact (covered.entry_congr indices).trans (inTail.trans original)
termination_by structural parents _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => parents

end Joining

section OriginalCover

variable {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (widths : Fin (firstParent :: remaining).length → AccuracyRequest)

/-- The original linked acquisition at one retained covered-parent occurrence.

The exact family retains its source preparation, range, target frame and both
payments for the common increment. Its body is the original linked cache type.
-/
@[expose] def Block (index : Fin (firstParent :: remaining).length) :=
  Linked (prepared.entry index) (ranges.entry index) target
    (admitted.trans ((allocation.bound_le_entry index).trans
      (ranges.entry index).stripBound_le_shiftedBound))
    (admitted.trans (allocation.bound_le_entry index)) (widths index)

/-- Actual linked block caches at the SAME original finite covered-parent occurrences and common admitted increment.

The family is a stored dependent product, not an acquisition callback. Each
entry consumes the exact original source preparation, Range, target frame
and coefficient count. No local shifted source Targets occur in its type.
-/
@[expose] def Blocks :=
  DependentProduct (firstParent :: remaining) (Block (target := target) prepared ranges allocation admitted widths)

/-- Join all actual shifted acquisitions on the SAME original closed geometric and signed root spines.

The original first retained Step is the resulting common signed root. All
adjacent and closing comparisons are derived from the two old spines and
actual endpoint caches. The joined list, covered patches and centered/root
chains are materialized once, before a global source request is allocated.
-/
def build (blocks : Blocks (target := target) prepared ranges allocation admitted widths)
    (geometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain (firstParent :: remaining) root root) :
    let first := DependentProduct.get (firstParent :: remaining) blocks 0
    ShiftedGeometry (target := target) (basis := basis) (count := count)
      (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name :=
  let first := DependentProduct.get (firstParent :: remaining) blocks 0
  let returning := roots.firstEquivalent.trans (prepared.entry 0).firstQueryEquivalent
  join (target := target) (prepared.entry 0).firstSample first.first returning (firstParent :: remaining)
    (fun index => (covered.entry index).val) (fun index => (covered.entry index).property)
    (fun index => prepared.entry index) (fun index => ranges.entry index)
    (fun index => admitted.trans ((allocation.bound_le_entry index).trans
      (ranges.entry index).stripBound_le_shiftedBound))
    (fun index => admitted.trans (allocation.bound_le_entry index)) widths
    (fun index => DependentProduct.get (firstParent :: remaining) blocks index)
    geometry roots (prepared.entry 0).firstSample first.first returning

/-- Read the original retained shifted-parent word at every actual original block occurrence.

The list contains only the already cached block parent lists. It preserves
original order and repeated blocks; it does not prepare a source or allocate
local Targets and introduces no replacement geometric parent.
-/
@[expose] def blockWords (blocks : Blocks (target := target) prepared ranges allocation admitted widths) :=
  List.ofFn (fun index =>
    (DependentProduct.get (firstParent :: remaining) blocks index).shifted.parents.covered.parents)

/-- The actual global builder retains exactly the flattened original block words, in their original occurrence order.

Only the list index is compared. The original geometric/root chains,
patches, centers and query owners remain those of the same stored blocks.
-/
theorem build_parents (blocks : Blocks (target := target) prepared ranges allocation admitted widths)
    (geometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain (firstParent :: remaining) root root) :
    (build (target := target) prepared ranges allocation admitted widths blocks geometry roots).parents =
      (blockWords prepared ranges allocation admitted widths blocks).flatten := by
  unfold build blockWords
  apply join_parents

/-- The actual global builder retains the exact original covering patch and finish witness at every block/child offset.

The bounded global occurrence and full prefix-offset law identify a single
original occurrence, including repeated parent values. Heterogeneous
equality preserves the complete patch/containment subtype; no covering
seed, grown neighborhood or source query is replaced or recomputed.
-/
theorem build_entry_heq (blocks : Blocks (target := target) prepared ranges allocation admitted widths)
    (geometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain (firstParent :: remaining) root root)
    (outer : Fin (firstParent :: remaining).length)
    (inner : Fin (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length)
    (globalIndex : Fin (build prepared ranges allocation admitted widths blocks geometry roots).parents.length)
    (offset : globalIndex.val = ((blockWords prepared ranges allocation admitted widths blocks).take
      outer.val).flatten.length + inner.val) :
    HEq ((build prepared ranges allocation admitted widths blocks geometry roots).covered.entry globalIndex)
      ((DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.coveredParents.entry inner) := by
  unfold build
  unfold blockWords at offset
  apply join_entry_heq
  exact offset

/-- The joined shifted list is nonempty because its first actual acquisition has a positive mesh count. -/
theorem build_parents_ne_nil (blocks : Blocks (target := target) prepared ranges allocation admitted widths)
    (geometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent))
    {root : Named} (roots : RootChain (firstParent :: remaining) root root) :
    (build (target := target) prepared ranges allocation admitted widths blocks geometry roots).parents ≠ [] := by
  intro empty
  have headNonempty := (DependentProduct.get (firstParent :: remaining) blocks 0).parents_ne_nil
  dsimp only [build, join, parents] at empty
  generalize (DependentProduct.get (firstParent :: remaining) blocks 0).shifted.parents.covered.parents =
    headParents at headNonempty empty
  cases headParents with
  | nil => exact headNonempty rfl
  | cons head tail => cases empty

end OriginalCover

end ShiftedGeometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
