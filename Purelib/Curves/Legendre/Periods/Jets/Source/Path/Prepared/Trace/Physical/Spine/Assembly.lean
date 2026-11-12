module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Append
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.RootChain
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Data.List.Append
import Purelib.Data.List.OfFn.Basic
public import Purelib.Data.List.Flatten.Occurrence
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.Gaussian.Equivalence

/-! # Ordered assembly of the same acquired physical source parents

The original nested Sources supplies every actual Parents, center family,
cover and completed source product. The operation joins only these stored
objects. The existing centered-data owner retains the exact path endpoints;
all six resulting source lists preserve the literal segment/child order.
The old Targets index remains unchanged and is not retagged as a new stage.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine.Sources

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain (PreparedPathCenteredData)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- Existing centered data, its exact covered parent spine and the same original source-preparation product.

This is only a dependent view of existing owners. The same original Targets
remain indices; no new allocation, preparation, root or observation is
introduced by the container.
-/
@[expose] def Assembled (start finish : Canonical) :=
  (geometry : PreparedPathCenteredData (Fibre.frameCurve frame) basis sheet start finish) ×
  (covered : CoveredParents count geometry.parents) × PreparedParents covered floor targets

namespace Assembled

/-- Read the same complete original centered parent list and connected lifted path. -/
@[expose] def geometry {start finish : Canonical}
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish) :
    PreparedPathCenteredData (Fibre.frameCurve frame) basis sheet start finish := assembled.1

/-- Read the actual appended original covering patches and endpoint containments. -/
@[expose] def covered {start finish : Canonical}
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish) :
    CoveredParents count assembled.geometry.parents := assembled.2.1

/-- Read the complete appended original source preparations on their unchanged Targets. -/
@[expose] def prepared {start finish : Canonical}
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish) :
    PreparedParents assembled.covered floor targets := assembled.2.2

/-- Join the two retained geometry/cover/source products at their identical actual physical endpoint.

Only ordered list and path constructors execute. Both original source
products keep all selected requests, centers, six models and endpoint caches.
No geometric or operational owner is chosen from a point-key equality.
-/
def append {start middle finish : Canonical}
    (first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start middle)
    (last : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) middle finish) :
    Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish :=
  let geometry : PreparedPathCenteredData (Fibre.frameCurve frame) basis sheet start finish :=
    { parents := first.geometry.parents ++ last.geometry.parents
      chain := first.geometry.chain.append last.geometry.chain }
  let covered := PreparedCoveredParentLists.CoveredParents.append first.covered last.covered
  let prepared := PreparedParents.append first.covered last.covered first.prepared last.prepared
  ⟨geometry, covered, prepared⟩

/-- The assembled original parent list is the exact append of the two stored input lists. -/
theorem append_parents {start middle finish : Canonical}
    (first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start middle)
    (last : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) middle finish) :
    (first.append last).geometry.parents = first.geometry.parents ++ last.geometry.parents := by rfl

/-- Every actual selected six-channel source list is the same append of its original stored input lists. -/
theorem append_cells {start middle finish : Canonical}
    (first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start middle)
    (last : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) middle finish)
    (channel : Fin 6) :
    (PreparedParents.sources (first.append last).covered (first.append last).prepared
      (first.append last).geometry.chain).cells channel =
      (PreparedParents.sources first.covered first.prepared first.geometry.chain).cells channel ++
        (PreparedParents.sources last.covered last.prepared last.geometry.chain).cells channel :=
  PreparedParents.append_cells first.covered last.covered first.prepared last.prepared
    first.geometry.chain last.geometry.chain channel

variable {start middle finish : Canonical}

/-- A right ordered source occurrence keeps the SAME full preparation after the actual original left-prefix offset. -/
theorem append_entry_right
    (first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start middle)
    (last : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) middle finish)
    (index : Fin last.geometry.parents.length)
    (globalIndex : Fin (first.append last).geometry.parents.length)
    (offset : globalIndex.val = first.geometry.parents.length + index.val) :
    HEq ((first.append last).prepared.entry globalIndex) (last.prepared.entry index) := by
  have bound : first.geometry.parents.length + index.val <
      (first.geometry.parents ++ last.geometry.parents).length :=
    Eq.mp (congrArg (fun value => value < (first.geometry.parents ++ last.geometry.parents).length) offset)
      globalIndex.isLt
  have indices : globalIndex = (⟨first.geometry.parents.length + index.val, bound⟩ :
      Fin (first.geometry.parents ++ last.geometry.parents).length) := Fin.ext offset
  exact (PreparedParents.entry_congr (first.append last).covered (first.append last).prepared indices).trans
    (PreparedParents.append_entry_right first.covered last.covered first.prepared last.prepared index bound)

end Assembled

/-- Assemble the same retained physical-segment source family in original clear-path order.

Each head reads its original materialized Parents and derives the existing
covered-chain view on those same stored centers. The unchanged actual tail
supplies the following family. No canonical centers,
covering patches, source preparations, root owners or observations are rebuilt.
-/
def assemble
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained →
    Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish
  | _, _, .nil point, _, _, _, _ => ⟨⟨[], .nil ⟨point, sheet⟩⟩, .nil, PUnit.unit⟩
  | _, _, .cons _ tail, within, _, retained, sources =>
      let first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) _ _ :=
        ⟨⟨sources.1.covered.parents, sources.1.covered.chain⟩, sources.1.coveredParents, sources.2.1⟩
      let following := assemble width tail within.tail retained.1.traced.finishOwner retained.2 sources.2.2
      first.append following
termination_by structural _ _ path _ _ _ _ => path

/-- Derive the signed root chain on the exact assembled original paid parent list.

Each actual Segment supplies its unchanged complete trace, original accepted
requests and retained canonical centers. The generalized original root-chain
operation consumes those actual suffix views; ordered append reuses the same
finishing Owner as the next physical acquisition's source.
-/
def rootChain
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    RootChain (assemble width path within owner retained kept).geometry.parents
      (ownerRootName owner.parameterNonzero owner)
      (ownerRootName (Acquisition.Spine.assemble width path within owner retained).traced.finishOwner.parameterNonzero
        (Acquisition.Spine.assemble width path within owner retained).traced.finishOwner)
  | _, _, .nil _, _, owner, _, _ => .nil (Approximation.Gaussian.Equivalence.NamedEquivalent.refl
      (ownerRootName owner.parameterNonzero owner))
  | _, _, .cons _ tail, within, _owner, retained, kept =>
      let first := kept.1.rootChain
      let following := rootChain width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2
      first.append following
termination_by structural _ _ path _ _ _ _ => path

/-- Close the same assembled signed roots with the actual retained original finishing-to-source OwnerJoin.

The join keeps both original Owners and its paid near-tail comparison.
It contributes only the final signed relation; the original ordered parents,
source product, centers and materialized physical trace remain unchanged.
-/
def closedRootChain
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) {point : Canonical}
    (path : ClearPath (Paths.polynomial parameter) ambient point point) (within : path.WithinAmbient)
    (owner : Owner ((Paths.polynomial parameter).eval point))
    (retained : Acquisition.Spine width path within owner)
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained)
    (join : OwnerJoin (Acquisition.Spine.assemble width path within owner retained).traced.finishOwner owner) :
    RootChain (assemble width path within owner retained kept).geometry.parents
      (ownerRootName owner.parameterNonzero owner) (ownerRootName owner.parameterNonzero owner) :=
  PreparedBankRootChains.RootChain.changeFinish
    (rootChain width path within owner retained kept) join.equivalent

/-- Read only the actual original segment parent lists in their retained physical path order. -/
@[expose] def parentWords
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained → List (List (CenteredEdge (Fibre.frameCurve frame) basis))
  | _, _, .nil _, _, _, _, _ => []
  | _, _, .cons _ tail, within, _, retained, sources =>
      sources.1.covered.parents ::
        parentWords width tail within.tail retained.1.traced.finishOwner retained.2 sources.2.2
termination_by structural _ _ path _ _ _ _ => path

/-- The assembled parent list is the literal flattening of the same retained original per-segment lists. -/
theorem assemble_parents
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (assemble width path within owner retained kept).geometry.parents =
      (parentWords width path within owner retained kept).flatten
  | _, _, .nil _, _, _, _, _ => rfl
  | _, _, .cons _ tail, within, _, retained, kept => by
      change kept.1.covered.parents ++
        (assemble width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2).geometry.parents =
          kept.1.covered.parents ++
            (parentWords width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2).flatten
      exact congrArg (List.append kept.1.covered.parents)
        (assemble_parents width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2)
termination_by structural _ _ path _ _ _ _ => path

/-- Read one selected actual cell list per original Segment without requesting any model or observation.
-/
@[expose] def cellWords
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (channel : Fin 6) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained →
      List (List Integration.Polynomial.Gaussian.Cell.Basic.CellModel)
  | _, _, .nil _, _, _, _, _ => []
  | _, _, .cons _ tail, within, _, retained, kept =>
      (PreparedParents.sources kept.1.coveredParents kept.2.1 kept.1.covered.chain).cells channel ::
        cellWords width channel tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2
termination_by structural _ _ path _ _ _ _ => path

/-- All six assembled lists are the exact original Segment/child flattening on the same stored cells. -/
theorem assemble_cells
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (channel : Fin 6) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (PreparedParents.sources (assemble width path within owner retained kept).covered
      (assemble width path within owner retained kept).prepared
      (assemble width path within owner retained kept).geometry.chain).cells channel =
        (cellWords width channel path within owner retained kept).flatten
  | _, _, .nil point, _, _, _, _ => by
      change (Path.nil (parameter := parameter) ⟨point, sheet⟩).cells channel = []
      exact Path.cells_nil ⟨point, sheet⟩ channel
  | _, _, .cons _head tail, within, _owner, retained, kept => by
      let first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) _ _ :=
        ⟨⟨kept.1.covered.parents, kept.1.covered.chain⟩, kept.1.coveredParents, kept.2.1⟩
      let following := assemble width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2
      change (PreparedParents.sources (first.append following).covered (first.append following).prepared
        (first.append following).geometry.chain).cells channel = _
      rewrite [Assembled.append_cells]
      have following_eq := assemble_cells width channel tail within.tail
        retained.1.traced.finishOwner retained.2 kept.2.2
      change (PreparedParents.sources first.covered first.prepared first.geometry.chain).cells channel ++
        (PreparedParents.sources following.covered following.prepared following.geometry.chain).cells channel = _
      rewrite [following_eq]
      rfl
termination_by structural _ _ path _ _ _ _ => path

section Occurrences

open Purelib.Data.List

attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- A complete existing physical Segment, its original Parents and its stored source preparation product.

Only existing Sigma/Subtype containers package the original mathematical
parents. The nominal segment, within witness, source Owner, acquired cache,
canonical centers, covering patches and complete source product are retained.
This is a dependent occurrence view, not another producer or root owner.
-/
@[expose] def SegmentSources
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) :=
  Σ endpoints : Canonical × Canonical,
    Σ clear : { segment : ClearSegment (Paths.polynomial parameter) ambient endpoints.1 endpoints.2 //
        segment.WithinAmbient },
      Σ owner : Owner ((Paths.polynomial parameter).eval endpoints.1),
        Σ acquired : Acquisition.Segment (segment := clear.val) (within := clear.property) (owner := owner)
            (width clear.val),
          Σ parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count acquired,
            PreparedParents parents.coveredParents floor targets

namespace SegmentSources

variable {width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
  AccuracyRequest}
variable (selected : SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) width)

/-- Read the exact physical start and finish of the original selected Segment. -/
@[expose] def endpoints := selected.1

/-- Read the same nominal original clear Segment, with no endpoint or orientation replacement. -/
@[expose] def segment := selected.2.1.val

/-- Read the original selected segment's ambient admission witness. -/
theorem within : selected.segment.WithinAmbient := selected.2.1.property

/-- Read the literal original source Owner of this stored acquired Segment. -/
@[expose] def owner := selected.2.2.1

/-- Read the whole original paid Segment cache, including subdivision, requests and finish-Owner handoffs. -/
@[expose] def acquired := selected.2.2.2.1

/-- Read the complete original Parents cache, including actual canonical centers and whole covered factory. -/
@[expose] def parents := selected.2.2.2.2.1

/-- Read the same entire original preparation product at the selected physical Segment. -/
@[expose] def prepared := selected.2.2.2.2.2

/-- Read one differential's original ordered cell list from the same retained Segment source caches. -/
@[expose] def cells (channel : Fin 6) :=
  (PreparedParents.sources selected.parents.coveredParents selected.prepared selected.parents.covered.chain).cells
    channel

end SegmentSources

/-- Read a complete original physical Segment source family at its original outer occurrence.

The head returns the identical supplied acquired Segment, Parents and source
product. A successor follows the SAME acquisition/source tails at the literal
previous finish Owner. No source factory or mathematical comparison runs.
-/
@[expose] def segmentAt
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    Fin (parentWords width path within owner retained kept).length →
    SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width
  | _, _, .nil _, _, _, _, _, index => Fin.elim0 index
  | start, _, .cons (middle := middle) head tail, within, owner, retained, kept, index =>
      Fin.cases ⟨(start, middle), ⟨head, within.head⟩, owner, retained.1, kept.1, kept.2.1⟩
        (fun next => segmentAt width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2 next) index
termination_by structural _ _ path _ _ _ _ _ => path

/-- The selected source tuple contains exactly the original word at its SAME outer occurrence. -/
theorem segmentAt_parents_eq
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (index : Fin (parentWords width path within owner retained kept).length) →
    (segmentAt width path within owner retained kept index).parents.covered.parents =
      (parentWords width path within owner retained kept)[index.val]'index.isLt
  | _, _, .nil _, _, _, _, _, index => Fin.elim0 index
  | _, _, .cons _head tail, within, _owner, retained, kept, index =>
      Fin.cases rfl
        (fun next => segmentAt_parents_eq width tail within.tail retained.1.traced.finishOwner retained.2
          kept.2.2 next) index
termination_by structural _ _ path _ _ _ _ _ => path

variable {width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
  AccuracyRequest}
variable {start middle finish : Canonical}
variable {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
variable {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
variable {within : (ClearPath.cons head tail).WithinAmbient}
variable {owner : Owner ((Paths.polynomial parameter).eval start)}
variable {retained : Acquisition.Spine width (.cons head tail) within owner}
variable {kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width (.cons head tail) within owner retained}

/-- Head lookup preserves the SAME entire acquired Segment/Parents/source tuple. -/
theorem segmentAt_zero : segmentAt width (.cons head tail) within owner retained kept ⟨0, Nat.zero_lt_succ _⟩ =
    ⟨(start, middle), ⟨head, within.head⟩, owner, retained.1, kept.1, kept.2.1⟩ := rfl

/-- Successor lookup follows the SAME original acquisition/source tail at the exact stored finish Owner. -/
theorem segmentAt_succ
    (index : Fin (parentWords width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2).length) :
    segmentAt width (.cons head tail) within owner retained kept index.succ =
      segmentAt width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2 index := rfl

/-- The original Segment model-list words equal their exact ordered bounded-occurrence table. -/
theorem cellWords_eq_ofFn
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (channel : Fin 6) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    cellWords width channel path within owner retained kept =
      List.ofFn (fun index : Fin (parentWords width path within owner retained kept).length =>
        (segmentAt width path within owner retained kept index).cells channel)
  | _, _, .nil _, _, _, _, _ => rfl
  | _, _, .cons head tail, within, owner, retained, kept => by
      let read := fun selected : SegmentSources (frame := frame) (basis := basis) (count := count)
          (floor := floor) (sheet := sheet) (targets := targets) width =>
        selected.cells channel
      let table := fun index : Fin
          ((parentWords width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2).length + 1) =>
        read (segmentAt width (.cons head tail) within owner retained kept index)
      have first := congrArg read (segmentAt_zero (width := width) (head := head) (tail := tail)
        (within := within) (owner := owner) (retained := retained) (kept := kept))
      have following := OfFn.Basic.ofFn_congr (fun index => congrArg read
        (segmentAt_succ (width := width) (head := head) (tail := tail)
          (within := within) (owner := owner) (retained := retained) (kept := kept) index))
      have ordered := (OfFn.Basic.ofFn_succ (function := table)).trans
        (congrArg₂ List.cons first following)
      exact (congrArg
        (List.cons ((PreparedParents.sources kept.1.coveredParents kept.2.1 kept.1.covered.chain).cells channel))
        (cellWords_eq_ofFn width channel tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2)).trans
          ordered.symm
termination_by structural _ _ path _ _ _ _ => path

/-- Exact ordered offsets identify the same complete original PreparedParent in the assembled source product.

The recursion follows the actual retained physical path and acquisition/source
spines. Original append entry laws retain the whole old preparation, not only
its point, selected cell or root name. Empty intervening parent words are
allowed and the literal previous finish Owner indexes every tail.
-/
theorem assemble_entry_heq
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (outer : Fin (parentWords width path within owner retained kept).length) →
    (child : Fin (segmentAt width path within owner retained kept outer).parents.covered.parents.length) →
    (globalIndex : Fin (assemble width path within owner retained kept).geometry.parents.length) →
    globalIndex.val = ((parentWords width path within owner retained kept).take outer.val).flatten.length + child.val →
    HEq ((assemble width path within owner retained kept).prepared.entry globalIndex)
      ((segmentAt width path within owner retained kept outer).prepared.entry child)
  := by
  intro start finish path
  induction path with
  | nil _point =>
      intro _ _ _ _ outer _ _ _
      exact Fin.elim0 outer
  | @cons start middle finish _head tail inductionHypothesis =>
      intro within _owner retained kept
      exact Fin.cases
        (fun child globalIndex offset => by
          let following := assemble width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2
          have scalar : globalIndex.val = child.val := offset.trans (Nat.zero_add child.val)
          have bound : child.val < (kept.1.covered.parents ++ following.geometry.parents).length :=
            Eq.mp (congrArg (fun value => value < (kept.1.covered.parents ++ following.geometry.parents).length)
              scalar) globalIndex.isLt
          have indices : globalIndex =
              (⟨child.val, bound⟩ : Fin (kept.1.covered.parents ++ following.geometry.parents).length) := Fin.ext scalar
          exact (PreparedParents.entry_congr
            (assemble width (.cons _head tail) within _owner retained kept).covered
            (assemble width (.cons _head tail) within _owner retained kept).prepared indices).trans
            (PreparedParents.append_entry_left kept.1.coveredParents following.covered kept.2.1 following.prepared
              child bound)
        )
        (fun outer => by
          let following := assemble width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2
          let first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
              (sheet := sheet) (targets := targets) start middle :=
            ⟨⟨kept.1.covered.parents, kept.1.covered.chain⟩, kept.1.coveredParents, kept.2.1⟩
          let Claim := fun (assembled : Assembled (frame := frame) (basis := basis)
              (count := count) (floor := floor) (sheet := sheet) (targets := targets) start finish)
              (chosen : SegmentSources (frame := frame) (basis := basis)
                (count := count) (floor := floor) (sheet := sheet) (targets := targets) width) =>
            (child : Fin chosen.parents.covered.parents.length) →
            (globalIndex : Fin assembled.geometry.parents.length) →
            globalIndex.val = ((parentWords width (.cons _head tail) within _owner retained kept).take
              (outer.val + 1)).flatten.length + child.val →
            HEq (assembled.prepared.entry globalIndex) (chosen.prepared.entry child)
          have sameSelected := segmentAt_succ (parameter := parameter) (frame := frame) (basis := basis)
            (count := count) (floor := floor) (sheet := sheet) (ambient := ambient) (targets := targets)
            (width := width) (head := _head) (tail := tail) (within := within) (owner := _owner)
            (retained := retained) (kept := kept) outer
          have sameAssembled : assemble width (.cons _head tail) within _owner retained kept =
              first.append following := by rfl
          have tailProof : Claim (first.append following)
              (segmentAt width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2 outer) := by
            intro child globalIndex offset
            let words := parentWords width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2
            have prefixLength : ((parentWords width (.cons _head tail) within _owner retained kept).take
                (outer.val + 1)).flatten.length =
                kept.1.covered.parents.length + (words.take outer.val).flatten.length := by
              change (kept.1.covered.parents ++ (words.take outer.val).flatten).length = _
              exact Append.length_append _ _
            let tailValue := (words.take outer.val).flatten.length + child.val
            have scalar : globalIndex.val = kept.1.covered.parents.length + tailValue :=
              (offset.trans (congrArg (fun value => value + child.val) prefixLength)).trans (Nat.add_assoc _ _ _)
            have fullBound : globalIndex.val < kept.1.covered.parents.length + following.geometry.parents.length :=
              Eq.mp (congrArg (fun length => globalIndex.val < length)
                (Append.length_append kept.1.covered.parents following.geometry.parents)) globalIndex.isLt
            have tailBound : tailValue < following.geometry.parents.length := Nat.lt_of_add_lt_add_left
              (Eq.mp (congrArg (fun value =>
                value < kept.1.covered.parents.length + following.geometry.parents.length) scalar) fullBound)
            let tailIndex : Fin following.geometry.parents.length := ⟨tailValue, tailBound⟩
            have handed := Assembled.append_entry_right first following tailIndex globalIndex scalar
            have original := inductionHypothesis within.tail retained.1.traced.finishOwner retained.2
              kept.2.2 outer child tailIndex rfl
            have finished := handed.trans original
            exact finished
          have assembledProof := Eq.mpr (congrArg
            (fun assembled => Claim assembled
              (segmentAt width tail within.tail retained.1.traced.finishOwner retained.2 kept.2.2 outer))
            sameAssembled) tailProof
          exact Eq.mpr (congrArg (Claim (assemble width (.cons _head tail) within _owner retained kept))
            sameSelected) assembledProof
        )

section Located

variable {start finish : Canonical}
variable (path : ClearPath (Paths.polynomial parameter) ambient start finish)
variable (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
variable (retained : Acquisition.Spine width path within owner)
variable (kept : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width path within owner retained)
variable (index : Fin (assemble width path within owner retained kept).geometry.parents.length)

/-- Transport the actual assembled source index to the identical flattened word at the same natural position. -/
@[expose] def flattenedIndex : Fin (parentWords width path within owner retained kept).flatten.length :=
  ⟨index.val, Eq.mp (congrArg (fun length => index.val < length)
    (congrArg List.length (assemble_parents width path within owner retained kept))) index.isLt⟩

/-- Locate the actual assembled global source occurrence with the original executable flatten worker exactly once. -/
def locate : Flatten.Occurrence (parentWords width path within owner retained kept)
    (flattenedIndex path within owner retained kept index) :=
  Flatten.locate (parentWords width path within owner retained kept)
    (flattenedIndex path within owner retained kept index)

/-- The stored location is the SAME original finite first-to-last block locator on this exact global source index. -/
theorem locate_eq : locate path within owner retained kept index =
    Flatten.locate (parentWords width path within owner retained kept)
      (flattenedIndex path within owner retained kept index) := by unfold locate; rfl

variable (position : Flatten.Occurrence (parentWords width path within owner retained kept)
  (flattenedIndex path within owner retained kept index))

/-- Read the complete original Segment/Parents/preparation cache selected by that SAME retained flatten occurrence. -/
@[expose] def selected := segmentAt width path within owner retained kept position.1

/-- Read the original local child index, transporting only its bound through exact parent-word identity. -/
@[expose] def child : Fin (selected path within owner retained kept index position).parents.covered.parents.length :=
  ⟨position.2.val.val, Eq.mpr (congrArg (fun parents => position.2.val.val < parents.length)
    (segmentAt_parents_eq width path within owner retained kept position.1)) position.2.val.isLt⟩

/-- The exact global parent is the SAME literal selected local child, independently of repeated equal values. -/
theorem parent_eq :
    (assemble width path within owner retained kept).geometry.parents[index.val]'index.isLt =
      (selected path within owner retained kept index position).parents.covered.parents[
        (child path within owner retained kept index position).val]'
          (child path within owner retained kept index position).isLt := by
  have globalParent := getElem_congr (assemble_parents width path within owner retained kept)
    (i := index.val) (j := index.val) rfl index.isLt
  have localParent := getElem_congr (segmentAt_parents_eq width path within owner retained kept position.1)
    (i := (child path within owner retained kept index position).val)
    (j := (child path within owner retained kept index position).val)
    rfl (child path within owner retained kept index position).isLt
  exact globalParent.trans (position.2.property.1.trans localParent.symm)

/-- The actual flattened offset locates that same complete original PreparedParent without source or query replay. -/
theorem prepared_heq :
    HEq ((assemble width path within owner retained kept).prepared.entry index)
      ((selected path within owner retained kept index position).prepared.entry
        (child path within owner retained kept index position)) :=
  assemble_entry_heq width path within owner retained kept position.1
    (child path within owner retained kept index position) index position.2.property.2

end Located
end Occurrences

namespace Assembled

variable {start middle finish : Canonical}

/-- A left source occurrence retains its complete original PreparedParent after assembling the same caches. -/
theorem append_entry_left
    (first : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start middle)
    (last : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) middle finish)
    (index : Fin first.geometry.parents.length)
    (globalIndex : Fin (first.append last).geometry.parents.length)
    (offset : globalIndex.val = index.val) :
    HEq ((first.append last).prepared.entry globalIndex) (first.prepared.entry index) := by
  have bound : index.val < (first.geometry.parents ++ last.geometry.parents).length :=
    Eq.mp (congrArg (fun value => value < (first.geometry.parents ++ last.geometry.parents).length) offset)
      globalIndex.isLt
  have indices : globalIndex = (⟨index.val, bound⟩ :
      Fin (first.geometry.parents ++ last.geometry.parents).length) := Fin.ext offset
  exact (PreparedParents.entry_congr (first.append last).covered (first.append last).prepared indices).trans
    (PreparedParents.append_entry_left first.covered last.covered first.prepared last.prepared index bound)

variable {nextStart nextFinish : Canonical}

/-- Transport the two physical endpoint indices of the SAME complete assembled source cache.

Only the original equality eliminators act. The ordered parent list, whole
covered spine, every prepared parent and its original allocation are retained;
no root Owner, signed comparison, source or observation is acquired.
-/
def castEndpoints
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (startEqual : start = nextStart) (finishEqual : finish = nextFinish) :
    Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) nextStart nextFinish := by
  cases startEqual
  cases finishEqual
  exact assembled

/-- Exact endpoint transport preserves the entire original assembled cache heterogeneously. -/
theorem castEndpoints_heq
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (startEqual : start = nextStart) (finishEqual : finish = nextFinish) :
    HEq (assembled.castEndpoints startEqual finishEqual) assembled := by
  cases startEqual
  cases finishEqual
  unfold castEndpoints
  rfl

/-- The transported assembled path retains its exact original ordered parent list. -/
theorem castEndpoints_parents
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (startEqual : start = nextStart) (finishEqual : finish = nextFinish) :
    (assembled.castEndpoints startEqual finishEqual).geometry.parents = assembled.geometry.parents := by
  cases startEqual
  cases finishEqual
  unfold castEndpoints
  rfl

/-- A bounded original source occurrence retains its complete preparation across endpoint-index transport. -/
theorem castEndpoints_entry_heq
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (startEqual : start = nextStart) (finishEqual : finish = nextFinish)
    (index : Fin assembled.geometry.parents.length)
    (transported : Fin (assembled.castEndpoints startEqual finishEqual).geometry.parents.length)
    (same : transported.val = index.val) :
    HEq ((assembled.castEndpoints startEqual finishEqual).prepared.entry transported)
      (assembled.prepared.entry index) := by
  cases startEqual
  cases finishEqual
  unfold castEndpoints at transported ⊢
  exact PreparedParents.entry_congr assembled.covered assembled.prepared (Fin.ext same)

/-- Distinct actual physical endpoints force a nonempty retained centered parent chain.

The claim concerns the same original geometric chain. It neither chooses a
root nor infers any signed relation from physical coordinate equality.
-/
theorem parents_ne_nil_of_endpoints_ne
    (assembled : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (different : start ≠ finish) : assembled.geometry.parents ≠ [] := by
  intro empty
  have lifted := CenteredPathChain.empty_eq
    (assembled.geometry.chain.castParents empty)
  exact different (congrArg (fun point : LiftedPoint 2 => point.coordinate) lifted)

/-- A whole equality of existing assembled source products preserves each complete original PreparedParent cache.

Both original occurrences retain their own exact finite bound. Equality
elimination transports the SAME complete geometry/cover/preparation product;
only the natural index equality remains, consumed by original entry_congr.
No cached source, root, model or observer is reconstructed.
-/
theorem entry_heq_of_eq
    (first last : Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (same : first = last)
    (firstIndex : Fin first.geometry.parents.length) (lastIndex : Fin last.geometry.parents.length)
    (values : firstIndex.val = lastIndex.val) :
    HEq (first.prepared.entry firstIndex) (last.prepared.entry lastIndex) := by
  cases same
  exact PreparedParents.entry_congr first.covered first.prepared (Fin.ext values)

end Assembled

/-- Read the signed source chain with the literal finish Owner of the SAME retained full paid acquisition.

The original covered_eq factory receipt identifies only its stored covered
path with its actual acquisition spine. It transports the terminal name of
the derived chain; no covered path, continuation or observation is rebuilt.
-/
def acquiredRootChain
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest)
    {start finish : Canonical} (path : ClearPath (Paths.polynomial parameter) ambient start finish)
    (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
    (paid : CoveredTracedPath.Acquisition width path within owner)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner paid.spine) :
    RootChain (assemble width path within owner paid.spine sources).geometry.parents
      (ownerRootName owner.parameterNonzero owner)
      (ownerRootName paid.covered.traced.finishOwner.parameterNonzero paid.covered.traced.finishOwner) := by
  have finish := congrArg (fun retained : CoveredTracedPath path owner =>
    ownerRootName retained.traced.finishOwner.parameterNonzero retained.traced.finishOwner) paid.covered_eq
  exact PreparedBankRootChains.RootChain.castNames rfl finish.symm
    (rootChain width path within owner paid.spine sources)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine.Sources

end
