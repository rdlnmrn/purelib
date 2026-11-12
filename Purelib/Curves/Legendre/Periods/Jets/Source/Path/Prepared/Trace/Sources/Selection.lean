module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Endpoints
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Observations
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # One accepted source occurrence with its actual old observation suffix

The original finite View selector threads the whole old row Spine together
with the same covering and prepared source tails. A selected head retains
its original singleton SourcePair and a deferred consumer of the actual
View, original source cache and source/moving/reset observations. New work
inside that consumer is performed only when its retained closure is used.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Sources

open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace renaming View -> TraceView
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision StepRequest CachedSource)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Physical.Comparison (SourcePair)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : Endpoint} {budget : PreparedTraceBudget segment left right} {accuracy : AccuracyRequest}

universe u

/-- The same complete covering/source tails and old row Spine at one exact Trace and center-family index. -/
@[expose] def Payload (row : Row) {current : Endpoint}
    {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) :=
  Σ covered : CoveredParents count (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision centers),
    PreparedParents covered floor targets × Primitive.Spine (row.expression parameter) accuracy trace.path

/-- Retain one original covering patch and preparation in the existing SourcePair on a singleton parent list. -/
@[expose] def singleton {parent : CenteredEdge (Fibre.frameCurve frame) basis} (patch : PreparedPatch parent)
    (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (prepared : PreparedParent patch count floor inside targets) :
    SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets) [parent] :=
  ⟨CoveredParents.cons patch inside CoveredParents.nil, ⟨prepared, PUnit.unit⟩⟩

/-- Result families keep the complete selected original source pair as their correctness-bearing index. -/
@[expose] def Results :=
  {parent : CenteredEdge (Fibre.frameCurve frame) basis} →
    SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets) [parent] → Type u

/-- The selected original source pair and one deferred result on that same pair, with no copied preparation owner. -/
@[expose] def Selected (result : Results (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets)) (parent : CenteredEdge (Fibre.frameCurve frame) basis) :=
  Σ source : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets) [parent],
    Unit → result source

/-- Consume one actual accepted View, its original source preparation and three complete old observation heads.

The old final suffix is available through parts.tail and parts.following.
The current Point caches, original patch and full prepared source are
supplied unchanged; no desired owner relation or observation agreement is
an argument to this producer interface.
-/
@[expose] def Consumer (row : Row) (result : Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets)) :=
  ∀ {current : Endpoint}
    {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {request : StepRequest} {cached : CachedSource segment current inherited request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
    {remaining : Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small)}
    {fits : budget.RequestsFit current
      (Subdivision.next current inherited request cached ordered small remaining).requests}
    {trace : PreparedTraceBudget.Trace budget
      (Subdivision.next current inherited request cached ordered small remaining) fits},
    (view : TraceView budget current inherited request cached ordered small remaining fits trace) →
    (center : PreparedEdge.CenterState
      (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet)) →
    (patch : PreparedPatch
      (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
        center⟩ : CenteredEdge (Fibre.frameCurve frame) basis)) →
    (inside : (patch.neighborhood count).box.Contains
      ((edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet).point 1)) →
    (prepared : PreparedParent patch count floor inside targets) →
    (selected : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      [⟨edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet, center⟩]) →
    selected = singleton patch inside prepared →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    view.Observations observed →
    result selected

/-- Read the same original source occurrence into that singleton pair without preparing its patch or Points. -/
def entryPair {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (index : Fin parents.length) :
    SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      [parents[index.val]'index.isLt] :=
  let selected := covered.entry index
  singleton selected.val selected.property (prepared.entry index)

/-- The whole singleton reads the identical original bounded covering and preparation caches. -/
theorem entryPair_eq {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (index : Fin parents.length) :
    entryPair covered prepared index =
      singleton (covered.entry index).val (covered.entry index).property (prepared.entry index) := by
  unfold entryPair
  rfl

/-- The singleton pair retains the entire original source preparation at that SAME bounded occurrence. -/
theorem entryPair_entry_heq {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (index : Fin parents.length) : HEq ((entryPair covered prepared index).2.entry 0) (prepared.entry index) := by
  unfold entryPair singleton PreparedParents.entry
  rfl

/-- Form one deferred head consumer and the literal following cover/preparation/observation payload together. -/
private def step (row : Row) (result : Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
    (consume : Consumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row result) :
    TraceView.ThreadConsumer (curve := Fibre.frameCurve frame) (differential := basis)
      (budget := budget) (within := within) (sheet := sheet)
      (Payload (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row)
      (Selected result) :=
  fun view centers retained => by
    cases retained with
    | mk covered both =>
      cases covered with
      | cons patch inside tail =>
        let parts := view.observations both.2
        let selected := singleton patch inside both.1.1
        let run : Unit → _ := fun _ => consume view centers.1 patch inside both.1.1 selected rfl both.2 parts
        exact ⟨⟨selected, run⟩, ⟨tail, both.1.2, parts.following⟩⟩

/-- Select one original source occurrence and defer its actual accepted-View consumer without repeating selection.

The original selector extracts each visited View once. At that same head
the old source/moving/reset observations are read once and the unchanged
following cache travels with the original prepared source tail. Only the
selected callback closure is returned; executing it is separate new work.
-/
def atParent (row : Row) (result : Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
    (consume : Consumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row result)
    {current : Endpoint}
    {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) subdivision)
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision sources.1).length) :
    Selected result
      ((centeredEdges (Fibre.frameCurve frame) basis sheet subdivision sources.1)[index.val]'index.isLt) :=
  PreparedTraceBudget.Trace.atParentWith (curve := Fibre.frameCurve frame) (differential := basis)
    (Payload (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row)
    (Selected result)
    (step row result consume) trace sources.1 ⟨sources.2.1, sources.2.2, observed⟩ index

section Readbacks

variable {current : Endpoint}
variable {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable (row : Row) (result : Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
variable (consume : Consumer (frame := frame) (basis := basis) (count := count) (floor := floor)
  (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row result)
variable (trace : PreparedTraceBudget.Trace budget
  (Subdivision.next current inherited request cached ordered small remaining) fits)
variable (centers : CenterStates (Fibre.frameCurve frame) basis sheet
  (Subdivision.next current inherited request cached ordered small remaining))
variable (patch : PreparedPatch
  (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
    centers.1⟩ : CenteredEdge (Fibre.frameCurve frame) basis))
variable (inside : (patch.neighborhood count).box.Contains
  ((edgeOfStep (Fibre.frameCurve frame) basis segment within
    current inherited request cached ordered small sheet).point 1))
variable (tail : CoveredParents count (centeredEdges (Fibre.frameCurve frame) basis sheet remaining centers.2))
variable (prepared : PreparedParents (CoveredParents.cons patch inside tail) floor targets)
variable (observed : Primitive.Spine (row.expression parameter) accuracy trace.path)

/-- The complete zero result retains the actual source cache and one deferred consumer of the same old View heads. -/
theorem atParent_head :
    atParent row result consume trace ⟨centers, ⟨CoveredParents.cons patch inside tail, prepared⟩⟩ observed
      ⟨0, Nat.zero_lt_succ _⟩ =
    ⟨singleton patch inside prepared.1,
      fun _ : Unit => consume (TraceView.build trace) centers.1 patch inside prepared.1
        (singleton patch inside prepared.1) rfl observed
        ((TraceView.build trace).observations observed)⟩ := by
  exact PreparedTraceBudget.Trace.atParentWith_head
    (curve := Fibre.frameCurve frame) (differential := basis) (within := within)
    (sheet := sheet) (budget := budget) trace centers
    (Payload (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row)
    (Selected result)
    (step row result consume) ⟨CoveredParents.cons patch inside tail, prepared, observed⟩

/-- A successor returns the entire original tail result with the identical prepared/observation payload. -/
theorem atParent_succ
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet remaining centers.2).length) :
    atParent row result consume trace ⟨centers, ⟨CoveredParents.cons patch inside tail, prepared⟩⟩ observed index.succ =
      atParent row result consume (TraceView.build trace).tailTrace
        ⟨centers.2, ⟨tail, prepared.2⟩⟩
        ((TraceView.build trace).observations observed).following index := by
  exact PreparedTraceBudget.Trace.atParentWith_succ
    (curve := Fibre.frameCurve frame) (differential := basis) (within := within)
    (sheet := sheet) (budget := budget) trace centers
    (Payload (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row)
    (Selected result)
    (step row result consume) ⟨CoveredParents.cons patch inside tail, prepared, observed⟩ index

end Readbacks

/-- The whole selected singleton SourcePair is exactly the original bounded source-cache lookup.

The proof follows the same original subdivision and finite occurrence.
No callback, observation factory or Point preparation is executed to
establish the source identity; it is independent of the deferred result.
-/
theorem atParent_source_eq (row : Row) (result : Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
    (consume : Consumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row result) :
    ∀ {current : Endpoint}
      {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current inherited)
      (fits : budget.RequestsFit current subdivision.requests)
      (trace : PreparedTraceBudget.Trace budget subdivision fits)
      (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := targets) subdivision)
      (observed : Primitive.Spine (row.expression parameter) accuracy trace.path)
      (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision sources.1).length),
      (atParent row result consume trace sources observed index).1 = entryPair sources.2.1 sources.2.2 index
  | _, _, .stop _ _, _, _, _, _, index => Fin.elim0 index
  | _, _, .next current inherited request cached ordered small remaining, fits, trace, sources, observed, index => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons patch inside tail =>
            refine Data.Fin.cases_induction ?_ ?_ index
            · have selected := congrArg Sigma.fst
                (atParent_head row result consume trace centers patch inside tail prepared observed)
              exact selected.trans (by unfold entryPair singleton; rfl)
            · intro next
              have selected := congrArg Sigma.fst
                (atParent_succ row result consume trace centers patch inside tail prepared observed next)
              exact selected.trans
                (atParent_source_eq row result consume remaining fits.2.2
                  (TraceView.build trace).tailTrace ⟨centers.2, ⟨tail, prepared.2⟩⟩
                  ((TraceView.build trace).observations observed).following next)
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- The selected original source preparation is the same complete cache at that original occurrence. -/
theorem atParent_entry_heq (row : Row) (result : Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
    (consume : Consumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row result)
    {current : Endpoint}
    {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) subdivision)
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path)
    (index : Fin (centeredEdges (Fibre.frameCurve frame) basis sheet subdivision sources.1).length) :
    HEq ((atParent row result consume trace sources observed index).1.2.entry 0) (sources.2.2.entry index) :=
  (Physical.Comparison.entry_heq_of_pair_eq
    (atParent_source_eq row result consume subdivision fits trace sources observed index) 0).trans
      (entryPair_entry_heq sources.2.1 sources.2.2 index)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Sources

end
