module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Sources.Selection
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Membership
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Observation
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.RootPath
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.TraceEndpoints
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # One selected physical source with its original View and old observations

The endpoint cache supplies its actual stored SourcePair. Whole original
parent/center transports align that same pair with the original rootTrace.
One shared selector carries the unchanged old Spine to its accepted View.
The output retains the selected source and deferred consumer, with a
whole preparation identity back to the literal EndpointPoints entry.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest} {row : Row}
variable {retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) widthRequest}
variable {parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count retained}
variable {prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {observed : Primitive.Spine (row.expression parameter) accuracy retained.traced.trace.get}
variable {compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) row retained parents prepared allocation observed}
variable {index : Fin parents.covered.parents.length}
variable {firstQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge 0
  (parents.covered.parents[index.val]'index.isLt).edge.baseInside}
variable {lastQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
  1 (of_decide_eq_true rfl)}
variable (kept : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery)

universe u

/-- The selected original source and deferred accepted-View consumer retain the SAME whole endpoint preparation. -/
@[expose] def ParentResult (result : Sources.Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets)) :=
  {value : Sources.Selected result (parents.covered.parents[index.val]'index.isLt) //
    value.1 = Sources.entryPair kept.pair.1 kept.pair.2 index ∧
      HEq (value.1.2.entry 0) kept.entry}

/-- A whole-parent index equality transports the selected original source and deferred consumer together. -/
private theorem transport_entry_heq
    (result : Sources.Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
    {first last : CenteredEdge (Fibre.frameCurve frame) basis} (same : first = last)
    (selected : Sources.Selected result first) :
    HEq ((Eq.mp (congrArg (Sources.Selected result) same) selected).1.2.entry 0)
      (selected.1.2.entry 0) := by
  cases same
  rfl

/-- Whole-parent transport preserves the same actual selected source projection. -/
private theorem transport_source_eq
    (result : Sources.Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
    {first last : CenteredEdge (Fibre.frameCurve frame) basis} (same : first = last)
    (selected : Sources.Selected result first) :
    (Eq.mp (congrArg (Sources.Selected result) same) selected).1 =
      Eq.mp (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
        SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
          (targets := targets) [parent]) same) selected.1 := by
  cases same
  rfl

/-- A transported original source pair has the identical singleton at the same bounded occurrence. -/
private theorem castParents_entryPair_eq
    {firstParents lastParents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (same : firstParents = lastParents)
    (covered : Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents
      count firstParents)
    (originalPrepared : PreparedParents (frame := frame) (basis := basis) covered floor targets)
    (first : Fin firstParents.length) (last : Fin lastParents.length) (sameIndex : first.val = last.val)
    (sameParent : (lastParents[last.val]'last.isLt) = (firstParents[first.val]'first.isLt)) :
    Eq.mp (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
        SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
          (targets := targets) [parent]) sameParent)
      (Sources.entryPair (PreparedParents.castParents same covered originalPrepared).1
        (PreparedParents.castParents same covered originalPrepared).2 last) =
      Sources.entryPair covered originalPrepared first := by
  cases same
  have sameBounded : first = last := Fin.ext sameIndex
  cases sameBounded
  cases sameParent
  rfl

/-- Select the original physical occurrence once with its actual old Spine, source cache and accepted View.

The rootTrace and internalSpine operations perform only original whole
index transports on supplied retained data. The stored endpoint SourcePair
is transported as a whole to the original center family. Selection runs
once, and its deferred consumer remains uncalled. No original Query,
Point, source, crop, OwnerJoin or observation is acquired again.
-/
def withParent (result : Sources.Results (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets))
    (consume : Sources.Consumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets)
      (budget := retained.traced.budget) (accuracy := accuracy) row result) :
    kept.ParentResult result :=
  let trace := retained.rootTrace retained.traced.trace.get rfl
  let old := Primitive.Spine.castPath trace.path_eq.symm (retained.internalSpine observed)
  let aligned := PreparedParents.castParents (frame := frame) (basis := basis)
    parents.parents_eq kept.pair.1 kept.pair.2
  let sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) retained.traced.prepared.subdivision :=
    ⟨parents.centers, aligned⟩
  let selected := Sources.atParent (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := targets) (budget := retained.traced.budget) (accuracy := accuracy)
    row result consume trace sources old (parents.centeredIndex index)
  have sameParent := getElem_congr parents.parents_eq
    (i := index.val) (j := (parents.centeredIndex index).val) rfl index.isLt
  let changed := Eq.mp (congrArg (Sources.Selected result) sameParent.symm) selected
  have selectedSource := Sources.atParent_source_eq (frame := frame) (basis := basis)
    (count := count) (floor := floor) (sheet := sheet) (targets := targets)
    (budget := retained.traced.budget) (accuracy := accuracy)
    row result consume retained.traced.prepared.subdivision _ trace sources old (parents.centeredIndex index)
  have changedSource : changed.1 = Sources.entryPair kept.pair.1 kept.pair.2 index :=
    (transport_source_eq result sameParent.symm selected).trans
      ((congrArg (fun source => Eq.mp (congrArg
          (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
            SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
              (targets := targets) [parent]) sameParent.symm) source) selectedSource).trans
        (castParents_entryPair_eq parents.parents_eq kept.pair.1 kept.pair.2
          index (parents.centeredIndex index) (parents.centeredIndex_val index).symm sameParent.symm))
  have selectedEntry := Sources.atParent_entry_heq (frame := frame) (basis := basis)
    (count := count) (floor := floor) (sheet := sheet) (targets := targets)
    (budget := retained.traced.budget) (accuracy := accuracy)
    row result consume trace sources old (parents.centeredIndex index)
  have originalEntry := PreparedParents.castParents_entry_heq (frame := frame) (basis := basis)
    parents.parents_eq kept.pair.1 kept.pair.2 index (parents.centeredIndex index)
    (parents.centeredIndex_val index).symm
  ⟨changed, changedSource, (transport_entry_heq result sameParent.symm selected).trans
    (selectedEntry.trans (originalEntry.trans (heq_of_eq kept.entry_eq).symm))⟩

namespace ParentResult

variable {kept}
variable {result : Sources.Results (frame := frame) (basis := basis)
  (count := count) (floor := floor) (targets := targets)}
variable (selected : kept.ParentResult result)

/-- Read the same whole original covering patch/preparation cache retained by the physical selector. -/
abbrev source : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) [parents.covered.parents[index.val]'index.isLt] := selected.val.1

/-- Read the single deferred consumer capturing its actual View, old observations and original source head. -/
abbrev run : Unit → result selected.source := selected.val.2

/-- The selected source retains every original Point/request/model cache of the literal endpoint preparation. -/
theorem entry_heq : HEq (selected.source.2.entry 0) kept.entry := selected.property.2

/-- The complete selected pair is the original bounded singleton, including its patch and preparation. -/
theorem source_eq : selected.source = Sources.entryPair kept.pair.1 kept.pair.2 index := selected.property.1

/-- One completed actual consumer value retains its pointwise factory on the same original selected result. -/
@[expose] def Executed := {cached : result selected.source // cached = selected.run ()}

/-- Execute the original deferred consumer once and retain the complete resulting cache.

The original ParentResult remains a distinct runtime input. Producers keep
it alongside this execution view, preserving the original source pair and
closure; this subtype does not replace that closure with a new factory.
-/
def execute : selected.Executed :=
  let cached := selected.run ()
  ⟨cached, rfl⟩

namespace Executed

variable {selected}
variable (executed : selected.Executed)

/-- Read the whole actual completed consumer cache without executing its original closure again. -/
abbrev value := executed.val

/-- The retained result is the pointwise execution of the original whole selected consumer at unit. -/
theorem factory_eq : executed.value = selected.run () := executed.property

end Executed

end ParentResult

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

end
