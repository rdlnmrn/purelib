module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Schedule
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Observation
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Actual physical primitive increments on the identical paid source parents

The old primitive spine belongs to the literal stored physical trace. Its
complete cache is transported through the original trace and endpoint
identities. The supplied source product and covering patches move together
through the original cached parent-list equality, without preparation. The
original ordered comparison fold then pays the SAME old physical endpoints
and actual retained source integrals.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest}
variable (row : Row)
variable (retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) widthRequest)
variable (parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count retained)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Transport the SAME original cover/source pair to its stored center family's exact extracted parent index.

The original parent-list certificate moves the whole dependent pair. No
patch, endpoint witness, source, child block or observation is recreated.
The retained canonical centers remain the same actual supplied cache.
-/
@[expose] def sources
    (prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets) :
    Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor) (sheet := sheet)
      retained.traced.prepared.subdivision :=
  let aligned := PreparedParents.castParents (frame := frame) (basis := basis)
    parents.parents_eq parents.coveredParents prepared
  ⟨parents.centers, ⟨aligned.1, aligned.2⟩⟩

/-- The source family uses the literal same complete center cache of the actual paid Parents input. -/
theorem sources_centers (prepared : PreparedParents (frame := frame) (basis := basis)
    parents.coveredParents floor targets) :
    (sources retained parents prepared).1 = parents.centers := rfl

/-- The original cover and completed source product remain one unchanged complete pair after index transport. -/
theorem sources_pair_heq (prepared : PreparedParents (frame := frame) (basis := basis)
    parents.coveredParents floor targets) :
    HEq (sources retained parents prepared).2
      (⟨parents.coveredParents, prepared⟩ :
        Σ covered : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count
          parents.covered.parents, PreparedParents (frame := frame) (basis := basis) covered floor targets) := by
  unfold sources
  exact PreparedParents.castParents_heq (frame := frame) (basis := basis)
    parents.parents_eq parents.coveredParents prepared

/-- The original ordered comparison cache uses the actual physical old spine and SAME original paid source family. -/
abbrev Comparison (prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents
  floor targets)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy retained.traced.trace.get) :=
  Compared row (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    retained.traced.budget allocation retained.traced.prepared.subdivision
    (sources retained parents prepared) retained.traced.fits (retained.internalSpine observed)

/-- Compare the literal old physical observations with their SAME retained source integrals once.

Both complete index transports are derived from original production
certificates. The old endpoint requests have their exact supplied scalar
allocation; no desired root relation or final sample bound is an input.
-/
def compare (prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor
  targets)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy retained.traced.trace.get) : Comparison row retained parents prepared allocation observed :=
  let sourceFamily := sources retained parents prepared
  let internal := retained.internalSpine observed
  Trace.compare row (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    retained.traced.budget allocation
    retained.traced.prepared.subdivision sourceFamily retained.traced.fits internal

namespace Comparison

variable {row : Row}

/-- A whole original covering spine and its dependent completed source preparations at one parent list.

The existing Sigma container retains the actual covering patches, endpoint
admissions and all count-paid Point/source caches. Changing the list index
must transport these two existing objects together.
-/
@[expose] def SourcePair (parentList : List (CenteredEdge (Fibre.frameCurve frame) basis)) :=
  Σ covered : CoveredParents count parentList,
    PreparedParents (frame := frame) (basis := basis) covered floor targets

section PairReadbacks

variable {parentList : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {first last : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
  (targets := targets) parentList}

/-- Whole-pair equality preserves one complete original prepared-parent occurrence heterogeneously. -/
theorem entry_heq_of_pair_eq (same : first = last) (index : Fin parentList.length) :
    HEq (PreparedParents.entry (frame := frame) (basis := basis) first.2 index)
      (PreparedParents.entry (frame := frame) (basis := basis) last.2 index) := by
  cases same
  rfl

/-- Whole-pair equality preserves the actual original first Point at this same bounded occurrence. -/
private theorem firstSample_heq_of_pair_eq (same : first = last) (index : Fin parentList.length) :
    HEq (PreparedParents.entry (frame := frame) (basis := basis) first.2 index).firstSample
      (PreparedParents.entry (frame := frame) (basis := basis) last.2 index).firstSample := by
  cases same
  rfl

/-- Whole-pair equality preserves the independent original last Point at this same bounded occurrence. -/
private theorem lastSample_heq_of_pair_eq (same : first = last) (index : Fin parentList.length) :
    HEq (PreparedParents.entry (frame := frame) (basis := basis) first.2 index).lastSample
      (PreparedParents.entry (frame := frame) (basis := basis) last.2 index).lastSample := by
  cases same
  rfl

end PairReadbacks

variable {retained parents}
variable {prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {observed : Primitive.Spine
  (row.expression parameter)
  accuracy retained.traced.trace.get}
variable (compared : Comparison row retained parents prepared allocation observed)

/-- The actual cached source family retains the SAME original physical center observations. -/
theorem sourceCenters_eq : compared.sources.1 = parents.centers :=
  (congrArg (fun value : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) retained.traced.prepared.subdivision => value.1)
    compared.sources_eq).trans (sources_centers retained parents prepared)

/-- Equality of the whole retained source family preserves its dependent covering/source pair. -/
private theorem sourceTail_heq_of_eq
    {first last : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) retained.traced.prepared.subdivision}
    (same : first = last) : HEq first.2 last.2 := by
  cases same
  rfl

/-- Read the stored covering/source pair at the original physical parent-list index.

Only whole dependent index transports execute. The actual stored source
family supplies both values; the original center equality and parent-list
readback restore their physical indices. No source selector, covering
factory, prepared parent, Point, Query or root acquisition is executed.
-/
def sourcePair : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) parents.covered.parents :=
  let aligned : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets)
      (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision parents.centers) :=
    cast (congrArg (fun centers : CenterStates (Fibre.frameCurve frame) basis sheet
        retained.traced.prepared.subdivision =>
      SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
        (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision centers))
      compared.sourceCenters_eq) compared.sources.2
  PreparedParents.castParents (frame := frame) (basis := basis) parents.parents_eq.symm aligned.1 aligned.2

/-- The original source-pair reader is exactly the whole cached projection and two index transports. -/
private theorem packaged_sourcePair_factory : compared.sourcePair =
    (let aligned : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
          (targets := targets)
          (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision parents.centers) :=
        cast (congrArg (fun centers : CenterStates (Fibre.frameCurve frame) basis sheet
            retained.traced.prepared.subdivision =>
          SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
            (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision centers))
          compared.sourceCenters_eq) compared.sources.2
     PreparedParents.castParents (frame := frame) (basis := basis)
       parents.parents_eq.symm aligned.1 aligned.2) := by rfl

/-- The whole reader factory consumes the SAME stored source pair and its original index certificates. -/
theorem sourcePair_factory : compared.sourcePair =
    (let aligned : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
          (targets := targets)
          (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision parents.centers) :=
        cast (congrArg (fun centers : CenterStates (Fibre.frameCurve frame) basis sheet
            retained.traced.prepared.subdivision =>
          SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
            (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision centers))
          compared.sourceCenters_eq) compared.sources.2
     PreparedParents.castParents (frame := frame) (basis := basis)
       parents.parents_eq.symm aligned.1 aligned.2) :=
  packaged_sourcePair_factory compared

/-- The entire stored pair is the SAME original physical cover and completed source product. -/
private theorem packaged_sourcePair_eq : compared.sourcePair =
    (⟨parents.coveredParents, prepared⟩ : SourcePair (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets) parents.covered.parents) := by
  let aligned : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets)
      (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision parents.centers) :=
    cast (congrArg (fun centers : CenterStates (Fibre.frameCurve frame) basis sheet
        retained.traced.prepared.subdivision =>
      SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
        (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision centers))
      compared.sourceCenters_eq) compared.sources.2
  have aligned_heq : HEq aligned compared.sources.2 :=
    cast_heq (congrArg (fun centers : CenterStates (Fibre.frameCurve frame) basis sheet
        retained.traced.prepared.subdivision =>
      SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
        (centeredEdges (Fibre.frameCurve frame) basis sheet retained.traced.prepared.subdivision centers))
      compared.sourceCenters_eq) compared.sources.2
  have cached_heq : HEq compared.sources.2 (sources retained parents prepared).2 :=
    sourceTail_heq_of_eq compared.sources_eq
  have returned := PreparedParents.castParents_heq (frame := frame) (basis := basis)
    parents.parents_eq.symm aligned.1 aligned.2
  have factory := packaged_sourcePair_factory compared
  dsimp only at factory
  exact factory.trans (eq_of_heq (returned.trans (aligned_heq.trans
    (cached_heq.trans (sources_pair_heq retained parents prepared)))))

/-- The stored pair preserves the complete original physical covering/source cache, including all endpoint Points. -/
theorem sourcePair_eq : compared.sourcePair =
    (⟨parents.coveredParents, prepared⟩ : SourcePair (frame := frame) (basis := basis)
      (count := count) (floor := floor) (targets := targets) parents.covered.parents) :=
  packaged_sourcePair_eq compared

/-- One actual parent occurrence retains its entire original PreparedParent through the SAME whole-pair readback. -/
theorem sourcePair_entry_heq (index : Fin parents.covered.parents.length) :
    HEq (PreparedParents.entry (frame := frame) (basis := basis) compared.sourcePair.2 index)
      (prepared.entry index) :=
  entry_heq_of_pair_eq compared.sourcePair_eq index

/-- The first endpoint lookup retains the whole original Point, seed refinement and cached parameter norm. -/
theorem sourcePair_firstSample_heq (index : Fin parents.covered.parents.length) :
    HEq (PreparedParents.entry (frame := frame) (basis := basis) compared.sourcePair.2 index).firstSample
      (prepared.entry index).firstSample :=
  firstSample_heq_of_pair_eq compared.sourcePair_eq index

/-- The independent last endpoint lookup retains its whole original Point without another observation. -/
theorem sourcePair_lastSample_heq (index : Fin parents.covered.parents.length) :
    HEq (PreparedParents.entry (frame := frame) (basis := basis) compared.sourcePair.2 index).lastSample
      (prepared.entry index).lastSample :=
  lastSample_heq_of_pair_eq compared.sourcePair_eq index

/-- The comparison cache retains the entire literal old physical spine through the exact original index transports. -/
theorem observed_heq : HEq compared.observed observed :=
  (heq_of_eq compared.observed_eq).trans (retained.internalSpine_heq observed)

/-- The source scalar is the SAME literal old physical source value. -/
theorem first_value : compared.observed.first.value = observed.first.value :=
  (congrArg (fun old : Primitive.Spine
    (row.expression parameter)
    accuracy (Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath retained.traced.budget
      retained.traced.prepared.subdivision retained.traced.fits) => old.first.value) compared.observed_eq).trans
    (retained.internalSpine_first_value observed)

/-- The target scalar is the SAME literal old physical final value. -/
theorem last_value : compared.observed.last.value = observed.last.value :=
  (congrArg (fun old : Primitive.Spine
    (row.expression parameter)
    accuracy (Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath retained.traced.budget
      retained.traced.prepared.subdivision retained.traced.fits) => old.last.value) compared.observed_eq).trans
    (retained.internalSpine_last_value observed)

/-- The SAME actual block sum telescopes on the literal old physical endpoints and retained source integrals. -/
theorem blockErrors_sum_eq : Norm.Sum.Basic.gaussianSum compared.blockErrors =
    observed.last.value - observed.first.value - Norm.Sum.Basic.gaussianSum compared.integrals := by
  have exactSum := Trace.Compared.blockErrors_sum_eq (frame := frame) (basis := basis)
    (count := count) (floor := floor) (sheet := sheet) compared
  rewrite [compared.first_value, compared.last_value] at exactSum
  exact exactSum

/-- Every actual stationary/moving occurrence pays the SAME physical old endpoint increment. -/
theorem integral_error_le : Norm.Basic.normSq
    (observed.last.value - observed.first.value - Norm.Sum.Basic.gaussianSum compared.integrals) ≤
      (retained.traced.prepared.subdivision.requests.length : Data.Rat.Fraction.Rational) *
        ((retained.traced.prepared.subdivision.requests.length : Data.Rat.Fraction.Rational) *
          (26 * targets.endpoint)) := by
  have paid := Trace.Compared.integral_error_le (frame := frame) (basis := basis)
    (count := count) (floor := floor) (sheet := sheet) compared
  rewrite [compared.first_value, compared.last_value] at paid
  exact paid

/-- A genuinely selected source stage pays the SAME old physical endpoint/source-integral residual.

The actual source and observation caches remain fixed inputs. The supplied
stage certificate is the original computed search's exact finite result;
its decay combines with the derived count bound, not with an assumed old
sample inequality or a second observation producer.
-/
theorem selected_error_lt {currentStage : Nat} (request : AccuracyRequest)
    (selection : Approximation.Rational.Geometric.Search.Selection
      (telescopeScale retained.traced.prepared.subdivision.requests.length) currentStage request.tolerance)
    (later : selection.stage ≤ stage) : Norm.Basic.normSq
      (observed.last.value - observed.first.value - Norm.Sum.Basic.gaussianSum compared.integrals) <
        request.tolerance := by
  have paid := Trace.selected_error_lt (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) compared request selection later
  rewrite [compared.first_value, compared.last_value] at paid
  exact paid

end Comparison

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical

end
