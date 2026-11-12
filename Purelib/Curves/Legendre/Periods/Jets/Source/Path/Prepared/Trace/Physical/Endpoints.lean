module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence.Trace
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison.EndpointQueries
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Actual cached physical source Points on retained endpoint Queries

The whole physical source pair and one complete local PreparedParent are
retained once. Both comparisons consume that entry's distinct original
Points and the supplied direct Queries. A matching whole-parent occurrence
then supplies the original source, moving and retention endpoint relations;
its actual selected endpoint Owners remain separate complete results.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache (EndpointResult)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine.Sources (ParentOccurrence)

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
variable (compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) row retained parents prepared allocation observed)
variable (index : Fin parents.covered.parents.length)
variable (firstQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge 0
  (parents.covered.parents[index.val]'index.isLt).edge.baseInside)
variable (lastQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
  1 (of_decide_eq_true rfl))

/-- The SAME cached pair, local preparation and two actual endpoint-Query comparisons.

The existing Sigma/subtype containers retain the original complete pair
and one actual preparation with their exact reader equations. The two
relations use the supplied Query Owners and separate cached Points; they
are operational root comparisons, not primitive-observation payments.
-/
@[expose] def EndpointPoints :=
  Σ pair : { cache : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
        (targets := targets) parents.covered.parents // cache = compared.sourcePair },
    Σ entry : { cache : PreparedParent (frame := frame) (basis := basis) (pair.val.1.entry index).val
          count floor (pair.val.1.entry index).property targets //
        cache = PreparedParents.entry (frame := frame) (basis := basis) pair.val.2 index },
      NamedEquivalent (ownerName firstQuery.owner) entry.val.firstSample.certificate.value.name ×
        NamedEquivalent (ownerName lastQuery.owner) entry.val.lastSample.certificate.value.name

/-- Read one original preparation and compare its two unchanged Points with the supplied Queries.

The pair, covering admission and local preparation are let-bound before
both original patch comparisons. No source selector, Query, Point, model
or root acquisition runs. The existing retained-query comparison uses the
original seed refinements and exact physical endpoint containment.
-/
def compareSourcePoints :
    EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery :=
  let pair := compared.sourcePair
  let covered := pair.1.entry index
  let actual := PreparedParents.entry (frame := frame) (basis := basis) pair.2 index
  let first := NamedEquivalent.transport firstQuery.name_eq rfl
    (PreparedParent.firstRetainedQueryEquivalent (frame := frame) (basis := basis)
      (patch := covered.val) (covered := covered.property) actual firstQuery)
  let last := NamedEquivalent.transport lastQuery.name_eq rfl
    (PreparedParent.lastRetainedQueryEquivalent (frame := frame) (basis := basis)
      (patch := covered.val) (covered := covered.property) actual lastQuery)
  ⟨⟨pair, rfl⟩, ⟨⟨actual, rfl⟩, ⟨first, last⟩⟩⟩

/-- The full endpoint cache is its original let-bound projection/comparison construction. -/
private theorem packaged_compareSourcePoints_eq : compareSourcePoints compared index firstQuery lastQuery =
    (show EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery from
      let pair := compared.sourcePair
      let covered := pair.1.entry index
      let actual := PreparedParents.entry (frame := frame) (basis := basis) pair.2 index
      let first := NamedEquivalent.transport firstQuery.name_eq rfl
        (PreparedParent.firstRetainedQueryEquivalent (frame := frame) (basis := basis)
          (patch := covered.val) (covered := covered.property) actual firstQuery)
      let last := NamedEquivalent.transport lastQuery.name_eq rfl
        (PreparedParent.lastRetainedQueryEquivalent (frame := frame) (basis := basis)
          (patch := covered.val) (covered := covered.property) actual lastQuery)
      ⟨⟨pair, rfl⟩, ⟨⟨actual, rfl⟩, ⟨first, last⟩⟩⟩) := by rfl

/-- The whole endpoint factory uses the actual stored pair, original entry and SAME supplied Queries. -/
theorem compareSourcePoints_eq : compareSourcePoints compared index firstQuery lastQuery =
    (show EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery from
      let pair := compared.sourcePair
      let covered := pair.1.entry index
      let actual := PreparedParents.entry (frame := frame) (basis := basis) pair.2 index
      let first := NamedEquivalent.transport firstQuery.name_eq rfl
        (PreparedParent.firstRetainedQueryEquivalent (frame := frame) (basis := basis)
          (patch := covered.val) (covered := covered.property) actual firstQuery)
      let last := NamedEquivalent.transport lastQuery.name_eq rfl
        (PreparedParent.lastRetainedQueryEquivalent (frame := frame) (basis := basis)
          (patch := covered.val) (covered := covered.property) actual lastQuery)
      ⟨⟨pair, rfl⟩, ⟨⟨actual, rfl⟩, ⟨first, last⟩⟩⟩) :=
  packaged_compareSourcePoints_eq compared index firstQuery lastQuery

namespace EndpointPoints

variable {compared index firstQuery lastQuery}
variable (kept : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery)

/-- The complete actual covering/source pair retained by this endpoint comparison. -/
abbrev pair : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) parents.covered.parents := kept.1.val

/-- The complete original local PreparedParent, including both independent Point caches. -/
abbrev entry : PreparedParent (frame := frame) (basis := basis) (kept.pair.1.entry index).val
    count floor (kept.pair.1.entry index).property targets := kept.2.1.val

/-- The endpoint cache retains the entire original source-pair reader result. -/
theorem pair_eq : kept.pair = compared.sourcePair := kept.1.property

/-- The retained preparation is the whole original bounded occurrence of the SAME stored pair. -/
theorem entry_eq : kept.entry = PreparedParents.entry (frame := frame) (basis := basis) kept.pair.2 index :=
  kept.2.1.property

/-- The whole retained preparation is the original physical source entry at this SAME bounded occurrence.

The complete pair identity transports the original patch, endpoint
admission and all Point/request/model caches together. It supplies no
relation between independently prepared domains or root sheets.
-/
theorem entry_heq : HEq kept.entry (prepared.entry index) :=
  (heq_of_eq kept.entry_eq).trans
    ((Physical.Comparison.entry_heq_of_pair_eq kept.pair_eq index).trans
      (compared.sourcePair_entry_heq index))

/-- Read the actual supplied zero-Query Owner's cached comparison to the SAME original first Point. -/
def firstEquivalent :
    NamedEquivalent (ownerName firstQuery.owner) kept.entry.firstSample.certificate.value.name := kept.2.2.1

/-- Read the independent unit-Query Owner's cached comparison to the SAME original last Point. -/
def lastEquivalent :
    NamedEquivalent (ownerName lastQuery.owner) kept.entry.lastSample.certificate.value.name := kept.2.2.2

/-- Compose the actual physical source/moving/reset comparisons with these SAME cached endpoint relations.

The occurrence is indexed by the entire literal centered parent, not by
matching coordinates. Its original comparison product is selected once;
the two original endpoint relations are read without another patch
comparison. Both distinct full moving/reset EndpointResults are retained.
No LocalRequest, new OwnerJoin or primitive observation is constructed.
-/
def tracePoints
    (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (parents.covered.parents[index.val]'index.isLt)) :
    NamedEquivalent (ownerName (parents.covered.parents[index.val]'index.isLt).edge.owner)
        kept.entry.firstSample.certificate.value.name ×
      (Σ moving : EndpointResult (parents.covered.parents[index.val]'index.isLt),
        NamedEquivalent (ownerName moving.1) kept.entry.lastSample.certificate.value.name) ×
      (Σ reset : EndpointResult (parents.covered.parents[index.val]'index.isLt),
        NamedEquivalent (ownerName reset.1) kept.entry.lastSample.certificate.value.name) :=
  let endpoints := occurrence.traceEndpoints
  let first := NamedEquivalent.transport firstQuery.name_eq.symm rfl kept.firstEquivalent
  let last := NamedEquivalent.transport lastQuery.name_eq.symm rfl kept.lastEquivalent
  let source := (endpoints.1 firstQuery).symm.trans first
  let moving := endpoints.2.1 lastQuery
  let reset := endpoints.2.2 lastQuery
  ⟨source, ⟨⟨moving, moving.2.symm.trans last⟩, ⟨reset, reset.2.symm.trans last⟩⟩⟩

end EndpointPoints

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

end
