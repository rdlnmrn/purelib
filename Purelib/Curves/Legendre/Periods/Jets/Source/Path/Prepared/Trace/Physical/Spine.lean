module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Observation.Spine
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual source integrals on one same-cache acquired physical path

Each original Segment retains its own Parents and completed source product.
The old physical observations are the actual segment views of one retained
whole spine. Per-child errors and integrals are concatenated in their exact
original order; literal shared vertices give a finite telescope. The source
allocation is an exact request-index admission, never a final error input.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

/-- The SAME actual physical acquisitions own their complete Parents and original source caches, independently of
row. -/
@[expose] def Sources
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    Acquisition.Spine width path within owner → Type 1
  | _, _, .nil _, _, _, _ => PUnit
  | _, _, .cons _head tail, within, _owner, retained =>
      Σ parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count retained.1,
        PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets ×
          Sources width tail within.tail retained.1.traced.finishOwner retained.2
termination_by structural _ _ path _ _ _ => path

namespace Sources

/-- Construct canonical center/cover caches once on each actual retained Segment, then prepare its SAME source
product. -/
def build
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained
  | _, _, .nil _, _, _, _ => PUnit.unit
  | _, _, .cons _head tail, within, _owner, retained =>
      let parents := Acquisition.Segment.Parents.build (curve := Fibre.frameCurve frame) basis sheet count retained.1
      let prepared := prepareCovered (frame := frame) (basis := basis) parents.coveredParents floor targets
      let following := build width tail within.tail retained.1.traced.finishOwner retained.2
      ⟨parents, ⟨prepared, following⟩⟩
termination_by structural _ _ path _ _ _ => path

end Sources

/-- One actual original Physical comparison per retained Segment, on its SAME old view and original source family. -/
@[expose] def Cache (row : Row)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width path within owner retained).traced.trace.get) →
    Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained observed → Type 1
  | _, _, .nil _, _, _, _, _, _, _ => PUnit
  | _, _, .cons _head tail, within, _owner, retained, sources, _observed, views =>
      Physical.Comparison row retained.1 sources.1 sources.2.1 allocation views.head ×
        Cache row width allocation tail within.tail retained.1.traced.finishOwner retained.2 sources.2.2
          views.following views.tail
termination_by structural _ _ path _ _ _ _ _ _ => path

namespace Cache

/-- Construct and retain the actual original Physical comparison once on each unchanged physical Segment view. -/
def build (row : Row)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width path within owner retained).traced.trace.get) →
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained observed) →
    Cache (frame := frame) (basis := basis) row width allocation path within owner retained sources observed views
  | _, _, .nil _, _, _, _, _, _, _ => PUnit.unit
  | _, _, .cons _head tail, within, _owner, retained, sources, _observed, views =>
      let compared := Physical.compare row retained.1 sources.1 sources.2.1 allocation views.head
      let following := build row width allocation tail within.tail retained.1.traced.finishOwner retained.2
        sources.2.2 views.following views.tail
      ⟨compared, following⟩
termination_by structural _ _ path _ _ _ _ _ _ => path

/-- Concatenate the actual original row-cell source integrals in their retained physical Segment and child order. -/
@[expose] def integrals (row : Row)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width path within owner retained).traced.trace.get) →
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained observed) →
    Cache (frame := frame) (basis := basis) row width allocation path within owner retained sources observed views →
      List Canonical
  | _, _, .nil _, _, _, _, _, _, _, _ => []
  | _, _, .cons _head tail, within, _owner, retained, sources, _observed, views, compared =>
      compared.1.integrals ++ integrals row width allocation tail within.tail retained.1.traced.finishOwner retained.2
        sources.2.2 views.following views.tail compared.2
termination_by structural _ _ path _ _ _ _ _ _ _ => path

/-- Concatenate every SAME actual complete-block error, retaining both stationary occurrences and each moving
integral. -/
@[expose] def errors (row : Row)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width path within owner retained).traced.trace.get) →
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained observed) →
    Cache (frame := frame) (basis := basis) row width allocation path within owner retained sources observed views →
      List Canonical
  | _, _, .nil _, _, _, _, _, _, _, _ => []
  | _, _, .cons _head tail, within, _owner, retained, sources, _observed, views, compared =>
      compared.1.blockErrors ++ errors row width allocation tail within.tail retained.1.traced.finishOwner retained.2
        sources.2.2 views.following views.tail compared.2
termination_by structural _ _ path _ _ _ _ _ _ _ => path

/-- The SAME actual error list counts precisely the original prepared requests across the retained acquisitions. -/
theorem errors_length (row : Row)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {start finish : Canonical} (path : ClearPath (Paths.polynomial parameter) ambient start finish)
      (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
      (retained : Acquisition.Spine width path within owner)
      (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
        (targets := targets) width path within owner retained)
      (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
        (Acquisition.Spine.assemble width path within owner retained).traced.trace.get)
      (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained observed)
      (compared : Cache (frame := frame) (basis := basis) row width allocation path within owner retained
        sources observed views),
      (errors (frame := frame) (basis := basis) row width allocation path within owner retained
        sources observed views compared).length = Acquisition.Spine.requestCount width path within owner retained
  | _, _, .nil _, _, _, _, _, _, _, _ => rfl
  | _, _, .cons _head tail, within, _owner, retained, sources, _observed, views, compared => by
      change (compared.1.blockErrors ++ _).length = retained.1.traced.prepared.subdivision.requests.length + _
      have head := Trace.Compared.blockErrors_length (frame := frame) (basis := basis) compared.1
      have following := errors_length row width allocation tail within.tail retained.1.traced.finishOwner retained.2
        sources.2.2 views.following views.tail compared.2
      rewrite [Append.length_append, head, following]
      rfl
termination_by structural _ _ path _ _ _ _ _ _ _ => path

/-- Every literal complete-block error is paid by its original old observations and SAME source allocation. -/
theorem errors_bounded (row : Row)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {start finish : Canonical} (path : ClearPath (Paths.polynomial parameter) ambient start finish)
      (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
      (retained : Acquisition.Spine width path within owner)
      (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
        (targets := targets) width path within owner retained)
      (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
        (Acquisition.Spine.assemble width path within owner retained).traced.trace.get)
      (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained observed)
      (compared : Cache (frame := frame) (basis := basis) row width allocation path within owner retained
        sources observed views),
      ∀ error ∈ errors (frame := frame) (basis := basis) row width allocation path within owner retained
        sources observed views compared, Norm.Basic.normSq error ≤ 26 * targets.endpoint
  | _, _, .nil _, _, _, _, _, _, _, _, _, member => by cases member
  | _, _, .cons head tail, within, _owner, retained, sources, _observed, views, compared, error, member => by
      rcases Membership.mem_append.mp member with inHead | inTail
      · exact Trace.Cache.blockErrors_bounded row (frame := frame) (basis := basis)
          (segment := head) (within := within.head) (left := zeroEndpoint) (right := oneEndpoint)
          retained.1.traced.budget allocation retained.1.traced.prepared.subdivision
          compared.1.sources retained.1.traced.fits compared.1.observed.first compared.1.observed.2
          compared.1.cache error inHead
      · exact errors_bounded row width allocation tail within.tail retained.1.traced.finishOwner retained.2
          sources.2.2 views.following views.tail compared.2 error inTail
termination_by structural _ _ path _ _ _ _ _ _ _ _ _ => path

/-- The SAME actual errors telescope exactly across literal old shared vertices and original source integrals. -/
theorem errors_sum_eq (row : Row)
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    ∀ {start finish : Canonical} (path : ClearPath (Paths.polynomial parameter) ambient start finish)
      (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
      (retained : Acquisition.Spine width path within owner)
      (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
        (targets := targets) width path within owner retained)
      (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
        (Acquisition.Spine.assemble width path within owner retained).traced.trace.get)
      (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained observed)
      (compared : Cache (frame := frame) (basis := basis) row width allocation path within owner retained
        sources observed views),
      Norm.Sum.Basic.gaussianSum (errors (frame := frame) (basis := basis) row width allocation path within owner
          retained sources observed views compared) = observed.last.value - observed.first.value -
        Norm.Sum.Basic.gaussianSum (integrals (frame := frame) (basis := basis) row width allocation path within owner
          retained sources observed views compared)
  | _, _, .nil _, _, _, _, _, observed, _, _ => by
      change (0 : Canonical) = observed.first.value - observed.first.value - 0
      ring1
  | _, _, .cons _head tail, within, _owner, retained, sources, observed, views, compared => by
      have firstBound := Physical.Comparison.blockErrors_sum_eq (frame := frame) (basis := basis)
        (row := row) (retained := retained.1) (parents := sources.1) (prepared := sources.2.1) compared.1
      have tailBound := errors_sum_eq row width allocation tail within.tail retained.1.traced.finishOwner retained.2
        sources.2.2 views.following views.tail compared.2
      have shared := congrArg (fun vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
        _ retained.1.traced.finishOwner accuracy => vertex.value) views.shared
      have first := congrArg (fun vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
        _ _owner accuracy => vertex.value) views.head_first
      have last := congrArg (fun vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
        _ (Acquisition.Spine.assemble width tail within.tail retained.1.traced.finishOwner
          retained.2).traced.finishOwner accuracy => vertex.value) views.following_last
      change Norm.Sum.Basic.gaussianSum (compared.1.blockErrors ++ _) = _
      rewrite [Norm.Sum.Basic.gaussianSum_append, firstBound, tailBound]
      change _ = observed.last.value - observed.first.value -
        Norm.Sum.Basic.gaussianSum (compared.1.integrals ++ _)
      rewrite [Norm.Sum.Basic.gaussianSum_append, shared, first, last]
      have telescope (a b c d e : Canonical) : (b - a - d) + (c - b - e) = c - a - (d + e) := by ring1
      exact telescope _ _ _ _ _
termination_by structural _ _ path _ _ _ _ _ _ _ => path

end Cache

variable {width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
  AccuracyRequest}
variable {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {within : path.WithinAmbient} {owner : Owner ((Paths.polynomial parameter).eval start)}
variable (row : Row) (retained : Acquisition width path within owner)
variable {observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
variable (views : Acquisition.Observations retained observed)
variable (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width path within owner retained.spine)
variable (allocation : targets.endpoint = 4 * accuracy.tolerance)

/-- Retain the SAME whole old view/source inputs and the actual Physical comparison fold with its complete factory
law. -/
@[expose] def Compared :=
  Σ keptViews : { value : Acquisition.Observations retained observed // value = views },
    Σ keptSources : { value : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet)
          (targets := targets) width path within owner retained.spine // value = sources },
      { compared : Cache (frame := frame) (basis := basis) row width allocation path within owner retained.spine
          keptSources.val keptViews.val.aligned keptViews.val.segments //
        compared = Cache.build (frame := frame) (basis := basis) row width allocation path within owner retained.spine
          keptSources.val keptViews.val.aligned keptViews.val.segments }

/-- Compare every literal retained physical Segment once using its SAME old spine and original prepared sources. -/
def compare : Compared row retained views sources allocation :=
  let compared := Cache.build (frame := frame) (basis := basis) row width allocation path within owner retained.spine
    sources views.aligned views.segments
  ⟨⟨views, rfl⟩, ⟨sources, rfl⟩, ⟨compared, rfl⟩⟩

namespace Compared

variable {row retained views sources allocation}
variable (compared : Compared row retained views sources allocation)

/-- Read the unchanged whole old physical-spine and exact segment-split cache supplied as the original input. -/
@[expose] def observations : Acquisition.Observations retained observed := compared.1.val

/-- Read the SAME whole original center/cover/preparation family on those literal physical acquisitions. -/
@[expose] def prepared : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    (targets := targets) width path within owner retained.spine := compared.2.1.val

/-- Read the complete actual ordered original Physical comparison execution. -/
@[expose] def cache : Cache (frame := frame) (basis := basis) row width allocation path within owner retained.spine
    compared.prepared compared.observations.aligned compared.observations.segments := compared.2.2.val

/-- The whole old input and its actual view factories remain literally the supplied complete cache. -/
theorem observations_eq : compared.observations = views := compared.1.property

/-- All original source caches remain the whole supplied original family without another preparation. -/
theorem prepared_eq : compared.prepared = sources := compared.2.1.property

/-- The actual Physical fold is the original factory on these identical stored inputs. -/
theorem cache_eq : compared.cache = Cache.build (frame := frame) (basis := basis) row width allocation path within
    owner retained.spine compared.prepared compared.observations.aligned compared.observations.segments :=
  compared.2.2.property

/-- Read every actual original row-cell source integral in physical Segment and primitive-child order. -/
@[expose] def integrals : List Canonical :=
  Cache.integrals (frame := frame) (basis := basis) row width allocation path within owner retained.spine
    compared.prepared compared.observations.aligned compared.observations.segments compared.cache

/-- Read every actual stationary/moving complete-block error without dropping an original occurrence. -/
@[expose] def errors : List Canonical :=
  Cache.errors (frame := frame) (basis := basis) row width allocation path within owner retained.spine
    compared.prepared compared.observations.aligned compared.observations.segments compared.cache

/-- The exact original source allocation pays every member of the SAME actual physical complete-block error list. -/
theorem errors_bounded : ∀ error ∈ compared.errors, Norm.Basic.normSq error ≤ 26 * targets.endpoint :=
  Cache.errors_bounded (frame := frame) (basis := basis) row width allocation path within owner retained.spine
    compared.prepared compared.observations.aligned compared.observations.segments compared.cache

/-- The full list retains the original moving-request count computed before source preparation or observation. -/
theorem errors_length : compared.errors.length =
    Acquisition.Spine.requestCount width path within owner retained.spine :=
  Cache.errors_length (frame := frame) (basis := basis) row width allocation path within owner retained.spine
    compared.prepared compared.observations.aligned compared.observations.segments compared.cache

/-- The actual old physical endpoints telescope against the SAME retained source-model integral samples. -/
theorem errors_sum_eq : Norm.Sum.Basic.gaussianSum compared.errors =
    observed.last.value - observed.first.value - Norm.Sum.Basic.gaussianSum compared.integrals := by
  have scalar := Cache.errors_sum_eq (frame := frame) (basis := basis) row width allocation path within owner
    retained.spine compared.prepared compared.observations.aligned compared.observations.segments compared.cache
  rewrite [compared.observations.first_value, compared.observations.last_value] at scalar
  exact scalar

/-- A computed finite count of the SAME old complete-block errors pays the actual physical endpoint/integral
residual. -/
theorem integral_error_le : Norm.Basic.normSq
    (observed.last.value - observed.first.value - Norm.Sum.Basic.gaussianSum compared.integrals) ≤
      (Acquisition.Spine.requestCount width path within owner retained.spine : Rational) *
        ((Acquisition.Spine.requestCount width path within owner retained.spine : Rational) *
          (26 * targets.endpoint)) := by
  have paid := Norm.Sum.Bounds.normSq_sum_le compared.errors (26 * targets.endpoint) compared.errors_bounded
  rewrite [compared.errors_sum_eq, compared.errors_length] at paid
  exact paid

end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

end
