module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Requests
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-! # Original full-block source errors across the same actual paid quarter

The original paid target list and whole old Block views drive every index.
Source families are prepared once independently of row. Each row comparison
consumes those SAME sources and old observations, then concatenates actual
per-Route errors and source integrals in order. Literal shared vertices
prove the telescope; no aggregate residual inequality is supplied.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
  (widthRequest)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Steps.Acquisition.Observation.Blocks

/-- The SAME actual paid Blocks retain complete original source families independently of the selected row. -/
@[expose] def Sources : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) → Type 1
  | [] => fun _ _ _ _ _ _ _ => PUnit
  | target :: targets => fun _ _ _ original sourceOwner _ paid =>
      PreparedParents.Trace.Physical.Spine.Sources (frame := frame) (basis := basis) (count := count)
        (floor := floor) (sheet := sheet) (targets := sourceTargets)
        (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
        original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine ×
        Sources targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail
termination_by structural targets => targets

namespace Sources

/-- Prepare each actual retained Route's original center/cover/source family once, shared by all row comparisons. -/
def build : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid
  | [] => fun _ _ _ _ _ _ _ => PUnit.unit
  | target :: targets => fun _ _ _ original sourceOwner _ paid =>
      let head := PreparedParents.Trace.Physical.Spine.Sources.build (frame := frame) (basis := basis)
        (count := count) (floor := floor) (sheet := sheet) (targets := sourceTargets)
        (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
        original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine
      let following := build targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail
      ⟨head, following⟩
termination_by structural targets => targets

end Sources

/-- Every original paid Block retains its actual per-Route comparison on the SAME old views and shared source family. -/
@[expose] def Cache (row : Row) (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance) :
    (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.trace) →
    Blocks actual regular (row.expression parameter) accuracy targets current reading originalOwner
      original sourceOwner agreement paid observed → Type 1
  | [] => fun _ _ _ _ _ _ _ _ _ _ => PUnit
  | target :: targets => fun _ _ _ original _sourceOwner _ paid sources _observed views =>
      PreparedParents.Trace.Physical.Spine.Compared (frame := frame) (basis := basis) (count := count)
        (floor := floor) (sheet := sheet) (targets := sourceTargets) row paid.head.paid.paid
        views.physical sources.1 allocation ×
        Cache row allocation targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
          views.following views.tail
termination_by structural targets => targets

namespace Cache

/-- Compare each actual paid Block once on its complete old physical views and SAME already prepared source family. -/
def build (row : Row) (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance) :
    (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.trace) →
    (views : Blocks actual regular (row.expression parameter) accuracy targets current reading originalOwner
      original sourceOwner agreement paid observed) →
    Cache (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
      sourceOwner agreement paid sources observed views
  | [] => fun _ _ _ _ _ _ _ _ _ _ => PUnit.unit
  | target :: targets => fun _ _ _ original _sourceOwner _ paid sources _observed views =>
      let head := compareHead (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (sourceTargets := sourceTargets) row views sources.1 allocation
      let following := build row allocation targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
        views.following views.tail
      ⟨head, following⟩
termination_by structural targets => targets

/-- Read the SAME original source integral list in exact paid Block, physical Segment and child order. -/
@[expose] def integrals (row : Row) (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance) :
    (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.trace) →
    (views : Blocks actual regular (row.expression parameter) accuracy targets current reading originalOwner
      original sourceOwner agreement paid observed) →
    Cache (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
      sourceOwner agreement paid sources observed views → List Canonical
  | [] => fun _ _ _ _ _ _ _ _ _ _ _ => []
  | target :: targets => fun _ _ _ original _sourceOwner _ paid sources _observed views compared =>
      compared.1.integrals ++ integrals row allocation targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
        views.following views.tail compared.2
termination_by structural targets => targets

/-- Read every actual full-block error, preserving all original stationary and moving occurrences in order. -/
@[expose] def errors (row : Row) (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance) :
    (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.trace) →
    (views : Blocks actual regular (row.expression parameter) accuracy targets current reading originalOwner
      original sourceOwner agreement paid observed) →
    Cache (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
      sourceOwner agreement paid sources observed views → List Canonical
  | [] => fun _ _ _ _ _ _ _ _ _ _ _ => []
  | target :: targets => fun _ _ _ original _sourceOwner _ paid sources _observed views compared =>
      compared.1.errors ++ errors row allocation targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
        views.following views.tail compared.2
termination_by structural targets => targets

/-- The flattened actual error list has precisely the SAME retained original moving-request count. -/
theorem errors_length (row : Row) (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance) :
    ∀ (targets : List Endpoint) (current : Endpoint) (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter positive current)
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : InitialAgreement current reading sourceOwner) (paid : Acquisition original sourceOwner agreement)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid)
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.trace)
    (views : Blocks actual regular (row.expression parameter) accuracy targets current reading originalOwner
      original sourceOwner agreement paid observed)
    (compared : Cache (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
      sourceOwner agreement paid sources observed views),
    (errors (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
        sourceOwner agreement paid sources observed views compared).length =
        Steps.Acquisition.Spine.requestCount targets current reading originalOwner original sourceOwner agreement paid
  | [] => fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  | target :: targets => fun _ _ _ original _sourceOwner _ paid sources _observed views compared => by
      change (compared.1.errors ++ _).length = _ + _
      have first := compared.1.errors_length
      have following := errors_length row allocation targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
        views.following views.tail compared.2
      rewrite [Append.length_append, first, following]
      rfl
termination_by structural targets => targets

/-- Every member of the SAME actual flattened list is paid by the original per-Route comparison cache. -/
theorem errors_bounded (row : Row) (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance) :
    ∀ (targets : List Endpoint) (current : Endpoint) (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter positive current)
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : InitialAgreement current reading sourceOwner) (paid : Acquisition original sourceOwner agreement)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid)
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.trace)
    (views : Blocks actual regular (row.expression parameter) accuracy targets current reading originalOwner
      original sourceOwner agreement paid observed)
    (compared : Cache (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
      sourceOwner agreement paid sources observed views),
    ∀ error ∈ errors (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
        sourceOwner agreement paid sources observed views compared,
      Norm.Basic.normSq error ≤ 26 * sourceTargets.endpoint
  | [] => fun _ _ _ _ _ _ _ _ _ _ _ _ member => by cases member
  | target :: targets => fun _ _ _ original _sourceOwner _ paid sources _observed views compared error member => by
      rcases Membership.mem_append.mp member with first | following
      · exact compared.1.errors_bounded error first
      · exact errors_bounded row allocation targets target original.nextReading
          original.headCovered.finishOwner original.tail
          paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
          views.following views.tail compared.2 error following
termination_by structural targets => targets

/-- Actual full-block errors telescope on the SAME old whole-quarter endpoints and original retained source
integrals. -/
theorem errors_sum_eq (row : Row) (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance) :
    ∀ (targets : List Endpoint) (current : Endpoint) (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter positive current)
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : InitialAgreement current reading sourceOwner) (paid : Acquisition original sourceOwner agreement)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid)
    (observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy paid.trace)
    (views : Blocks actual regular (row.expression parameter) accuracy targets current reading originalOwner
      original sourceOwner agreement paid observed)
    (compared : Cache (frame := frame) (basis := basis) row allocation targets current reading originalOwner original
      sourceOwner agreement paid sources observed views),
    Norm.Sum.Basic.gaussianSum (errors (frame := frame) (basis := basis) row allocation targets current reading
        originalOwner original
        sourceOwner agreement paid sources observed views compared) =
      observed.last.value - observed.first.value -
      Norm.Sum.Basic.gaussianSum (integrals (frame := frame) (basis := basis)
        row allocation targets current reading originalOwner original
        sourceOwner agreement paid sources observed views compared)
  | [] => fun _ _ _ _ _ _ _ _ observed _ _ => by
      change (0 : Canonical) = observed.first.value - observed.first.value - 0
      ring1
  | target :: targets => fun _ _ _ original sourceOwner _ paid sources observed views compared => by
      have firstBound := compared.1.errors_sum_eq
      have tailBound := errors_sum_eq row allocation targets target original.nextReading
        original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
        views.following views.tail compared.2
      have shared := congrArg (fun vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
        _ paid.head.finishOwner accuracy => vertex.value) views.shared
      have first := congrArg (fun vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
        _ sourceOwner accuracy => vertex.value) views.head_first
      have last := congrArg (fun vertex : OwnerPath.Primitive.Vertex (row.expression parameter)
        _ paid.tail.finishOwner accuracy => vertex.value) views.following_last
      change Norm.Sum.Basic.gaussianSum (compared.1.errors ++ _) = _
      rewrite [Norm.Sum.Basic.gaussianSum_append, firstBound, tailBound]
      change _ = observed.last.value - observed.first.value -
        Norm.Sum.Basic.gaussianSum (compared.1.integrals ++ _)
      rewrite [Norm.Sum.Basic.gaussianSum_append]
      have endpoint := congrArg₂ (fun left right : Canonical => left + right)
        (congrArg (fun value : Canonical => views.head.last.value - value -
          Norm.Sum.Basic.gaussianSum compared.1.integrals) first)
        (congrArg₂ (fun finish start : Canonical => finish - start -
          Norm.Sum.Basic.gaussianSum (integrals row allocation targets target original.nextReading
            original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement
            paid.tail sources.2 views.following views.tail compared.2)) last shared)
      have telescope (a b c d e : Canonical) : (b - a - d) + (c - b - e) = c - a - (d + e) := by ring1
      exact endpoint.trans (telescope _ _ _ _ _)
termination_by structural targets => targets

end Cache

end Steps.Acquisition.Observation.Blocks

namespace Steps.Acquisition.Quarter

variable {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {givenQuarter : Steps.Quarter actual regular current reading originalOwner}
variable {agreement : InitialAgreement current reading sourceOwner}

section Preparation

variable (quarter : Quarter givenQuarter sourceOwner agreement)

/-- The actual whole paid quarter retains one complete original per-Block source family shared by all primitive rows. -/
abbrev Sources := Observation.Blocks.Sources (frame := frame) (basis := basis) (count := count)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) quarter.originalQuarter.cache.val current reading
  originalOwner quarter.originalQuarter.steps sourceOwner agreement quarter.receipt

namespace Sources

/-- Prepare the original actual quarter's source family once without observing any row expression. -/
def build : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    (sourceTargets := sourceTargets) quarter :=
  Observation.Blocks.Sources.build (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (sourceTargets := sourceTargets) quarter.originalQuarter.cache.val current reading originalOwner
    quarter.originalQuarter.steps sourceOwner agreement quarter.receipt

end Sources

end Preparation

section Comparison

variable (row : Row) (quarter : Quarter givenQuarter sourceOwner agreement)
variable {observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy quarter.receipt.trace}
variable (views : Observations quarter observed)
variable (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (sourceTargets := sourceTargets) quarter)
variable (allocation : sourceTargets.endpoint = 4 * accuracy.tolerance)

/-- The SAME old whole quarter views and shared source family retain every actual original per-Route comparison
cache. -/
@[expose] def Compared :=
  Σ keptViews : { value : Observations quarter observed // value = views },
    Σ keptSources : { value : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (sourceTargets := sourceTargets) quarter // value = sources },
      { cache : Blocks.Cache (frame := frame) (basis := basis) row allocation
          quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
          agreement quarter.receipt keptSources.val keptViews.val.original keptViews.val.blocks //
        cache = Blocks.Cache.build (frame := frame) (basis := basis) row allocation
          quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
          agreement quarter.receipt keptSources.val keptViews.val.original keptViews.val.blocks }

/-- Compare the actual original source families with their SAME complete old quarter observations once, without
preparing rows. -/
def compare : Compared row quarter views sources allocation :=
  let cache := Blocks.Cache.build (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt sources views.original views.blocks
  ⟨⟨views, rfl⟩, ⟨sources, rfl⟩, ⟨cache, rfl⟩⟩

namespace Compared

variable {row quarter views sources allocation}
variable (compared : Compared row quarter views sources allocation)

/-- Read the SAME complete old quarter/Block/physical Segment views without another split or observer. -/
@[expose] def observations : Observations quarter observed := compared.1.val

/-- Read the unchanged shared original source family, independent of the selected primitive row. -/
@[expose] def prepared : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    (sourceTargets := sourceTargets) quarter := compared.2.1.val

/-- Read all actual retained original per-Route source comparisons in the same paid target-list order. -/
@[expose] def cache : Blocks.Cache (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt compared.prepared compared.observations.original
    compared.observations.blocks := compared.2.2.val

/-- The complete old observation views are the supplied original cache, with no comparison or observation replay. -/
theorem observations_eq : compared.observations = views := compared.1.property

/-- The complete original source family is the identical supplied shared input. -/
theorem prepared_eq : compared.prepared = sources := compared.2.1.property

/-- Every stored per-Route comparison is the factory on these SAME actual source families and complete old
observations. -/
theorem cache_eq : compared.cache = Blocks.Cache.build (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt compared.prepared compared.observations.original
    compared.observations.blocks := compared.2.2.property

/-- Read the exact original source-model integrals in paid Block, physical Segment and child order. -/
@[expose] def integrals : List Canonical :=
  Blocks.Cache.integrals (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt compared.prepared compared.observations.original
    compared.observations.blocks compared.cache

/-- Read every same original stationary/moving full-block error in the identical paid execution order. -/
@[expose] def errors : List Canonical :=
  Blocks.Cache.errors (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt compared.prepared compared.observations.original
    compared.observations.blocks compared.cache

/-- All actual full-block errors are paid by the SAME original per-Route caches and exact source allocation. -/
theorem errors_bounded : ∀ error ∈ compared.errors, Norm.Basic.normSq error ≤ 26 * sourceTargets.endpoint :=
  Blocks.Cache.errors_bounded (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt compared.prepared compared.observations.original
    compared.observations.blocks compared.cache

/-- The flattened list has precisely this SAME original paid quarter's retained prepared moving-request count. -/
theorem errors_length : compared.errors.length = quarter.requestCount :=
  Blocks.Cache.errors_length (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt compared.prepared compared.observations.original
    compared.observations.blocks compared.cache

/-- The SAME actual flattened errors telescope on the original old quarter endpoints and actual source-model
integrals. -/
theorem errors_sum_eq : Norm.Sum.Basic.gaussianSum compared.errors =
    observed.last.value - observed.first.value - Norm.Sum.Basic.gaussianSum compared.integrals := by
  have scalar := Blocks.Cache.errors_sum_eq (frame := frame) (basis := basis) row allocation
    quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps sourceOwner
    agreement quarter.receipt compared.prepared compared.observations.original
    compared.observations.blocks compared.cache
  have first := congrArg (fun old : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
    quarter.receipt.trace => old.first.value) compared.observations.original_eq
  have last := congrArg (fun old : OwnerPath.Primitive.Spine (row.expression parameter) accuracy
    quarter.receipt.trace => old.last.value) compared.observations.original_eq
  rewrite [first, last] at scalar
  exact scalar

/-- The computed actual quarter count pays the SAME old endpoint/source-integral residual with no aggregate-bound
input. -/
theorem integral_error_le : Norm.Basic.normSq
    (observed.last.value - observed.first.value - Norm.Sum.Basic.gaussianSum compared.integrals) ≤
      (quarter.requestCount : Rational) * ((quarter.requestCount : Rational) * (26 * sourceTargets.endpoint)) := by
  have paid := Norm.Sum.Bounds.normSq_sum_le compared.errors (26 * sourceTargets.endpoint) compared.errors_bounded
  rewrite [compared.errors_sum_eq, compared.errors_length] at paid
  exact paid

end Compared

end Comparison

end Steps.Acquisition.Quarter

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
