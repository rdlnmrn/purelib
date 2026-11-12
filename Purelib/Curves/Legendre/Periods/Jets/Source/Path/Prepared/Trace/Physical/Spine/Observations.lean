module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Fin
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction

/-! # Original source occurrences and their retained physical observations

The reader follows the same acquired ClearPath, source family and old segment
split cache. It returns an existing whole Segment observation and its already
computed Physical comparison. No source, observation, Query or Owner is
acquired. The original Compared still retains the whole old input, including
its nil case and every stationary or repeated occurrence.
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

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest}
variable {width : {start finish : Canonical} →
  ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}

namespace Sources

/-- One original Segment observation and its retained comparison on the identical source tuple.

The complete observation contains every original Vertex and stationary
comparison. The comparison is the original fold result on those observations,
its exact acquired Segment, Parents and prepared source product.
-/
@[expose] def SegmentObservation (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance)
    (selected : SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width) :=
  Σ observed : Primitive.Spine (row.expression parameter) accuracy selected.acquired.traced.trace.get,
    Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) row selected.acquired selected.parents selected.prepared allocation observed

namespace SegmentObservation

variable {row : Row} {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {selected : SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) width}
variable (stored : SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) (width := width) row allocation selected)

/-- Read the complete old physical Segment observation without selecting another observation. -/
def observed : Primitive.Spine (row.expression parameter) accuracy
    selected.acquired.traced.trace.get := stored.1

/-- The observation getter returns the complete first component of the retained cache. -/
private theorem packaged_observed_eq : stored.observed = stored.1 := rfl

/-- The observation getter returns the complete first component of the retained cache.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ObservedEqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {row : Row}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {selected : SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width}
    (stored : SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation selected),
    stored.observed = stored.1

/-- The observation getter returns the complete first component of the retained cache. -/
theorem observed_eq : ObservedEqLaw := by
  unfold ObservedEqLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width row allocation selected stored
  exact packaged_observed_eq stored

/-- Read the existing source comparison on that same complete old Segment observation. -/
def comparison : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) row selected.acquired selected.parents selected.prepared allocation stored.observed := stored.2

/-- The comparison's internal observation is the whole original physical Segment cache under its owned transport.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ObservedHeqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {row : Row}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {selected : SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width}
    (stored : SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation selected),
    HEq stored.comparison.observed stored.observed

/-- The comparison's internal observation is the whole original physical Segment cache under its owned transport. -/
theorem observed_heq : ObservedHeqLaw := by
  unfold ObservedHeqLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width row allocation selected stored
  exact Physical.Comparison.observed_heq stored.comparison

/-- The actual retained source comparison pays its original Segment endpoint increment and source-model sum.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def IntegralErrorLeLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {row : Row}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {selected : SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width}
    (stored : SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation selected),
    Norm.Basic.normSq
    (stored.observed.last.value - stored.observed.first.value -
      Norm.Sum.Basic.gaussianSum stored.comparison.integrals) ≤
      (selected.acquired.traced.prepared.subdivision.requests.length : Rational) *
        ((selected.acquired.traced.prepared.subdivision.requests.length : Rational) *
          (26 * targets.endpoint))

/-- The actual retained source comparison pays its original Segment endpoint increment and source-model sum.

The count is the selected Segment's actual request count. It is not a count
of newly chosen cut pieces, and the original observation accuracy is unchanged.
-/
theorem integral_error_le : IntegralErrorLeLaw := by
  unfold IntegralErrorLeLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width row allocation selected stored
  exact Physical.Comparison.integral_error_le stored.comparison

end SegmentObservation
end Sources

namespace Cache

/-- Package one complete old observation and comparison at an abstract literal source tuple. -/
private def packSegmentObservation (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance)
    {start finish : Canonical} (segment : ClearSegment (Paths.polynomial parameter) ambient start finish)
    (within : segment.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
    (acquired : Acquisition.Segment (segment := segment) (within := within) (owner := owner) (width segment))
    (parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count acquired)
    (prepared : PreparedParents parents.coveredParents floor targets)
    (observed : Primitive.Spine (row.expression parameter) accuracy acquired.traced.trace.get)
    (compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) row acquired parents prepared allocation observed) :
    Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation
      ⟨(start, finish), ⟨segment, within⟩, owner, acquired, parents, prepared⟩ :=
  ⟨observed, compared⟩

/-- Select a whole observation through abstract source-index equations before specializing physical caches.

The two equality transports change only the complete source index. Both
branches retain their original whole observation/comparison values; the
successor receives the literal ordered recursive result without replay.
-/
private def selectSegmentObservation (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance)
    {size : Nat}
    (selected : Fin (size + 1) → Sources.SegmentSources (frame := frame) (basis := basis)
      (count := count) (floor := floor) (sheet := sheet) (targets := targets) width)
    (first : Sources.SegmentSources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width)
    (following : Fin size → Sources.SegmentSources (frame := frame) (basis := basis)
      (count := count) (floor := floor) (sheet := sheet) (targets := targets) width)
    (first_eq : selected ⟨0, Nat.zero_lt_succ size⟩ = first)
    (following_eq : ∀ index, selected index.succ = following index)
    (observedFirst : Sources.SegmentObservation (frame := frame) (basis := basis) (count := count)
      (floor := floor) (sheet := sheet) (targets := targets) (width := width) row allocation first)
    (observedFollowing : ∀ index, Sources.SegmentObservation (frame := frame) (basis := basis)
      (count := count) (floor := floor) (sheet := sheet) (targets := targets) (width := width)
      row allocation (following index)) (index : Fin (size + 1)) :
    Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation (selected index) :=
  Data.Fin.casesDependent (motive := fun position => Sources.SegmentObservation (frame := frame)
      (basis := basis) (count := count) (floor := floor) (sheet := sheet) (targets := targets)
      (width := width) row allocation (selected position))
    (Eq.mp (congrArg (fun value : Sources.SegmentSources (frame := frame) (basis := basis) (count := count)
        (floor := floor) (sheet := sheet) (targets := targets) width =>
      Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := targets) (width := width) row allocation value) first_eq.symm) observedFirst)
    (fun next => Eq.mp
      (congrArg (fun value : Sources.SegmentSources (frame := frame) (basis := basis) (count := count)
          (floor := floor) (sheet := sheet) (targets := targets) width =>
        Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) (width := width) row allocation value) (following_eq next).symm)
      (observedFollowing next)) index

/-- Locate the existing physical observation and comparison at one original source-Segment occurrence.

The head packages the literal old split head and the already retained head
comparison. A successor follows the original acquisition, source, observation
and comparison tails at their actual finish Owner. No executable factory is
repeated. A stationary cons remains a separate occurrence; nil has no index.
-/
def segmentAt (row : Row)
    (width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width path within owner retained) →
    (observed : Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width path within owner retained).traced.trace.get) →
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width path within owner retained
      observed) →
    Cache (frame := frame) (basis := basis) row width allocation path within owner retained sources observed views →
    (index : Fin (Sources.parentWords (frame := frame) (basis := basis) width path within owner retained
      sources).length) →
    Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation
      (Sources.segmentAt (frame := frame) (basis := basis) width path within owner retained sources index)
  | _, _, .nil _, _, _, _, _, _, _, _, index => Fin.elim0 index
  | start, _, .cons (middle := middle) head tail, within, owner, retained, sources, _observed, views, compared, index =>
      selectSegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := targets) (width := width) row allocation
        (size := (Sources.parentWords (frame := frame) (basis := basis) width tail within.tail
          retained.1.traced.finishOwner retained.2 sources.2.2).length)
        (fun position => Sources.segmentAt (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) width (.cons head tail) within owner retained sources position)
        ⟨(start, middle), ⟨head, within.head⟩, owner, retained.1, sources.1, sources.2.1⟩
        (fun next => Sources.segmentAt (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) width tail within.tail retained.1.traced.finishOwner retained.2
          sources.2.2 next)
        (Sources.segmentAt_zero (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) (width := width) (head := head) (tail := tail)
          (within := within) (owner := owner) (retained := retained) (kept := sources))
        (fun next => Sources.segmentAt_succ (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) (width := width) (head := head) (tail := tail)
          (within := within) (owner := owner) (retained := retained) (kept := sources) next)
        (packSegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
          (sheet := sheet) (targets := targets) (width := width) row allocation head within.head owner retained.1
          sources.1 sources.2.1 views.head compared.1)
        (fun next => segmentAt row width allocation tail within.tail retained.1.traced.finishOwner retained.2
          sources.2.2 views.following views.tail compared.2 next) index
termination_by structural _ _ path _ _ _ _ _ _ _ _ => path

section Readbacks

variable {row : Row} {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {start middle finish : Canonical}
variable {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
variable {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
variable {within : (ClearPath.cons head tail).WithinAmbient}
variable {owner : Owner ((Paths.polynomial parameter).eval start)}
variable {retained : Acquisition.Spine width (.cons head tail) within owner}
variable {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) width (.cons head tail) within owner retained}
variable {observed : Primitive.Spine (row.expression parameter) accuracy
  (Acquisition.Spine.assemble width (.cons head tail) within owner retained).traced.trace.get}
variable (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width (.cons head tail) within
  owner retained observed)
variable (compared : Cache (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner
  retained sources observed views)

/-- Head lookup returns both complete original cached values, including the actual comparison witness. -/
private theorem packaged_segmentAt_zero :
    segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained sources
      observed views compared ⟨0, Nat.zero_lt_succ _⟩ = ⟨views.head, compared.1⟩ := by rfl

/-- Head lookup returns the identical complete cached observation and comparison.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def SegmentAtZeroLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {row : Row}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {start : Canonical}
    {middle : Canonical}
    {finish : Canonical}
    {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
    {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
    {within : (ClearPath.cons head tail).WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {retained : Acquisition.Spine width (.cons head tail) within owner}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width (.cons head tail) within owner retained}
    {observed : Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width (.cons head tail) within owner retained).traced.trace.get}
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width (.cons head tail) within
      owner retained observed)
    (compared : Cache (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner
      retained sources observed views),
    segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained sources
      observed views compared ⟨0, Nat.zero_lt_succ _⟩ = ⟨views.head, compared.1⟩

/-- Head lookup returns the identical complete cached observation and comparison. -/
theorem segmentAt_zero : SegmentAtZeroLaw := by
  unfold SegmentAtZeroLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width row allocation start middle finish head tail within owner retained sources observed views compared
  exact packaged_segmentAt_zero views compared

/-- Head lookup reads the identical whole head observation from the original split cache. -/
private theorem packaged_segmentAt_zero_observed :
    (segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained
      sources observed views compared ⟨0, Nat.zero_lt_succ _⟩).observed = views.head := by rfl

/-- Head lookup reads the identical whole head observation from the original split cache.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def SegmentAtZeroObservedLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {row : Row}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {start : Canonical}
    {middle : Canonical}
    {finish : Canonical}
    {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
    {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
    {within : (ClearPath.cons head tail).WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {retained : Acquisition.Spine width (.cons head tail) within owner}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width (.cons head tail) within owner retained}
    {observed : Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width (.cons head tail) within owner retained).traced.trace.get}
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width (.cons head tail) within
      owner retained observed)
    (compared : Cache (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner
      retained sources observed views),
    (segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained
      sources observed views compared ⟨0, Nat.zero_lt_succ _⟩).observed = views.head

/-- Head lookup reads the identical whole head observation from the original split cache. -/
theorem segmentAt_zero_observed : SegmentAtZeroObservedLaw := by
  unfold SegmentAtZeroObservedLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width row allocation start middle finish head tail within owner retained sources observed views compared
  exact packaged_segmentAt_zero_observed views compared

/-- Successor lookup returns the identical whole result from the original ordered tails. -/
private theorem packaged_segmentAt_succ
    (index : Fin (Sources.parentWords (frame := frame) (basis := basis) width tail within.tail
      retained.1.traced.finishOwner retained.2 sources.2.2).length) :
    segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained sources
      observed views compared index.succ =
      segmentAt (frame := frame) (basis := basis) row width allocation tail within.tail
        retained.1.traced.finishOwner retained.2 sources.2.2 views.following views.tail compared.2 index := by rfl

/-- Successor lookup returns the identical whole result from the original ordered tails.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def SegmentAtSuccLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {row : Row}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {start : Canonical}
    {middle : Canonical}
    {finish : Canonical}
    {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
    {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
    {within : (ClearPath.cons head tail).WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {retained : Acquisition.Spine width (.cons head tail) within owner}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width (.cons head tail) within owner retained}
    {observed : Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width (.cons head tail) within owner retained).traced.trace.get}
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width (.cons head tail) within
      owner retained observed)
    (compared : Cache (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner
      retained sources observed views)
    (index : Fin (Sources.parentWords (frame := frame) (basis := basis) width tail within.tail
      retained.1.traced.finishOwner retained.2 sources.2.2).length),
    segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained sources
      observed views compared index.succ =
      segmentAt (frame := frame) (basis := basis) row width allocation tail within.tail
        retained.1.traced.finishOwner retained.2 sources.2.2 views.following views.tail compared.2 index

/-- Successor lookup returns the identical whole result from the original ordered tails. -/
theorem segmentAt_succ : SegmentAtSuccLaw := by
  unfold SegmentAtSuccLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width row allocation start middle finish head tail within owner retained sources observed views compared
    index
  exact packaged_segmentAt_succ views compared index

/-- The selected head and literal old suffix reconstruct the complete supplied original observation spine.

This is a whole Split-factory readback. It preserves the actual stationary
comparisons as well as moving observations, without replacing a shared Vertex
by an independently acquired cache at the same Owner or coordinate.
-/
private theorem packaged_segmentAt_zero_append :
    Primitive.Spine.append
      (segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained
        sources observed views compared
        ⟨0, Nat.zero_lt_succ _⟩).observed views.following
      (views.shared.trans (congrArg (fun value => value.last)
        (segmentAt_zero_observed views compared)).symm) = observed := by
  have same := Primitive.Spine.append_congr (segmentAt_zero_observed views compared)
    (Eq.refl views.following)
    (views.shared.trans (congrArg (fun value => value.last) (segmentAt_zero_observed views compared)).symm)
    views.shared
  have projected := congrArg (fun divided : Primitive.Spine.Split
      (expression := row.expression parameter) (accuracy := accuracy) retained.1.traced.trace.get
      (Acquisition.Spine.assemble width tail within.tail retained.1.traced.finishOwner retained.2).traced.trace.get =>
        Primitive.Spine.append divided.before divided.after divided.shared) views.divided_eq
  dsimp only at projected
  exact same.trans (projected.trans (Primitive.Spine.append_split observed))

/-- The retained head and literal suffix reconstruct the complete original observation spine.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def SegmentAtZeroAppendLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {row : Row}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {start : Canonical}
    {middle : Canonical}
    {finish : Canonical}
    {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
    {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
    {within : (ClearPath.cons head tail).WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {retained : Acquisition.Spine width (.cons head tail) within owner}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width (.cons head tail) within owner retained}
    {observed : Primitive.Spine (row.expression parameter) accuracy
      (Acquisition.Spine.assemble width (.cons head tail) within owner retained).traced.trace.get}
    (views : Acquisition.Spine.Segments (row.expression parameter) accuracy width (.cons head tail) within
      owner retained observed)
    (compared : Cache (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner
      retained sources observed views),
    Primitive.Spine.append
      (segmentAt (frame := frame) (basis := basis) row width allocation (.cons head tail) within owner retained
        sources observed views compared
        ⟨0, Nat.zero_lt_succ _⟩).observed views.following
      (views.shared.trans (congrArg (fun value => value.last)
        (segmentAt_zero_observed views compared)).symm) = observed

/-- The retained head and literal suffix reconstruct the complete original observation spine. -/
theorem segmentAt_zero_append : SegmentAtZeroAppendLaw := by
  unfold SegmentAtZeroAppendLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width row allocation start middle finish head tail within owner retained sources observed views compared
  exact packaged_segmentAt_zero_append views compared

end Readbacks
end Cache

namespace Compared

variable {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {within : path.WithinAmbient} {owner : Owner ((Paths.polynomial parameter).eval start)}
variable {row : Row} {retained : Acquisition width path within owner}
variable {observed : Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
variable {views : Acquisition.Observations retained observed}
variable {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) width path within owner retained.spine}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable (compared : Compared row retained views sources allocation)

/-- Read one original source Segment together with the identical physical observation/comparison pair it consumed. -/
def segmentAt (index : Fin (Sources.parentWords (frame := frame) (basis := basis) width path within owner
  retained.spine compared.prepared).length) :
    Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation
      (Sources.segmentAt (frame := frame) (basis := basis) width path within owner retained.spine compared.prepared
        index) :=
  Cache.segmentAt (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := targets) row width allocation path within owner retained.spine compared.prepared
    compared.observations.aligned compared.observations.segments compared.cache index

/-- Read the physical observation/comparison pair selected by an actual retained global parent occurrence.

The same ordered Flatten occurrence determines its original Segment; its
original local child index and whole prepared-parent transport remain the
existing Sources readers. Repeated equal parents are never deduplicated.
-/
def parentSegment
    (index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).geometry.parents.length)
    (position : Flatten.Occurrence (Sources.parentWords (frame := frame) (basis := basis) width path within owner
      retained.spine compared.prepared)
      (Sources.flattenedIndex (frame := frame) (basis := basis) path within owner retained.spine
        compared.prepared index)) :
    Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation
      (Sources.selected (frame := frame) (basis := basis) path within owner retained.spine
        compared.prepared index position) :=
  segmentAt (frame := frame) (basis := basis) compared position.1

/-- The global parent keeps its original complete preparation at the same physical Segment and local child index.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ParentSegmentPreparedHeqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {start : Canonical}
    {finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {within : path.WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {row : Row}
    {retained : Acquisition width path within owner}
    {observed : Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
    {views : Acquisition.Observations retained observed}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width path within owner retained.spine}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    (compared : Compared row retained views sources allocation)
    (index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).geometry.parents.length)
    (position : Flatten.Occurrence (Sources.parentWords (frame := frame) (basis := basis) width path within owner
      retained.spine compared.prepared)
      (Sources.flattenedIndex (frame := frame) (basis := basis) path within owner retained.spine
      compared.prepared index)),
    HEq ((Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).prepared.entry index)
      ((Sources.selected (frame := frame) (basis := basis) path within owner retained.spine
        compared.prepared index position).prepared.entry
        (Sources.child (frame := frame) (basis := basis) path within owner retained.spine compared.prepared
          index position))

/-- The global parent keeps its original complete preparation at the same physical Segment and local child index. -/
theorem parentSegment_prepared_heq : ParentSegmentPreparedHeqLaw := by
  unfold ParentSegmentPreparedHeqLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width start finish path within owner row retained observed views sources allocation compared index
    position
  exact Sources.prepared_heq (frame := frame) (basis := basis) path within owner retained.spine compared.prepared
      index position

/-- One original global parent retains its computed occurrence and whole existing Segment observation.

The finite location is the original Sources locator on the same assembled
parent index. The second value is read from the retained observation and
comparison spine at that exact location; neither value selects a new source.
-/
@[expose] def ParentObservation
    (index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).geometry.parents.length) :=
  Σ position : {value : Flatten.Occurrence
      (Sources.parentWords (frame := frame) (basis := basis) width path within owner retained.spine
        compared.prepared)
      (Sources.flattenedIndex (frame := frame) (basis := basis) path within owner retained.spine
        compared.prepared index) //
    value = Sources.locate (frame := frame) (basis := basis) path within owner retained.spine
      compared.prepared index},
    {value : Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := targets) (width := width) row allocation
        (Sources.selected (frame := frame) (basis := basis) path within owner retained.spine
          compared.prepared index position.val) //
      value = compared.parentSegment index position.val}

variable (index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
  compared.prepared).geometry.parents.length)

/-- Locate an actual global parent once and read its original complete Segment observation/comparison cache. -/
def observeParent : ParentObservation (allocation := allocation) compared index :=
  let position := Sources.locate (frame := frame) (basis := basis) path within owner retained.spine
    compared.prepared index
  let observed := compared.parentSegment index position
  ⟨⟨position, rfl⟩, ⟨observed, rfl⟩⟩

/-- The whole parent-observation factory retains one original location and the cache read at that same location. -/
private theorem packaged_observeParent_factory :
    observeParent (allocation := allocation) compared index =
      (let position := Sources.locate (frame := frame) (basis := basis) path within owner retained.spine
         compared.prepared index
       let observed := compared.parentSegment index position
       ⟨⟨position, rfl⟩, ⟨observed, rfl⟩⟩ : ParentObservation (allocation := allocation) compared index) := by rfl

/-- The whole parent-observation factory retains one original location and the cache read at that same location.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ObserveParentFactoryLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {start : Canonical}
    {finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {within : path.WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {row : Row}
    {retained : Acquisition width path within owner}
    {observed : Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
    {views : Acquisition.Observations retained observed}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width path within owner retained.spine}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    (compared : Compared row retained views sources allocation)
    (index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).geometry.parents.length),
    observeParent (allocation := allocation) compared index =
      (let position := Sources.locate (frame := frame) (basis := basis) path within owner retained.spine
         compared.prepared index
       let observed := compared.parentSegment index position
       ⟨⟨position, rfl⟩, ⟨observed, rfl⟩⟩ : ParentObservation (allocation := allocation) compared index)

/-- The whole parent-observation factory retains one original location and the cache read at that same location. -/
theorem observeParent_factory : ObserveParentFactoryLaw := by
  unfold ObserveParentFactoryLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width start finish path within owner row retained observed views sources allocation compared index
  exact packaged_observeParent_factory compared index

namespace ParentObservation

variable {compared index}
variable (kept : ParentObservation (allocation := allocation) compared index)

/-- Read the actual retained block/local occurrence without running the finite locator again. -/
def position : Flatten.Occurrence
    (Sources.parentWords (frame := frame) (basis := basis) width path within owner retained.spine compared.prepared)
    (Sources.flattenedIndex (frame := frame) (basis := basis) path within owner retained.spine
      compared.prepared index) := kept.1.val

/-- Read the whole original physical Segment observation and its same-source comparison. -/
def segment : Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := targets) (width := width) row allocation
    (Sources.selected (frame := frame) (basis := basis) path within owner retained.spine
      compared.prepared index kept.position) := kept.2.val

/-- The cached location retains its complete original finite locator equation.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def PositionEqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {start : Canonical}
    {finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {within : path.WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {row : Row}
    {retained : Acquisition width path within owner}
    {observed : Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
    {views : Acquisition.Observations retained observed}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width path within owner retained.spine}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {compared : Compared row retained views sources allocation}
    {index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).geometry.parents.length}
    (kept : ParentObservation (allocation := allocation) compared index),
    kept.position =
    Sources.locate (frame := frame) (basis := basis) path within owner retained.spine compared.prepared index

/-- The cached location retains its complete original finite locator equation. -/
theorem position_eq : PositionEqLaw := by
  unfold PositionEqLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width start finish path within owner row retained observed views sources allocation compared index kept
  exact kept.1.property

/-- The stored Segment cache retains the exact read from the supplied original comparison spine.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def SegmentEqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {start : Canonical}
    {finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {within : path.WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {row : Row}
    {retained : Acquisition width path within owner}
    {observed : Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
    {views : Acquisition.Observations retained observed}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width path within owner retained.spine}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {compared : Compared row retained views sources allocation}
    {index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).geometry.parents.length}
    (kept : ParentObservation (allocation := allocation) compared index),
    kept.segment = compared.parentSegment index kept.position

/-- The stored Segment cache retains the exact read from the supplied original comparison spine. -/
theorem segment_eq : SegmentEqLaw := by
  unfold SegmentEqLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width start finish path within owner row retained observed views sources allocation compared index kept
  exact kept.2.property

/-- The same located global parent retains its complete original local preparation under exact index transport.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def PreparedHeqLaw : Prop :=
  ∀
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {floor : Nat}
    {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}
    {baseStart : LiftedPoint 2}
    {baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {accuracy : AccuracyRequest}
    {width : {start finish : Canonical} →
      ClearSegment (Paths.polynomial parameter) ambient start finish → AccuracyRequest}
    {start : Canonical}
    {finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {within : path.WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {row : Row}
    {retained : Acquisition width path within owner}
    {observed : Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
    {views : Acquisition.Observations retained observed}
    {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) width path within owner retained.spine}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    {compared : Compared row retained views sources allocation}
    {index : Fin (Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).geometry.parents.length}
    (kept : ParentObservation (allocation := allocation) compared index),
    HEq ((Sources.assemble (frame := frame) (basis := basis) width path within owner retained.spine
      compared.prepared).prepared.entry index)
      ((Sources.selected (frame := frame) (basis := basis) path within owner retained.spine
        compared.prepared index kept.position).prepared.entry
        (Sources.child (frame := frame) (basis := basis) path within owner retained.spine compared.prepared
          index kept.position))

/-- The same located global parent retains its complete original local preparation under exact index transport. -/
theorem prepared_heq : PreparedHeqLaw := by
  unfold PreparedHeqLaw
  intro parameter frame basis count floor sheet ambient baseStart baseFinish original stage targets accuracy
    width start finish path within owner row retained observed views sources allocation compared index kept
  exact compared.parentSegment_prepared_heq index kept.position

end ParentObservation

end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

end
