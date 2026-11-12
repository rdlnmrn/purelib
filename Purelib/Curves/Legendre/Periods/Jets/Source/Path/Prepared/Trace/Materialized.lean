module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Telescope
public import Purelib.Riemann.Paths.PreparedPathTrace.Materialized.Primitive
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Paths.PreparedSubdivisionTrace

/-! # Actual old row observations on a materialized complete segment

The given original segment trace and whole-path identity transport the
same old primitive Spine. The existing source comparison fold consumes
its same centres, covering patches, six-channel sources and endpoint
requests. Both stationary roles and every original moving occurrence stay
in their original order, with the old accuracy unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Request

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment zeroEndpoint oneEndpoint)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget (ownerPath)
open Purelib.Riemann.Paths

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {ambient : Geometry.Rational.Box} {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish prepared.finishOwner)
    (trace : PreparedTraceBudget.Trace budget prepared.subdivision fits) (kept : HEq trace.path materialized)
    {row : Row} {accuracy : AccuracyRequest}
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized)
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
    (sources : Sources (frame := frame) (basis := basis) (targets := targets)
      (count := count) (floor := floor) (sheet := sheet) prepared.subdivision)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)

/-- Compare the SAME old materialized segment Spine to its original source-bank relation integrals.

The original endpoint/whole-Owner laws transport the given observation
cache to its same raw Trace. The original Request.fromObserved then
constructs each source/model endpoint comparison once on those old
Vertices. No trace, centre, patch, source, query, model or observation is
reconstructed. The allocation is genuine equality of the two existing
request indices, not a final numerical estimate.
-/
def fromCompleteSegment :
    Compared row (frame := frame) (basis := basis) budget allocation prepared.subdivision sources fits
      (castObserved row budget prepared.subdivision fits trace.path trace.path_eq
        (PreparedPathTrace.CompleteSegment.observations prepared materialized trace kept observed)) :=
  let rawObserved := PreparedPathTrace.CompleteSegment.observations prepared materialized trace kept observed
  fromObserved row (frame := frame) (basis := basis) budget prepared.subdivision fits trace.path trace.path_eq
    sources allocation rawObserved

/-- The actual complete comparison retains the SAME whole source-bank object with all original requests and models. -/
theorem fromCompleteSegment_sources :
    (fromCompleteSegment prepared budget fits materialized trace kept observed sources allocation).sources =
      sources :=
  Compared.sources_eq _

/-- The actual comparison retains the SAME entire old observation execution heterogeneously. -/
theorem fromCompleteSegment_observed_heq :
    HEq (fromCompleteSegment prepared budget fits materialized trace kept observed sources allocation).observed
      observed :=
  (heq_of_eq (Compared.observed_eq _)).trans
    ((castObserved_heq row budget prepared.subdivision fits trace.path trace.path_eq _).trans
      (PreparedPathTrace.CompleteSegment.observations_heq prepared materialized trace kept observed))

/-- The old first scalar survives both exact raw-Trace and canonical path-index transports unchanged. -/
theorem fromCompleteSegment_first_value :
    (fromCompleteSegment prepared budget fits materialized trace kept observed sources allocation).observed.first.value
      = observed.first.value :=
  (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
      (ownerPath budget prepared.subdivision fits) => old.first.value)
    (Compared.observed_eq _)).trans
      ((congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
          (ownerPath budget prepared.subdivision fits) => old.first.value)
        (castObserved_eq_castPath row budget prepared.subdivision fits trace.path trace.path_eq _)).trans
        ((Primitive.Spine.castPath_first_value trace.path_eq _).trans
          (PreparedPathTrace.CompleteSegment.observations_first_value prepared materialized trace kept observed)))

/-- The distinct old final scalar survives the same complete observation transports unchanged. -/
theorem fromCompleteSegment_last_value :
    (fromCompleteSegment prepared budget fits materialized trace kept observed sources allocation).observed.last.value =
      observed.last.value :=
  (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
      (ownerPath budget prepared.subdivision fits) => old.last.value)
    (Compared.observed_eq _)).trans
      ((congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
          (ownerPath budget prepared.subdivision fits) => old.last.value)
        (castObserved_eq_castPath row budget prepared.subdivision fits trace.path trace.path_eq _)).trans
        ((Primitive.Spine.castPath_last_value trace.path_eq _).trans
          (PreparedPathTrace.CompleteSegment.observations_last_value prepared materialized trace kept observed)))

/-- There is exactly one actual complete-block error per retained original moving request, including stationary ones. -/
theorem fromCompleteSegment_block_count :
    (fromCompleteSegment prepared budget fits materialized trace kept observed sources allocation).blockErrors.length =
      prepared.subdivision.requests.length := Compared.blockErrors_length _

/-- The SAME old materialized primitive increment pays its actual ordered original source integrals.

Each source polynomial keeps its own primitive and constant. The existing
Row.integral_error_le and two genuine endpoint comparisons control each
moving contribution; the old stationary comparisons pay both retained
handoffs. The finite count-square bound is explicit. No independent
normalization, cross-face return or global requested accuracy is claimed.
-/
theorem fromCompleteSegment_integral_le :
    Norm.Basic.normSq (observed.last.value - observed.first.value - gaussianSum
      (fromCompleteSegment prepared budget fits materialized trace kept observed sources allocation).integrals) ≤
      (prepared.subdivision.requests.length : Rational) *
        ((prepared.subdivision.requests.length : Rational) * (26 * targets.endpoint)) := by
  let completed := fromCompleteSegment prepared budget fits materialized trace kept observed sources allocation
  have original := completed.integral_error_le
  have first := fromCompleteSegment_first_value prepared budget fits materialized trace kept observed sources allocation
  have last := fromCompleteSegment_last_value prepared budget fits materialized trace kept observed sources allocation
  exact (congrArg₂ (fun first last : Canonical =>
    Norm.Basic.normSq (last - first - gaussianSum completed.integrals)) first last).symm.trans_le original

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Request

end
