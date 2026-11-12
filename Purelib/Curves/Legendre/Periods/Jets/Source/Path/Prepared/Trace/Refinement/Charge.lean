module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Charge
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Exact whole-cache source and observation charges

Every actual request retains its two old stationary allowances, original
Point/source charge and counted comparison request. Structural sums give
the exact whole charge in the same measured child and request counts;
no old observation is retagged or assumed small.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

open Trace.Materialized renaming Sources -> MaterializedSources
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {accuracy : AccuracyRequest}

/-- Both actual old stationary allowances and the original endpoint vertex charges have coefficient five halves. -/
private theorem old_charge (allowance : Rational) :
    allowance + ((allowance + allowance) / 4 + allowance) = (5 / 2 : Rational) * allowance := by
  rewrite [Field.div_eq_mul_inv_direct]
  have coefficient : (4 : Rational)⁻¹ + (4 : Rational)⁻¹ + 2 = (5 / 2 : Rational) := by decide +kernel
  calc
    _ = allowance * ((4 : Rational)⁻¹ + (4 : Rational)⁻¹ + 2) := by ring1
    _ = _ := by rewrite [coefficient]; ring1

namespace Cache

variable {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint}

/-- The same actual raw trace cache has an exact charge in its retained child count and original request count. -/
theorem charge_eq (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    (retained : Cache (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed) →
    let children := childCount (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed retained
    charge (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed retained =
      (5 / 2 : Rational) * (subdivision.requests.length : Rational) * accuracy.tolerance +
      (97 / 8 : Rational) * (children : Rational) * targets.endpoint +
      4 * ((children : Rational) + (subdivision.requests.length : Rational)) * request.tolerance
  | _, _, .stop _ _, _, _, _, _, _ => by
      change (0 : Rational) = (5 / 2 : Rational) * 0 * accuracy.tolerance +
        (97 / 8 : Rational) * 0 * targets.endpoint + 4 * (0 + 0) * request.tolerance
      ring1
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, retained => by
      let head := retained.1.val
      let tailChildren := childCount (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget remaining centers.2 fits.2.2 head.nextTrace head.nextObserved retained.2
      have localCharge : head.charge = (5 / 2 : Rational) * accuracy.tolerance +
          (97 / 8 : Rational) * (head.childCount : Rational) * targets.endpoint +
          4 * ((head.childCount : Rational) + 1) * request.tolerance := by
        change accuracy.tolerance +
          (Points.charge targets request head.childCount accuracy accuracy + accuracy.tolerance) = _
        rewrite [Points.charge_eq targets request head.childCount accuracy accuracy]
        calc
          _ = (accuracy.tolerance + ((accuracy.tolerance + accuracy.tolerance) / 4 + accuracy.tolerance)) +
              (97 / 8 : Rational) * (head.childCount : Rational) * targets.endpoint +
              4 * ((head.childCount : Rational) + 1) * request.tolerance := by ring1
          _ = _ := by rewrite [old_charge accuracy.tolerance]; ring1
      have following := charge_eq row diameter positive request budget remaining centers.2 fits.2.2
        head.nextTrace head.nextObserved retained.2
      change head.charge + charge (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget remaining centers.2 fits.2.2
            head.nextTrace head.nextObserved retained.2 =
        (5 / 2 : Rational) * ((remaining.requests.length + 1 : Nat) : Rational) * accuracy.tolerance +
        (97 / 8 : Rational) * ((head.childCount + tailChildren : Nat) : Rational) * targets.endpoint +
        4 * (((head.childCount + tailChildren : Nat) : Rational) +
          ((remaining.requests.length + 1 : Nat) : Rational)) * request.tolerance
      rewrite [localCharge, following, Cast.natCast_add_direct head.childCount tailChildren,
        Cast.natCast_add_direct remaining.requests.length 1]
      ring1
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

end Cache

namespace Materialized.Cache

/-- The exact whole charge retains measured children and every original request before the step-count readback. -/
private theorem charge_requests_eq
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (retained : Materialized.Cache (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers) →
    let children := childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers retained
    charge (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers retained =
      (5 / 2 : Rational) * (MaterializedSources.requestCount lineage : Rational) * accuracy.tolerance +
      (97 / 8 : Rational) * (children : Rational) * targets.endpoint +
      4 * ((children : Rational) + (MaterializedSources.requestCount lineage : Rational)) * request.tolerance
  | _, _, _, _, _, .nil _ _, _, _ => by
      change (0 : Rational) = (5 / 2 : Rational) * 0 * accuracy.tolerance +
        (97 / 8 : Rational) * 0 * targets.endpoint + 4 * (0 + 0) * request.tolerance
      ring1
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining, centers, retained => by
      let compared := retained.1.2.2
      let tailChildren := childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request remaining centers.2 retained.2
      have headCharge : compared.charge =
          (5 / 2 : Rational) * (first.subdivision.requests.length : Rational) * accuracy.tolerance +
          (97 / 8 : Rational) * (compared.childCount : Rational) * targets.endpoint +
          4 * ((compared.childCount : Rational) + (first.subdivision.requests.length : Rational)) *
            request.tolerance :=
        Refinement.Cache.charge_eq
          (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor) (targets := targets)
          (accuracy := accuracy) row diameter positive request budget first.subdivision compared.centers fits
          compared.actualTrace compared.observations compared.completed
      have following := charge_requests_eq row diameter positive request remaining centers.2 retained.2
      change compared.charge + charge (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request remaining centers.2 retained.2 =
        (5 / 2 : Rational) *
          ((first.subdivision.requests.length + MaterializedSources.requestCount remaining : Nat) : Rational) *
          accuracy.tolerance +
        (97 / 8 : Rational) * ((compared.childCount + tailChildren : Nat) : Rational) * targets.endpoint +
        4 * (((compared.childCount + tailChildren : Nat) : Rational) +
          ((first.subdivision.requests.length + MaterializedSources.requestCount remaining : Nat) : Rational)) *
          request.tolerance
      rewrite [headCharge, following, Cast.natCast_add_direct compared.childCount tailChildren,
        Cast.natCast_add_direct first.subdivision.requests.length (MaterializedSources.requestCount remaining)]
      ring1
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- The actual complete charge separates old allowances, all source children and every comparison request.

The original prepared step count includes stationary/repeated requests.
This equality concerns any given actual cache, including the given-geometry
completion; it requires no convenience-builder or final-accuracy premise.
-/
theorem charge_eq {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (lineage : TraceLineage prepared) (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (retained : Materialized.Cache (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers) :
    let children := childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers retained
    charge (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers retained =
      (5 / 2 : Rational) * (prepared.stepCount : Rational) * accuracy.tolerance +
      (97 / 8 : Rational) * (children : Rational) * targets.endpoint +
      4 * ((children : Rational) + (prepared.stepCount : Rational)) * request.tolerance := by
  have actual := charge_requests_eq (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage centers retained
  exact actual.trans (congrArg (fun total : Nat =>
    (5 / 2 : Rational) * (total : Rational) * accuracy.tolerance +
    (97 / 8 : Rational) *
      (childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers retained : Rational) * targets.endpoint +
    4 * ((childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers retained : Rational) + (total : Rational)) * request.tolerance)
    (MaterializedSources.requestCount_eq_stepCount lineage))

end Materialized.Cache

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

end
