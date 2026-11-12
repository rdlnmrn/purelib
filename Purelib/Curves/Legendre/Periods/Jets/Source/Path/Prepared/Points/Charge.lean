module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Exact charges for original mixed-request source refinements

The original finite recurrence retains both old endpoint requests and each
actual new source/Point/join charge. Its affine count formula is exact:
no old observation allowance is discarded or retagged to a later request.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

variable {start finish : LiftedPoint 2} {original : LiftedPath 2 start finish} {stage : Nat}

/-- The actual mixed-request stationary charge keeps one quarter of each endpoint tolerance and its own tail request. -/
theorem junctionCharge_eq (first last request : AccuracyRequest) :
    junctionCharge first last request = (first.tolerance + last.tolerance) / 4 + 4 * request.tolerance := by
  change 16 * (first.tolerance / ((64 : Nat) : Rational) + last.tolerance / ((64 : Nat) : Rational)) +
    4 * request.tolerance = _
  rewrite [Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct]
  have coefficient : (16 : Rational) * ((64 : Nat) : Rational)⁻¹ = (4 : Rational)⁻¹ := by
    rewrite [Cast.natCast_eq_fromInt 64]
    decide +kernel
  calc
    _ = (first.tolerance + last.tolerance) * (16 * ((64 : Nat) : Rational)⁻¹) +
        4 * request.tolerance := by ring1
    _ = _ := by rewrite [coefficient]; ring1

/-- The exact source recurrence is affine in the actual child count while preserving both original endpoint requests. -/
theorem charge_affine (targets : CellEndpoints.Targets original stage) (request : AccuracyRequest) :
    (children : Nat) → (first last : AccuracyRequest) →
    charge targets request children first last = junctionCharge first last request + (children : Rational) *
      (32 * (Primitive.vertexRequest (PreparedParents.Trace.localAccuracy targets)).tolerance +
        12 * targets.endpoint + 4 * request.tolerance)
  | 0, first, last => by
      change junctionCharge first last request = junctionCharge first last request + (0 : Rational) * _
      ring1
  | children + 1, first, last => by
      change junctionCharge first (PreparedParents.Trace.localAccuracy targets) request + 12 * targets.endpoint +
        charge targets request children (PreparedParents.Trace.localAccuracy targets) last = _
      have following := charge_affine targets request children (PreparedParents.Trace.localAccuracy targets) last
      rewrite [following]
      have nextCount : ((children + 1 : Nat) : Rational) = (children : Rational) + 1 :=
        Cast.natCast_add_direct children 1
      rewrite [nextCount]
      unfold junctionCharge
      ring1
termination_by structural children _ _ => children

/-- The two new endpoint vertex contributions at one actual child equal one eighth of its source endpoint allocation. -/
private theorem localVertex_charge (targets : CellEndpoints.Targets original stage) :
    32 * (Primitive.vertexRequest (PreparedParents.Trace.localAccuracy targets)).tolerance = targets.endpoint / 8 := by
  change 32 * ((targets.endpoint / 4) / ((64 : Nat) : Rational)) = targets.endpoint / 8
  rewrite [Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct]
  have coefficient : (32 : Rational) * ((4 : Rational)⁻¹ * ((64 : Nat) : Rational)⁻¹) = (8 : Rational)⁻¹ := by
    rewrite [Cast.natCast_eq_fromInt 64]
    decide +kernel
  calc
    _ = targets.endpoint * (32 * ((4 : Rational)⁻¹ * ((64 : Nat) : Rational)⁻¹)) := by ring1
    _ = _ := congrArg (fun scalar : Rational => targets.endpoint * scalar) coefficient

/-- The actual child charge separates both old allowances, exact source allocation and all counted comparison requests.

The original request count is children plus one, including the real
stationary comparison when children is zero. The source coefficient 97/8
includes the same independently selected Point observations at every child.
-/
theorem charge_eq (targets : CellEndpoints.Targets original stage) (request : AccuracyRequest)
    (children : Nat) (first last : AccuracyRequest) :
    charge targets request children first last = (first.tolerance + last.tolerance) / 4 +
      (97 / 8 : Rational) * (children : Rational) * targets.endpoint +
      4 * ((children : Rational) + 1) * request.tolerance := by
  have sourceStep : targets.endpoint / 8 + 12 * targets.endpoint = (97 / 8 : Rational) * targets.endpoint := by
    rewrite [Field.div_eq_mul_inv_direct]
    have coefficient : (8 : Rational)⁻¹ + 12 = (97 / 8 : Rational) := by decide +kernel
    calc
      _ = targets.endpoint * ((8 : Rational)⁻¹ + 12) := by ring1
      _ = _ := by rewrite [coefficient]; ring1
  rewrite [charge_affine targets request children first last, junctionCharge_eq first last request,
    localVertex_charge targets, sourceStep]
  ring1

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

end
