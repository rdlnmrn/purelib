module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation.Uniform
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment.Uniform
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Distance
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Fixed positive work requests before genuinely finer chart geometry

One original fixed-envelope numerator cache computes its cost once. The
same retained regular parameter gives a positive global geometric cap.
Their minimum remains below every genuine finer Anchor's own Allocation
request, without a maximum over a changing fine layer or new observations.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope.Numerator

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
open Segment.Reading

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {differential : OddPowerDifferential (Paths.polynomial parameter)}
variable {reference : Fraction.Rational} {regular : parameter ≠ criticalValue site}
variable (retained : Numerator (quarter := quarter) differential reference regular)
variable (data : Waist.Differential.Bounds.Data site parameter differential)

/-- Compute the original fixed-envelope cost from its actual cached numerator, scale, radius floor and exponent. -/
def cost : Fraction.Rational :=
  Coefficient.Allocation.Uniform.costCeiling (data.scaleNorm * retained.cache.value)
    (data.scaleNorm * retained.cache.slope) (Payment.Uniform.radiusFloor site parameter)
    (Payment.sensitivity site parameter) differential.denominatorExponent

/-- The SAME fixed cost has an explicit nonnegative floor before any finer observations are requested. -/
theorem cost_nonnegative : 0 ≤ retained.cost data :=
  Coefficient.Allocation.Uniform.costCeiling_nonnegative _ _ _ _ _

variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {fine : Fraction.Rational} {fineInside : FixedRootBoxPath.Inside fine}
variable {source : Transport.Reading actual fine fineInside} {anchor : Parameter.Anchor source.lift}

/-- The SAME fixed coarse cost bounds the actual original Allocation of every genuinely finer retained Anchor. -/
theorem fine_cost_le (bounds : Coefficient.Bounds data anchor)
    (paid : (fine - reference) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    Coefficient.Allocation.cost bounds ≤ retained.cost data := by
  have numerator := retained.fine_bounds_le bounds paid
  exact Coefficient.Allocation.Uniform.cost_le bounds
    (Payment.Uniform.radiusFloor_positive site parameter anchor.regular) (radius_bounds anchor).1
    numerator.1 numerator.2

/-- Compute one strictly positive common work request from the fixed cache before building any finer geometry. -/
def request (target : AccuracyRequest) : AccuracyRequest :=
  (⟨target.tolerance / (1 + retained.cost data), Fraction.Order.Field.div_pos_direct target.positive
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1)
      (retained.cost_nonnegative data))⟩ : AccuracyRequest).minimum
    (Payment.Uniform.spatialRequest site parameter regular)

/-- The original fixed-envelope request retains its exact scalar minimum without unfolding its factory. -/
theorem request_tolerance (target : AccuracyRequest) :
    (retained.request data target).tolerance =
      min (target.tolerance / (1 + retained.cost data))
        (Payment.Uniform.spatialRequest site parameter regular).tolerance := by
  unfold request
  rfl

/-- The SAME computed positive request lies below every finer Anchor's actual original individual work request. -/
theorem fine_request_le (target : AccuracyRequest) (bounds : Coefficient.Bounds data anchor)
    (paid : (fine - reference) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    (retained.request data target).tolerance ≤ (Coefficient.Allocation.request bounds target).tolerance := by
  have costBound := retained.fine_cost_le data bounds paid
  have denominator := Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (Coefficient.Allocation.cost_nonnegative bounds)
  have quotient := Fraction.Order.Field.div_le_div_of_nonneg_left_direct target.positive.1 denominator
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) costBound)
  have geometric := Payment.Uniform.spatialRequest_le anchor
  rewrite [Coefficient.Allocation.request_tolerance bounds target]
  change min (target.tolerance / (1 + retained.cost data))
      (Payment.Uniform.spatialRequest site parameter regular).tolerance ≤
    min (target.tolerance / (1 + Coefficient.Allocation.cost bounds)) (Payment.spatialRequest anchor).tolerance
  exact Fraction.Order.Basic.min_le_min quotient geometric

/-- The fixed request computes one sufficient finer chart depth without inspecting a changing fine-node bank. -/
def chartWidthMinimum (target : AccuracyRequest) : Nat :=
  Transport.Spatial.Parallel.Geometry.widthMinimum site parameter (retained.request data target)

variable {last : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside last}
variable {following : Transport.Reading actual last lastInside}
variable {payment : (last - fine) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}

/-- The SAME computed fixed depth pays the original individual fine Allocation on every actual new Route edge.

Both width premises are original chart certificates. The first locates the
actual fine Anchor in its retained coarse block; the second is paid by the
new finite dyadic geometry chosen before observations. No pointwise source
or coefficient discrepancy is an input to this path-distance construction.
-/
theorem fine_route_pointBound (target : AccuracyRequest) (bounds : Coefficient.Bounds data anchor)
    (coarsePaid : (fine - reference) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7)
    (geometry : Transport.Spatial.Parallel.Geometry source following anchor.regular payment)
    (widthPaid : (fine - last) ^ 2 ≤
      Approximation.Rational.Geometric.Basic.quarterRadius 1 (retained.chartWidthMinimum data target)) :
    Polynomial.Geometry.ClearPath.PointBound
      (Transport.Spatial.coordinate site parameter 2 quarter positive fine)
      (Coefficient.Allocation.request bounds target).tolerance geometry.route.path :=
  (geometry.route_pointBound_of_depth (retained.request data target) widthPaid).mono
    (retained.fine_request_le data target bounds coarsePaid)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope.Numerator

end
