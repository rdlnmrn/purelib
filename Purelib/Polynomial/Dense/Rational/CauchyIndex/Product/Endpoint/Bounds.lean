module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Sign.Endpoint
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Radius

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint.Bounds

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Six componentwise endpoint stabilities for the two factors and their
displayed product coordinates.

The original factors and their displayed product retain six distinct
coordinate conditions. Each condition uses the same oriented start
and stop values and its own original polynomial owner. -/
public structure EndpointStabilities
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (start stop : Fraction.Rational) : Prop where
  /-- The first factor real coordinate is stable between the displayed endpoints. -/ leftReal :
    Sign.Endpoint.EndpointStable A start stop
  /-- The first factor imaginary coordinate is stable between the displayed endpoints. -/ leftImag :
    Sign.Endpoint.EndpointStable B start stop
  /-- The second factor real coordinate is stable between the displayed endpoints. -/ rightReal :
    Sign.Endpoint.EndpointStable C start stop
  /-- The second factor imaginary coordinate is stable between the displayed endpoints. -/ rightImag :
    Sign.Endpoint.EndpointStable D start stop
  /-- The product real coordinate is stable between the displayed endpoints. -/ productReal :
    Sign.Endpoint.EndpointStable E start stop
  /-- The product imaginary coordinate is stable between the displayed endpoints. -/ productImag :
    Sign.Endpoint.EndpointStable H start stop

/-- One finite minimum covers all six endpoint-coordinate stability tests.

The original nested rational minima retain each of the six input
coordinate radii, in their displayed order. The same endpoint and
root interval supply every constituent bound. -/
@[expose] public def endpointStabilitiesRadiusSq
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (root : Data.Rat.Interval.Bounds)
    (endpoint : Fraction.Rational) : Fraction.Rational :=
  min (Sign.Endpoint.endpointStabilityRadiusSq A root endpoint)
    (min (Sign.Endpoint.endpointStabilityRadiusSq B root endpoint)
      (min (Sign.Endpoint.endpointStabilityRadiusSq C root endpoint)
        (min (Sign.Endpoint.endpointStabilityRadiusSq D root endpoint)
          (min (Sign.Endpoint.endpointStabilityRadiusSq E root endpoint)
            (Sign.Endpoint.endpointStabilityRadiusSq H root endpoint)))))

/-- The common squared stability radius for all six coordinates is positive.

Every retained coordinate radius is strictly positive. Repeated
minimum positivity therefore certifies the same displayed nested
minimum without replacing its operation or coordinate order. -/
public theorem endpointStabilitiesRadiusSq_pos
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (root : Data.Rat.Interval.Bounds)
    (endpoint : Fraction.Rational) :
    0 < endpointStabilitiesRadiusSq A B C D E H root endpoint := by
  unfold endpointStabilitiesRadiusSq
  apply Fraction.Order.Basic.lt_min
  · exact Sign.Endpoint.endpointStabilityRadiusSq_pos A root endpoint
  · apply Fraction.Order.Basic.lt_min
    · exact Sign.Endpoint.endpointStabilityRadiusSq_pos B root endpoint
    · apply Fraction.Order.Basic.lt_min
      · exact Sign.Endpoint.endpointStabilityRadiusSq_pos C root endpoint
      · apply Fraction.Order.Basic.lt_min
        · exact Sign.Endpoint.endpointStabilityRadiusSq_pos D root endpoint
        · apply Fraction.Order.Basic.lt_min
          · exact Sign.Endpoint.endpointStabilityRadiusSq_pos E root endpoint
          · exact Sign.Endpoint.endpointStabilityRadiusSq_pos H root endpoint

/-- An oriented refinement below the common squared radius certifies all six endpoint stabilities.

The interval retains its original containing interval; either orientation of its endpoints is permitted. -/
public theorem endpointStabilities_of_refined_radiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    {start stop : Fraction.Rational}
    (refines : interval.Refines root)
    (orientation :
      (start = interval.lower ∧ stop = interval.upper) ∨
      (start = interval.upper ∧ stop = interval.lower))
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      endpointStabilitiesRadiusSq A B C D E H root start) :
    EndpointStabilities A B C D E H start stop := by
  have radiusA : Interval.Radius.sampleRadiusSq interval interval.lower <
      Sign.Endpoint.endpointStabilityRadiusSq A root start :=
    radius.trans_le (Fraction.Order.Basic.min_le_left _ _)
  have radiusB : Interval.Radius.sampleRadiusSq interval interval.lower <
      Sign.Endpoint.endpointStabilityRadiusSq B root start :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have radiusC : Interval.Radius.sampleRadiusSq interval interval.lower <
      Sign.Endpoint.endpointStabilityRadiusSq C root start :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  have radiusD : Interval.Radius.sampleRadiusSq interval interval.lower <
      Sign.Endpoint.endpointStabilityRadiusSq D root start :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))))
  have radiusE : Interval.Radius.sampleRadiusSq interval interval.lower <
      Sign.Endpoint.endpointStabilityRadiusSq E root start :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))))
  have radiusH : Interval.Radius.sampleRadiusSq interval interval.lower <
      Sign.Endpoint.endpointStabilityRadiusSq H root start :=
    radius.trans_le ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)))))
  exact
    { leftReal := Sign.Endpoint.endpointStable_of_refined_radiusSq
        refines orientation radiusA
      leftImag := Sign.Endpoint.endpointStable_of_refined_radiusSq
        refines orientation radiusB
      rightReal := Sign.Endpoint.endpointStable_of_refined_radiusSq
        refines orientation radiusC
      rightImag := Sign.Endpoint.endpointStable_of_refined_radiusSq
        refines orientation radiusD
      productReal := Sign.Endpoint.endpointStable_of_refined_radiusSq
        refines orientation radiusE
      productImag := Sign.Endpoint.endpointStable_of_refined_radiusSq
        refines orientation radiusH }

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Endpoint.Bounds
