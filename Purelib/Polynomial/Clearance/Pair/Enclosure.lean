module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Interval.Gap
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
public import Purelib.Polynomial.Dense.Rational.Enclosure.Basic
import Purelib.Polynomial.Dense.Rational.Enclosure.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached polynomial pair enclosures

Both descending rational coefficient tables are evaluated in the retained interval algebra once. Their component
enclosures and derived quadrance and coordinate bounds are cached with exact construction equalities.
-/

namespace Purelib.Polynomial.Clearance.Pair.Enclosure

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

set_option genInjectivity false in
/-- Cached component enclosures for a Gaussian polynomial evaluated at real
parameters.  The scalar bounds are stored as data, so downstream root and
quotient estimates do not rerun either coefficient fold.

The certificate retains both polynomial interval folds and their exact readback equalities. Each comparison uses those
same enclosures and the supplied interval membership. -/
public structure Components (realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial)
  (parameters : Data.Rat.Interval.Bounds) where
  /-- The retained interval enclosure of the real polynomial. -/ realRange : Data.Rat.Interval.Bounds
  /-- The real interval is exactly the original polynomial enclosure result. -/ realRange_eq : realRange =
    Dense.Rational.Enclosure.Basic.evaluate realPolynomial parameters
  /-- The retained interval enclosure of the imaginary polynomial. -/ imagRange : Data.Rat.Interval.Bounds
  /-- The imaginary interval is exactly the original polynomial enclosure result. -/ imagRange_eq : imagRange =
    Dense.Rational.Enclosure.Basic.evaluate imagPolynomial parameters
  /-- The cached upper bound on pair evaluation quadrance. -/ normCeiling : Fraction.Rational
  /-- The ceiling is the sum of the two retained interval square bounds. -/ normCeiling_eq : normCeiling =
    realRange.squareBound + imagRange.squareBound
  /-- The cached lower bound on pair evaluation quadrance. -/ normFloor : Fraction.Rational
  /-- The floor is the sum of the squared gaps of the two retained intervals. -/ normFloor_eq : normFloor =
    Data.Rat.Interval.Gap.gap realRange ^ 2 + Data.Rat.Interval.Gap.gap imagRange ^ 2
  /-- The cached lower bound on the larger absolute coordinate. -/ coordinateFloor : Fraction.Rational
  /-- The coordinate floor is the larger gap of the two retained intervals. -/ coordinateFloor_eq : coordinateFloor =
    max (Data.Rat.Interval.Gap.gap realRange) (Data.Rat.Interval.Gap.gap imagRange)

constructive_injectivity Components

namespace Components

/-- Compute and retain both polynomial interval enclosures and their derived bounds.

The initial leaf is constructed for the supplied source and interval. Refinement then consumes the fixed depth budget
and retains its actual certificate tree. -/
@[expose] public def prepare (realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial)
  (parameters : Data.Rat.Interval.Bounds) :
    Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters :=
  let realRange := Dense.Rational.Enclosure.Basic.evaluate realPolynomial parameters
  let imagRange := Dense.Rational.Enclosure.Basic.evaluate imagPolynomial parameters
  { realRange, realRange_eq := rfl
    imagRange, imagRange_eq := rfl
    normCeiling := realRange.squareBound + imagRange.squareBound, normCeiling_eq := rfl
    normFloor := Data.Rat.Interval.Gap.gap realRange ^ 2 + Data.Rat.Interval.Gap.gap imagRange ^ 2, normFloor_eq := rfl
    coordinateFloor := max (Data.Rat.Interval.Gap.gap realRange) (Data.Rat.Interval.Gap.gap imagRange),
      coordinateFloor_eq := rfl }

variable {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial} {parameters :
  Data.Rat.Interval.Bounds}

/-- The retained real enclosure contains every real-polynomial value on the parameter interval.

The cached range is exactly the real coefficient-table enclosure. Interval Horner containment transports membership of
the supplied parameter to that same range. -/
public theorem real_contains (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    data.realRange.Contains (realPolynomial.eval parameter) := by
  rw [data.realRange_eq]
  exact Dense.Rational.Enclosure.Basic.evaluate_contains _ _ inside

/-- The retained imaginary enclosure contains every imaginary-polynomial value on the parameter interval.

The cached range is exactly the imaginary coefficient-table enclosure. Interval Horner containment transports membership
of the supplied parameter to that same range. -/
public theorem imag_contains (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    data.imagRange.Contains (imagPolynomial.eval parameter) := by
  rw [data.imagRange_eq]
  exact Dense.Rational.Enclosure.Basic.evaluate_contains _ _ inside

/-- The cached quadrance ceiling is nonnegative.

Each retained range has a nonnegative square ceiling. Their exact sum is the cached pair ceiling. -/
public theorem normCeiling_nonnegative (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial
  parameters) :
    0 ≤ data.normCeiling := by
  rw [data.normCeiling_eq]
  exact add_nonneg data.realRange.squareBound_nonneg data.imagRange.squareBound_nonneg

/-- The cached enclosure ceiling is no larger than the sum of squared Horner ceilings.

Each cached component enclosure is bounded by its scalar Horner square majorant. Adding those two comparisons bounds the
retained quadrance ceiling. -/
public theorem normCeiling_le_horner (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial
  parameters) :
    data.normCeiling ≤ Dense.Rational.Bounds.Horner.evalSqBound realPolynomial parameters +
      Dense.Rational.Bounds.Horner.evalSqBound imagPolynomial parameters := by
  rw [data.normCeiling_eq, data.realRange_eq, data.imagRange_eq]
  exact add_le_add (Dense.Rational.Enclosure.Bounds.evaluate_squareBound_le _ _)
    (Dense.Rational.Enclosure.Bounds.evaluate_squareBound_le _ _)

/-- The cached quadrance floor is nonnegative.

The squared coordinate floors are nonnegative. Their sum is below the retained maximum with the optional sample
proposal. -/
public theorem normFloor_nonnegative (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial
  parameters) :
    0 ≤ data.normFloor := by
  rw [data.normFloor_eq]
  exact add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- The cached coordinate floor is nonnegative.

The real-coordinate floor is nonnegative and below the cached maximum of both coordinate floors. -/
public theorem coordinateFloor_nonnegative (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial
  parameters) :
    0 ≤ data.coordinateFloor := by
  rw [data.coordinateFloor_eq]
  exact (Data.Rat.Interval.Gap.gap_nonnegative data.realRange).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The pair's evaluation quadrance lies below its cached enclosure ceiling.

Both coordinate values lie in their cached interval enclosures. Adding the two interval square bounds gives the exact
retained ceiling. -/
public theorem sum_sq_le (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^ 2 ≤ data.normCeiling := by
  rw [data.normCeiling_eq]
  exact add_le_add (data.realRange.sq_le_squareBound (data.real_contains inside))
    (data.imagRange.sq_le_squareBound (data.imag_contains inside))

/-- The cached enclosure floor bounds the pair's evaluation quadrance from below.

The enclosure or sample certificates bound the same two polynomial values on the supplied interval. The retained floor
readback combines those bounds without changing either coordinate. -/
public theorem normFloor_le (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    data.normFloor ≤ realPolynomial.eval parameter ^ 2 + imagPolynomial.eval parameter ^ 2 := by
  rw [data.normFloor_eq]
  exact add_le_add (Data.Rat.Interval.Gap.gap_sq_le data.realRange (data.real_contains inside))
    (Data.Rat.Interval.Gap.gap_sq_le data.imagRange (data.imag_contains inside))

/-- The cached coordinate floor bounds the larger absolute coordinate from below.

Each retained coordinate floor bounds its own polynomial magnitude. The maximum comparison preserves those two distinct
coordinate bounds. -/
public theorem coordinateFloor_le (data : Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial parameters)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    data.coordinateFloor ≤ max (Fraction.abs (realPolynomial.eval parameter)) (Fraction.abs (imagPolynomial.eval
      parameter)) := by
  rw [data.coordinateFloor_eq]
  exact Fraction.Order.Basic.max_le
    ((Data.Rat.Interval.Gap.gap_le_abs data.realRange (data.real_contains inside)).trans
      (Fraction.Order.Basic.le_max_left _ _))
    ((Data.Rat.Interval.Gap.gap_le_abs data.imagRange (data.imag_contains inside)).trans
      (Fraction.Order.Basic.le_max_right _ _))

end Components
end Purelib.Polynomial.Clearance.Pair.Enclosure
