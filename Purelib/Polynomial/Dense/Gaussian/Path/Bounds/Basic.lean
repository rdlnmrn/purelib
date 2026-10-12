module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Gaussian.Cast
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
public import Purelib.Polynomial.Clearance.Pair.Cover.Retained
import Purelib.Polynomial.Clearance.Pair.Enclosure
import Purelib.Polynomial.Clearance.Pair.Sample
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Geometry.Rational

set_option genInjectivity false in
/-- Executable geometry and estimates for one polynomial on the exact line
`origin + t * direction`; the oriented direction is never changed.

The record retains the composed parameter polynomial, coordinate tables, interval enclosures, endpoint sample and both
quantitative floors. Each cache is linked to its exact construction on the supplied oriented affine path. -/
public structure Data (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction : Canonical)
    (interval : Data.Rat.Interval.Bounds) where
  /-- The retained Gaussian coefficient table for composition with the original oriented line. -/ parameterPolynomial :
    Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The cached parameter polynomial is exactly the original affine substitution. -/ parameterPolynomial_eq :
    parameterPolynomial = Dense.Gaussian.Substitution.Affine.composeLine polynomial origin direction
  /-- The retained real coordinate polynomial of the parameter table. -/ realPolynomial :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The retained real table is exactly the parameter polynomial's real-part table. -/ realPolynomial_eq :
    realPolynomial = Dense.Gaussian.Components.realPart parameterPolynomial
  /-- The retained imaginary coordinate polynomial of the parameter table. -/ imagPolynomial :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The retained imaginary table is exactly the parameter polynomial's imaginary-part table. -/ imagPolynomial_eq :
    imagPolynomial = Dense.Gaussian.Components.imagPart parameterPolynomial
  /-- The cached component enclosures indexed by the retained coordinate tables and original interval. -/ enclosures :
    Clearance.Pair.Enclosure.Components realPolynomial imagPolynomial interval
  /-- The cached exact Gaussian value at the interval's lower endpoint. -/ sample : Canonical
  /-- The cached sample equals parameter-polynomial evaluation at the retained lower endpoint. -/ sample_eq : sample =
    parameterPolynomial.eval (Cast.Path.ofCoordinate interval.lower)
  /-- The retained quadrance ceiling read from the cached component enclosures. -/ valueBound : Fraction.Rational
  /-- The value ceiling is exactly the cached enclosure ceiling. -/ valueBound_eq : valueBound = enclosures.normCeiling
  /-- The cached sum of the real and imaginary squared-Lipschitz bounds. -/ slopeBound : Fraction.Rational
  /-- The slope cache equals the two coefficient-computed coordinate bounds on the original interval. -/ slopeBound_eq :
    slopeBound = Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound realPolynomial interval +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound imagPolynomial interval
  /-- The optional retained refinement cover for the exact coordinate tables and interval. -/ clearance : Option
    (Clearance.Pair.Cover.Retained realPolynomial imagPolynomial interval)
  /-- The combined sample, enclosure and optional-cover quadrance floor. -/ lowerBound : Fraction.Rational
  /-- The cached floor is exactly the maximum of the three retained lower-bound proposals. -/ lowerBound_eq : lowerBound
    = max (max (Data.Gaussian.Norm.Basic.normSq sample / 2 -
    slopeBound * Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower) enclosures.normFloor)
      (Clearance.Pair.Cover.Retained.optionalNorm clearance)

constructive_injectivity Data

/-- The cheap value/slope and endpoint-preflight stage.  Clients requiring
separation subsequently call `Data.sharpen`; numerator-only bounds need not.

Both coordinate enclosures and the lower-endpoint sample are computed once. The returned record retains those exact
caches, their coefficient-derived slope and the stronger sample/enclosure floor without constructing a refinement cover.
-/
@[expose] public def prepareCoarse (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
  Canonical)
    (interval : Data.Rat.Interval.Bounds) : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
      interval :=
  let parameterPolynomial := Dense.Gaussian.Substitution.Affine.composeLine polynomial origin direction
  let realPolynomial := Dense.Gaussian.Components.realPart parameterPolynomial
  let imagPolynomial := Dense.Gaussian.Components.imagPart parameterPolynomial
  let enclosures := Clearance.Pair.Enclosure.Components.prepare realPolynomial imagPolynomial interval
  let sample := parameterPolynomial.eval (Cast.Path.ofCoordinate interval.lower)
  let slopeBound := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound realPolynomial interval +
    Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound imagPolynomial interval
  { parameterPolynomial, parameterPolynomial_eq := rfl
    realPolynomial, realPolynomial_eq := rfl
    imagPolynomial, imagPolynomial_eq := rfl
    enclosures
    sample, sample_eq := rfl
    valueBound := enclosures.normCeiling, valueBound_eq := rfl
    slopeBound, slopeBound_eq := rfl
    clearance := none
    lowerBound := max (Data.Gaussian.Norm.Basic.normSq sample / 2 -
      slopeBound * Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower) enclosures.normFloor
    lowerBound_eq := by
      exact (Fraction.Order.Basic.max_eq_left (enclosures.normFloor_nonnegative.trans (Fraction.Order.Basic.le_max_right
        _ _))).symm }

namespace Data

variable {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} {origin direction : Canonical} {interval :
  Data.Rat.Interval.Bounds}

/-- Evaluate the retained parameter polynomial at the supplied exact rational parameter.

The operation evaluates the cached parameter polynomial at the supplied rational parameter. It reuses the retained
affine composition instead of composing the source coefficient table again. -/
@[expose] public def value (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
  (parameter : Fraction.Rational) : Canonical :=
  data.parameterPolynomial.eval (Cast.Path.ofCoordinate parameter)

/-- The retained parameter evaluation agrees with the original polynomial on the original oriented affine line.

The retained parameter-polynomial equality links its evaluation to the exact source polynomial on the supplied oriented
affine line. -/
public theorem value_eq (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval) (parameter :
  Fraction.Rational) :
    data.value parameter = polynomial.eval (Affine.line origin direction parameter) := by
  rw [Dense.Gaussian.Path.Bounds.Basic.Data.value, data.parameterPolynomial_eq,
    Dense.Gaussian.Substitution.Affine.eval_composeLine]

/-- The retained real coordinate polynomial evaluates to the real part of the cached path value.

The retained real coefficient table is the real-part projection of the cached parameter polynomial. Evaluation
transports that projection at the supplied parameter. -/
public theorem real_eval (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval) (parameter
  : Fraction.Rational) :
    data.realPolynomial.eval parameter = (data.value parameter).re := by
  rw [data.realPolynomial_eq, Dense.Gaussian.Components.eval_realPart]
  rfl

/-- The retained imaginary coordinate polynomial evaluates to the imaginary part of the cached path value.

The retained imaginary coefficient table is the imaginary-part projection of the cached parameter polynomial. Evaluation
transports that projection at the supplied parameter. -/
public theorem imag_eval (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval) (parameter
  : Fraction.Rational) :
    data.imagPolynomial.eval parameter = (data.value parameter).im := by
  rw [data.imagPolynomial_eq, Dense.Gaussian.Components.eval_imagPart]
  rfl

/-- The cached component-enclosure value ceiling is nonnegative.

The retained value ceiling is exactly the cached enclosure ceiling. Both component interval square bounds are
nonnegative. -/
public theorem valueBound_nonnegative (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval) :
    0 ≤ data.valueBound := by
  rw [data.valueBound_eq]
  exact data.enclosures.normCeiling_nonnegative

/-- The cached component-enclosure ceiling is bounded by the two squared Horner majorants.

The retained component enclosure ceiling is bounded by the two scalar Horner majorants. This compares the same
coordinate tables and parameter interval. -/
public theorem valueBound_le_horner (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
  :
    data.valueBound ≤ Dense.Rational.Bounds.Horner.evalSqBound data.realPolynomial interval +
      Dense.Rational.Bounds.Horner.evalSqBound data.imagPolynomial interval := by
  rw [data.valueBound_eq]
  exact data.enclosures.normCeiling_le_horner

/-- The cached sum of coordinate squared-Lipschitz multipliers is nonnegative.

The cached slope is the sum of two nonnegative squared-Lipschitz bounds for the retained coordinate coefficient tables.
-/
public theorem slopeBound_nonnegative (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval) :
    0 ≤ data.slopeBound := by
  rw [data.slopeBound_eq]
  exact add_nonneg (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2
    (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg _ _).2

/-- The cached value ceiling bounds path evaluation quadrance throughout the original interval.

Interval membership bounds both cached coordinate evaluations by their retained enclosure square ceilings. Their exact
sum is the cached path-value ceiling. -/
public theorem normSq_value_le (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
    {parameter : Fraction.Rational} (inside : interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq (data.value parameter) ≤ data.valueBound := by
  have bounds := data.enclosures.sum_sq_le inside
  rw [data.real_eval, data.imag_eval, ← data.valueBound_eq] at bounds
  exact bounds

/-- A cached component separation, before squaring.  Root-denominator
estimates can use it without approximating a square root of a squared bound.

The readback combines the cached enclosure coordinate floor with the optional retained-cover floor. It performs no new
enclosure fold or refinement. -/
@[expose] public def coordinateLower (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
  : Fraction.Rational :=
  max data.enclosures.coordinateFloor (Clearance.Pair.Cover.Retained.optionalCoordinate data.clearance)

/-- The combined enclosure and retained-cover coordinate floor is nonnegative.

The enclosure coordinate floor is nonnegative and below the readback maximum with the optional retained-cover floor. -/
public theorem coordinateLower_nonnegative (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval) :
    0 ≤ data.coordinateLower := data.enclosures.coordinateFloor_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

/-- The combined coordinate floor bounds the larger absolute component of the retained path value.

Both floor proposals bound the same pair of cached coordinate evaluations on the supplied interval. Their maximum
preserves those distinct coordinate bounds. -/
public theorem coordinateLower_le_value (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval)
    {parameter : Fraction.Rational} (inside : interval.Contains parameter) :
    data.coordinateLower ≤ max (Fraction.abs ((data.value parameter).re)) (Fraction.abs ((data.value parameter).im)) :=
      by
  have bound := data.enclosures.coordinateFloor_le inside
  rw [data.real_eval, data.imag_eval] at bound
  have extra := Clearance.Pair.Cover.Retained.optionalCoordinate_le data.clearance inside
  rw [data.real_eval, data.imag_eval] at extra
  exact Fraction.Order.Basic.max_le bound extra

/-- The combined coordinate floor bounds the larger absolute component of the original polynomial along the affine path.

The exact affine evaluation equality transports the cached coordinate bound to the source polynomial without changing
origin or direction. -/
public theorem coordinateLower_le (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
    {parameter : Fraction.Rational} (inside : interval.Contains parameter) :
    data.coordinateLower ≤ max (Fraction.abs ((polynomial.eval (Affine.line origin direction parameter)).re))
      (Fraction.abs ((polynomial.eval (Affine.line origin direction parameter)).im)) := by
  rw [← data.value_eq]
  exact data.coordinateLower_le_value inside

/-- The cached aggregate quadrance floor is nonnegative.

The optional retained-cover floor is nonnegative. It is below the cached maximum with the sample and enclosure
proposals. -/
public theorem lowerBound_nonnegative (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval) :
    0 ≤ data.lowerBound := by
  rw [data.lowerBound_eq]
  exact (Clearance.Pair.Cover.Retained.optionalNorm_nonnegative data.clearance).trans (Fraction.Order.Basic.le_max_right
    _ _)

/-- Every previously certified positive sample margin is preserved.

The sample-and-variation proposal is one argument of the cached maximum. Combining enclosure or cover bounds therefore
preserves this proposal. -/
public theorem sampleMargin_le_lowerBound (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval) :
    Data.Gaussian.Norm.Basic.normSq data.sample / 2 - data.slopeBound *
      Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower ≤ data.lowerBound := by
  rw [data.lowerBound_eq]
  exact (Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The cached slope multiplier bounds squared variation between two parameters in the original interval.

Both supplied parameters belong to the same retained interval. The original two squared-Lipschitz comparisons sum to the
cached slope times their squared difference. -/
public theorem normSq_value_sub_le (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
    {left right : Fraction.Rational} (leftInside : interval.Contains left)
    (rightInside : interval.Contains right) :
    Data.Gaussian.Norm.Basic.normSq (data.value left - data.value right) ≤ data.slopeBound * (left - right) ^ 2 := by
  have bounds := add_le_add
    (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le data.realPolynomial interval leftInside rightInside)
    (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le data.imagPolynomial interval leftInside rightInside)
  rw [data.real_eval, data.real_eval, data.imag_eval, data.imag_eval] at bounds
  calc
    Data.Gaussian.Norm.Basic.normSq (data.value left - data.value right) ≤ _ := bounds
    _ = data.slopeBound * (left - right) ^ 2 := by
      rw [data.slopeBound_eq]
      ring1

/-- Reuse the existing endpoint sample and finite difference calculation.
The clearance cover may consume this certificate without evaluating either
parameter polynomial or recomputing its Horner slope at the root.

The certificate consumes the cached lower-endpoint sample and slope. Only its retained radius is read from the same
interval; both coordinate evaluations and their Horner slopes are reused. -/
@[expose] public def sampleCertificate (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval) :
    Clearance.Pair.Sample.Certificate data.realPolynomial data.imagPolynomial interval :=
  let radiusSq := Data.Rat.Interval.Radius.sampleRadiusSq interval interval.lower
  { sample := data.sample
    sample_eq := by
      rw [data.sample_eq]
      exact Purelib.Data.Gaussian.Basic.ext
        (data.real_eval (parameter := interval.lower)).symm
        (data.imag_eval (parameter := interval.lower)).symm
    slopeBound := data.slopeBound, slopeBound_eq := data.slopeBound_eq
    radiusSq, radiusSq_eq := rfl
    normFloor := Data.Gaussian.Norm.Basic.normSq data.sample / 2 - data.slopeBound * radiusSq, normFloor_eq := rfl }

/-- The computed lower bound is valid even when neither proposal gives a
positive margin.  Such a zero bound is inconclusive, not a root certificate.

The sample, enclosure and optional retained cover each bound the same cached path quadrance. Their displayed maximum is
therefore a valid uniform floor. -/
public theorem lowerBound_le_value (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
    {parameter : Fraction.Rational} (inside : interval.Contains parameter) :
    data.lowerBound ≤ Data.Gaussian.Norm.Basic.normSq (data.value parameter) := by
  rw [data.lowerBound_eq]
  apply Fraction.Order.Basic.max_le
  · apply Fraction.Order.Basic.max_le
    · have bound := data.sampleCertificate.normFloor_le inside
      rw [data.real_eval, data.imag_eval] at bound
      exact bound
    · have bound := data.enclosures.normFloor_le inside
      rw [data.real_eval, data.imag_eval] at bound
      exact bound
  · have bound := Clearance.Pair.Cover.Retained.optionalNorm_le data.clearance inside
    rw [data.real_eval, data.imag_eval] at bound
    exact bound

/-- The retained lower bound bounds the original polynomial quadrance throughout the oriented affine interval.

The exact affine evaluation equality transfers the cached quadrance floor to the supplied polynomial on its oriented
path. -/
public theorem lowerBound_le (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
    {parameter : Fraction.Rational} (inside : interval.Contains parameter) :
    data.lowerBound ≤ Data.Gaussian.Norm.Basic.normSq (polynomial.eval (Affine.line origin direction parameter)) := by
  rw [← data.value_eq]
  exact data.lowerBound_le_value inside

/-- A positive retained lower bound proves nonvanishing at every parameter in the original interval.

A positive retained floor bounds the source evaluation quadrance at each contained parameter. A zero evaluation would
have zero quadrance and violate that strict bound. -/
public theorem eval_nonzero (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
    (positive : 0 < data.lowerBound) {parameter : Fraction.Rational}
    (inside : interval.Contains parameter) :
    polynomial.eval (Affine.line origin direction parameter) ≠ 0 := by
  intro zero
  have bound := positive.trans_le (data.lowerBound_le inside)
  rw [zero, Norm.Basic.normSq_zero] at bound
  exact (lt_irrefl _ bound).elim
end Data
end Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
