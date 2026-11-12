module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Quotient
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.PrimitiveLoop
import Purelib.Polynomial.Dense.Gaussian.Substitution.Power
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Retained polynomial bounds for the actual circle form numerator

The same original padded numerator supplies a polynomial in the actual cap
parameter. Its monomial denominator has constant positive quadrance on the
supplied circle. Two original cached Horner tables give a finite quotient
sensitivity before any stage or observation handler is constructed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Bounds.Box
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelRootChannels
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Rational.Budget
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.RationalFunctions.Curve.Canonical.Circle.Integral (circleBox circleBox_contains)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}

/-- The original padded numerator and both actual polynomial tables of the same cap-parameter scalar quotient. -/
abbrev Polynomials (differential : OddPowerDifferential curve.polynomial) :=
  (padded : { value : Basic.CanonicalCoefficients.CoefficientPolynomial //
    value = Reciprocal.padded differential.numerator (2 * genus) }) ×
  (_numerator : { value : Basic.CanonicalCoefficients.CoefficientPolynomial //
    value = (Substitution.Power.substitute padded.val (Primitives.degree curve)).scale
      ((Primitives.degree curve : Canonical) * (-differential.scale)) }) ×
    { value : Basic.CanonicalCoefficients.CoefficientPolynomial //
      value = DensePolynomial.shift (Primitives.degree curve * (genus + 1)) (DensePolynomial.constant 1) }

/-- Retain the original padded table and compute its substituted numerator and monomial denominator once. -/
def polynomials (differential : OddPowerDifferential curve.polynomial)
    (padded : { value : Basic.CanonicalCoefficients.CoefficientPolynomial //
      value = Reciprocal.padded differential.numerator (2 * genus) } :=
        ⟨Reciprocal.padded differential.numerator (2 * genus), rfl⟩) : Polynomials differential :=
  let numerator := (Substitution.Power.substitute padded.val (Primitives.degree curve)).scale
    ((Primitives.degree curve : Canonical) * (-differential.scale))
  let denominator := DensePolynomial.shift (Primitives.degree curve * (genus + 1)) (DensePolynomial.constant 1)
  ⟨padded, ⟨numerator, rfl⟩, ⟨denominator, rfl⟩⟩

namespace Polynomials

open Purelib.Data.Rat.Fraction.Order

variable {differential : OddPowerDifferential curve.polynomial}

/-- Read the actual retained polynomial numerator at its original curve and differential indices. -/
@[expose] def numerator (data : Polynomials differential) : Basic.CanonicalCoefficients.CoefficientPolynomial :=
  data.2.1.val

/-- Read the same retained monomial denominator of the original cap-parameter scalar quotient. -/
@[expose] def denominator (data : Polynomials differential) : Basic.CanonicalCoefficients.CoefficientPolynomial :=
  data.2.2.val

/-- The retained polynomial numerator evaluates to the same actual padded coefficient on the original cap power map. -/
theorem numerator_eval (data : Polynomials differential) (parameter : Canonical) :
    data.numerator.eval parameter = (Primitives.degree curve : Canonical) *
      (-differential.scale * data.1.val.eval (Primitives.point curve parameter)) := by
  change data.2.1.val.eval parameter = _
  rewrite [data.2.1.property, DensePolynomial.eval_scale, Substitution.Power.eval_substitute]
  exact Gaussian.Basic.mul_assoc _ _ _

/-- The actual monomial denominator evaluates to the same finite cap power at the original parameter. -/
theorem denominator_eval (data : Polynomials differential) (parameter : Canonical) :
    data.denominator.eval parameter = parameter ^ (Primitives.degree curve * (genus + 1)) := by
  change data.2.2.val.eval parameter = _
  rewrite [data.2.2.property, DensePolynomial.eval_shift, DensePolynomial.eval_constant, Gaussian.Basic.one_mul]
  rfl

/-- The positive scalar denominator floor computed from the same actual circle base. -/
@[expose] def lower (base : Canonical) : Fraction.Rational :=
  Norm.Basic.normSq base ^ (Primitives.degree curve * (genus + 1))

/-- The original nonzero circle base makes the actual monomial denominator floor strictly positive. -/
theorem lower_positive (base : Canonical) (nonzero : base ≠ 0) : 0 < lower (curve := curve) base :=
  Arithmetic.pow_pos_direct (Norm.Basic.normSq_pos nonzero) _

/-- Every actual retained circle point has exactly the same positive monomial denominator quadrance. -/
theorem denominator_norm (data : Polynomials differential) (base : Canonical)
    (actual : { value : RationalCurve // value = circle base }) (time : Fraction.Rational) :
    Norm.Basic.normSq (data.denominator.eval (actual.val.point time)) = lower (curve := curve) base := by
  rewrite [denominator_eval, Norm.Power.normSq_pow, actual.property, point_normSq]
  rfl

/-- The same actual retained scalar numerator is the quotient of the original two stored polynomial tables. -/
theorem numerator_ratio {parameter : Canonical}
    {inside : collar.box.Contains (Primitives.point curve parameter)}
    {prepared : Preparation cap parameter inside} (data : Polynomials differential)
    (cached : Coefficient differential prepared) (nonzero : parameter ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus) :
    cached.numerator = data.numerator.eval parameter / data.denominator.eval parameter := by
  rewrite [cached.numerator_padded nonzero bound data.1, numerator_eval, denominator_eval]
  rewrite [Primitives.point, pow_mul]
  rfl

/-- The two actual original Horner caches at the same retained polynomial tables and original circle box. -/
abbrev Bounds (data : Polynomials differential) (base : Canonical) :=
  HornerCache data.numerator (circleBox base) × HornerCache data.denominator (circleBox base)

/-- Compute each original Horner value/slope table once from the retained actual polynomial and box. -/
def bounds (data : Polynomials differential) (base : Canonical) : data.Bounds base :=
  let numerator := denseHornerNormBounds data.numerator (circleBox base)
  let denominator := denseHornerNormBounds data.denominator (circleBox base)
  ⟨⟨numerator, rfl⟩, ⟨denominator, rfl⟩⟩

namespace Bounds

/-- Transport the same whole original numerator/denominator cache pair to a rotated quarter's identical circle box.

The original box equality preserves both actual Horner values and their
coefficient-table certificates. This is a type transport of the supplied
whole pair; neither coefficient fold nor cache producer is evaluated again.
-/
def onQuarter {data : Polynomials differential} {base : Canonical} (cached : data.Bounds base)
    (quarter : Quarter.UnitCircuitQuarter) : data.Bounds (Integral.quarterBase base quarter) :=
  cast (congrArg (fun box : Geometry.Rational.Box =>
    HornerCache data.numerator box × HornerCache data.denominator box)
      (Integral.circleBox_quarterBase base quarter).symm) cached

/-- Rotating to an actual original quarter preserves the complete supplied coefficient-cache pair. -/
theorem onQuarter_heq {data : Polynomials differential} {base : Canonical} (cached : data.Bounds base)
    (quarter : Quarter.UnitCircuitQuarter) : HEq (cached.onQuarter quarter) cached := by
  unfold onQuarter
  exact cast_heq _ _

/-- Rotating the original whole coefficient cache preserves its exact saved numerator value ceiling. -/
theorem onQuarter_numerator_value {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) (quarter : Quarter.UnitCircuitQuarter) :
    (cached.onQuarter quarter).1.val.value = cached.1.val.value := by
  have first := congrArg (fun value : Polynomial.Bounds.Horner => value.value)
    (cached.onQuarter quarter).1.property
  have last := congrArg (fun value : Polynomial.Bounds.Horner => value.value) cached.1.property
  have scalar := congrArg (fun box : Geometry.Rational.Box =>
    (denseHornerNormBounds data.numerator box).value) (Integral.circleBox_quarterBase base quarter)
  exact first.trans (scalar.trans last.symm)

/-- Read the finite scalar quotient sensitivity directly from the two actual stored original Horner tables. -/
@[expose] def slope {data : Polynomials differential} {base : Canonical} (cached : data.Bounds base) :
    Fraction.Rational :=
  quotientLipschitzBound data.numerator data.denominator (circleBox base) (lower (curve := curve) base)
    cached.1 cached.2

/-- A nonzero original circle base gives a nonnegative sensitivity for its actual retained scalar quotient. -/
theorem slope_nonnegative {data : Polynomials differential} {base : Canonical} (cached : data.Bounds base)
    (nonzero : base ≠ 0) : 0 ≤ cached.slope :=
  quotientLipschitzBound_nonnegative data.numerator data.denominator (circleBox base) _
    (lower_positive base nonzero) cached.1 cached.2

/-- The two actual full-form scalar numerators obey the same retained polynomial quotient sensitivity on the circle.

The original zero-free circle supplies both actual monomial floors.
The supplied original numerator degree bound identifies each whole form's
stored scalar with those same two polynomial tables before applying the
finite quotient estimate from their retained Horner caches.
-/
theorem numerator_difference_le {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (actual : { value : RationalCurve // value = circle base }) (first last : Fraction.Rational)
    {firstInside : collar.box.Contains (Primitives.point curve (actual.val.point first))}
    {lastInside : collar.box.Contains (Primitives.point curve (actual.val.point last))}
    {firstPrepared : Preparation cap (actual.val.point first) firstInside}
    {lastPrepared : Preparation cap (actual.val.point last) lastInside}
    (firstCoefficient : Coefficient differential firstPrepared)
    (lastCoefficient : Coefficient differential lastPrepared) :
    Norm.Basic.normSq (lastCoefficient.numerator - firstCoefficient.numerator) ≤
      cached.slope * Norm.Basic.normSq (actual.val.point last - actual.val.point first) := by
  rewrite [data.numerator_ratio lastCoefficient (point_nonzero base nonzero actual last) bound,
    data.numerator_ratio firstCoefficient (point_nonzero base nonzero actual first) bound]
  apply normSq_eval_div_sub_eval_div_le data.numerator data.denominator
    (circleBox_contains base actual last) (circleBox_contains base actual first)
    (lower (curve := curve) base) (lower_positive base nonzero)
  · exact (data.denominator_norm base actual last).symm.le
  · exact (data.denominator_norm base actual first).symm.le

/-- The actual retained numerator Horner value bounds the scalar quotient on the same nonzero circle.

The same monomial denominator has constant positive quadrance. The
original whole coefficient cache is identified with the retained quotient
before applying the original finite polynomial value bound.
-/
theorem numerator_norm_le {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) (nonzero : base ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (actual : { value : RationalCurve // value = circle base }) (time : Fraction.Rational)
    {inside : collar.box.Contains (Primitives.point curve (actual.val.point time))}
    {prepared : Preparation cap (actual.val.point time) inside}
    (coefficient : Coefficient differential prepared) :
    Norm.Basic.normSq coefficient.numerator ≤ cached.1.val.value / lower (curve := curve) base := by
  have positive := lower_positive (curve := curve) base nonzero
  have denominatorPositive : 0 < Norm.Basic.normSq (data.denominator.eval (actual.val.point time)) := by
    rewrite [data.denominator_norm base actual time]
    exact positive
  have denominatorNonzero : data.denominator.eval (actual.val.point time) ≠ 0 := by
    intro zero
    rewrite [zero, Norm.Basic.normSq_zero] at denominatorPositive
    exact denominatorPositive.not_ge (Fraction.Order.Basic.le_refl _)
  have magnitude := normSq_eval_le_denseEvalNormBound data.numerator (circleBox_contains base actual time)
  change Norm.Basic.normSq (data.numerator.eval (actual.val.point time)) ≤
    (denseHornerNormBounds data.numerator (circleBox base)).value at magnitude
  rewrite [← cached.1.property] at magnitude
  rewrite [data.numerator_ratio coefficient (point_nonzero base nonzero actual time) bound,
    Gaussian.Field.normSq_div _ _ denominatorNonzero, data.denominator_norm base actual time]
  exact Fraction.Order.Field.divide_mono magnitude positive

/-- The same regional clearance gives a positive root floor independent of every circle mesh. -/
@[expose] def rootLower : Fraction.Rational := min 1 (cap.clearance.bound / 4) / 8

/-- The original positive regional clearance makes the uniform numerical root floor positive. -/
theorem rootLower_positive : 0 < rootLower (cap := cap) :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Basic.lt_min (by decide)
      (Fraction.Order.Field.div_pos_direct cap.clearance.positive (by decide))) (by decide)

/-- The actual retained original numerator Horner value bounds every exact scalar numerator sampler. -/
@[expose] def numeratorCeiling {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) : Fraction.Rational :=
  2 * (1 + cached.1.val.value / lower (curve := curve) base)

/-- The original retained polynomial bound gives one ceiling for every prepared regular-root sampler. -/
@[expose] def rootCeiling
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial) : Fraction.Rational :=
  2 * (1 + 2 * (1 + (4 + bounds.numeratorUpper)))

/-- The retained numerator Horner ceiling divided by the positive circle denominator floor is nonnegative.

The same cached polynomial bound and nonzero circle base determine both
scalars. No numerical sampler or new Horner table is constructed. -/
theorem numerator_norm_bound_nonnegative {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) (nonzero : base ≠ 0) : 0 ≤ cached.1.val.value / lower (curve := curve) base := by
  have numerator := (denseHornerNormBounds_nonneg data.numerator (circleBox base)).1
  change 0 ≤ (denseHornerNormBounds data.numerator (circleBox base)).value at numerator
  rewrite [← cached.1.property] at numerator
  exact Fraction.Order.Field.div_nonneg_direct numerator (lower_positive base nonzero).le

/-- The actual supplied numerator table gives a nonnegative uniform exact-numerator sampling ceiling. -/
theorem numeratorCeiling_nonnegative {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) (nonzero : base ≠ 0) : 0 ≤ cached.numeratorCeiling :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (cached.numerator_norm_bound_nonnegative nonzero))

/-- The same original cached polynomial majorant makes the uniform numerical root sampler ceiling nonnegative. -/
theorem rootCeiling_nonnegative
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial) :
    0 ≤ rootCeiling bounds :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) (add_nonneg (by decide) bounds.numeratorUpper_nonnegative))))

/-- One finite ceiling pays both the actual coefficient's spatial increment and independently requested accuracy.

The original two Horner caches, retained derivative bound and original
regional root floor are read once. The finite power sensitivity accounts
for the cap's original coordinate map in either degree parity.
-/
@[expose] def separationCeiling {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial) : Fraction.Rational :=
  16 * Quotient.quotientBound 1 cached.numeratorCeiling (rootCeiling bounds) (rootLower (cap := cap))
    (cached.slope + 1) (32 * bounds.bound * Norm.Power.differenceFactor 1 (Primitives.degree curve) + 1) + 1

/-- The derived uniform coefficient ceiling is nonnegative at the original nonzero circle base. -/
theorem separationCeiling_nonnegative {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) (nonzero : base ≠ 0)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial) :
    0 ≤ cached.separationCeiling bounds := by
  have rootSlope : 0 ≤ 32 * bounds.bound * Norm.Power.differenceFactor 1 (Primitives.degree curve) :=
    Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le
      bounds.bound_nonnegative) (Norm.Power.differenceFactor_nonnegative
        (by decide : (0 : Fraction.Rational) ≤ 1) (Primitives.degree curve))
  exact add_nonneg (Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide)).le
    (Quotient.ApproximationQuotientVariation.quotientBound_nonnegative
      (by decide : (0 : Fraction.Rational) ≤ 1)
      (cached.numeratorCeiling_nonnegative nonzero) (rootCeiling_nonnegative bounds)
      (rootLower_positive (cap := cap)).le (add_nonneg (cached.slope_nonnegative nonzero) (by decide))
      (add_nonneg rootSlope (by decide)))) (by decide)

/-- Actual cached coefficients obey the derived common spatial-and-accuracy ceiling.

Both original numerical root guards retain their own parents and floors.
The displayed guard and sampler bounds concern those actual supplied
caches. The same circle's exact numerator quotient and finite cap-power
sensitivity derive all remaining variation terms internally.
-/
theorem separation_le {data : Polynomials differential} {base : Canonical}
    (cached : data.Bounds base) (nonzero : base ≠ 0) (unitBound : Norm.Basic.normSq base ≤ 1)
    (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (actual : { value : RationalCurve // value = circle base }) (first last : Fraction.Rational)
    {firstInside : collar.box.Contains (Primitives.point curve (actual.val.point first))}
    {lastInside : collar.box.Contains (Primitives.point curve (actual.val.point last))}
    {firstPrepared : Preparation cap (actual.val.point first) firstInside}
    {lastPrepared : Preparation cap (actual.val.point last) lastInside}
    (firstCoefficient : Coefficient differential firstPrepared)
    (lastCoefficient : Coefficient differential lastPrepared)
    (firstLower : rootLower (cap := cap) ≤ firstPrepared.1.prepared.apart.certificate.lowerSq)
    (lastLower : rootLower (cap := cap) ≤ lastPrepared.1.prepared.apart.certificate.lowerSq)
    (samplerBound : (Name.Sampling.approximation firstPrepared.1.certificate.value.name).centerBound ≤
      rootCeiling bounds)
    (accuracy : Fraction.Rational) (accuracyNonnegative : 0 ≤ accuracy) :
    Coefficient.separationBound bounds firstCoefficient lastCoefficient accuracy ≤
      cached.separationCeiling bounds *
        (Norm.Basic.normSq (actual.val.point last - actual.val.point first) + accuracy) := by
  let movement := Norm.Basic.normSq (actual.val.point last - actual.val.point first)
  let powerFactor := Norm.Power.differenceFactor 1 (Primitives.degree curve)
  let rootSlope := 32 * bounds.bound * powerFactor
  have movementNonnegative : 0 ≤ movement := Norm.Basic.normSq_nonneg _
  have slopeNonnegative := cached.slope_nonnegative nonzero
  have rootSlopeNonnegative : 0 ≤ rootSlope := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le bounds.bound_nonnegative)
    (Norm.Power.differenceFactor_nonnegative (by decide : (0 : Fraction.Rational) ≤ 1) _)
  have numeratorDifference := cached.numerator_difference_le nonzero degreeBound actual first last
    firstCoefficient lastCoefficient
  have firstPointBound : Norm.Basic.normSq (actual.val.point first) ≤ 1 := by
    rewrite [actual.property, point_normSq]
    exact unitBound
  have lastPointBound : Norm.Basic.normSq (actual.val.point last) ≤ 1 := by
    rewrite [actual.property, point_normSq]
    exact unitBound
  have powerDifference := Norm.Power.difference_normSq_le lastPointBound firstPointBound
    (Primitives.degree curve)
  change Norm.Basic.normSq (Primitives.point curve (actual.val.point last) -
    Primitives.point curve (actual.val.point first)) ≤ powerFactor * movement at powerDifference
  rewrite [Norm.Basic.normSq_eq_canonical] at powerDifference
  have rootDifference := Arithmetic.mul_le_mul_of_nonneg_left_direct powerDifference
    (Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le
      bounds.bound_nonnegative)
  have numeratorMovement : Norm.Basic.normSq (lastCoefficient.numerator - firstCoefficient.numerator) + accuracy ≤
      (cached.slope + 1) * (movement + accuracy) := by
    have augmented := Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct numeratorDifference
        (Fraction.Order.Basic.le_refl accuracy))
      (add_nonneg (Arithmetic.mul_nonneg_direct slopeNonnegative accuracyNonnegative)
        movementNonnegative)
    rewrite [_root_.add_zero] at augmented
    exact augmented.trans_eq (by ring1)
  have rootMovement :
      32 * bounds.bound * Canonical.normSq (Primitives.point curve (actual.val.point last) -
        Primitives.point curve (actual.val.point first)) + accuracy ≤
      (rootSlope + 1) * (movement + accuracy) := by
    have augmented := Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct rootDifference
        (Fraction.Order.Basic.le_refl accuracy))
      (add_nonneg (Arithmetic.mul_nonneg_direct rootSlopeNonnegative accuracyNonnegative)
        movementNonnegative)
    rewrite [_root_.add_zero] at augmented
    exact augmented.trans_eq (by dsimp only [rootSlope]; ring1)
  have numeratorSampler :
      (Name.Sampling.approximation (Coherence.exact firstCoefficient.numerator).name).centerBound ≤
        cached.numeratorCeiling := by
    change 2 * (1 + Norm.Basic.normSq firstCoefficient.numerator) ≤ _
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (1 : Fraction.Rational))
        (cached.numerator_norm_le nonzero degreeBound actual first firstCoefficient)) (by decide)
  have commonLower : rootLower (cap := cap) ≤
      Name.Coherent.Division.SampleEquivalence.commonLower
        lastPrepared.1.certificate.apart firstPrepared.1.certificate.apart :=
    Fraction.Order.Basic.le_min lastLower firstLower
  have numeratorRequestNonnegative :
      0 ≤ Norm.Basic.normSq (lastCoefficient.numerator - firstCoefficient.numerator) + accuracy :=
    add_nonneg (Norm.Basic.normSq_nonneg _) accuracyNonnegative
  have rootRequestNonnegative :
      0 ≤ 32 * bounds.bound * Canonical.normSq (Primitives.point curve (actual.val.point last) -
        Primitives.point curve (actual.val.point first)) + accuracy :=
    add_nonneg (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le bounds.bound_nonnegative)
      (Canonical.normSq_nonneg _)) accuracyNonnegative
  have firstStage := Quotient.quotientBound_antitone_lowerSq (numeratorSlope := 1)
    (by decide : (0 : Fraction.Rational) ≤ 1)
    (Name.Sampling.approximation (Coherence.exact firstCoefficient.numerator).name).centerBound_nonneg
    (Name.Sampling.approximation firstPrepared.1.certificate.value.name).centerBound_nonneg
    numeratorRequestNonnegative rootRequestNonnegative (rootLower_positive (cap := cap)) commonLower
  have secondStage := Quotient.quotientBound_mono (slope := 1) (by decide : (0 : Fraction.Rational) ≤ 1)
    (Name.Sampling.approximation (Coherence.exact firstCoefficient.numerator).name).centerBound_nonneg
    numeratorRequestNonnegative rootRequestNonnegative (rootLower_positive (cap := cap))
    numeratorSampler samplerBound numeratorMovement rootMovement
    (Name.Sampling.approximation firstPrepared.1.certificate.value.name).centerBound_nonneg
  have estimate := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (firstStage.trans secondStage)
      (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide)).le) (Fraction.Order.Basic.le_refl accuracy)
  have enlarged := Arithmetic.add_le_add_direct estimate movementNonnegative
  rewrite [_root_.add_zero] at enlarged
  exact enlarged.trans_eq (by
    change _ = (16 * Quotient.quotientBound 1 cached.numeratorCeiling (rootCeiling bounds)
      (rootLower (cap := cap)) (cached.slope + 1) (rootSlope + 1) + 1) * (movement + accuracy)
    unfold Quotient.quotientBound
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1)

end Bounds

end Polynomials

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

end
