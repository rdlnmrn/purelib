module

public import Purelib.Polynomial.Winding.Circle.Operations
public import Purelib.Polynomial.Dense.Gaussian.Conjugate
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.RationalFunctions.Curve.Canonical.Circle.Conjugate
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Affine
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.Ring

/-!
# Original circle winding under coefficient conjugation

The same retained chart coordinate polynomials undergo rational parameter
reflection and imaginary-coordinate negation. Their two independent Cauchy
indices therefore retain both actual orientation changes.
-/

public section

namespace Purelib.Polynomial.Clearance.Circle.Certificate

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Gaussian

/-- Coefficient conjugation retains the same original complete-circle quadrance margin. -/
@[expose] def conjugate {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (clearance : Certificate polynomial) : Certificate (Conjugate.polynomial polynomial) :=
  { bound := clearance.bound
    positive := clearance.positive
    lower := by
      intro point unit
      rewrite [Conjugate.eval]
      have preserved : Norm.Basic.normSq (Canonical.conj (polynomial.eval (Canonical.conj point))) =
          Norm.Basic.normSq (polynomial.eval (Canonical.conj point)) := Norm.Basic.normSq_conj _
      rewrite [preserved]
      apply clearance.lower (Canonical.conj point)
      have reflection : (Canonical.conj point).normSq = point.normSq :=
        (Norm.Basic.normSq_eq_canonical _).symm.trans
          ((Norm.Basic.normSq_conj point).trans (Norm.Basic.normSq_eq_canonical point))
      exact reflection.trans unit }

/-- Coefficient reversal retains the same original complete-circle quadrance margin.

The original reciprocal evaluation is multiplied by a unit-quadrance power.
Its reflected point remains on the same rational unit circle.
-/
@[expose] def reversed {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (clearance : Certificate polynomial) : Certificate (Reciprocal.reversed polynomial) :=
  { bound := clearance.bound
    positive := clearance.positive
    lower := by
      intro point unit
      have nonzero : point ≠ 0 := by
        intro zero
        have impossible := zero ▸ unit
        exact (by decide +kernel : (0 : Purelib.Data.Rat.Fraction.Rational) ≠ 1) impossible
      rewrite [Reciprocal.reversed_identity polynomial point nonzero, Norm.Basic.normSq_mul,
        Power.normSq_pow, Norm.Basic.normSq_eq_canonical point, unit, one_pow,
        Purelib.Data.Rat.Fraction.Field.one_mul, Canonical.inv_eq_conj_of_normSq_one point unit]
      apply clearance.lower (Canonical.conj point)
      exact (Norm.Basic.normSq_eq_canonical _).symm.trans
        ((Norm.Basic.normSq_conj point).trans ((Norm.Basic.normSq_eq_canonical point).trans unit)) }

end Purelib.Polynomial.Clearance.Circle.Certificate

namespace Purelib.Polynomial.Winding.Circle

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.RationalFunctions.Curve.Canonical.Circle

section Charts

open Purelib.RationalFunctions.Curve

/-- A retained chart pair reads the original value times its actual real denominator power. -/
private theorem chart_value {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : RationalCurve}
    (data : Substitution.Retained polynomial curve) (parameter : Rational)
    (denominator : curve.denominatorAt parameter = (⟨parameter ^ 2 + 1, 0⟩ : Canonical))
    (nonzero : curve.denominatorAt parameter ≠ 0) :
    (⟨data.real.eval parameter, data.imaginary.eval parameter⟩ : Canonical) =
      (⟨(parameter ^ 2 + 1) ^ polynomial.coeffs.length, 0⟩ : Canonical) * polynomial.eval (curve.point parameter) := by
  rewrite [data.coordinates, data.state_value, eval_clearedEval polynomial curve parameter nonzero,
    eval_denominatorPower, denominator, Purelib.Data.Gaussian.Power.realAxis_pow]
  rfl

/-- Coefficient conjugation reflects the original chart parameter and negates its actual imaginary coordinate. -/
private theorem chart_conjugate {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : RationalCurve}
    (source : Substitution.Retained polynomial curve)
    (target : Substitution.Retained (Conjugate.polynomial polynomial) curve)
    (denominator : ∀ parameter : Rational, curve.denominatorAt parameter = (⟨parameter ^ 2 + 1, 0⟩ : Canonical))
    (nonzero : ∀ parameter : Rational, curve.denominatorAt parameter ≠ 0)
    (reflection : ∀ parameter : Rational, Canonical.conj (curve.point parameter) = curve.point (-parameter))
    (parameter : Rational) :
    (⟨target.real.eval parameter, target.imaginary.eval parameter⟩ : Canonical) =
      Canonical.conj (⟨source.real.eval (-parameter), source.imaginary.eval (-parameter)⟩ : Canonical) := by
  rewrite [chart_value target parameter (denominator parameter) (nonzero parameter),
    chart_value source (-parameter) (denominator (-parameter)) (nonzero (-parameter)),
    Dense.Map.map_length, Conjugate.eval, reflection, Canonical.conj_mul]
  have payment : Canonical.conj (⟨((-parameter) ^ 2 + 1) ^ polynomial.coeffs.length, 0⟩ : Canonical) =
      (⟨(parameter ^ 2 + 1) ^ polynomial.coeffs.length, 0⟩ : Canonical) := by
    apply Canonical.ext
    · change ((-parameter) ^ 2 + 1) ^ polynomial.coeffs.length =
        (parameter ^ 2 + 1) ^ polynomial.coeffs.length
      apply congrArg (fun value : Rational => value ^ polynomial.coeffs.length)
      ring1
    · change -(0 : Rational) = 0
      ring1
  rewrite [payment]
  rfl

end Charts

section Indices

open Purelib.RationalFunctions
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.Polynomial.Dense.Rational
open Purelib.Polynomial.Dense.Rational.Substitution

/-- The actual coefficient-conjugated chart's real table is the reflected original real table. -/
private theorem chart_real {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : RationalCurve}
    (source : Curve.Substitution.Retained polynomial curve)
    (target : Curve.Substitution.Retained (Conjugate.polynomial polynomial) curve)
    (denominator : ∀ parameter : Rational, curve.denominatorAt parameter = (⟨parameter ^ 2 + 1, 0⟩ : Canonical))
    (nonzero : ∀ parameter : Rational, curve.denominatorAt parameter ≠ 0)
    (reflection : ∀ parameter : Rational, Canonical.conj (curve.point parameter) = curve.point (-parameter)) :
    target.real.normalize = (Affine.subst source.real 0 (-1)).normalize := by
  apply Extensionality.rational_normalized_eq_of_eval_eq (DensePolynomial.normalize_normalize _)
    (DensePolynomial.normalize_normalize _)
  intro parameter
  rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_normalize, Affine.subst_eval,
    show (0 : Rational) + (-1) * parameter = -parameter by ring1]
  have reading := congrArg Canonical.re (chart_conjugate source target denominator nonzero reflection parameter)
  exact reading

/-- The actual coefficient-conjugated chart's imaginary table is the negative reflected original table. -/
private theorem chart_imaginary {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : RationalCurve}
    (source : Curve.Substitution.Retained polynomial curve)
    (target : Curve.Substitution.Retained (Conjugate.polynomial polynomial) curve)
    (denominator : ∀ parameter : Rational, curve.denominatorAt parameter = (⟨parameter ^ 2 + 1, 0⟩ : Canonical))
    (nonzero : ∀ parameter : Rational, curve.denominatorAt parameter ≠ 0)
    (reflection : ∀ parameter : Rational, Canonical.conj (curve.point parameter) = curve.point (-parameter)) :
    target.imaginary.normalize = (-(Affine.subst source.imaginary 0 (-1))).normalize := by
  apply Extensionality.rational_normalized_eq_of_eval_eq (DensePolynomial.normalize_normalize _)
    (DensePolynomial.normalize_normalize _)
  intro parameter
  rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_normalize, DensePolynomial.eval_neg, Affine.subst_eval,
    show (0 : Rational) + (-1) * parameter = -parameter by ring1]
  have reading := congrArg Canonical.im (chart_conjugate source target denominator nonzero reflection parameter)
  exact reading

/-- Parameter reflection and imaginary negation preserve the actual doubled index of one retained chart. -/
private theorem chart_index {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : RationalCurve}
    (source : Curve.Substitution.Retained polynomial curve)
    (target : Curve.Substitution.Retained (Conjugate.polynomial polynomial) curve)
    (denominator : ∀ parameter : Rational, curve.denominatorAt parameter = (⟨parameter ^ 2 + 1, 0⟩ : Canonical))
    (nonzero : ∀ parameter : Rational, curve.denominatorAt parameter ≠ 0)
    (reflection : ∀ parameter : Rational, Canonical.conj (curve.point parameter) = curve.point (-parameter))
    (clearance : Clearance.Pair.Basic.Certificate source.real source.imaginary Boundary.parameters) :
    CauchyIndex.Basic.Sturm.cauchyIndex2 target.real target.imaginary (-1) 1 =
      CauchyIndex.Basic.Sturm.cauchyIndex2 source.real source.imaginary (-1) 1 := by
  let real := Affine.subst source.real 0 (-1)
  let imaginary := Affine.subst source.imaginary 0 (-1)
  have atStart : real.eval (-1) ≠ 0 ∨ imaginary.eval (-1) ≠ 0 := by
    change (Affine.subst source.real 0 (-1)).eval (-1) ≠ 0 ∨
      (Affine.subst source.imaginary 0 (-1)).eval (-1) ≠ 0
    rewrite [Affine.subst_eval, Affine.subst_eval, show (0 : Rational) + (-1) * (-1) = 1 by decide +kernel]
    exact clearance.eval_ne_zero (by decide +kernel)
  have atStop : real.eval 1 ≠ 0 ∨ imaginary.eval 1 ≠ 0 := by
    change (Affine.subst source.real 0 (-1)).eval 1 ≠ 0 ∨
      (Affine.subst source.imaginary 0 (-1)).eval 1 ≠ 0
    rewrite [Affine.subst_eval, Affine.subst_eval, show (0 : Rational) + (-1) * 1 = -1 by decide +kernel]
    exact clearance.eval_ne_zero (by decide +kernel)
  have affine := CauchyIndex.Affine.cauchyIndex2_affine source.real source.imaginary 0 (-1) (-1) 1
    (by decide +kernel)
  rewrite [show (0 : Rational) + (-1) * (-1) = 1 by decide +kernel,
    show (0 : Rational) + (-1) * 1 = -1 by decide +kernel] at affine
  calc
    _ = CauchyIndex.Basic.Sturm.cauchyIndex2 target.real.normalize target.imaginary.normalize (-1) 1 :=
      (CauchyIndex.Basic.cauchyIndex2_normalize _ _ _ _).symm
    _ = CauchyIndex.Basic.Sturm.cauchyIndex2 real.normalize (-imaginary).normalize (-1) 1 :=
      congrArg₂ (fun first second => CauchyIndex.Basic.Sturm.cauchyIndex2 first second (-1) 1)
        (chart_real source target denominator nonzero reflection)
        (chart_imaginary source target denominator nonzero reflection)
    _ = CauchyIndex.Basic.Sturm.cauchyIndex2 real (-imaginary) (-1) 1 :=
      CauchyIndex.Basic.cauchyIndex2_normalize _ _ _ _
    _ = -CauchyIndex.Basic.Sturm.cauchyIndex2 real imaginary (-1) 1 :=
      CauchyIndex.Basic.cauchyIndex2_neg_denominator atStart atStop
    _ = -CauchyIndex.Basic.Sturm.cauchyIndex2 source.real source.imaginary 1 (-1) := congrArg Neg.neg affine
    _ = CauchyIndex.Basic.Sturm.cauchyIndex2 source.real source.imaginary (-1) 1 := by
      rewrite [CauchyIndex.Basic.cauchyIndex2_reverse]
      ring1

/-- Coefficient conjugation preserves the independently computed original circle raw winding.

Each actual target chart pair reflects the original parameter and negates the
imaginary coordinate. The original affine Cauchy-index law and denominator
negation cancel their two sign changes, including all original chart joins.
-/
theorem raw_conjugate {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (clearance : Clearance.Circle.Certificate polynomial) (source : Boundary.Substitutions polynomial)
    (target : Boundary.Substitutions (Conjugate.polynomial polynomial)) : raw target = raw source := by
  let bounds := clearance.onBoundary source
  have primary := chart_index source.primary target.primary (circle_denominatorAt 1)
    (circle_denominator_ne 1) conj_circle bounds.primary
  have reciprocal := chart_index source.reciprocal target.reciprocal (reciprocalCircle_denominatorAt 1)
    (reciprocalCircle_denominator_ne 1) conj_reciprocalCircle bounds.reciprocal
  unfold raw
  rewrite [primary, reciprocal]
  rfl

end Indices

section Reciprocal

open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction.Order

/-- The original reciprocal product has the coordinate-power direction with a strictly positive real multiplier. -/
private theorem reversed_product_positive
    {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (clearance : Clearance.Circle.Certificate polynomial) (point : Canonical) (unit : point.normSq = 1) :
    0 < ((DensePolynomial.shift polynomial.natDegree (DensePolynomial.constant (1 : Canonical))).eval point).re *
        ((Reciprocal.reversed polynomial * Conjugate.polynomial polynomial).eval point).re +
      ((DensePolynomial.shift polynomial.natDegree (DensePolynomial.constant (1 : Canonical))).eval point).im *
        ((Reciprocal.reversed polynomial * Conjugate.polynomial polynomial).eval point).im := by
  have nonzero : point ≠ 0 := by
    intro zero
    have impossible := zero ▸ unit
    exact (by decide +kernel : (0 : Rational) ≠ 1) impossible
  have reflected : (Canonical.conj point).normSq = 1 :=
    (Norm.Basic.normSq_eq_canonical _).symm.trans
      ((Norm.Basic.normSq_conj point).trans ((Norm.Basic.normSq_eq_canonical point).trans unit))
  rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_constant, Canonical.one_mul,
    DensePolynomial.eval_mul, Reciprocal.reversed_identity polynomial point nonzero,
    Canonical.inv_eq_conj_of_normSq_one point unit, Conjugate.eval]
  have identity (direction value : Canonical) :
      direction.re * ((direction * value) * Canonical.conj value).re +
        direction.im * ((direction * value) * Canonical.conj value).im =
      Norm.Basic.normSq direction * Norm.Basic.normSq value := by
    change direction.re * ((direction.re * value.re - direction.im * value.im) * value.re -
          (direction.re * value.im + direction.im * value.re) * (-value.im)) +
        direction.im * ((direction.re * value.re - direction.im * value.im) * (-value.im) +
          (direction.re * value.im + direction.im * value.re) * value.re) =
      (direction.re ^ 2 + direction.im ^ 2) * (value.re ^ 2 + value.im ^ 2)
    ring1
  rewrite [identity, Power.normSq_pow, Norm.Basic.normSq_eq_canonical point, unit, one_pow,
    Purelib.Data.Rat.Fraction.Field.one_mul]
  exact Norm.Basic.normSq_pos (clearance.eval_ne reflected)

/-- Coefficient reversal complements the independently computed raw circle winding in the original degree.

The actual reversed and coefficient-conjugated polynomials multiply to a
positive real multiple of the degree coordinate power. The original product
and half-plane comparisons retain their independently computed chart events.
-/
theorem raw_reversed {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (clearance : Clearance.Circle.Certificate polynomial) (source : Boundary.Substitutions polynomial)
    (target : Boundary.Substitutions (Reciprocal.reversed polynomial)) :
    raw target = 4 * (polynomial.natDegree : Int) - raw source := by
  let conjugatePaths := Boundary.Substitutions.prepare (Conjugate.polynomial polynomial)
  let productPaths := Boundary.Substitutions.prepare (Reciprocal.reversed polynomial * Conjugate.polynomial polynomial)
  let constantPaths := Boundary.Substitutions.prepare (DensePolynomial.constant (1 : Canonical))
  let powerPaths := Boundary.Substitutions.prepare
    (DensePolynomial.shift polynomial.natDegree (DensePolynomial.constant (1 : Canonical)))
  have comparison := Comparison.raw_eq_of_positiveDot
    ((Clearance.Circle.Certificate.constant 1 (by decide +kernel)).shift polynomial.natDegree)
    (clearance.reversed.product clearance.conjugate) powerPaths productPaths
    (reversed_product_positive clearance)
  have product := raw_mul clearance.reversed clearance.conjugate target conjugatePaths productPaths
  have coordinate := raw_shift (Clearance.Circle.Certificate.constant 1 (by decide +kernel))
    constantPaths polynomial.natDegree powerPaths
  rewrite [raw_constant] at coordinate
  have conjugate := raw_conjugate clearance source conjugatePaths
  rewrite [conjugate] at product
  have balance := product.symm.trans (comparison.trans coordinate)
  calc
    raw target = (raw target + raw source) - raw source := by ring1
    _ = (0 + 4 * (polynomial.natDegree : Int)) - raw source := congrArg (fun value : Int => value - raw source) balance
    _ = _ := by ring1

end Reciprocal

end Purelib.Polynomial.Winding.Circle

end
