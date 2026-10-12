module

public import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Rational.Box.Sample.Parabola
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Finite Hermitian restrictions to retained parabolic arcs

The retained centre and positive coordinate radius determine a polynomial
of degree at most four. A nonzero Hermitian form has a nonzero restriction:
its radial, imaginary, real and constant coefficients give explicit pivots.
-/

public section

namespace Purelib.Geometry.Projective.Hermitian.HermitianForm

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- Restrict the original Hermitian form to the actual retained parabolic arc.

The descending coefficient list retains the quartic radial term, zero
cubic term, quadratic imaginary term, linear real term and centre value.
Each coefficient uses the same original centre and coordinate radius.
-/
@[expose] def restrictParabola {outer : Box} (form : HermitianForm) (arc : Box.Sample.Parabola outer) :
    Dense.Basic.DensePolynomial Fraction.Rational :=
  ⟨[form.radial * arc.radius ^ 2, 0,
    form.radial * (arc.radius ^ 2 + 2 * arc.center.im * arc.radius) + form.imagLinear * arc.radius,
    (2 * form.radial * arc.center.re + form.realLinear) * arc.radius,
    form.eval arc.center]⟩

/-- Evaluating the retained restriction polynomial gives the form value at the same original arc sample. -/
theorem eval_restrictParabola {outer : Box} (form : HermitianForm) (arc : Box.Sample.Parabola outer)
    (parameter : Fraction.Rational) :
    (form.restrictParabola arc).eval parameter = form.eval (arc.point parameter) := by
  unfold restrictParabola Dense.Basic.DensePolynomial.eval Dense.Basic.DensePolynomial.evalCoeffs
    Box.Sample.Parabola.point HermitianForm.eval Gaussian.Norm.Basic.normSq
  dsimp only [List.foldl]
  ring1

/-- Every coefficientwise nonzero Hermitian form has a represented nonzero restriction to the retained positive arc. -/
theorem restrictParabola_nonzero {outer : Box} (form : HermitianForm) (arc : Box.Sample.Parabola outer)
    (nonzero : ¬form.IsZero) : (form.restrictParabola arc).isZero = false := by
  have radiusNonzero : arc.radius ≠ 0 := arc.positive.ne'
  by_cases radialZero : form.radial = 0
  · have quarticZero : form.radial * arc.radius ^ 2 = 0 := by rewrite [radialZero]; ring1
    have quadraticEq :
        form.radial * (arc.radius ^ 2 + 2 * arc.center.im * arc.radius) + form.imagLinear * arc.radius =
          form.imagLinear * arc.radius := by rewrite [radialZero]; ring1
    have linearEq : (2 * form.radial * arc.center.re + form.realLinear) * arc.radius =
        form.realLinear * arc.radius := by rewrite [radialZero]; ring1
    change ([form.radial * arc.radius ^ 2, 0,
      form.radial * (arc.radius ^ 2 + 2 * arc.center.im * arc.radius) + form.imagLinear * arc.radius,
      (2 * form.radial * arc.center.re + form.realLinear) * arc.radius,
      form.eval arc.center].dropWhile (fun value => decide (value = 0))).isEmpty = false
    rewrite [quarticZero, quadraticEq, linearEq,
      List.DropWhile.cons_of_true _ 0 _ (by decide), List.DropWhile.cons_of_true _ 0 _ (by decide)]
    by_cases imaginaryZero : form.imagLinear = 0
    · have quadraticZero : form.imagLinear * arc.radius = 0 := by rewrite [imaginaryZero]; ring1
      rewrite [quadraticZero, List.DropWhile.cons_of_true _ 0 _ (by decide)]
      by_cases realZero : form.realLinear = 0
      · have linearZero : form.realLinear * arc.radius = 0 := by rewrite [realZero]; ring1
        have centerValue : form.eval arc.center = form.constant := by
          unfold eval
          rewrite [radialZero, realZero, imaginaryZero]
          ring1
        have constantNonzero : form.constant ≠ 0 := fun constantZero =>
          nonzero ⟨radialZero, realZero, imaginaryZero, constantZero⟩
        rewrite [linearZero, centerValue, List.DropWhile.cons_of_true _ 0 _ (by decide),
          List.DropWhile.cons_of_false _ form.constant [] (decide_eq_false constantNonzero)]
        rfl
      · have linearNonzero := Fraction.Field.mul_ne_zero_direct realZero radiusNonzero
        rewrite [List.DropWhile.cons_of_false _ (form.realLinear * arc.radius) _ (decide_eq_false linearNonzero)]
        rfl
    · have quadraticNonzero := Fraction.Field.mul_ne_zero_direct imaginaryZero radiusNonzero
      rewrite [List.DropWhile.cons_of_false _ (form.imagLinear * arc.radius) _ (decide_eq_false quadraticNonzero)]
      rfl
  · exact Dense.Basic.DensePolynomial.isZero_false_of_coeffs_cons rfl
      (Fraction.Field.mul_ne_zero_direct radialZero (Fraction.Order.Arithmetic.pow_pos_direct arc.positive 2).ne')

/-- Retain the nonzero restriction polynomial, using the unit polynomial for a coefficientwise universal zero form. -/
@[expose] def guardedRestriction {outer : Box} (form : HermitianForm) (arc : Box.Sample.Parabola outer) :
    Dense.Basic.DensePolynomial Fraction.Rational :=
  if form.IsZero then Dense.Basic.DensePolynomial.constant 1 else form.restrictParabola arc

/-- Every guarded restriction is a represented nonzero polynomial. -/
theorem guardedRestriction_nonzero {outer : Box} (form : HermitianForm) (arc : Box.Sample.Parabola outer) :
    (form.guardedRestriction arc).isZero = false := by
  by_cases zero : form.IsZero
  · rewrite [guardedRestriction, if_pos zero]
    exact Dense.Basic.DensePolynomial.isZero_false_of_eval_ne (x := 0) (by
      rewrite [Dense.Basic.DensePolynomial.eval_constant]
      exact Fraction.Field.zero_ne_one.symm)
  · rewrite [guardedRestriction, if_neg zero]
    exact form.restrictParabola_nonzero arc zero

/-- Nonzero guarded evaluation excludes every non-universal Hermitian boundary at the same retained arc sample. -/
theorem eval_ne_zero_of_guardedRestriction {outer : Box} (form : HermitianForm) (arc : Box.Sample.Parabola outer)
    {parameter : Fraction.Rational} (nonzero : ¬form.IsZero)
    (evaluatesNonzero : (form.guardedRestriction arc).eval parameter ≠ 0) : form.eval (arc.point parameter) ≠ 0 := by
  rewrite [guardedRestriction, if_neg nonzero, eval_restrictParabola] at evaluatesNonzero
  exact evaluatesNonzero

end Purelib.Geometry.Projective.Hermitian.HermitianForm
