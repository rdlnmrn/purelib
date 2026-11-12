module

public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-! # Fractional weights on one retained polynomial-pair denotation

The full numerator and divisor modify the original polynomial expression.
At its actual coordinate their exact quotient is passed to the original
Scaling operation. Pointwise reinterpretation keeps that same cached pair
and channel, without another denominator observation or generator reading.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Multiply the complete numerator by N and the complete denominator by D in the same quadratic expression. -/
@[expose] def scaleFraction {radicand : Coefficients} (numerator divisor : Coefficients)
    (original : Expression radicand) :
    Expression radicand :=
  ⟨Pair.scale numerator original.numerator, divisor * original.denominator⟩

/-- Both original denominator guards give the actual quotient-weighted expression's domain. -/
theorem defined_scaleFraction {radicand : Coefficients} (numerator divisor : Coefficients)
    (original : Expression radicand) (point : Canonical) (defined : original.Defined point)
    (nonzero : divisor.eval point ≠ 0) : (Expression.scaleFraction numerator divisor original).Defined point := by
  change (divisor * original.denominator).eval point ≠ 0
  rewrite [eval_mul]
  exact Field.mul_ne_zero_direct nonzero defined

/-- Two explicit nonzero denominators distribute one scalar quotient product. -/
private theorem quotient_product (numerator value divisor original : Canonical)
    (divisorNonzero : divisor ≠ 0) (originalNonzero : original ≠ 0) :
    numerator * value / (divisor * original) = (numerator / divisor) * (value / original) := by
  apply Field.mul_right_cancel_of_ne (Field.mul_ne_zero_direct divisorNonzero originalNonzero)
  calc
    _ = numerator * value := ExplicitField.div_mul_cancel _ (Field.mul_ne_zero_direct divisorNonzero originalNonzero)
    _ = ((numerator / divisor) * divisor) * ((value / original) * original) := by
      rewrite [ExplicitField.div_mul_cancel _ divisorNonzero, ExplicitField.div_mul_cancel _ originalNonzero]
      rfl
    _ = _ := by ring1

/-- The whole evaluated pair is scaled by the exact full N(w)/D(w) at the actual retained coordinate. -/
theorem evaluate_scaleFraction {radicand : Coefficients} (numerator divisor : Coefficients)
    (original : Expression radicand) (point : Canonical) (defined : original.Defined point)
    (nonzero : divisor.eval point ≠ 0) :
    (Expression.scaleFraction numerator divisor original).evaluate point =
      Pair.scale (numerator.eval point / divisor.eval point) (original.evaluate point) := by
  apply Pair.ext
  · change (numerator * original.numerator.re).eval point / (divisor * original.denominator).eval point =
      (numerator.eval point / divisor.eval point) * (original.numerator.re.eval point / original.denominator.eval point)
    rewrite [eval_mul, eval_mul]
    exact quotient_product _ _ _ _ nonzero defined
  · change (numerator * original.numerator.im).eval point / (divisor * original.denominator).eval point =
      (numerator.eval point / divisor.eval point) * (original.numerator.im.eval point / original.denominator.eval point)
    rewrite [eval_mul, eval_mul]
    exact quotient_product _ _ _ _ nonzero defined

/-- Use original Scaling for the actual quotient, then retain the same cached pair/channel under the full expression.

The target retains both complete polynomial inputs in its source expression.
The computed exact coefficient is passed to the existing Scaling owner;
no alternative scaling record or new factor observation is introduced.
-/
def Denotation.scaleFraction {radicand : Coefficients} {original : Expression radicand}
    {point : Canonical} {generator : CoherentNamed} (source : Denotation original point generator)
    (numerator divisor : Coefficients) (nonzero : divisor.eval point ≠ 0) :
    (scaled : source.Scaling (constant (numerator.eval point / divisor.eval point))) ×
    { target : Denotation (Expression.scaleFraction numerator divisor original) point generator //
      target.value = scaled.target.value ∧ target.channel = scaled.target.channel } := by
  let factor := numerator.eval point / divisor.eval point
  let scaled := source.scale (constant factor)
  have scalarized : (original.scale (constant factor)).evaluate point =
      Pair.scale factor (original.evaluate point) :=
    (evaluate_scale (constant factor) original point).trans
      (congrArg (fun value => Pair.scale value (original.evaluate point)) (eval_constant factor point))
  have equal : (Expression.scaleFraction numerator divisor original).evaluate point =
      (original.scale (constant factor)).evaluate point :=
    (evaluate_scaleFraction numerator divisor original point source.defined nonzero).trans scalarized.symm
  let target := scaled.target.reinterpretAt (Expression.scaleFraction numerator divisor original) equal
    (defined_scaleFraction numerator divisor original point source.defined nonzero)
  exact ⟨scaled, ⟨target, ⟨rfl, rfl⟩⟩⟩

/-- Fractional scaling retains the complete original Scaling and same-pair reinterpretation factory value. -/
private theorem Denotation.packaged_scaleFraction_factory {radicand : Coefficients} {original : Expression radicand}
    {point : Canonical} {generator : CoherentNamed} (source : Denotation original point generator)
    (numerator divisor : Coefficients) (nonzero : divisor.eval point ≠ 0) :
    source.scaleFraction numerator divisor nonzero =
(
  by
    let factor := numerator.eval point / divisor.eval point
    let scaled := source.scale (constant factor)
    have scalarized : (original.scale (constant factor)).evaluate point =
        Pair.scale factor (original.evaluate point) :=
      (evaluate_scale (constant factor) original point).trans
        (congrArg (fun value => Pair.scale value (original.evaluate point)) (eval_constant factor point))
    have equal : (Expression.scaleFraction numerator divisor original).evaluate point =
        (original.scale (constant factor)).evaluate point :=
      (evaluate_scaleFraction numerator divisor original point source.defined nonzero).trans scalarized.symm
    let target := scaled.target.reinterpretAt (Expression.scaleFraction numerator divisor original) equal
      (defined_scaleFraction numerator divisor original point source.defined nonzero)
    exact ⟨scaled, ⟨target, ⟨rfl, rfl⟩⟩⟩
  : (scaled : source.Scaling (constant (numerator.eval point / divisor.eval point))) ×
    { target : Denotation (Expression.scaleFraction numerator divisor original) point generator //
      target.value = scaled.target.value ∧ target.channel = scaled.target.channel }) := by rfl

/-- Fractional scaling retains the complete original Scaling and same-pair reinterpretation factory value. -/
theorem Denotation.scaleFraction_factory {radicand : Coefficients} {original : Expression radicand}
    {point : Canonical} {generator : CoherentNamed} (source : Denotation original point generator)
    (numerator divisor : Coefficients) (nonzero : divisor.eval point ≠ 0) :
    source.scaleFraction numerator divisor nonzero =
(
  by
    let factor := numerator.eval point / divisor.eval point
    let scaled := source.scale (constant factor)
    have scalarized : (original.scale (constant factor)).evaluate point =
        Pair.scale factor (original.evaluate point) :=
      (evaluate_scale (constant factor) original point).trans
        (congrArg (fun value => Pair.scale value (original.evaluate point)) (eval_constant factor point))
    have equal : (Expression.scaleFraction numerator divisor original).evaluate point =
        (original.scale (constant factor)).evaluate point :=
      (evaluate_scaleFraction numerator divisor original point source.defined nonzero).trans scalarized.symm
    let target := scaled.target.reinterpretAt (Expression.scaleFraction numerator divisor original) equal
      (defined_scaleFraction numerator divisor original point source.defined nonzero)
    exact ⟨scaled, ⟨target, ⟨rfl, rfl⟩⟩⟩
  : (scaled : source.Scaling (constant (numerator.eval point / divisor.eval point))) ×
    { target : Denotation (Expression.scaleFraction numerator divisor original) point generator //
      target.value = scaled.target.value ∧ target.channel = scaled.target.channel }) :=
  source.packaged_scaleFraction_factory numerator divisor nonzero

/-- The actual cached fractional scaling output compares to its same retained full-expression channel. -/
def Denotation.scaleFraction_equivalent {radicand : Coefficients} {original : Expression radicand}
    {point : Canonical} {generator : CoherentNamed} (source : Denotation original point generator)
    (numerator divisor : Coefficients)
    (retained : (scaled : source.Scaling (constant (numerator.eval point / divisor.eval point))) ×
      { target : Denotation (Expression.scaleFraction numerator divisor original) point generator //
        target.value = scaled.target.value ∧ target.channel = scaled.target.channel }) :
    NamedEquivalent retained.1.output.name retained.2.val.channel.name :=
  NamedEquivalent.transport rfl (congrArg CoherentNamed.name retained.2.property.2.symm) retained.1.equivalent

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

end
