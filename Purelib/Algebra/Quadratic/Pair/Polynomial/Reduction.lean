module

public import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Polynomial.Dense.GCD
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached cancellation of a quadratic numerator's common denominator

Two retained Euclidean calculations remove a common factor from both
quadratic numerator coordinates and their displayed denominator. The source
expression remains the domain owner; a reduced expression can additionally
be considered as a separately certified extension at cancelled points.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense

variable {radicand : Coefficients}

/-- The original real-coordinate and denominator Euclidean calculation type. -/
@[expose] def FirstReduction (original : Expression radicand) : Type :=
  GCD.BezoutResult original.numerator.re original.denominator

/-- The second Euclidean calculation uses the retained first common factor. -/
@[expose] def SecondReduction (original : Expression radicand) (first : FirstReduction original) : Type :=
  GCD.BezoutResult original.numerator.im first.gcd

/-- Build the reduced expression from the two cached original Euclidean results. -/
@[expose] def reducedExpression (original : Expression radicand) (first : FirstReduction original)
    (second : SecondReduction original first) : Expression radicand :=
  ⟨⟨first.pFactor * second.qFactor, second.pFactor⟩, first.qFactor * second.qFactor⟩

/-- The original denominator factors through the retained common factor and reduced denominator. -/
theorem reduced_denominator (original : Expression radicand) (first : FirstReduction original)
    (second : SecondReduction original first) (point : Canonical) :
    original.denominator.eval point = second.gcd.eval point *
      (reducedExpression original first second).denominator.eval point := by
  change original.denominator.eval point = second.gcd.eval point * (first.qFactor * second.qFactor).eval point
  rewrite [first.qIdentity point, second.qIdentity point, DensePolynomial.eval_mul]
  ring1

/-- Both original numerator coordinates share the same retained cancelled factor. -/
theorem reduced_equal (original : Expression radicand) (first : FirstReduction original)
    (second : SecondReduction original first) : original.Equal (reducedExpression original first second) := by
  apply equal_of_cross_eval
  · intro point
    change original.numerator.re.eval point * (first.qFactor * second.qFactor).eval point =
      (first.pFactor * second.qFactor).eval point * original.denominator.eval point
    rewrite [DensePolynomial.eval_mul, DensePolynomial.eval_mul, first.pIdentity point,
      first.qIdentity point, second.qIdentity point]
    ring1
  · intro point
    change original.numerator.im.eval point * (first.qFactor * second.qFactor).eval point =
      second.pFactor.eval point * original.denominator.eval point
    rewrite [DensePolynomial.eval_mul, second.pIdentity point, first.qIdentity point, second.qIdentity point]
    ring1

set_option genInjectivity false in
/-- Cached common-factor cancellation retaining the original quotient domain and both Euclidean witnesses. -/
structure Cancellation (original : Expression radicand) where
  /-- The actual original expression retained as executable data. -/
  source : Expression radicand
  /-- The retained source is the original domain owner. -/
  source_eq : source = original
  /-- The first cached Euclidean calculation on the original real numerator and denominator. -/
  first : FirstReduction original
  /-- The second cached Euclidean calculation consumes the retained first common factor. -/
  second : SecondReduction original first
  /-- The retained reduced coefficient expression. -/
  reduced : Expression radicand
  /-- The reduced expression uses the two exact cached Euclidean results. -/
  reduced_eq : reduced = reducedExpression original first second
  /-- Exact coefficient equality after clearing the original and reduced denominators. -/
  equal : original.Equal reduced
  /-- The original denominator retains the cancelled factor at every scalar coordinate. -/
  denominator_eq : ∀ point : Canonical,
    original.denominator.eval point = second.gcd.eval point * reduced.denominator.eval point

constructive_injectivity Cancellation

/-- Execute two Euclidean calculations once and cache their common-denominator cancellation. -/
@[expose] def cancel (original : Expression radicand) : Cancellation original :=
  let first := GCD.extendedGCD original.numerator.re original.denominator
  let second := GCD.extendedGCD original.numerator.im first.gcd
  let reduced := reducedExpression original first second
  ⟨original, rfl, first, second, reduced, rfl, reduced_equal original first second,
    reduced_denominator original first second⟩

/-- Definedness of the original quotient supplies definedness of the retained reduction. -/
theorem Cancellation.defined {original : Expression radicand} (retained : Cancellation original)
    (point : Canonical) (defined : original.Defined point) : retained.reduced.Defined point := by
  intro zero
  apply defined
  calc
    original.denominator.eval point = retained.second.gcd.eval point * retained.reduced.denominator.eval point :=
      retained.denominator_eq point
    _ = 0 := by rewrite [zero, mul_zero]; rfl

/-- Cancellation preserves the original readback on the original source domain. -/
theorem Cancellation.evaluate_eq {original : Expression radicand} (retained : Cancellation original)
    (point : Canonical) (defined : original.Defined point) :
    original.evaluate point = retained.reduced.evaluate point :=
  retained.equal.evaluate_eq point defined (retained.defined point defined)

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

end
