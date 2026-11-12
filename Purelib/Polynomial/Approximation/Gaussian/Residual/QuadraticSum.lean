module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Dense.Gaussian.EvenQuartic
public import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original quadratic-root sums with a computed quartic residual -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order

namespace QuadraticSum

/-- The actual two rational quadratic parameters determine the displayed quartic coefficient table. -/
@[expose] def polynomial (first second : Rational) :=
  Dense.Gaussian.EvenQuartic.polynomial (2 * (first + second)) ((first - second) ^ 2)

/-- The first quadratic error's cofactor is evaluated on the same two retained input sample programs. -/
@[expose] def firstProgram (first second : Rational) (left right : GeometricApproximation) :
    GeometricApproximation :=
  ((left.mul left).add ((GeometricApproximation.exact 6).mul (right.mul right))).add
    ((GeometricApproximation.exact ⟨-first - 2 * second, 0⟩).add
      ((GeometricApproximation.exact 4).mul (left.mul right)))

/-- The second quadratic error's cofactor is evaluated on the same two retained input sample programs. -/
@[expose] def secondProgram (first second : Rational) (left right : GeometricApproximation) :
    GeometricApproximation :=
  (right.mul right).add ((GeometricApproximation.exact ⟨4 * first - second, 0⟩).add
    ((GeometricApproximation.exact 4).mul (left.mul right)))

/-- The quartic evaluation of the same original sum is the two original quadratic residuals with their cofactors. -/
theorem identity (first second : Rational) (left right : Canonical) :
    (polynomial first second).eval (left + right) =
      (Power.Gaussian.rootPolynomial ⟨first, 0⟩ ⟨2, by decide⟩).eval left *
        (left * left + 6 * (right * right) + (⟨-first - 2 * second, 0⟩ + 4 * (left * right))) +
      (Power.Gaussian.rootPolynomial ⟨second, 0⟩ ⟨2, by decide⟩).eval right *
        (right * right + (⟨4 * first - second, 0⟩ + 4 * (left * right))) := by
  rewrite [polynomial, Dense.Gaussian.EvenQuartic.eval, Power.Gaussian.rootPolynomial_eval,
    Power.Gaussian.rootPolynomial_eval]
  change (left + right) ^ 4 - ⟨2 * (first + second), 0⟩ * (left + right) ^ 2 +
    ⟨(first - second) ^ 2, 0⟩ = (left ^ 2 - ⟨first, 0⟩) *
      (left * left + 6 * (right * right) + (⟨-first - 2 * second, 0⟩ + 4 * (left * right))) +
      (right ^ 2 - ⟨second, 0⟩) * (right * right + (⟨4 * first - second, 0⟩ + 4 * (left * right)))
  have middle : (⟨2 * (first + second), 0⟩ : Canonical) = 2 * (⟨first, 0⟩ + ⟨second, 0⟩) := by
    apply Purelib.Data.Gaussian.Basic.Canonical.ext
    · change 2 * (first + second) = 2 * (first + second) - 0 * (0 + 0)
      ring1
    · change 0 = 2 * (0 + 0) + 0 * (first + second)
      ring1
  have constant : (⟨(first - second) ^ 2, 0⟩ : Canonical) = (⟨first, 0⟩ - ⟨second, 0⟩) ^ 2 := by
    rewrite [pow_two, pow_two]
    apply Purelib.Data.Gaussian.Basic.Canonical.ext
    · change (first - second) * (first - second) =
        (first - second) * (first - second) - (0 - 0) * (0 - 0)
      ring1
    · change 0 = (first - second) * (0 - 0) + (0 - 0) * (first - second)
      ring1
  have firstConstant : (⟨-first - 2 * second, 0⟩ : Canonical) = -⟨first, 0⟩ - 2 * ⟨second, 0⟩ := by
    apply Purelib.Data.Gaussian.Basic.Canonical.ext
    · change -first - 2 * second = -first - (2 * second - 0 * 0)
      ring1
    · change 0 = -0 - (2 * 0 + 0 * second)
      ring1
  have secondConstant : (⟨4 * first - second, 0⟩ : Canonical) = 4 * ⟨first, 0⟩ - ⟨second, 0⟩ := by
    apply Purelib.Data.Gaussian.Basic.Canonical.ext
    · change 4 * first - second = (4 * first - 0 * 0) - second
      ring1
    · change 0 = (4 * 0 + 0 * first) - 0
      ring1
  rewrite [middle, constant, firstConstant, secondConstant]
  ring1

end QuadraticSum

set_option genInjectivity false in
/-- Both actual original quadratic residuals with their unchanged sum channel and retained cofactor sample caches.

The original two input records remain stored with their identities. Finite
geometric arithmetic computes the two cofactor magnitude bounds and the sum
sample program; no companion elimination or replacement root is constructed.
-/
structure QuadraticSum {firstParameter secondParameter : Rational} {firstChannel secondChannel : CoherentNamed}
    (originalFirst : Residual (Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩) firstChannel)
    (originalSecond : Residual (Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩) secondChannel) where
  /-- The actual retained first quadratic residual and original sample cache. -/
  first : Residual (Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩) firstChannel
  /-- The retained first input is the supplied original record. -/
  first_eq : first = originalFirst
  /-- The actual retained second quadratic residual and original sample cache. -/
  second : Residual (Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩) secondChannel
  /-- The retained second input is the supplied original record. -/
  second_eq : second = originalSecond
  /-- The same finite geometric first cofactor program and computed magnitude bound. -/
  firstCofactor : GeometricApproximation
  /-- The retained first cofactor consumes both same original source caches. -/
  firstCofactor_eq : firstCofactor = QuadraticSum.firstProgram firstParameter secondParameter first.source second.source
  /-- The same finite geometric second cofactor program and computed magnitude bound. -/
  secondCofactor : GeometricApproximation
  /-- The retained second cofactor consumes both same original source caches. -/
  secondCofactor_eq : secondCofactor =
    QuadraticSum.secondProgram firstParameter secondParameter first.source second.source
  /-- The actual unchanged same-index original sum sample program. -/
  result : GeometricApproximation
  /-- The retained sum program reads both original samples at the same index. -/
  result_eq : result = first.source.add second.source
  /-- The original numerical sum channel agrees with this same retained source program. -/
  equivalent : NamedEquivalent (CoherentNamed.add firstChannel secondChannel).name result.toApproximation.toNamed
  /-- The computed quartic residual scale from both original errors and same retained cofactor bounds. -/
  scale : Rational
  /-- The scale consumes the same original input scales and actual cofactor magnitude bounds. -/
  scale_eq : scale = 2 * (firstCofactor.centerBound * first.scale + secondCofactor.centerBound * second.scale)

constructive_injectivity QuadraticSum

namespace QuadraticSum

variable {firstParameter secondParameter : Rational} {firstChannel secondChannel : CoherentNamed}
variable {first : Residual (Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩) firstChannel}
variable {second : Residual (Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩) secondChannel}

/-- Build the actual original quadratic-sum numerical certificate once, retaining both input and cofactor caches. -/
@[expose] def ofResiduals
    (first : Residual (Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩) firstChannel)
    (second : Residual (Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩) secondChannel) :
    QuadraticSum first second :=
  let left := firstProgram firstParameter secondParameter first.source second.source
  let right := secondProgram firstParameter secondParameter first.source second.source
  let result := first.source.add second.source
  let equivalent := Geometric.Coherent.Comparison.add_agreesWith firstChannel secondChannel first.source second.source
    result first.equivalent second.equivalent (fun _ => rfl)
  let scale := 2 * (left.centerBound * first.scale + right.centerBound * second.scale)
  ⟨first, rfl, second, rfl, left, rfl, right, rfl, result, rfl, equivalent, scale, rfl⟩

/-- The retained cofactor and original input scales make the computed quartic allowance nonnegative. -/
theorem scale_nonnegative (certificate : QuadraticSum first second) : 0 ≤ certificate.scale := by
  rewrite [certificate.scale_eq]
  exact Arithmetic.mul_nonneg_direct (by decide)
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct certificate.firstCofactor.centerBound_nonneg certificate.first.scale_nonnegative)
      (Arithmetic.mul_nonneg_direct certificate.secondCofactor.centerBound_nonneg certificate.second.scale_nonnegative))

/-- Every actual sum sample obeys the quartic residual allowance computed from both original quadratic errors. -/
theorem bound (certificate : QuadraticSum first second) (index : Nat) :
    normSq ((polynomial firstParameter secondParameter).eval (certificate.result.sample index)) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius certificate.scale index := by
  have identity : (polynomial firstParameter secondParameter).eval (certificate.result.sample index) =
      (Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩).eval
          (certificate.first.source.sample index) * certificate.firstCofactor.sample index +
      (Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩).eval
          (certificate.second.source.sample index) * certificate.secondCofactor.sample index := by
    rewrite [certificate.result_eq, certificate.firstCofactor_eq, certificate.secondCofactor_eq]
    exact identity firstParameter secondParameter _ _
  rewrite [identity]
  have sum := Purelib.Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩).eval
      (certificate.first.source.sample index) * certificate.firstCofactor.sample index)
    ((Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩).eval
      (certificate.second.source.sample index) * certificate.secondCofactor.sample index)
  rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_mul, Purelib.Data.Gaussian.Norm.Basic.normSq_mul] at sum
  have left := Arithmetic.mul_le_mul_of_nonneg_left_direct (certificate.firstCofactor.sample_bounded index)
    (Purelib.Data.Gaussian.Norm.Basic.normSq_nonneg
      ((Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩).eval
        (certificate.first.source.sample index)))
  have right := Arithmetic.mul_le_mul_of_nonneg_left_direct (certificate.secondCofactor.sample_bounded index)
    (Purelib.Data.Gaussian.Norm.Basic.normSq_nonneg
      ((Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩).eval
        (certificate.second.source.sample index)))
  have leftResidual := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (certificate.first.bound index) certificate.firstCofactor.centerBound_nonneg
  have rightResidual := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (certificate.second.bound index) certificate.secondCofactor.centerBound_nonneg
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (left.trans leftResidual) (right.trans rightResidual))
    (by decide : (0 : Rational) ≤ 2)
  apply sum.trans (paid.trans_eq _)
  rewrite [certificate.scale_eq, Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
    Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
    Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- Consume the same retained sum program and computed allowance on the unchanged original sum channel. -/
@[expose] def residualCertificate (certificate : QuadraticSum first second) :
    Residual (polynomial firstParameter secondParameter) (CoherentNamed.add firstChannel secondChannel) :=
  .ofGeometric (by rewrite [polynomial, Dense.Gaussian.EvenQuartic.degree]; decide)
    certificate.result certificate.equivalent certificate.scale certificate.scale_nonnegative certificate.bound

/-- The same actual original sample caches are read by every retained sum residual sample. -/
theorem residualCertificate_sample (certificate : QuadraticSum first second) (index : Nat) :
    certificate.residualCertificate.source.sample index =
      certificate.first.source.sample index + certificate.second.source.sample index := by
  change certificate.result.sample index = _
  rewrite [certificate.result_eq]
  rfl

end QuadraticSum

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
