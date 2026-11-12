module

public import Purelib.Polynomial.Approximation.CoherentEvaluation
public import Purelib.Polynomial.Dense.Gaussian.Division
public import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Approximation.Evaluation
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Operational polynomial division on one retained coherent input

Exact scalar identities of finite dense polynomials transport through the
original coherent Horner channels and the same retained geometric sampler.
Division and Bezout certificates reuse the original completed records; the
annihilator equation concerns the original channel rather than its samples.
-/

public section

namespace Purelib.Polynomial.Approximation.CoherentEvaluation

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- A retained finite division run reconstructs the original dividend's operational evaluation.

The supplied run equality identifies the original quotient, remainder and
step cache with the actual division of the displayed inputs. Its exact scalar
identity is specialized at each sample of the unchanged retained source.
-/
def division_agrees {dividend divisor : CoefficientPolynomial}
    (division : DensePolynomial.DivResult dividend divisor)
    (computed : division = dividend.divMod divisor)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Horner.polynomialEval dividend input).name
      (CoherentNamed.add (Horner.polynomialEval division.remainder input)
        (CoherentNamed.mul (Horner.polynomialEval divisor input)
          (Horner.polynomialEval division.quotient input))).name := by
  let remainder := Evaluation.evaluate division.remainder source
  let factor := Evaluation.evaluate divisor source
  let quotient := Evaluation.evaluate division.quotient source
  have samples : ∀ index,
      (Evaluation.evaluate dividend source).toApproximation.sample index =
        (remainder.add (factor.mul quotient)).toApproximation.sample index := by
    intro index
    change (Evaluation.evaluate dividend source).sample index = (remainder.add (factor.mul quotient)).sample index
    dsimp only [remainder, factor, quotient]
    simp only [GeometricApproximation.add_sample, GeometricApproximation.mul_sample,
      Evaluation.evaluate_sample, -eq_self, -iff_self]
    rewrite [computed]
    exact (Dense.Gaussian.Division.division_evaluation_equation dividend divisor
      (source.sample index)).symm
  let sumAgreement := add_agrees (Horner.polynomialEval division.remainder input)
    (CoherentNamed.mul (Horner.polynomialEval divisor input)
      (Horner.polynomialEval division.quotient input)) remainder (factor.mul quotient)
    (evaluate_agrees division.remainder input source sourceEq)
    (mul_agrees (Horner.polynomialEval divisor input)
      (Horner.polynomialEval division.quotient input) factor quotient
      (evaluate_agrees divisor input source sourceEq)
      (evaluate_agrees division.quotient input source sourceEq))
  exact (evaluate_agrees dividend input source sourceEq).trans
    (((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Evaluation.evaluate dividend source).toApproximation
      (remainder.add (factor.mul quotient)).toApproximation samples).toNamed).trans
        sumAgreement.symm)

/-- An original operational annihilator equation reduces the dividend evaluation to its retained remainder.

The original division run is reused. The zero equation removes its divisor
term by operational arithmetic; no approximate input sample is asserted to
be an exact root.
-/
def remainder_agrees {dividend divisor : CoefficientPolynomial}
    (division : DensePolynomial.DivResult dividend divisor)
    (computed : division = dividend.divMod divisor)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval divisor input).name
      (Coherence.exact 0).name) :
    NamedEquivalent (Horner.polynomialEval dividend input).name
      (Horner.polynomialEval division.remainder input).name := by
  let factor := Horner.polynomialEval divisor input
  let quotient := Horner.polynomialEval division.quotient input
  let remainder := Horner.polynomialEval division.remainder input
  let vanished := (Product.Congruence.coherentMul_respects factor (Coherence.exact 0)
    quotient quotient zero (NamedEquivalent.refl _)).trans
      (Arithmetic.Mul.coherentMul_zero_left quotient)
  let sum := (Sum.Congruence.coherentAdd_respects remainder remainder
    (CoherentNamed.mul factor quotient) (Coherence.exact 0)
    (NamedEquivalent.refl _) vanished).trans (Arithmetic.Add.coherentAdd_zero_right remainder)
  exact (division_agrees division computed input source sourceEq).trans sum

/-- The stored Bezout identity compares the original gcd evaluation with its ordered operational combination.

The original gcd and both retained coefficient polynomials are consumed at
the same source samples. The supplied completed record contains the scalar
identity; this construction does not rerun Euclid.
-/
def bezout_agrees {first second : CoefficientPolynomial}
    (bezout : Dense.GCD.BezoutResult first second)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed) :
    NamedEquivalent (Horner.polynomialEval bezout.gcd input).name
      (CoherentNamed.add
        (CoherentNamed.mul (Horner.polynomialEval bezout.left input)
          (Horner.polynomialEval first input))
        (CoherentNamed.mul (Horner.polynomialEval bezout.right input)
          (Horner.polynomialEval second input))).name := by
  let left := Evaluation.evaluate bezout.left source
  let firstSource := Evaluation.evaluate first source
  let right := Evaluation.evaluate bezout.right source
  let secondSource := Evaluation.evaluate second source
  let combination := (left.mul firstSource).add (right.mul secondSource)
  let agreement := add_agrees
    (CoherentNamed.mul (Horner.polynomialEval bezout.left input)
      (Horner.polynomialEval first input))
    (CoherentNamed.mul (Horner.polynomialEval bezout.right input)
      (Horner.polynomialEval second input))
    (left.mul firstSource) (right.mul secondSource)
    (mul_agrees (Horner.polynomialEval bezout.left input) (Horner.polynomialEval first input)
      left firstSource (evaluate_agrees bezout.left input source sourceEq)
      (evaluate_agrees first input source sourceEq))
    (mul_agrees (Horner.polynomialEval bezout.right input) (Horner.polynomialEval second input)
      right secondSource (evaluate_agrees bezout.right input source sourceEq)
      (evaluate_agrees second input source sourceEq))
  have samples : ∀ index, (Evaluation.evaluate bezout.gcd source).toApproximation.sample index =
      combination.toApproximation.sample index := by
    intro index
    change (Evaluation.evaluate bezout.gcd source).sample index = combination.sample index
    dsimp only [combination, left, firstSource, right, secondSource]
    simp only [GeometricApproximation.add_sample, GeometricApproximation.mul_sample,
      Evaluation.evaluate_sample, -eq_self, -iff_self]
    exact bezout.identity (source.sample index)
  exact (evaluate_agrees bezout.gcd input source sourceEq).trans
    (((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Evaluation.evaluate bezout.gcd source).toApproximation
      combination.toApproximation samples).toNamed).trans agreement.symm)

/-- A nonzero constant gcd gives an operational inverse product for the original second evaluation.

The retained inverse polynomial has the scalar evaluation of the original
right Bezout coefficient scaled by the inverse gcd constant. The annihilator
equation removes the first term; exact operational arithmetic proves the
second evaluation times that same inverse channel is one. The product
certificate can be consumed by the original factor preparation operation.
-/
def bezout_inverse_agrees {annihilator polynomial : CoefficientPolynomial}
    (bezout : Dense.GCD.BezoutResult annihilator polynomial)
    (value : Canonical) (gcdConstant : bezout.gcd = DensePolynomial.constant value)
    (nonzero : value ≠ 0) (inversePolynomial : CoefficientPolynomial)
    (inverseEval : ∀ point : Canonical,
      inversePolynomial.eval point = value⁻¹ * bezout.right.eval point)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator input).name
      (Coherence.exact 0).name)
    (inverseCache : CoherentNamed := Horner.polynomialEval inversePolynomial input)
    (inverseCacheEq : inverseCache = Horner.polynomialEval inversePolynomial input := by rfl)
    (hornerCache : Option (Horner.Accumulations input (Coherence.exact 0) inversePolynomial.coeffs) := none) :
    NamedEquivalent
      (CoherentNamed.mul (Horner.polynomialEval polynomial input) inverseCache).name
      (Coherence.exact 1).name := by
  let first := Horner.polynomialEval annihilator input
  let second := Horner.polynomialEval polynomial input
  let left := Horner.polynomialEval bezout.left input
  let right := Horner.polynomialEval bezout.right input
  let inverse := inverseCache
  let exactInverse := Coherence.exact value⁻¹
  let vanished := (Product.Congruence.coherentMul_respects left left first (Coherence.exact 0)
    (NamedEquivalent.refl _) zero).trans (Arithmetic.Mul.coherentMul_zero_right left)
  let collapsed := (Sum.Congruence.coherentAdd_respects (CoherentNamed.mul left first) (Coherence.exact 0)
    (CoherentNamed.mul right second) (CoherentNamed.mul right second) vanished
    (NamedEquivalent.refl _)).trans (Arithmetic.Add.coherentAdd_zero_left (CoherentNamed.mul right second))
  have constant : NamedEquivalent (Horner.polynomialEval bezout.gcd input).name
      (Coherence.exact value).name := by
    rewrite [gcdConstant]
    exact evaluate_constant_agrees value input source sourceEq
  let rightProduct := ((bezout_agrees bezout input source sourceEq).trans collapsed).symm.trans constant
  let rightSource := Evaluation.evaluate bezout.right source
  let inverseSource := (GeometricApproximation.exact value⁻¹).mul rightSource
  have inverseSamples : ∀ index, (Evaluation.evaluate inversePolynomial source).toApproximation.sample index =
      inverseSource.toApproximation.sample index := by
    intro index
    change (Evaluation.evaluate inversePolynomial source).sample index = inverseSource.sample index
    dsimp only [inverseSource, rightSource]
    simp only [GeometricApproximation.mul_sample, GeometricApproximation.exact_sample,
      Evaluation.evaluate_sample, -eq_self, -iff_self]
    exact inverseEval (source.sample index)
  let inverseAgreement := (evaluate_agrees inversePolynomial input source sourceEq hornerCache).trans
    (((Sequence.Equivalence.approximationEquivalentOfSamplesEq
      (Evaluation.evaluate inversePolynomial source).toApproximation inverseSource.toApproximation
      inverseSamples).toNamed).trans
        (mul_agrees exactInverse right (GeometricApproximation.exact value⁻¹) rightSource
          (exact_agrees value⁻¹) (evaluate_agrees bezout.right input source sourceEq)).symm)
  have cachedInverseAgreement : NamedEquivalent inverse.name (CoherentNamed.mul exactInverse right).name := by
    have agreement := inverseAgreement
    rewrite [← inverseCacheEq] at agreement
    exact agreement
  let replaceInverse := Product.Congruence.coherentMul_respects second second inverse
    (CoherentNamed.mul exactInverse right) (NamedEquivalent.refl _) cachedInverseAgreement
  let rearrange := (Product.Laws.coherentMul_comm second (CoherentNamed.mul exactInverse right)).trans
    (Product.Laws.coherentMul_assoc exactInverse right second)
  let replaceProduct := Product.Congruence.coherentMul_respects exactInverse exactInverse
    (CoherentNamed.mul right second) (Coherence.exact value) (NamedEquivalent.refl _) rightProduct
  have exactProduct := Name.Coherent.Exact.Arithmetic.exact_mul value⁻¹ value
  rewrite [Canonical.inv_mul_cancel value nonzero] at exactProduct
  exact replaceInverse.trans (rearrange.trans (replaceProduct.trans exactProduct))

/-- Supplying the actual cached inverse preserves the complete original default product certificate after exact
endpoint transport. -/
theorem bezout_inverse_agrees_eq_default {annihilator polynomial : CoefficientPolynomial}
    (bezout : Dense.GCD.BezoutResult annihilator polynomial)
    (value : Canonical) (gcdConstant : bezout.gcd = DensePolynomial.constant value)
    (nonzero : value ≠ 0) (inversePolynomial : CoefficientPolynomial)
    (inverseEval : ∀ point : Canonical, inversePolynomial.eval point = value⁻¹ * bezout.right.eval point)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator input).name (Coherence.exact 0).name)
    (inverseCache : CoherentNamed) (inverseCacheEq : inverseCache = Horner.polynomialEval inversePolynomial input) :
    (inverseCacheEq ▸ bezout_inverse_agrees bezout value gcdConstant nonzero inversePolynomial inverseEval
      input source sourceEq zero inverseCache inverseCacheEq) =
      bezout_inverse_agrees bezout value gcdConstant nonzero inversePolynomial inverseEval
        input source sourceEq zero := by
  cases inverseCacheEq
  rfl

/-- The retained inverse Horner execution preserves the original complete Bezout unit-product certificate. -/
theorem bezout_inverse_agrees_cached_eq_default {annihilator polynomial : CoefficientPolynomial}
    (bezout : Dense.GCD.BezoutResult annihilator polynomial)
    (value : Canonical) (gcdConstant : bezout.gcd = DensePolynomial.constant value)
    (nonzero : value ≠ 0) (inversePolynomial : CoefficientPolynomial)
    (inverseEval : ∀ point : Canonical, inversePolynomial.eval point = value⁻¹ * bezout.right.eval point)
    (input : CoherentNamed) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent input.name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator input).name (Coherence.exact 0).name)
    (inverseCache : CoherentNamed) (inverseCacheEq : inverseCache = Horner.polynomialEval inversePolynomial input)
    (cached : Horner.Accumulations input (Coherence.exact 0) inversePolynomial.coeffs) :
    bezout_inverse_agrees bezout value gcdConstant nonzero inversePolynomial inverseEval
        input source sourceEq zero inverseCache inverseCacheEq (some cached) =
      bezout_inverse_agrees bezout value gcdConstant nonzero inversePolynomial inverseEval
        input source sourceEq zero inverseCache inverseCacheEq := by
  unfold bezout_inverse_agrees
  rewrite [evaluate_agrees_cached_eq_default]
  rfl

end Purelib.Polynomial.Approximation.CoherentEvaluation
