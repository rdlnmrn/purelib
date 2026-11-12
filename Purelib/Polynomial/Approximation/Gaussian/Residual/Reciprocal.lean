module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Approximation.Gaussian.Geometric.Inverse
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Prepared reciprocals of retained quantitative polynomial residuals

An actual successful denominator preparation supplies a whole-ball lower
quadrance. Its original operational comparison computes a finite floor at which
the same retained residual samples have a uniform positive lower quadrance.
Only that original tail is inverted; the original prepared quotient remains
the numerical output channel.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent Comparison)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)

namespace Reciprocal

/-- A positive-degree reciprocal annihilator, allowing all degree drops in the reversed original coefficient table.

One displayed coordinate factor is retained after reversal. It preserves an
annihilator for every nonzero original root even if the original constant term
vanishes and reversal becomes constant.
-/
@[expose] def polynomial (source : CoefficientPolynomial) : CoefficientPolynomial :=
  Dense.Basic.DensePolynomial.shift 1 (Dense.Gaussian.Reciprocal.reversed source)

/-- The displayed reciprocal annihilator has positive degree for every positive-degree original polynomial. -/
theorem degreePositive {source : CoefficientPolynomial} (positive : 0 < source.natDegree) :
    0 < (polynomial source).natDegree := by
  rw [polynomial, Dense.Gaussian.Reciprocal.shifted_degree _
    (Dense.Gaussian.Reciprocal.reversed_nonzero (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos positive))]
  omega0

private theorem inverse_inverse {point : Canonical} (nonzero : point ≠ 0) : (point⁻¹)⁻¹ = point := by
  apply Field.mul_right_cancel_of_ne (ExplicitField.inv_ne_zero nonzero)
  calc
    _ = point⁻¹ * (point⁻¹)⁻¹ := by ring1
    _ = 1 := ExplicitField.mul_inv_cancel _ (ExplicitField.inv_ne_zero nonzero)
    _ = point * point⁻¹ := (ExplicitField.mul_inv_cancel point nonzero).symm

/-- Finite evaluation of the retained reciprocal annihilator clears the original denominator by its computed power. -/
theorem eval (source : CoefficientPolynomial) {point : Canonical} (nonzero : point ≠ 0) :
    (polynomial source).eval point⁻¹ = point⁻¹ ^ (source.natDegree + 1) * source.eval point := by
  rw [polynomial, Dense.Basic.DensePolynomial.eval_shift,
    Dense.Gaussian.Reciprocal.reversed_identity source _ (ExplicitField.inv_ne_zero nonzero),
    inverse_inverse nonzero, pow_one, pow_succ]
  ring1

private def dropEquivalent (source : GeometricApproximation) (anchor : Nat) :
    Equivalent source.toApproximation (source.drop anchor).toApproximation where
  compare firstStart secondStart target positive := by
    let comparison := (Equivalent.refl source.toApproximation).compare firstStart secondStart target positive
    refine ⟨comparison.leftIndex, comparison.rightIndex, comparison.left_ge, comparison.right_ge, ?_⟩
    intro firstLater secondLater firstOrder secondOrder
    change normSq (source.sample firstLater - source.sample (anchor + secondLater)) < target
    exact comparison.close firstOrder (by omega0)

end Reciprocal

variable {polynomial : CoefficientPolynomial} {channel : CoherentNamed}

set_option genInjectivity false in
/-- One reciprocal computation retaining the original residual, successful denominator preparation and paid exclusion.

The comparison computes the actual tail floor from whole-ball apartness.
The same stored tail and its inverse sample program supply the reciprocal's
quantitative bound and operational comparison to the original prepared output.
-/
structure Reciprocal (original : Residual polynomial channel) (prepared : Prepared channel) where
  /-- The actual original residual certificate consumed by this computation. -/
  input : Residual polynomial channel
  /-- The retained input is the supplied original certificate. -/
  input_eq : input = original
  /-- The actual denominator-cleared reciprocal coefficient polynomial cached from the original polynomial. -/
  annihilator : CoefficientPolynomial
  /-- The cached reciprocal retains the original coefficient reversal and displayed coordinate factor. -/
  annihilator_eq : annihilator = Purelib.Polynomial.Approximation.Gaussian.Residual.Reciprocal.polynomial polynomial
  /-- The actual reciprocal residual scale cached from the original residual and preparation floor. -/
  residualScale : Rational
  /-- The cached scale retains the original degree, apartness floor and exact original input scale. -/
  residualScale_eq : residualScale =
    (prepared.apart.certificate.lowerSq / 4)⁻¹ ^ (polynomial.natDegree + 1) * input.scale
  /-- The same raw source samples are compared to the actual retained apart denominator's sampling trajectory. -/
  comparison : Comparison input.source.toApproximation (Name.Sampling.approximation prepared.denominator.name)
    0 0 (prepared.apart.certificate.lowerSq / 4)
  /-- The actual original source tail beginning at the computed paid index. -/
  tail : GeometricApproximation
  /-- The tail retains the original sample program and computed original index shift. -/
  tail_eq : tail = input.source.drop comparison.leftIndex
  /-- The whole original retained tail obeys the computed positive exclusion floor. -/
  lower : ∀ index, prepared.apart.certificate.lowerSq / 4 ≤ normSq (tail.sample index)
  /-- The actual inverse sample program cached from the same original retained tail. -/
  result : GeometricApproximation
  /-- The cached inverse was computed from the same tail and proved exclusion floor. -/
  result_eq : result =
    tail.inverse (prepared.apart.certificate.lowerSq / 4)
    (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive) lower
  /-- Every actual inverse sample is the inverse of the same retained original tail sample. -/
  result_sample : ∀ index, result.sample index = (tail.sample index)⁻¹
  /-- The actual prepared quotient agrees with the same cached inverse sample program. -/
  equivalent : NamedEquivalent (prepared.quotient (CoherentNamed.Coherence.exact 1)).name
    result.toApproximation.toNamed

constructive_injectivity Reciprocal

namespace Reciprocal

/-- Compute a reciprocal cache using the original numerical residual and an actual successful preparation.

The stored comparison and original denominator apartness compute the entire
exclusion bound. No separate nonzero sample premise or caller-chosen floor is
used to invert the original tail.
-/
def ofPrepared (input : Residual polynomial channel) (prepared : Prepared channel) : Reciprocal input prepared := by
  let comparison := (Equivalent.trans (Equivalent.symm (Equivalent.toNamed_sampling input.source.toApproximation))
    (input.equivalent.symm.trans prepared.equivalent)).compare 0 0
      (prepared.apart.certificate.lowerSq / 4)
      (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive)
  let tail := input.source.drop comparison.leftIndex
  have lower : ∀ index, prepared.apart.certificate.lowerSq / 4 ≤ normSq (tail.sample index) := by
    intro index
    let point := (Name.Sampling.approximation prepared.denominator.name).sample comparison.rightIndex
    have pointLower : prepared.apart.certificate.lowerSq ≤ normSq point :=
      prepared.apart.certificate.lower _ (prepared.denominator.name.process.possible_inside
        (Process.Sampling.witnessAt_possible _ _ _))
    have close := comparison.close (leftLater := comparison.leftIndex + index)
      (rightLater := comparison.rightIndex) (by omega0) (Nat.le_refl _)
    have small : 4 * normSq (tail.sample index - point) ≤ normSq point := by
      have paid := (Fraction.Order.Field.lt_div_iff_pos (by decide : (0 : Rational) < 4)).mp close
      have translated : 4 * normSq (tail.sample index - point) =
          normSq (input.source.toApproximation.sample (comparison.leftIndex + index) -
            (Name.Sampling.approximation prepared.denominator.name).sample comparison.rightIndex) * 4 := by
        change 4 * normSq (tail.sample index - point) = normSq (tail.sample index - point) * 4
        ring1
      exact (translated.trans_le paid.le).trans pointLower
    have divided : prepared.apart.certificate.lowerSq / 4 ≤ normSq point / 4 := by
      apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Rational) < 4)).mpr
      exact pointLower.trans_eq
        (Fraction.Field.div_mul_cancel_of_ne (normSq point) 4 (by decide)).symm
    exact divided.trans (Data.Gaussian.Norm.Bounds.lower_of_tail (tail.sample index) point small)
  let result := tail.inverse (prepared.apart.certificate.lowerSq / 4)
    (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive) lower
  have nonzero : ∀ index, tail.sample index ≠ 0 := by
    intro index zero
    have bound := lower index
    rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at bound
    exact (not_le_of_gt (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive)) bound
  have resultSample : ∀ index, result.sample index = (tail.sample index)⁻¹ := by
    intro index
    change Field.inv (tail.sample index) = (tail.sample index)⁻¹
    exact (Field.inv_eq (tail.sample index)).symm
  let inverseChannel := CoherentNamed.ofApproximation result.toApproximation
  have sourceTail : NamedEquivalent channel.name tail.toApproximation.toNamed :=
    input.equivalent.trans (dropEquivalent input.source comparison.leftIndex).toNamed
  have pointwise : NamedEquivalent (CoherentNamed.mul
      (CoherentNamed.ofApproximation tail.toApproximation) inverseChannel).name
      (GeometricApproximation.exact 1).toApproximation.toNamed :=
    Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise tail.toApproximation
      result.toApproximation (GeometricApproximation.exact 1).toApproximation (by
        intro index
        change 1 = tail.sample index * result.sample index
        rw [resultSample]
        exact (ExplicitField.mul_inv_cancel _ (nonzero index)).symm)
  have exactUnit : NamedEquivalent (GeometricApproximation.exact 1).toApproximation.toNamed
      (CoherentNamed.Coherence.exact 1).name :=
    (Sequence.Equivalence.approximationEquivalentOfSamplesEq (GeometricApproximation.exact 1).toApproximation
      (Sequence.Constant.constantApproximation 1) (fun _ => rfl)).toNamed.trans
        (Sequence.Name.Exact.exact_toConstantNamed 1).symm
  have product : NamedEquivalent (CoherentNamed.mul channel inverseChannel).name
      (CoherentNamed.Coherence.exact 1).name :=
    (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects channel
      (CoherentNamed.ofApproximation tail.toApproximation) inverseChannel inverseChannel
      sourceTail (NamedEquivalent.refl _)).trans (pointwise.trans exactUnit)
  let annihilator := Reciprocal.polynomial polynomial
  let residualScale := (prepared.apart.certificate.lowerSq / 4)⁻¹ ^ (polynomial.natDegree + 1) * input.scale
  exact ⟨input, rfl, annihilator, rfl, residualScale, rfl, comparison, tail, rfl, lower, result, rfl, resultSample,
    prepared.reciprocal_equivalent_of_product inverseChannel product⟩

/-- The cached reciprocal reads the inverse of the original retained sample at the computed paid floor. -/
theorem sample {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) (index : Nat) :
    cache.result.sample index = (original.source.sample (cache.comparison.leftIndex + index))⁻¹ := by
  have originalInput := congrArg (fun input => input.source.sample (cache.comparison.leftIndex + index)) cache.input_eq
  exact (cache.result_sample index).trans
    (congrArg (fun point : Canonical => point⁻¹)
      ((congrArg (fun source : GeometricApproximation => source.sample index) cache.tail_eq).trans originalInput))

/-- Every cached original tail sample is nonzero by the same stored computed exclusion bound. -/
theorem nonzero {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) (index : Nat) : cache.tail.sample index ≠ 0 := by
  intro zero
  have bound := cache.lower index
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at bound
  exact (not_le_of_gt (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive)) bound

/-- The reciprocal polynomial residual scale computed from the stored input scale and prepared exclusion floor. -/
@[expose] def scale {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) : Rational := cache.residualScale

/-- The computed reciprocal scale is nonnegative. -/
theorem scale_nonnegative {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) : 0 ≤ cache.scale := by
  rw [scale, cache.residualScale_eq]
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.pow_nonneg_direct
      (Fraction.Order.Field.inv_pos_direct
        (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive)).le _)
    cache.input.scale_nonnegative

/-- Every same cached inverse sample obeys the reciprocal polynomial's computed geometric residual bound. -/
theorem bound {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) (index : Nat) :
    normSq (cache.annihilator.eval (cache.result.sample index)) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius cache.scale index := by
  rw [cache.annihilator_eq, cache.result_sample, Reciprocal.eval polynomial (cache.nonzero index),
    Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Power.normSq_pow]
  have inverseBound : normSq ((cache.tail.sample index)⁻¹) ≤ (prepared.apart.certificate.lowerSq / 4)⁻¹ := by
    rw [Field.inv_eq, Field.normSq_inv _ (cache.nonzero index)]
    exact Fraction.Order.Field.inv_le_inv_of_pos_direct
      (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive) (cache.lower index)
  have powerBound := Order.Arithmetic.pow_le_pow_direct
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) inverseBound (polynomial.natDegree + 1)
  have inputBound : normSq (polynomial.eval (cache.tail.sample index)) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius cache.input.scale index := by
    have tailSample := congrArg (fun source : GeometricApproximation => source.sample index) cache.tail_eq
    rw [tailSample]
    exact (cache.input.bound (cache.comparison.leftIndex + index)).trans
      (Approximation.Rational.Geometric.Basic.quarterRadius_antitone cache.input.scale_nonnegative (by omega0))
  have multiplied := Order.Arithmetic.mul_le_mul_direct powerBound inputBound
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (Order.Arithmetic.pow_nonneg_direct
      (Fraction.Order.Field.inv_pos_direct
        (Data.Rat.Bounds.Quarter.quarter_pos prepared.apart.certificate.positive)).le _)
  exact multiplied.trans_eq (by
    rw [scale, cache.residualScale_eq, Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1)

/-- Read the retained reciprocal numerical certificate on the actual original prepared quotient channel.

The certificate consumes this cache's actual inverse sample program, original
input bound and computed exclusion scale. It creates no new preparation or
branch selection.
-/
@[expose] def residualCertificate {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) :
    Residual cache.annihilator (prepared.quotient (CoherentNamed.Coherence.exact 1)) :=
  ⟨by rw [cache.annihilator_eq]; exact Reciprocal.degreePositive cache.input.degreePositive,
    cache.result, cache.equivalent,
    cache.scale, cache.scale_nonnegative, cache.bound⟩

/-- The reciprocal certificate consumes the same stored inverse sample program. -/
theorem residualCertificate_source {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) : cache.residualCertificate.source = cache.result := rfl

/-- The reciprocal certificate consumes the same computed exclusion scale. -/
theorem residualCertificate_scale {original : Residual polynomial channel} {prepared : Prepared channel}
    (cache : Reciprocal original prepared) : cache.residualCertificate.scale = cache.scale := rfl

end Reciprocal

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
