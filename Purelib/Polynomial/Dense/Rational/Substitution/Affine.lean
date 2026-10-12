module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Bool.Decide
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Division
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Finite affine substitution of rational dense polynomials

Horner substitution is normalized executable coefficient data.  Its degree
bound follows from the finite fold.  A displayed inverse affine substitution
then proves exact degree preservation, using only the bounded evaluation grid
of `Purelib.Polynomial.Dense.Rational.Extensionality`, not an infinite-field argument.
-/

namespace Purelib.Polynomial.Dense.Rational.Substitution.Affine

open Purelib.Data.Rat Purelib.Polynomial
open Purelib.Data.List.DropWhile
open Purelib.Data.Nat.Order

public section
/-- Rational dense polynomials in descending coefficient order.

The exact alias retains the original finite coefficient list and executable
normalization, without changing the represented polynomial's owner. -/
abbrev CoefficientPolynomial := Dense.Basic.DensePolynomial Fraction.Rational

/-- The dense linear polynomial with coefficients `[slope, origin]`.

It evaluates to the affine expression `origin + slope * point`, including zero slopes. -/
@[expose] def linear (origin slope : Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) := ⟨[slope,
  origin]⟩

/-- Evaluate the displayed linear polynomial as its affine expression. -/
theorem linear_eval (origin slope point : Fraction.Rational) :
    (linear origin slope).eval point = origin + slope * point := by
  change (0 * point + slope) * point + origin = _
  ring1

/-- An affine polynomial has normalized coefficient count at most two.

The original displayed coefficients are the slope and origin. Removing their
leading zero prefix cannot increase this two-entry list's length. -/
private theorem linear_degreeCount_le (origin slope : Fraction.Rational) :
    (linear origin slope).degreeCount ≤ 2 := by
  change ([slope, origin].dropWhile (· = 0)).length ≤ 2
  exact Purelib.Data.List.DropWhile.length_le (fun value : Fraction.Rational => decide (value = 0))
    [slope, origin]

/-- One polynomial Horner step for affine substitution.

Multiply the accumulator by the displayed linear polynomial and add the normalized constant coefficient. -/
@[expose] def step (origin slope : Fraction.Rational) (accumulator : CoefficientPolynomial) (coefficient :
  Fraction.Rational) :
  (Dense.Basic.DensePolynomial Fraction.Rational) :=
  accumulator * linear origin slope + (Dense.Basic.DensePolynomial.constant coefficient).normalize

/-- One affine Horner step increases normalized coefficient count by at most one. -/
private theorem step_degreeCount_le (origin slope : Fraction.Rational)
    (accumulator : CoefficientPolynomial) (coefficient : Fraction.Rational) :
    (step origin slope accumulator coefficient).degreeCount ≤ accumulator.degreeCount + 1 := by
  have product := Dense.Basic.DensePolynomial.degreeCount_mul_le accumulator (linear origin slope)
  have lineBound := linear_degreeCount_le origin slope
  have addition := Dense.Basic.DensePolynomial.degreeCount_add_le_of_normalized
    (Dense.Basic.DensePolynomial.normalize_mul accumulator (linear origin slope))
    (Dense.Basic.DensePolynomial.normalize_normalize (Dense.Basic.DensePolynomial.constant coefficient))
  have constantBound := Dense.Basic.DensePolynomial.degreeCount_constant_le_one coefficient
  rw [Dense.Basic.DensePolynomial.degreeCount_normalize] at addition
  apply addition.trans
  rw [Purelib.Data.Nat.Order.max_eq_natMax]
  exact Purelib.Data.Nat.Order.max_le (by omega) (by omega)

/-- An affine Horner fold preserves a normalized starting accumulator. -/
private theorem fold_normalized (origin slope : Fraction.Rational) :
    ∀ (coefficients : List Fraction.Rational) (accumulator : CoefficientPolynomial),
      accumulator.normalize = accumulator →
        (coefficients.foldl (step origin slope) accumulator).normalize =
          coefficients.foldl (step origin slope) accumulator
  | [], _, normalized => normalized
  | coefficient :: remaining, accumulator, _ =>
      fold_normalized origin slope remaining (step origin slope accumulator coefficient)
        (Dense.Basic.DensePolynomial.normalize_add _ _)

/-- Bound the coefficient count after an affine Horner fold.

The final count is at most the initial accumulator count plus the number of processed coefficients. -/
private theorem fold_degreeCount_le (origin slope : Fraction.Rational) :
    ∀ (coefficients : List Fraction.Rational) (accumulator : CoefficientPolynomial),
      (coefficients.foldl (step origin slope) accumulator).degreeCount ≤
        accumulator.degreeCount + coefficients.length
  | [], _ => Nat.le_refl _
  | coefficient :: remaining, accumulator => by
      have stepBound := step_degreeCount_le origin slope accumulator coefficient
      have restBound := fold_degreeCount_le origin slope remaining (step origin slope accumulator coefficient)
      change (remaining.foldl (step origin slope) (step origin slope accumulator coefficient)).degreeCount ≤ _
      simp only [List.length_cons]
      omega

/-- Polynomial affine Horner folding agrees with scalar Horner evaluation.

The scalar evaluation uses the affine image of the point and the value of the initial polynomial accumulator. -/
private theorem fold_eval (origin slope point : Fraction.Rational) :
    ∀ (coefficients : List Fraction.Rational) (accumulator : CoefficientPolynomial),
      (coefficients.foldl (step origin slope) accumulator).eval point =
        coefficients.foldl (fun value coefficient => value * (origin + slope * point) + coefficient)
          (accumulator.eval point)
  | [], _ => rfl
  | coefficient :: remaining, accumulator => by
      rw [List.foldl_cons, fold_eval]
      have computed : (step origin slope accumulator coefficient).eval point =
          accumulator.eval point * (origin + slope * point) + coefficient := by
        rw [step, Dense.Basic.DensePolynomial.eval_add,
          Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_normalize,
          Dense.Basic.DensePolynomial.eval_constant, linear_eval]
      change remaining.foldl
        (fun value coefficient => value * (origin + slope * point) + coefficient)
        ((step origin slope accumulator coefficient).eval point) = _
      exact congrArg
        (remaining.foldl (fun value coefficient => value * (origin + slope * point) + coefficient))
        computed

/-- Canonical finite affine substitution, accepting nonnormalized inputs. -/
@[expose] def subst (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) :
  (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  polynomial.normalize.coeffs.foldl (step origin slope) 0

/-- Affine substitution returns a normalized coefficient table. -/
theorem subst_normalized (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) :
    (subst polynomial origin slope).normalize = subst polynomial origin slope :=
  fold_normalized origin slope polynomial.normalize.coeffs 0 rfl

/-- Normalizing the input does not change affine substitution. -/
theorem subst_normalize (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) :
    subst polynomial.normalize origin slope = subst polynomial origin slope := by
  unfold subst
  rw [Dense.Basic.DensePolynomial.normalize_normalize]

/-- Evaluate an affine-substituted polynomial at a rational point.

Its value is the original polynomial evaluated at the affine image of that point. -/
theorem subst_eval (polynomial : CoefficientPolynomial) (origin slope point : Fraction.Rational) :
    (subst polynomial origin slope).eval point = polynomial.eval (origin + slope * point) := by
  rw [subst, fold_eval]
  change polynomial.normalize.eval (origin + slope * point) = _
  exact Dense.Basic.DensePolynomial.eval_normalize _ _

/-- Affine substitution never increases normalized coefficient count. -/
theorem subst_degreeCount_le (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) :
    (subst polynomial origin slope).degreeCount ≤ polynomial.degreeCount := by
  have bound := fold_degreeCount_le origin slope polynomial.normalize.coeffs 0
  change (subst polynomial origin slope).degreeCount ≤ 0 + polynomial.degreeCount at bound
  exact (Nat.zero_add polynomial.degreeCount) ▸ bound

/-- Undo affine substitution with its displayed inverse parameters.

For nonzero slope, substituting origin `-origin / slope` and reciprocal slope into the result recovers the normalized
original polynomial. -/
theorem subst_inverse (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) (nonzero : slope ≠ 0) :
    subst (subst polynomial origin slope) (-origin / slope) slope⁻¹ = polynomial.normalize := open Purelib.Algebra.Field
      in by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (subst_normalized _ _ _) (Dense.Basic.DensePolynomial.normalize_normalize _)
  intro point
  rw [subst_eval, subst_eval, Dense.Basic.DensePolynomial.eval_normalize]
  have inverse : origin + slope * (-origin / slope + slope⁻¹ * point) = point := by
    calc
      _ = origin + (-origin + point) * (slope * slope⁻¹) := by
        rw [ExplicitField.div_eq_mul_inv]
        ring1
      _ = point := by rw [Fraction.Field.mul_inv_cancel slope nonzero]; ring1
  rw [inverse]

/-- Nonzero slope preserves degree, including the zero polynomial. -/
theorem subst_degreeCount (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) (nonzero : slope ≠ 0)
  :
    (subst polynomial origin slope).degreeCount = polynomial.degreeCount := by
  apply Nat.le_antisymm (subst_degreeCount_le polynomial origin slope)
  have reverse := subst_degreeCount_le (subst polynomial origin slope) (-origin / slope) slope⁻¹
  rw [subst_inverse polynomial origin slope nonzero, Dense.Basic.DensePolynomial.degreeCount_normalize] at reverse
  exact reverse

/-- A nonzero affine slope preserves the polynomial zero test. -/
theorem subst_isZero (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) (nonzero : slope ≠ 0) :
    (subst polynomial origin slope).isZero = polynomial.isZero := by
  cases zero : polynomial.isZero with
  | true =>
      apply Dense.Basic.DensePolynomial.isZero_true_of_degreeCount_eq_zero
      rw [subst_degreeCount polynomial origin slope nonzero, Dense.Basic.DensePolynomial.degreeCount_eq_zero_of_isZero
        zero]
  | false =>
      apply Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true
      intro transformedZero
      have degreeZero := Dense.Basic.DensePolynomial.degreeCount_eq_zero_of_isZero transformedZero
      rw [subst_degreeCount polynomial origin slope nonzero] at degreeZero
      have positive := Dense.Basic.DensePolynomial.degreeCount_pos_of_isZero_false zero
      omega

/-- Affine substitution commutes with polynomial negation. -/
theorem subst_neg (polynomial : CoefficientPolynomial) (origin slope : Fraction.Rational) :
    subst (-polynomial) origin slope = -(subst polynomial origin slope) := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (subst_normalized _ _ _) (Dense.Basic.DensePolynomial.normalize_neg _)
  intro point
  rw [subst_eval, Dense.Basic.DensePolynomial.eval_neg, Dense.Basic.DensePolynomial.eval_neg, subst_eval]

/-- Invertible affine substitution commutes with the actual finite
long-division remainder, not just with its evaluation specification. -/
theorem subst_remainder (dividend divisor : CoefficientPolynomial) (origin slope : Fraction.Rational) (nonzero : slope
  ≠ 0) :
    (Dense.Basic.DensePolynomial.divMod (subst dividend origin slope) (subst divisor origin slope)).remainder =
      subst (Dense.Basic.DensePolynomial.divMod dividend divisor).remainder origin slope := by
  cases zero : divisor.isZero with
  | true =>
      have transformedZero : (subst divisor origin slope).isZero = true := by
        rw [subst_isZero divisor origin slope nonzero, zero]
      rw [Dense.Rational.Division.remainder_of_divisor_zero _ _ transformedZero,
        Dense.Rational.Division.remainder_of_divisor_zero _ _ zero,
        subst_normalize, subst_normalized]
  | false =>
      symm
      apply Dense.Rational.Division.remainder_unique
        (subst dividend origin slope) (subst divisor origin slope)
        (subst (Dense.Basic.DensePolynomial.divMod dividend divisor).quotient origin slope)
        (subst (Dense.Basic.DensePolynomial.divMod dividend divisor).remainder origin slope)
      · rw [subst_isZero divisor origin slope nonzero, zero]
      · exact subst_normalized _ _ _
      · rw [subst_degreeCount _ origin slope nonzero, subst_degreeCount _ origin slope nonzero]
        exact Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt dividend divisor zero
      · intro point
        rw [subst_eval, subst_eval, subst_eval, subst_eval]
        exact Dense.Basic.DensePolynomial.divMod_eval_equation dividend divisor _

end

end Purelib.Polynomial.Dense.Rational.Substitution.Affine
