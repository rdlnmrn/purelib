module

public import Purelib.Polynomial.RecursiveDense.Rational.Basic
import Purelib.Polynomial.RecursiveDense.Rational.Avoidance
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Bool.Decide
import Mathlib.Data.Int.Cast.Defs

/-!
# Integer coefficients and characteristic transfer

The original recursively dense rational polynomial retains every scalar
coefficient. A denominator-one certificate identifies its integer coefficients,
which can be evaluated in any supplied explicit field. A rational identity on
a nonzero polynomial locus therefore transfers to every characteristic.
-/

public section

namespace Purelib.Polynomial.RecursiveDense.Rational.Basic

universe u

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Ring
open Purelib.Data.Bool
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast (representative_mul_den)
open Purelib.Polynomial.RecursiveDense.Rational

/-- A coordinate tuple over the supplied scalar carrier, with exactly the indexed number of variables. -/
@[expose] def PointOver (K : Type u) : Nat → Type u
  | 0 => PUnit
  | arity + 1 => PointOver K arity × K

/-- Read the same rational coordinates in the original rational point type. -/
@[expose] def PointOver.toRationalPoint : {arity : Nat} → PointOver Rational arity → Point arity
  | 0, _ => ()
  | _ + 1, (inner, outer) => (PointOver.toRationalPoint inner, outer)

mutual

  /-- Every original scalar coefficient has denominator one. -/
  @[expose] def Expression.Integral : {arity : Nat} → Expression arity → Prop
    | _, .constant coefficient => coefficient.den = 1
    | _, .next coefficients => coefficients.Integral

  /-- Every polynomial in the original finite coefficient sequence has integer coefficients. -/
  @[expose] def Coefficients.Integral {arity : Nat} : Coefficients arity → Prop
    | .nil => True
    | .cons coefficient remaining => coefficient.Integral ∧ remaining.Integral

end

mutual

  /-- Evaluate the certified integer coefficients of the original polynomial in the supplied field.

The original scalar numerator is cast into the field. The retained denominator-one certificate identifies that integer
with the original rational coefficient; the same ordered Horner traversal evaluates the original coefficient sequence.
-/
  @[expose] def Expression.evalIntegral {K : Type*} [ExplicitField K] :
      {arity : Nat} → (polynomial : Expression arity) → polynomial.Integral → PointOver K arity → K
    | _, .constant coefficient, _, _ => (coefficient.num : K)
    | _, .next coefficients, integral, (inner, outer) => coefficients.evalIntegral integral inner outer 0

  /-- Evaluate a certified integer coefficient sequence by the original accumulated Horner traversal. -/
  @[expose] def Coefficients.evalIntegral {K : Type*} [ExplicitField K] {arity : Nat} :
      (coefficients : Coefficients arity) → coefficients.Integral → PointOver K arity → K → K → K
    | .nil, _, _, _, value => value
    | .cons coefficient remaining, integral, inner, outer, value =>
        remaining.evalIntegral integral.2 inner outer (value * outer + coefficient.evalIntegral integral.1 inner)

end

mutual

  /-- Integer-coefficient evaluation over the rationals agrees with the original rational polynomial evaluation. -/
  theorem Expression.evalIntegral_rational :
      ∀ {arity : Nat} (polynomial : Expression arity) (integral : polynomial.Integral)
        (point : PointOver Rational arity),
      polynomial.evalIntegral integral point = polynomial.eval point.toRationalPoint
    | _, .constant coefficient, integral, _ => by
        have value := representative_mul_den coefficient
        change coefficient * (coefficient.den : Rational) = (coefficient.num : Rational) at value
        change coefficient.den = 1 at integral
        rw [integral] at value
        change coefficient * 1 = (coefficient.num : Rational) at value
        rw [mul_one] at value
        exact value.symm
    | _, .next coefficients, integral, (inner, outer) =>
        Coefficients.evalIntegral_rational coefficients integral inner outer 0

  /-- Integer-coefficient Horner evaluation over the rationals preserves the original point and accumulator. -/
  theorem Coefficients.evalIntegral_rational {arity : Nat} :
      ∀ (coefficients : Coefficients arity) (integral : coefficients.Integral)
        (inner : PointOver Rational arity) (outer value : Rational),
      coefficients.evalIntegral integral inner outer value = coefficients.eval inner.toRationalPoint outer value
    | .nil, _, _, _, _ => rfl
    | .cons coefficient remaining, integral, inner, outer, value => by
        change remaining.evalIntegral integral.2 inner outer
          (value * outer + coefficient.evalIntegral integral.1 inner) =
          remaining.eval inner.toRationalPoint outer (value * outer + coefficient.eval inner.toRationalPoint)
        rw [Expression.evalIntegral_rational coefficient integral.1 inner]
        exact Coefficients.evalIntegral_rational remaining integral.2 inner outer _

end

mutual

  /-- A polynomial whose original rational coefficient test is zero evaluates to zero in every supplied field. -/
  theorem Expression.evalIntegral_eq_zero {K : Type*} [ExplicitField K] :
      ∀ {arity : Nat} (polynomial : Expression arity) (integral : polynomial.Integral),
      polynomial.isZero = true → ∀ point : PointOver K arity, polynomial.evalIntegral integral point = 0
    | _, .constant coefficient, integral, zero, _ => by
        have coefficientZero : coefficient = 0 := of_decide_eq_true zero
        cases coefficientZero
        change ((0 : Int) : K) = 0
        exact IntCast.cast_zero
    | _, .next coefficients, integral, zero, (inner, outer) =>
        Coefficients.evalIntegral_eq_zero coefficients integral zero inner outer

  /-- A zero original coefficient sequence evaluates to zero from the zero Horner accumulator in every supplied field.
-/
  theorem Coefficients.evalIntegral_eq_zero {K : Type*} [ExplicitField K] {arity : Nat} :
      ∀ (coefficients : Coefficients arity) (integral : coefficients.Integral),
      coefficients.isZero = true → ∀ (inner : PointOver K arity) (outer : K),
        coefficients.evalIntegral integral inner outer 0 = 0
    | .nil, _, _, _, _ => rfl
    | .cons coefficient remaining, integral, zero, inner, outer => by
        have both := (Decide.and_true_iff _ _).mp zero
        change remaining.evalIntegral integral.2 inner outer
          (0 * outer + coefficient.evalIntegral integral.1 inner) = 0
        rw [Expression.evalIntegral_eq_zero coefficient integral.1 both.1 inner, zero_mul, zero_add]
        exact Coefficients.evalIntegral_eq_zero remaining integral.2 both.2 inner outer

end

/-- An original integer-coefficient polynomial vanishing on a nonzero rational polynomial locus vanishes over every
supplied explicit field, in every characteristic.

Finite rational avoidance proves that every original scalar coefficient is zero. Its retained integer coefficient
therefore casts to zero in the target field, and the original finite Horner traversal proves the transferred identity.
-/
theorem Expression.transfer_integral_identity {arity : Nat} (polynomial locus : Expression arity)
    (integral : polynomial.Integral) (locusNonzero : locus.isZero = false)
    (vanishes : ∀ point : Point arity, locus.eval point ≠ 0 → polynomial.eval point = 0)
    {K : Type*} [ExplicitField K] (point : PointOver K arity) : polynomial.evalIntegral integral point = 0 :=
  polynomial.evalIntegral_eq_zero integral
    (Avoidance.isZero_of_vanishes_where_second_nonzero polynomial locus locusNonzero vanishes) point

end Purelib.Polynomial.RecursiveDense.Rational.Basic
