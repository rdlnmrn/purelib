module
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.NatCast
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Replicate
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.GCD.Extended
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Divisibility

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
import Mathlib.Data.List.Basic

/-!
# Finite rational unit monomials and power differences

Repeated original shifts build unit monomials and their power-minus-one
differences. Retained finite geometric sums and the certified natural Euclidean
recursion supply their explicit polynomial divisibility and Bezout witnesses.
-/

namespace Purelib.Polynomial.Dense.Rational.PowerMinusOne

open Purelib.Polynomial.Dense
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Data.Nat
open Purelib.Algebra
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- The monomial `X^degree`, built by finite repeated shifts.

Every successor shifts the same retained unit polynomial once. The original coefficient program supplies all
intermediate normalized polynomials. -/
@[expose] public def monomialOne : Nat → Divisibility.CoefficientPolynomial
  | 0 => Basic.DensePolynomial.constant 1
  | degree + 1 => Basic.DensePolynomial.shift 1 (monomialOne degree)

/-- The zeroth unit monomial is the constant-one polynomial. -/
@[simp] public theorem monomialOne_zero : monomialOne 0 = Basic.DensePolynomial.constant 1 := rfl

/-- Construct the next unit monomial by shifting its predecessor once. -/
@[simp] public theorem monomialOne_succ (degree : Nat) :
    monomialOne (degree + 1) = Basic.DensePolynomial.shift 1 (monomialOne degree) := rfl

/-- The unit monomial evaluates as the point raised to its displayed degree.

The original degree-zero table evaluates to the field unit. Each retained successor shift contributes one additional
factor of the supplied point. -/
@[simp] public theorem eval_monomialOne (degree : Nat) (point : Fraction.Rational) :
    (monomialOne degree).eval point = point ^ degree := by
  induction degree with
  | zero =>
      rewrite [monomialOne_zero,
        Basic.DensePolynomial.eval_constant, pow_zero]
      exact Eq.refl _
  | succ degree inductionHypothesis =>
      rw [monomialOne_succ, Basic.DensePolynomial.eval_shift, inductionHypothesis, pow_one,
        pow_succ]

/-- Every unit monomial is represented as nonzero.

At the displayed point one, the original monomial evaluates to one. The rational zero and one certificates exclude a
zero normalized table. -/
public theorem monomialOne_nonzero (degree : Nat) :
    (monomialOne degree).isZero = false :=
  Basic.DensePolynomial.isZero_false_of_eval_ne (x := 1) (by
    rw [eval_monomialOne, one_pow]
    exact Fraction.Field.zero_ne_one.symm)

/-- Every recursively constructed unit monomial is already normalized.

The original constant-one base is normalized. Each retained successor shift returns the same normalized polynomial
representation. -/
public theorem monomialOne_normalized : ∀ degree : Nat,
    (monomialOne degree).normalize = monomialOne degree
  | 0 => Basic.DensePolynomial.normalize_constant_of_ne Fraction.Field.zero_ne_one.symm
  | degree + 1 => by rw [monomialOne_succ, Basic.DensePolynomial.normalize_shift]

/-- The descending unit-monomial table is one followed by the displayed number of zeros.

The original unit entry remains the normalized leading coefficient. Every successor appends exactly one retained
rational zero to its descending table. -/
public theorem monomialOne_coeffs : ∀ degree : Nat,
    (monomialOne degree).coeffs = 1 :: List.replicate degree 0
  | 0 => rfl
  | degree + 1 => by
      rw [monomialOne_succ, Basic.DensePolynomial.shift,
        if_neg (fun equal => Bool.noConfusion
          ((monomialOne_nonzero degree).symm.trans equal)),
        monomialOne_normalized, monomialOne_coeffs]
      apply congrArg (List.cons (1 : Fraction.Rational))
      calc
        List.replicate degree (0 : Fraction.Rational) ++ [0] =
            List.replicate degree 0 ++ List.replicate 1 0 := rfl
        _ = List.replicate (degree + 1) 0 :=
          (Replicate.replicate_add degree 1 (0 : Fraction.Rational)).symm

/-- The unit monomial has its displayed natural degree.

The retained table has one unit entry and the displayed number of zeros. Its original natural-degree readback subtracts
the same single leading slot. -/
public theorem monomialOne_natDegree (degree : Nat) :
    (monomialOne degree).natDegree = degree := by
  unfold Basic.DensePolynomial.natDegree Basic.DensePolynomial.degreeCount
  rw [monomialOne_normalized, monomialOne_coeffs]
  rewrite [List.length_cons, Replicate.length_replicate]
  exact Subtraction.add_sub_cancel_right degree 1

/-- Every unit monomial has leading coefficient one.

Normalization retains the original leading unit of the descending table. The degree-zero case uses that same singleton
coefficient. -/
public theorem monomialOne_leadingCoeff (degree : Nat) :
    (monomialOne degree).leadingCoeff = 1 := by
  unfold Basic.DensePolynomial.leadingCoeff
  rw [monomialOne_normalized, monomialOne_coeffs]
  rfl

/-- The finite polynomial `X^degree-1`.

The displayed unit monomial and original constant-one polynomial supply the same retained subtraction operation and
normalized coefficient table. -/
@[expose] public def powerMinusOne (degree : Nat) : (Basic.DensePolynomial Fraction.Rational) :=
  monomialOne degree - Basic.DensePolynomial.constant 1

/-- The displayed power-minus-one polynomial evaluates as the point power minus one.

Scalar evaluation transports the original polynomial subtraction and constant-one readback, preserving the supplied
point and displayed exponent. -/
@[simp] public theorem eval_powerMinusOne (degree : Nat) (point : Fraction.Rational) :
    (powerMinusOne degree).eval point = point ^ degree - 1 := by
  rw [powerMinusOne, Basic.DensePolynomial.eval_sub, eval_monomialOne, Basic.DensePolynomial.eval_constant]

/-- The power-minus-one subtraction returns an already normalized polynomial.

The original dense subtraction normalizes its completed output table. Applying that same normalization again retains the
original result. -/
public theorem powerMinusOne_normalized (degree : Nat) :
    (powerMinusOne degree).normalize = powerMinusOne degree :=
  Basic.DensePolynomial.normalize_sub _ _

/-- A positive-degree power-minus-one polynomial has one, the intervening zeros and negative one as its descending
table.

The original padded subtraction pairs the leading unit with zero and the final zero with negative one. Its interior
retained zero block keeps the displayed length. -/
public theorem powerMinusOne_coeffs (degree : Nat) :
    (powerMinusOne (degree + 1)).coeffs =
      (1 : Fraction.Rational) :: List.replicate degree 0 ++ [(-1 : Fraction.Rational)] := by
  unfold powerMinusOne
  change (Basic.DensePolynomial.add (monomialOne (degree + 1))
    (Basic.DensePolynomial.neg (Basic.DensePolynomial.constant 1))).coeffs = _
  have negConstant : Basic.DensePolynomial.neg (Basic.DensePolynomial.constant (1 : Fraction.Rational)) = ⟨[-1]⟩ := by
    apply Basic.DensePolynomial.ext
    change (-Basic.DensePolynomial.constant (1 : Fraction.Rational) : Divisibility.CoefficientPolynomial).coeffs = [-1]
    rw [Basic.DensePolynomial.neg_coeffs, Basic.DensePolynomial.normalize_constant_of_ne
      Fraction.Field.zero_ne_one.symm]
    rfl
  rw [negConstant]
  unfold Basic.DensePolynomial.add
  rw [monomialOne_coeffs]
  unfold Basic.DensePolynomial.padLeft
  simp only [List.length_cons, Replicate.length_replicate, List.length_nil,
    Nat.zero_add]
  have maximum : max (degree + 1 + 1) 1 = degree + 1 + 1 := by
    exact Nat.le_antisymm
      (Order.max_le (Nat.le_refl _) (Nat.succ_le_succ (Nat.zero_le _)))
      (Order.le_max_left _ _)
  rw [maximum]
  simp only [Nat.sub_self, List.replicate_zero, List.nil_append]
  have padding : degree + 1 + 1 - 1 = degree + 1 :=
    Subtraction.add_sub_cancel_right (degree + 1) 1
  rw [padding, List.replicate_succ, List.cons_append,
    List.zipWith_cons_cons, add_zero]
  rw [Basic.DensePolynomial.normalize_coeffs]
  change
    ((1 : Fraction.Rational) :: List.zipWith (· + ·)
      ((0 : Fraction.Rational) :: List.replicate degree 0)
      (List.replicate degree 0 ++ [(-1 : Fraction.Rational)])).dropWhile
        (· = 0) = _
  rewrite [DropWhile.cons_of_false
    (fun value : Fraction.Rational => decide (value = 0)) 1 _
    (decide_eq_false Fraction.Field.zero_ne_one.symm)]
  apply congrArg (List.cons 1)
  have zeroList :
      (0 : Fraction.Rational) :: List.replicate degree 0 =
        List.replicate
          (List.replicate degree (0 : Fraction.Rational) ++ [-1]).length 0 := by
    simp only [Append.length_append, Replicate.length_replicate, List.length_cons,
      List.length_nil]
    rw [List.replicate_succ]
  rw [zeroList, Basic.DensePolynomial.zipWith_replicate_zero_add]
  rfl

/-- A positive-degree power-minus-one polynomial is represented as nonzero.

The positive degree supplies a normalized table whose original first entry is one. That displayed entry makes its
original emptiness test false. -/
public theorem powerMinusOne_nonzero (degree : Nat) :
    (powerMinusOne (degree + 1)).isZero = false := by
  unfold Basic.DensePolynomial.isZero
  rw [powerMinusOne_normalized, powerMinusOne_coeffs]
  rfl

/-- A positive-degree power-minus-one polynomial has its displayed natural degree.

The original normalized table retains its leading and constant entries around the displayed zero block. Subtracting one
from that exact slot count gives the stated successor degree. -/
public theorem powerMinusOne_natDegree (degree : Nat) :
    (powerMinusOne (degree + 1)).natDegree = degree + 1 := by
  unfold Basic.DensePolynomial.natDegree Basic.DensePolynomial.degreeCount
  rw [powerMinusOne_normalized, powerMinusOne_coeffs]
  rewrite [Append.length_append, List.length_cons, Replicate.length_replicate]
  exact Subtraction.add_sub_cancel_right (degree + 1) 1

/-- A positive-degree power-minus-one polynomial is monic.

The positive degree keeps the original unit monomial entry first after subtraction and normalization, so its retained
leading-coefficient readback is one. -/
public theorem powerMinusOne_leadingCoeff (degree : Nat) :
    (powerMinusOne (degree + 1)).leadingCoeff = 1 := by
  unfold Basic.DensePolynomial.leadingCoeff
  rw [powerMinusOne_normalized, powerMinusOne_coeffs]
  rfl

/-- The derivative of a unit monomial evaluates as its degree times the preceding point power.

The degree-zero case is handled by the zero scalar factor and natural subtraction. -/
public theorem eval_derivative_monomialOne : ∀ degree : Nat,
    ∀ point : Fraction.Rational,
    (Derivative.derivative (monomialOne degree)).eval point =
      (degree : Fraction.Rational) * point ^ (degree - 1)
  | 0, point => by
      change (0 : Divisibility.CoefficientPolynomial).eval point = (0 : Fraction.Rational) * point ^ (0 - 1)
      rewrite [Basic.DensePolynomial.eval_zero, zero_mul]
      exact Eq.refl _
  | degree + 1, point => by
      rw [monomialOne_succ,
        Derivative.eval_derivative_shift_one,
        eval_derivative_monomialOne degree point, eval_monomialOne]
      rewrite [NatCast.add, Nat.cast_one]
      cases degree with
      | zero =>
          change (0 : Fraction.Rational) * point ^ 0 * point + point ^ 0 =
            (0 + 1) * point ^ 0
          rewrite [pow_zero]
          ring0
      | succ degree =>
          rewrite [Subtraction.add_sub_cancel_right degree 1,
            Subtraction.add_sub_cancel_right (degree + 1) 1, pow_succ]
          ring0

/-- Differentiating a positive-degree power-minus-one polynomial removes the constant term and gives the expected
monomial value.

The original derivative subtraction removes the constant-one derivative. Its retained unit monomial derivative supplies
the same preceding point power. -/
public theorem eval_derivative_powerMinusOne (degree : Nat) (point : Fraction.Rational) :
    (Derivative.derivative
      (powerMinusOne (degree + 1))).eval point =
      (degree + 1 : Nat) * point ^ degree := by
  rw [powerMinusOne, Derivative.eval_derivative_sub,
    eval_derivative_monomialOne]
  change ((degree + 1 : Nat) : Fraction.Rational) * point ^ (degree + 1 - 1) - 0 = _
  rw [Subtraction.add_sub_cancel_right]
  ring0

/-- `X^n-1` is square-free in the constructive rationals, with the explicit
Bezout certificate `-(X^n-1) + (X/n)(X^n-1)' = 1`.

The successor exponent has a nonzero rational cast. Its original reciprocal, negative constant and scaled unit monomial
supply the displayed finite Bezout witnesses. -/
public theorem powerMinusOne_evalCoprime_derivative (degree : Nat) :
    Divisibility.EvalCoprime (powerMinusOne (degree + 1))
      (Derivative.derivative
        (powerMinusOne (degree + 1))) := open Purelib.Algebra.Field in by
  let reciprocal : Fraction.Rational := ((degree + 1 : Nat) : Fraction.Rational)⁻¹
  refine ⟨Basic.DensePolynomial.constant (-1), Basic.DensePolynomial.scale reciprocal (monomialOne 1), ?_⟩
  intro point
  simp only [Basic.DensePolynomial.eval_constant, Basic.DensePolynomial.eval_scale, eval_monomialOne,
    eval_powerMinusOne, eval_derivative_powerMinusOne, pow_one]
  have degreeNonzero : (((degree + 1 : Nat) : Fraction.Rational)) ≠ 0 := by
    intro zero
    have naturalZero := Fraction.Cast.Compatibility.natCast_injective_direct
      (zero.trans (Nat.cast_zero).symm)
    exact Nat.noConfusion naturalZero
  have inverseCancel : reciprocal * (((degree + 1 : Nat) : Fraction.Rational)) = 1 := by
    rw [mul_comm]
    exact ExplicitField.mul_inv_cancel _ degreeNonzero
  symm
  change
    -1 * (point ^ (degree + 1) - 1) +
        (reciprocal * point) *
          (((degree + 1 : Nat) : Fraction.Rational) * point ^ degree) = 1
  calc
    -1 * (point ^ (degree + 1) - 1) +
        (reciprocal * point) *
          (((degree + 1 : Nat) : Fraction.Rational) * point ^ degree) =
        1 + (reciprocal * (((degree + 1 : Nat) : Fraction.Rational)) - 1) *
          (point ^ degree * point) := by
            rw [pow_succ]
            ring0
    _ = 1 := by
      rw [inverseCancel]
      ring0

/-- Finite geometric quotient in steps of one displayed exponent.

Each original successor adds the unit monomial at its count times the displayed step. The same original quotient prefix
is retained in the recursive input. -/
@[expose] public def geometricQuotient (step : Nat) : Nat → Divisibility.CoefficientPolynomial
  | 0 => 0
  | count + 1 => geometricQuotient step count + monomialOne (count * step)

/-- The geometric quotient with no terms is the empty zero polynomial. -/
@[simp] public theorem geometricQuotient_zero (step : Nat) :
    geometricQuotient step 0 = 0 := rfl

/-- Extend a geometric quotient by the next unit monomial at a multiple of the step exponent. -/
@[simp] public theorem geometricQuotient_succ (step count : Nat) :
    geometricQuotient step (count + 1) =
      geometricQuotient step count + monomialOne (count * step) := rfl

/-- The finite geometric quotient times `point^step - 1` evaluates to `point^(count * step) - 1`.

The retained last monomial cancels the preceding endpoint after multiplication by the same step-power difference.
Structural recursion identifies both original finite endpoints. -/
public theorem eval_geometricQuotient (step : Nat) : ∀ count : Nat,
    ∀ point : Fraction.Rational,
    (geometricQuotient step count).eval point * (point ^ step - 1) =
      point ^ (count * step) - 1
  | 0, point => by
      simp only [geometricQuotient_zero, Basic.DensePolynomial.eval_zero, zero_mul, pow_zero]
      ring0
  | count + 1, point => by
      rw [geometricQuotient_succ, Basic.DensePolynomial.eval_add, eval_monomialOne,
        add_mul, eval_geometricQuotient step count point]
      rw [Multiplication.right_distrib, Nat.one_mul, pow_add]
      ring0

/-- Natural exponent divisibility gives displayed divisibility of the corresponding power-minus-one polynomials.

A literal finite geometric sum supplies the quotient; the identity also covers zero exponents. -/
public theorem powerMinusOne_evalDvd_of_dvd {smaller larger : Nat}
    (divides : smaller ∣ larger) :
    Divisibility.EvalDvd (powerMinusOne smaller) (powerMinusOne larger) := by
  rcases divides with ⟨quotient, rfl⟩
  refine ⟨geometricQuotient smaller quotient, ?_⟩
  intro point
  simp only [eval_powerMinusOne, Basic.DensePolynomial.eval_mul]
  calc
    point ^ (smaller * quotient) - 1 =
        point ^ (quotient * smaller) - 1 := by rw [Nat.mul_comm]
    _ =
        (geometricQuotient smaller quotient).eval point *
          (point ^ smaller - 1) :=
      (eval_geometricQuotient smaller quotient point).symm
    _ = (point ^ smaller - 1) *
        (geometricQuotient smaller quotient).eval point := by ring0

/-- Subtracting exponents is literal Euclidean division for the special
polynomials `X^n-1`.

The supplied natural bound reconstructs the larger exponent from its retained difference and smaller exponent. The same
unit monomial supplies the literal scalar quotient. -/
public theorem powerMinusOne_subtraction_identity
    {smaller larger : Nat} (ordered : smaller ≤ larger) :
    Divisibility.EvalEq (powerMinusOne larger)
      (monomialOne (larger - smaller) * powerMinusOne smaller +
        powerMinusOne (larger - smaller)) := by
  intro point
  simp only [eval_powerMinusOne, Basic.DensePolynomial.eval_add, Basic.DensePolynomial.eval_mul, eval_monomialOne]
  have powerSplit : point ^ larger =
      point ^ (larger - smaller) * point ^ smaller := by
    calc
      point ^ larger = point ^ ((larger - smaller) + smaller) := by
        apply congrArg (fun exponent : Nat => point ^ exponent)
        exact ((Nat.add_comm (larger - smaller) smaller).trans
          (Subtraction.add_sub_of_le ordered)).symm
      _ = point ^ (larger - smaller) * point ^ smaller := pow_add _ _ _
  rw [powerSplit]
  ring0

/-- The finite subtraction algorithm gives explicit Bezout coefficients for
`X^m-1` and `X^n-1`.  Its exponent is the result of the project's certified,
structurally recursive Euclidean computation.

Positive original exponents reduce by the same retained subtraction branches. The supplied fuel bound justifies
recursion and preserves each original polynomial coefficient witness. -/
private theorem powerMinusOne_evalBezout_gcdAux :
    ∀ fuel first second : Nat, first + second < fuel →
      ∃ left right : Divisibility.CoefficientPolynomial, ∀ point : Fraction.Rational,
        (powerMinusOne (GCD.Extended.compute first second).gcd).eval point =
          left.eval point * (powerMinusOne first).eval point +
            right.eval point * (powerMinusOne second).eval point
  | 0, first, second, enoughFuel =>
      False.elim ((Nat.not_lt_zero _ ) enoughFuel)
  | fuel + 1, first, second, enoughFuel => by
      by_cases firstZero : first = 0
      · subst first
        refine ⟨0, Basic.DensePolynomial.constant 1, ?_⟩
        intro point
        rw [GCD.Extended.compute_gcd_zero_left]
        rewrite [Basic.DensePolynomial.eval_zero, zero_mul,
          Basic.DensePolynomial.eval_constant, one_mul, zero_add]
        exact Eq.refl _
      · by_cases secondZero : second = 0
        · subst second
          refine ⟨Basic.DensePolynomial.constant 1, 0, ?_⟩
          intro point
          rw [GCD.Extended.compute_gcd_zero_right]
          rewrite [Basic.DensePolynomial.eval_constant, one_mul,
            Basic.DensePolynomial.eval_zero, zero_mul, add_zero]
          exact Eq.refl _
        · by_cases ordered : first ≤ second
          · rcases powerMinusOne_evalBezout_gcdAux fuel first
                (second - first) (by
                  rewrite [Subtraction.add_sub_of_le ordered]
                  exact Nat.lt_of_lt_of_le
                    (Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero firstZero))
                    (Nat.le_of_lt_succ enoughFuel)) with
              ⟨left, right, identity⟩
            refine ⟨left - right * monomialOne (second - first), right, ?_⟩
            intro point
            have split := powerMinusOne_subtraction_identity ordered point
            simp only [Basic.DensePolynomial.eval_add, Basic.DensePolynomial.eval_mul] at split
            have gcdStable :=
              GCD.Extended.compute_gcd_sub_right ordered
            simp only [Basic.DensePolynomial.eval_sub, Basic.DensePolynomial.eval_mul]
            calc
              (powerMinusOne
                  (GCD.Extended.compute first second).gcd).eval point =
                  (powerMinusOne
                    (GCD.Extended.compute first
                      (second - first)).gcd).eval point := by
                    rw [gcdStable]
              _ = left.eval point * (powerMinusOne first).eval point +
                    right.eval point *
                      (powerMinusOne (second - first)).eval point :=
                identity point
              _ = (left.eval point - right.eval point *
                      (monomialOne (second - first)).eval point) *
                    (powerMinusOne first).eval point +
                  right.eval point * (powerMinusOne second).eval point := by
                    rw [split]
                    ring0
          · have reverse : second ≤ first := Nat.le_of_not_ge ordered
            rcases powerMinusOne_evalBezout_gcdAux fuel (first - second)
                second (by
                  rewrite [Nat.add_comm (first - second) second,
                    Subtraction.add_sub_of_le reverse]
                  exact Nat.lt_of_lt_of_le
                    (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero secondZero))
                    (Nat.le_of_lt_succ enoughFuel)) with ⟨left, right, identity⟩
            refine ⟨left, right - left * monomialOne (first - second), ?_⟩
            intro point
            have split := powerMinusOne_subtraction_identity reverse point
            simp only [Basic.DensePolynomial.eval_add, Basic.DensePolynomial.eval_mul] at split
            have gcdStable :=
              GCD.Extended.compute_gcd_sub_left reverse
            simp only [Basic.DensePolynomial.eval_sub, Basic.DensePolynomial.eval_mul]
            calc
              (powerMinusOne
                  (GCD.Extended.compute first second).gcd).eval point =
                  (powerMinusOne
                    (GCD.Extended.compute (first - second)
                      second).gcd).eval point := by
                    rw [gcdStable]
              _ = left.eval point *
                    (powerMinusOne (first - second)).eval point +
                  right.eval point * (powerMinusOne second).eval point :=
                identity point
              _ = left.eval point * (powerMinusOne first).eval point +
                  (right.eval point - left.eval point *
                      (monomialOne (first - second)).eval point) *
                    (powerMinusOne second).eval point := by
                      rw [split]
                      ring0

/-- Public finite Bezout certificate for the two displayed exponents.

Fuel one beyond the sum of the original exponents supplies the original subtraction recursion. Its retained two
polynomial coefficients certify the computed greatest-common-divisor exponent. -/
public theorem powerMinusOne_evalBezout_gcd (first second : Nat) :
    ∃ left right : Divisibility.CoefficientPolynomial, ∀ point : Fraction.Rational,
      (powerMinusOne (GCD.Extended.compute first second).gcd).eval point =
        left.eval point * (powerMinusOne first).eval point +
          right.eval point * (powerMinusOne second).eval point :=
  powerMinusOne_evalBezout_gcdAux (first + second + 1) first second (by omega0)
end Purelib.Polynomial.Dense.Rational.PowerMinusOne
