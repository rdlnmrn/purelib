import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.FinitePolynomial

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace CCL.DividedDifference

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := CCL.FinitePolynomial.Polynomial

open RFAP.ConstructiveGaussian.Gaussian
open CCL.FinitePolynomial

/-- The expanded finite kernel for `x^degree-y^degree`. -/
def powerKernel (x y : Gaussian) : Nat → Gaussian
  | 0 => 0
  | degree + 1 => x ^ degree + y * powerKernel x y degree

@[simp] theorem powerKernel_zero (x y : Gaussian) :
    powerKernel x y 0 = 0 := rfl

@[simp] theorem powerKernel_succ (x y : Gaussian) (degree : Nat) :
    powerKernel x y (degree + 1) =
      x ^ degree + y * powerKernel x y degree := rfl

/-- The finite geometric factorization, including the diagonal case where
the right side is zero without performing a division by zero. -/
theorem power_sub_power_factor (x y : Gaussian) : ∀ degree,
    x ^ degree - y ^ degree = (x - y) * powerKernel x y degree
  | 0 => by
      simp only [pow_zero, sub_self, powerKernel_zero, mul_zero]
  | degree + 1 => by
      rw [pow_succ, pow_succ, powerKernel_succ]
      calc
        x ^ degree * x - y ^ degree * y =
            (x - y) * x ^ degree + y * (x ^ degree - y ^ degree) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1
        _ = (x - y) * x ^ degree +
            y * ((x - y) * powerKernel x y degree) := by
          rw [power_sub_power_factor x y degree]
        _ = (x - y) * (x ^ degree + y * powerKernel x y degree) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1

/-- The familiar finite derivative of one nonnegative power. -/
def powerDerivative (x : Gaussian) : Nat → Gaussian
  | 0 => 0
  | degree + 1 =>
      CCL.FiniteExp.scale (degree + 1 : Coordinate) (x ^ degree)

private theorem powerDerivative_succ_identity (x : Gaussian) : ∀ degree,
    powerDerivative x (degree + 1) =
      x ^ degree + x * powerDerivative x degree
  | 0 => by
      simp only [powerDerivative, pow_zero, mul_zero,
        add_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, one_re, one_im] <;> ring1
  | degree + 1 => by
      simp only [powerDerivative, pow_succ]
      rw [Nat.cast_add, Nat.cast_one]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re,
          mul_im] <;> ring1

/-- Putting the two inputs of the expanded kernel equal gives the power
derivative directly. -/
theorem powerKernel_diagonal (x : Gaussian) : ∀ degree,
    powerKernel x x degree = powerDerivative x degree
  | 0 => rfl
  | degree + 1 => by
      rw [powerKernel_succ, powerKernel_diagonal,
        powerDerivative_succ_identity]

/-! ## Dense finite polynomials -/

/-- Secant kernel for a low-to-high finite coefficient list.  The constant
coefficient disappears structurally, while the tail is evaluated by the
same finite Horner program as the original polynomial. -/
def coefficientsKernel (x y : Gaussian) : List Coordinate → Gaussian
  | [] => 0
  | _constant :: remaining =>
      evalCoefficients x remaining + y * coefficientsKernel x y remaining

def polynomialKernel (polynomial : Polynomial) (x y : Gaussian) : Gaussian :=
  coefficientsKernel x y polynomial.coefficients

theorem evalCoefficients_sub_factor (x y : Gaussian) : ∀ coefficients,
    evalCoefficients x coefficients - evalCoefficients y coefficients =
      (x - y) * coefficientsKernel x y coefficients
  | [] => by
      simp only [evalCoefficients_nil, sub_self, coefficientsKernel, mul_zero]
  | coefficient :: remaining => by
      rw [evalCoefficients_cons, evalCoefficients_cons, coefficientsKernel]
      calc
        (CCL.FiniteExp.scale coefficient 1 +
              x * evalCoefficients x remaining) -
            (CCL.FiniteExp.scale coefficient 1 +
              y * evalCoefficients y remaining) =
            (x - y) * evalCoefficients x remaining +
              y * (evalCoefficients x remaining -
                evalCoefficients y remaining) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1
        _ = (x - y) * evalCoefficients x remaining +
            y * ((x - y) * coefficientsKernel x y remaining) := by
          rw [evalCoefficients_sub_factor x y remaining]
        _ = (x - y) *
            (evalCoefficients x remaining +
              y * coefficientsKernel x y remaining) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1

/-- Every finite polynomial difference is factored by the displayed input
difference using the constructed kernel. -/
theorem eval_sub_factor (polynomial : Polynomial) (x y : Gaussian) :
    eval polynomial x - eval polynomial y =
      (x - y) * polynomialKernel polynomial x y :=
  evalCoefficients_sub_factor x y polynomial.coefficients

private theorem derivativeFrom_eval_identity (x : Gaussian) :
    ∀ (factor : Nat) (coefficients : List Coordinate),
      evalCoefficients x (derivativeFrom factor coefficients) =
        CCL.FiniteExp.scale (factor : Coordinate)
            (evalCoefficients x coefficients) +
          x * coefficientsKernel x x coefficients
  | factor, [] => by
      simp only [derivativeFrom, evalCoefficients_nil, coefficientsKernel,
        mul_zero, add_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, zero_re, zero_im] <;> ring1
  | factor, coefficient :: remaining => by
      rw [derivativeFrom, evalCoefficients_cons, evalCoefficients_cons,
        coefficientsKernel,
        derivativeFrom_eval_identity x (factor + 1) remaining]
      rw [Nat.cast_add, Nat.cast_one]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re,
          mul_im, one_re, one_im] <;> ring1

/-- The diagonal of the polynomial secant kernel is exactly the evaluation
of the already executable formal derivative. -/
theorem polynomialKernel_diagonal (polynomial : Polynomial) (x : Gaussian) :
    polynomialKernel polynomial x x = eval (derivative polynomial) x := by
  cases polynomial with
  | mk coefficients =>
    cases coefficients with
    | nil => rfl
    | cons constant remaining =>
      change coefficientsKernel x x (constant :: remaining) =
        evalCoefficients x (derivativeFrom 1 remaining)
      rw [coefficientsKernel,
        derivativeFrom_eval_identity x 1 remaining]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re,
          mul_im, Nat.cast_one] <;> ring1

/-! ## Exact compositional secant identities -/

/-- The displayed product-rule kernel factors a product difference. -/
theorem product_kernel_factor
    (x y fX fY gX gY deltaF deltaG : Gaussian)
    (fFactor : fX - fY = (x - y) * deltaF)
    (gFactor : gX - gY = (x - y) * deltaG) :
    fX * gX - fY * gY =
      (x - y) * (deltaF * gX + fY * deltaG) := by
  calc
    fX * gX - fY * gY =
        (fX - fY) * gX + fY * (gX - gY) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
        ring1
    _ = ((x - y) * deltaF) * gX +
        fY * ((x - y) * deltaG) := by rw [fFactor, gFactor]
    _ = (x - y) * (deltaF * gX + fY * deltaG) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
        ring1

/-- The displayed chain-rule kernel factors a composite difference. -/
theorem composition_kernel_factor
    (x y innerX innerY outerX outerY deltaInner deltaOuter : Gaussian)
    (innerFactor : innerX - innerY = (x - y) * deltaInner)
    (outerFactor : outerX - outerY =
      (innerX - innerY) * deltaOuter) :
    outerX - outerY = (x - y) * (deltaInner * deltaOuter) := by
  calc
    outerX - outerY = (innerX - innerY) * deltaOuter := outerFactor
    _ = ((x - y) * deltaInner) * deltaOuter := by rw [innerFactor]
    _ = (x - y) * (deltaInner * deltaOuter) :=
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _

/-- Difference of two displayed reciprocals, proved from finite inverse
cancellation certificates. -/
theorem inverse_sub_inverse {left right : Gaussian}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left⁻¹ - right⁻¹ =
      -(left - right) * (left⁻¹ * right⁻¹) := by
  calc
    left⁻¹ - right⁻¹ = left⁻¹ * 1 - 1 * right⁻¹ := by
      rw [mul_one, one_mul]
    _ = left⁻¹ * (right * right⁻¹) -
        (left * left⁻¹) * right⁻¹ := by
      simp only [RFAP.ExplicitField.mul_inv_cancel right rightNonzero,
        RFAP.ExplicitField.mul_inv_cancel left leftNonzero, mul_one, one_mul]
    _ = -(left - right) * (left⁻¹ * right⁻¹) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im, mul_re, mul_im] <;>
        ring1

/-- The reciprocal-rule kernel factors a reciprocal difference without
testing equality of an opaque value. -/
theorem reciprocal_kernel_factor
    (x y fX fY deltaF : Gaussian)
    (fXNonzero : fX ≠ 0) (fYNonzero : fY ≠ 0)
    (factor : fX - fY = (x - y) * deltaF) :
    fX⁻¹ - fY⁻¹ =
      (x - y) * (-(deltaF * (fX⁻¹ * fY⁻¹))) := by
  calc
    fX⁻¹ - fY⁻¹ =
        -(fX - fY) * (fX⁻¹ * fY⁻¹) :=
      inverse_sub_inverse fXNonzero fYNonzero
    _ = (-((x - y) * deltaF)) * (fX⁻¹ * fY⁻¹) := by
      rw [factor]
    _ = (x - y) * (-(deltaF * (fX⁻¹ * fY⁻¹))) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im, mul_re, mul_im] <;>
        ring1

/-! ## Signed powers and finite Laurent term lists -/

/-- A finite exponent syntax.  `negative predecessor` represents
`-(predecessor+1)`, so there is no duplicate representation of zero. -/
inductive Exponent where
  | nonnegative : Nat → Exponent
  | negative : Nat → Exponent
deriving DecidableEq

def signedPower (x : Gaussian) : Exponent → Gaussian
  | .nonnegative degree => x ^ degree
  | .negative predecessor => (x ^ (predecessor + 1))⁻¹

def signedPowerKernel (x y : Gaussian) : Exponent → Gaussian
  | .nonnegative degree => powerKernel x y degree
  | .negative predecessor =>
      -(powerKernel x y (predecessor + 1) *
        ((x ^ (predecessor + 1))⁻¹ * (y ^ (predecessor + 1))⁻¹))

def signedPowerDerivative (x : Gaussian) : Exponent → Gaussian
  | .nonnegative degree => powerDerivative x degree
  | .negative predecessor =>
      CCL.FiniteExp.scale
        (-((predecessor + 1 : Nat) : Coordinate))
        ((x ^ (predecessor + 2))⁻¹)

theorem signedPower_sub_factor (x y : Gaussian)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) : ∀ exponent,
    signedPower x exponent - signedPower y exponent =
      (x - y) * signedPowerKernel x y exponent
  | .nonnegative degree => power_sub_power_factor x y degree
  | .negative predecessor => by
      let degree := predecessor + 1
      have xPowerNonzero :=
        RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct x xNonzero degree
      have yPowerNonzero :=
        RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct y yNonzero degree
      rw [signedPower, signedPower, signedPowerKernel]
      calc
        (x ^ degree)⁻¹ - (y ^ degree)⁻¹ =
            -(x ^ degree - y ^ degree) *
              ((x ^ degree)⁻¹ * (y ^ degree)⁻¹) :=
          inverse_sub_inverse xPowerNonzero yPowerNonzero
        _ = (-((x - y) * powerKernel x y degree)) *
              ((x ^ degree)⁻¹ * (y ^ degree)⁻¹) := by
          rw [power_sub_power_factor x y degree]
        _ = (x - y) *
            (-(powerKernel x y degree *
              ((x ^ degree)⁻¹ * (y ^ degree)⁻¹))) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, neg_re, neg_im, mul_re, mul_im] <;>
            ring1

private theorem negative_power_diagonal_algebra (x : Gaussian)
    (xNonzero : x ≠ 0) (predecessor : Nat) :
    x ^ predecessor *
        ((x ^ (predecessor + 1))⁻¹ *
          (x ^ (predecessor + 1))⁻¹) =
      (x ^ (predecessor + 2))⁻¹ := by
  have higherNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct x xNonzero
      (predecessor + 2)
  have currentNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct x xNonzero
      (predecessor + 1)
  have currentInvMul :
      (x ^ (predecessor + 1))⁻¹ * x ^ (predecessor + 1) = 1 := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
      RFAP.ConstructiveGaussian.Gaussian.inv_mul
        (x ^ (predecessor + 1)) currentNonzero
  have higherInvMul :
      (x ^ (predecessor + 2))⁻¹ * x ^ (predecessor + 2) = 1 := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
      RFAP.ConstructiveGaussian.Gaussian.inv_mul
        (x ^ (predecessor + 2)) higherNonzero
  have currentPower :
      x ^ (predecessor + 1) = x ^ predecessor * x := by
    exact pow_succ x predecessor
  have higherPower :
      x ^ (predecessor + 2) = x ^ (predecessor + 1) * x := by
    rw [show predecessor + 2 = (predecessor + 1) + 1 by ring1]
    exact pow_succ x (predecessor + 1)
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne higherNonzero
  calc
    (x ^ predecessor *
          ((x ^ (predecessor + 1))⁻¹ *
            (x ^ (predecessor + 1))⁻¹)) *
        x ^ (predecessor + 2) =
      (x ^ (predecessor + 1) * (x ^ (predecessor + 1))⁻¹) *
        ((x ^ (predecessor + 1))⁻¹ *
          x ^ (predecessor + 1)) := by
        rw [higherPower, currentPower]
        ring1
    _ = 1 := by
      simp only [RFAP.ExplicitField.mul_inv_cancel _ currentNonzero,
        currentInvMul, RFAP.ConstructiveGaussian.Gaussian.one_mul]
    _ = (x ^ (predecessor + 2))⁻¹ *
        x ^ (predecessor + 2) := by
      exact higherInvMul.symm

private theorem scale_mul_product (factor : Coordinate)
    (left right : Gaussian) :
    CCL.FiniteExp.scale factor (left * right) =
      CCL.FiniteExp.scale factor left * right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

/-- The negative-power kernel also collapses on the diagonal to the familiar
`-m*x^(-m-1)` formula, under the necessary displayed nonzero certificate. -/
theorem signedPowerKernel_diagonal (x : Gaussian) (xNonzero : x ≠ 0) :
    ∀ exponent,
      signedPowerKernel x x exponent = signedPowerDerivative x exponent
  | .nonnegative degree => powerKernel_diagonal x degree
  | .negative predecessor => by
      rw [signedPowerKernel, signedPowerDerivative,
        powerKernel_diagonal, powerDerivative]
      rw [← scale_mul_product,
        negative_power_diagonal_algebra x xNonzero predecessor]
      rw [Nat.cast_add, Nat.cast_one]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, neg_re, neg_im] <;> ring1

/-- One displayed Laurent term with a rational coefficient. -/
structure LaurentTerm where
  coefficient : Coordinate
  exponent : Exponent
deriving DecidableEq

def LaurentTerm.eval (term : LaurentTerm) (x : Gaussian) : Gaussian :=
  CCL.FiniteExp.scale term.coefficient
    (signedPower x term.exponent)

def LaurentTerm.kernel (term : LaurentTerm) (x y : Gaussian) : Gaussian :=
  CCL.FiniteExp.scale term.coefficient
    (signedPowerKernel x y term.exponent)

def LaurentTerm.derivativeEval (term : LaurentTerm) (x : Gaussian) : Gaussian :=
  CCL.FiniteExp.scale term.coefficient
    (signedPowerDerivative x term.exponent)

/-- A Laurent polynomial is finite syntax, not a function represented by an
infinite set of input-output pairs.  Repeated exponents are harmless. -/
structure LaurentPolynomial where
  terms : List LaurentTerm
deriving DecidableEq

def sumGaussian : List Gaussian → Gaussian
  | [] => 0
  | value :: remaining => value + sumGaussian remaining

def LaurentPolynomial.eval (polynomial : LaurentPolynomial)
    (x : Gaussian) : Gaussian :=
  sumGaussian (polynomial.terms.map fun term => term.eval x)

def LaurentPolynomial.kernel (polynomial : LaurentPolynomial)
    (x y : Gaussian) : Gaussian :=
  sumGaussian (polynomial.terms.map fun term => term.kernel x y)

def LaurentPolynomial.derivativeEval (polynomial : LaurentPolynomial)
    (x : Gaussian) : Gaussian :=
  sumGaussian (polynomial.terms.map fun term => term.derivativeEval x)

private theorem scale_sub (factor : Coordinate) (left right : Gaussian) :
    CCL.FiniteExp.scale factor (left - right) =
      CCL.FiniteExp.scale factor left -
        CCL.FiniteExp.scale factor right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, sub_re, sub_im] <;> ring1

private theorem scale_mul_right (factor : Coordinate)
    (left right : Gaussian) :
    CCL.FiniteExp.scale factor (left * right) =
      left * CCL.FiniteExp.scale factor right := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

theorem LaurentTerm.eval_sub_factor (term : LaurentTerm) (x y : Gaussian)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) :
    term.eval x - term.eval y = (x - y) * term.kernel x y := by
  simp only [LaurentTerm.eval, LaurentTerm.kernel]
  rw [← scale_sub]
  rw [signedPower_sub_factor x y xNonzero yNonzero term.exponent]
  exact scale_mul_right term.coefficient (x - y)
    (signedPowerKernel x y term.exponent)

theorem LaurentTerm.kernel_diagonal (term : LaurentTerm) (x : Gaussian)
    (xNonzero : x ≠ 0) :
    term.kernel x x = term.derivativeEval x := by
  simp only [LaurentTerm.kernel, LaurentTerm.derivativeEval,
    signedPowerKernel_diagonal x xNonzero term.exponent]

private theorem sumGaussian_sub_factor (x y : Gaussian)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) :
    ∀ terms : List LaurentTerm,
      sumGaussian (terms.map fun term => term.eval x) -
          sumGaussian (terms.map fun term => term.eval y) =
        (x - y) *
          sumGaussian (terms.map fun term => term.kernel x y)
  | [] => by simp only [List.map_nil, sumGaussian, sub_self, mul_zero]
  | term :: remaining => by
      rw [List.map_cons, List.map_cons, List.map_cons,
        sumGaussian, sumGaussian, sumGaussian]
      calc
        (term.eval x +
              sumGaussian (remaining.map fun next => next.eval x)) -
            (term.eval y +
              sumGaussian (remaining.map fun next => next.eval y)) =
            (term.eval x - term.eval y) +
              (sumGaussian (remaining.map fun next => next.eval x) -
                sumGaussian (remaining.map fun next => next.eval y)) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im] <;>
            ring1
        _ = (x - y) * term.kernel x y +
            (x - y) *
              sumGaussian (remaining.map fun next => next.kernel x y) := by
          rw [LaurentTerm.eval_sub_factor term x y xNonzero yNonzero,
            sumGaussian_sub_factor x y xNonzero yNonzero remaining]
        _ = (x - y) *
            (term.kernel x y +
              sumGaussian (remaining.map fun next => next.kernel x y)) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
            ring1

/-- Linear extension of the signed-power factorization to every displayed
finite Laurent term list. -/
theorem LaurentPolynomial.eval_sub_factor
    (polynomial : LaurentPolynomial) (x y : Gaussian)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) :
    polynomial.eval x - polynomial.eval y =
      (x - y) * polynomial.kernel x y :=
  sumGaussian_sub_factor x y xNonzero yNonzero polynomial.terms

private theorem sumGaussian_kernel_diagonal (x : Gaussian)
    (xNonzero : x ≠ 0) : ∀ terms : List LaurentTerm,
    sumGaussian (terms.map fun term => term.kernel x x) =
      sumGaussian (terms.map fun term => term.derivativeEval x)
  | [] => rfl
  | term :: remaining => by
      rw [List.map_cons, List.map_cons, sumGaussian, sumGaussian,
        LaurentTerm.kernel_diagonal term x xNonzero,
        sumGaussian_kernel_diagonal x xNonzero remaining]

/-- Diagonal evaluation of a finite Laurent secant kernel is its executable
termwise derivative, including all negative exponents. -/
theorem LaurentPolynomial.kernel_diagonal
    (polynomial : LaurentPolynomial) (x : Gaussian) (xNonzero : x ≠ 0) :
    polynomial.kernel x x = polynomial.derivativeEval x :=
  sumGaussian_kernel_diagonal x xNonzero polynomial.terms

/-! ## Rational polynomial expressions -/

/-- A finite rational expression in one variable.  Evaluation at a supplied
point requires a separate nonzero-denominator certificate in every theorem
which uses field cancellation. -/
structure RationalPolynomial where
  numerator : Polynomial
  denominator : Polynomial

namespace RationalPolynomial

def eval (expression : RationalPolynomial) (x : Gaussian) : Gaussian :=
  CCL.FinitePolynomial.eval expression.numerator x /
    CCL.FinitePolynomial.eval expression.denominator x

def kernel (expression : RationalPolynomial) (x y : Gaussian) : Gaussian :=
  let numeratorY :=
    CCL.FinitePolynomial.eval expression.numerator y
  let denominatorX :=
    CCL.FinitePolynomial.eval expression.denominator x
  let denominatorY :=
    CCL.FinitePolynomial.eval expression.denominator y
  (polynomialKernel expression.numerator x y * denominatorY -
      numeratorY * polynomialKernel expression.denominator x y) /
    (denominatorX * denominatorY)

def derivativeEval (expression : RationalPolynomial) (x : Gaussian) :
    Gaussian :=
  let numerator :=
    CCL.FinitePolynomial.eval expression.numerator x
  let denominator :=
    CCL.FinitePolynomial.eval expression.denominator x
  let numeratorDerivative :=
    CCL.FinitePolynomial.eval
      (CCL.FinitePolynomial.derivative expression.numerator) x
  let denominatorDerivative :=
    CCL.FinitePolynomial.eval
      (CCL.FinitePolynomial.derivative expression.denominator) x
  (numeratorDerivative * denominator - numerator * denominatorDerivative) /
    (denominator * denominator)

private theorem div_mul_right_product (numerator left right : Gaussian)
    (leftNonzero : left ≠ 0) :
    numerator / left * (left * right) = numerator * right := by
  rw [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    numerator * left⁻¹ * (left * right) =
        numerator * (left⁻¹ * left) * right := by ring1
    _ = numerator * 1 * right := by
      rw [RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel left leftNonzero]
    _ = numerator * right := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]

private theorem div_sub_div (leftNumerator leftDenominator
    rightNumerator rightDenominator : Gaussian)
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0) :
    leftNumerator / leftDenominator -
        rightNumerator / rightDenominator =
      (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (leftDenominator * rightDenominator) := by
  have productNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      leftNonzero rightNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    productNonzero
  calc
    (leftNumerator / leftDenominator -
          rightNumerator / rightDenominator) *
        (leftDenominator * rightDenominator) =
      leftNumerator / leftDenominator *
          (leftDenominator * rightDenominator) -
        rightNumerator / rightDenominator *
          (leftDenominator * rightDenominator) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = leftNumerator * rightDenominator -
        rightNumerator * leftDenominator := by
      have rightProduct :
          rightNumerator / rightDenominator *
              (leftDenominator * rightDenominator) =
            rightNumerator * leftDenominator := by
        calc
          rightNumerator / rightDenominator *
              (leftDenominator * rightDenominator) =
              rightNumerator / rightDenominator *
                (rightDenominator * leftDenominator) := by
            ring1
          _ = rightNumerator * leftDenominator :=
            div_mul_right_product rightNumerator rightDenominator
              leftDenominator rightNonzero
      rw [div_mul_right_product leftNumerator leftDenominator rightDenominator
          leftNonzero, rightProduct]
    _ = ((leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (leftDenominator * rightDenominator)) *
          (leftDenominator * rightDenominator) := by
      exact (RFAP.ExplicitField.div_mul_cancel _ productNonzero).symm

/-- The finite quotient-rule kernel factors the difference of two rational
expression evaluations. -/
theorem eval_sub_factor (expression : RationalPolynomial) (x y : Gaussian)
    (xDenominatorNonzero :
      CCL.FinitePolynomial.eval expression.denominator x ≠ 0)
    (yDenominatorNonzero :
      CCL.FinitePolynomial.eval expression.denominator y ≠ 0) :
    expression.eval x - expression.eval y =
      (x - y) * expression.kernel x y := by
  let numeratorX :=
    CCL.FinitePolynomial.eval expression.numerator x
  let numeratorY :=
    CCL.FinitePolynomial.eval expression.numerator y
  let denominatorX :=
    CCL.FinitePolynomial.eval expression.denominator x
  let denominatorY :=
    CCL.FinitePolynomial.eval expression.denominator y
  let numeratorKernel := polynomialKernel expression.numerator x y
  let denominatorKernel := polynomialKernel expression.denominator x y
  have numeratorFactor : numeratorX - numeratorY =
      (x - y) * numeratorKernel :=
    CCL.DividedDifference.eval_sub_factor
      expression.numerator x y
  have denominatorFactor : denominatorX - denominatorY =
      (x - y) * denominatorKernel :=
    CCL.DividedDifference.eval_sub_factor
      expression.denominator x y
  rw [RationalPolynomial.eval, RationalPolynomial.eval,
    RationalPolynomial.kernel]
  change numeratorX / denominatorX - numeratorY / denominatorY = _
  rw [div_sub_div numeratorX denominatorX numeratorY denominatorY
    xDenominatorNonzero yDenominatorNonzero]
  have crossNumerator :
      numeratorX * denominatorY - numeratorY * denominatorX =
        (numeratorX - numeratorY) * denominatorY -
          numeratorY * (denominatorX - denominatorY) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
  have factoredNumerator :
      numeratorX * denominatorY - numeratorY * denominatorX =
      (x - y) *
        (numeratorKernel * denominatorY -
          numeratorY * denominatorKernel) := by
    calc
      numeratorX * denominatorY - numeratorY * denominatorX =
          (numeratorX - numeratorY) * denominatorY -
            numeratorY * (denominatorX - denominatorY) := crossNumerator
      _ = ((x - y) * numeratorKernel) * denominatorY -
            numeratorY * ((x - y) * denominatorKernel) := by
        rw [numeratorFactor, denominatorFactor]
      _ = (x - y) *
          (numeratorKernel * denominatorY -
            numeratorY * denominatorKernel) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
  rw [factoredNumerator, RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv]
  exact RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _

/-- On the diagonal, the rational secant kernel is exactly the executable
quotient-rule derivative. -/
theorem kernel_diagonal (expression : RationalPolynomial) (x : Gaussian) :
    expression.kernel x x = expression.derivativeEval x := by
  rw [RationalPolynomial.kernel, RationalPolynomial.derivativeEval,
    polynomialKernel_diagonal, polynomialKernel_diagonal]

end RationalPolynomial

end CCL.DividedDifference
