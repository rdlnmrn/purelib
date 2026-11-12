module

public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation.Secant
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Antiderivative
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
public import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.List.Reverse
import Purelib.Data.List.Prefix.Take
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Inverse.Subtraction
import Purelib.Data.Gaussian.Power
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Finite reciprocal-coordinate polynomial primitives

The low coefficient block excluding the logarithmic degree is reversed and
padded in the original reciprocal-polynomial owner. Its original finite
antiderivative gives a single-valued primitive at nonzero coordinates.
-/

public section

namespace Purelib.Polynomial.Ascending.Gaussian.Antiderivative

open Purelib
open Purelib.Polynomial
open Purelib.Data.List.Prefix
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Algebra.Field (ExplicitField)

/-- Reverse the finite nonlogarithmic coefficient block into its bounded reciprocal variable.

Order zero has no nonlogarithmic polar terms. Positive order retains the
original low block, including zero and missing entries, through the original
padded reciprocal at degree one less than that order.
-/
@[expose] def reciprocalNumerator (source : CoefficientPolynomial) : Nat → CoefficientPolynomial
  | 0 => Ascending.Gaussian.Basic.zero
  | order + 1 => Dense.Evaluation.fromDense
      (Dense.Gaussian.Reciprocal.padded (Dense.Evaluation.toDense ⟨source.coefficients.take (order + 1)⟩) order)

/-- The retained original low block has the required finite degree for its displayed padded reversal. -/
private theorem reciprocalNumerator_bound (source : CoefficientPolynomial) (order : Nat) :
    (Dense.Evaluation.toDense ⟨source.coefficients.take (order + 1)⟩).natDegree ≤ order := by
  have count := Dense.Basic.DensePolynomial.degreeCount_le_coeffs_length
    (Dense.Evaluation.toDense ⟨source.coefficients.take (order + 1)⟩)
  change (Dense.Evaluation.toDense ⟨source.coefficients.take (order + 1)⟩).degreeCount ≤
    (source.coefficients.take (order + 1)).reverse.length at count
  rw [Data.List.Reverse.length_reverse] at count
  have taken := Take.length_take_le source.coefficients (order + 1)
  change (Dense.Evaluation.toDense ⟨source.coefficients.take (order + 1)⟩).degreeCount - 1 ≤ order
  omega0

/-- Read the actual reciprocal numerator at the guarded inverse of the same original coordinate. -/
theorem reciprocalNumerator_eval (source : CoefficientPolynomial) (order : Nat) (point : Canonical)
    (nonzero : point ≠ 0) :
    Evaluation.eval (reciprocalNumerator source (order + 1)) point⁻¹ =
      point⁻¹ ^ order * Evaluation.eval ⟨source.coefficients.take (order + 1)⟩ point := by
  rw [reciprocalNumerator, Dense.Evaluation.fromDense_eval,
    Dense.Gaussian.Reciprocal.padded_identity _ _ (reciprocalNumerator_bound source order)
      _ (ExplicitField.inv_ne_zero nonzero), Dense.Evaluation.toDense_eval,
    ExplicitField.inverse_inverse_nonzero nonzero]

/-- The same original coefficient block, its retained padded reversal and its retained polynomial antiderivative.

Both cached tables keep the original source and omitted logarithmic degree
as indices. The primitive is computed from that actual retained reversal.
-/
abbrev ReciprocalPrimitive (source : CoefficientPolynomial) (order : Nat) :=
  (reversed : { value : CoefficientPolynomial // value = reciprocalNumerator source order }) ×
    { value : CoefficientPolynomial // value = antiderivative reversed.val }

/-- Build the original padded reciprocal once and its original polynomial antiderivative once. -/
@[expose] def reciprocalPrimitive (source : CoefficientPolynomial) (order : Nat) :
    ReciprocalPrimitive source order :=
  let reversed := reciprocalNumerator source order
  let primitive := antiderivative reversed
  ⟨⟨reversed, rfl⟩, ⟨primitive, rfl⟩⟩

namespace ReciprocalPrimitive

variable {source : CoefficientPolynomial} {order : Nat}

/-- Evaluate the retained nonlogarithmic primitive at the same reciprocal coordinate, with its inversion sign. -/
@[expose] def value (retained : ReciprocalPrimitive source order) (point : Canonical) : Canonical :=
  -Evaluation.eval retained.2.val point⁻¹

/-- The finite first-order coefficient of the same retained primitive at its actual reciprocal coordinate. -/
@[expose] def derivativeValue (retained : ReciprocalPrimitive source order) (point : Canonical) : Canonical :=
  Evaluation.eval retained.1.val point⁻¹ * point⁻¹ ^ 2

/-- The cached primitive's original polynomial derivative consumes the same retained reversal. -/
theorem polynomial_derivative (retained : ReciprocalPrimitive source order) (point : Canonical) :
    (Dense.Gaussian.GCD.derivative (Dense.Evaluation.toDense retained.2.val)).eval point =
      Evaluation.eval retained.1.val point := by
  rw [retained.2.property]
  exact Dense.Antiderivative.toDense_antiderivative_derivative retained.1.val point

/-- The actual reciprocal primitive coefficient equals precisely the original nonlogarithmic polar block.

The original coordinate's nonzero guard permits inversion and power
cancellation. Order zero and a source shorter than the selected block are
included; the omitted next coefficient is the separate logarithmic term.
-/
theorem derivativeValue_eq (retained : ReciprocalPrimitive source order) (point : Canonical)
    (nonzero : point ≠ 0) :
    retained.derivativeValue point =
      Evaluation.eval ⟨source.coefficients.take order⟩ point * (point ^ (order + 1))⁻¹ := by
  rw [derivativeValue, retained.1.property]
  cases order with
  | zero =>
      change (0 : Canonical) * point⁻¹ ^ 2 = 0 * (point ^ (0 + 1))⁻¹
      rw [Basic.zero_mul, Basic.zero_mul]
  | succ order =>
      rw [reciprocalNumerator_eval source order point nonzero,
        ExplicitField.inverse_pow_nonzero nonzero]
      rw [show order + 1 + 1 = order + 2 from rfl, pow_add]
      ring1

/-- The finite reciprocal-coordinate secant kernel of the same actual cached primitive polynomial. -/
@[expose] def kernel (retained : ReciprocalPrimitive source order) (left right : Canonical) : Canonical :=
  Evaluation.polynomialKernel retained.2.val left⁻¹ right⁻¹ * (left⁻¹ * right⁻¹)

/-- The actual reciprocal primitive difference factors without dividing by the difference of its guarded coordinates.

Both nonzero witnesses concern the original displayed coordinates. Their
original inverse-difference identity composes the same cached polynomial's
finite secant kernel, retaining the inversion sign exactly.
-/
theorem sub_factor (retained : ReciprocalPrimitive source order) (left right : Canonical)
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    retained.value left - retained.value right = (left - right) * retained.kernel left right := by
  rw [value, value, kernel]
  have negative : -Evaluation.eval retained.2.val left⁻¹ - -Evaluation.eval retained.2.val right⁻¹ =
      -(Evaluation.eval retained.2.val left⁻¹ - Evaluation.eval retained.2.val right⁻¹) := by ring1
  rw [negative, Evaluation.eval_sub_factor, Inverse.Subtraction.inverse_sub_inverse leftNonzero rightNonzero]
  ring1

/-- The diagonal of the same retained reciprocal kernel is its exact nonlogarithmic polar coefficient. -/
theorem kernel_diagonal (retained : ReciprocalPrimitive source order) (point : Canonical) :
    retained.kernel point point = retained.derivativeValue point := by
  rw [kernel, Evaluation.polynomialKernel_diagonal, retained.polynomial_derivative, derivativeValue, pow_two]

/-- The same source separates into its actual primitive coefficient, original logarithmic scalar and regular tail. -/
theorem split (retained : ReciprocalPrimitive source order) (point : Canonical) (nonzero : point ≠ 0) :
    Evaluation.eval source point * (point ^ (order + 1))⁻¹ =
      retained.derivativeValue point + Coefficient.coefficient source order * point⁻¹ +
        Evaluation.eval (Arithmetic.divideByPower (order + 1) source) point := by
  rw [retained.derivativeValue_eq point nonzero]
  exact Evaluation.eval_polar_split source order point nonzero

/-- The retained primitive increment is the negative exact polynomial integral between the same inverse endpoints. -/
theorem increment (retained : ReciprocalPrimitive source order) (start finish : Canonical) :
    retained.value finish - retained.value start =
      -Integral.definiteIntegral retained.1.val start⁻¹ finish⁻¹ := by
  rw [value, value, retained.2.property, Integral.definiteIntegral]
  ring1

end ReciprocalPrimitive

end Purelib.Polynomial.Ascending.Gaussian.Antiderivative

end
