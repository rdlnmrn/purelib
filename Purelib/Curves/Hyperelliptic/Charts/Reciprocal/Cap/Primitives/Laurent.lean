module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients.Primitive
import Purelib.Curves.Hyperelliptic.Charts.Infinity
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # The retained principal polynomial in the actual cap parameter -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

variable {genus : Nat} {curve : HyperellipticCurve genus} {jet : InfinityCoefficients.Jet curve}
  {polynomial : Dense.Basic.DensePolynomial Canonical} {scale : Canonical}

/-- The logarithmic pivot degree of the actual cap parameter's principal polynomial.

The original coordinate degree and original genus determine its denominator
power. The subtraction is exact because the cap degree is one or two.
-/
@[expose] def parameterOrder (curve : HyperellipticCurve genus) : Nat := degree curve * (genus + 1) - 1

/-- Substitute the actual cap parameter in the supplied retained principal polynomial once.

An even-degree curve keeps the literal supplied C table. An odd-degree curve
uses the original square-substitution traversal and exact Jacobian factor
two. No numerator product or inverse-root jet is recomputed.
-/
@[expose] def parameterPolynomial (retained : jet.Principal polynomial scale) : CoefficientPolynomial :=
  match curve.degreeShape with
  | .odd _ => Arithmetic.scale 2 ⟨Infinity.evenCoefficients retained.val.coefficients⟩
  | .even _ => retained.val

/-- The retained pivot plus one is exactly the original parameter denominator power. -/
theorem parameterOrder_succ (curve : HyperellipticCurve genus) :
    parameterOrder curve + 1 = degree curve * (genus + 1) := by
  cases shape : curve.degreeShape <;>
    simp only [parameterOrder, degree, HyperellipticReciprocal.originOrder, shape] <;> omega0

/-- Evaluation uses the actual original coordinate power and its original Jacobian factor. -/
theorem parameterPolynomial_eval (retained : jet.Principal polynomial scale) (parameter : Canonical) :
    Evaluation.eval (parameterPolynomial retained) parameter =
      (degree curve : Canonical) * Evaluation.eval retained.val (point curve parameter) := by
  cases shape : curve.degreeShape with
  | odd =>
      rewrite [parameterPolynomial, shape, Evaluation.eval_scale]
      change 2 * Evaluation.evalCoeffs (Infinity.evenCoefficients retained.val.coefficients) parameter = _
      rewrite [Infinity.evalCoeffs_evenCoefficients, Infinity.evenHorner_eq_evalCoeffs]
      simp only [point, degree, HyperellipticReciprocal.originOrder, shape]
      rfl
  | even =>
      rewrite [parameterPolynomial, shape]
      simp only [point, degree, HyperellipticReciprocal.originOrder, shape]
      change Evaluation.eval retained.val parameter = (1 : Canonical) * Evaluation.eval retained.val (parameter ^ 1)
      rewrite [pow_one, Data.Gaussian.Basic.one_mul]
      rfl

/-- The actual ramified parameter has zero logarithmic pivot, including genus zero.

The supplied whole table is the original retained parameter substitution.
Its defining readback transports the finite parity calculation; omission
retains the literal original canonical table.
-/
theorem parameterPolynomial_odd_pivot (retained : jet.Principal polynomial scale)
    (ramified : HyperellipticReciprocal.originOrder curve = 1)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained } :=
      ⟨parameterPolynomial retained, rfl⟩) :
    Coefficient.coefficient table.val (parameterOrder curve) = 0 := by
  rewrite [table.property]
  cases shape : curve.degreeShape with
  | odd =>
      rewrite [parameterPolynomial, shape]
      have order : parameterOrder curve = 2 * genus + 1 := by
        simp only [parameterOrder, degree, HyperellipticReciprocal.originOrder, shape]
        omega0
      rewrite [order, Arithmetic.coefficient_scale]
      change 2 * Coefficient.coefficientList (Infinity.evenCoefficients retained.val.coefficients) (2 * genus + 1) = 0
      rewrite [Infinity.evenCoefficients_odd, Data.Gaussian.Basic.mul_zero]
      rfl
  | even =>
      rewrite [HyperellipticReciprocal.originOrder, shape] at ramified
      cases ramified

/-- The actual unramified parameter keeps the original retained C pivot literally.

The supplied whole table retains the same original principal product.
Its exact readback reduces the unramified substitution to the original
pivot; omission retains the literal original canonical table.
-/
theorem parameterPolynomial_even_pivot (retained : jet.Principal polynomial scale)
    (regular : HyperellipticReciprocal.originOrder curve = 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained } :=
      ⟨parameterPolynomial retained, rfl⟩) :
    Coefficient.coefficient table.val (parameterOrder curve) =
      Coefficient.coefficient retained.val genus := by
  rewrite [table.property]
  cases shape : curve.degreeShape with
  | odd =>
      rewrite [HyperellipticReciprocal.originOrder, shape] at regular
      cases regular
  | even =>
      rewrite [parameterPolynomial, shape]
      have order : parameterOrder curve = genus := by
        simp only [parameterOrder, degree, HyperellipticReciprocal.originOrder, shape]
        omega0
      rewrite [order]
      rfl

/-- The same stored parameter polynomial splits into its actual primitive, logarithmic pivot and literal regular tail.

The supplied original reciprocal primitive is indexed by the retained
substituted table. The nonzero witness concerns the actual cap parameter;
no branch choice, integral comparison or physical residue is assumed.
-/
theorem parameter_split (retained : jet.Principal polynomial scale)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained })
    (primitive : Antiderivative.ReciprocalPrimitive table.val (parameterOrder curve))
    (parameter : Canonical) (nonzero : parameter ≠ 0) :
    ((degree curve : Canonical) * Evaluation.eval retained.val (point curve parameter)) *
        (parameter ^ (degree curve * (genus + 1)))⁻¹ =
      primitive.derivativeValue parameter +
        Coefficient.coefficient table.val (parameterOrder curve) * parameter⁻¹ +
          Evaluation.eval (Arithmetic.divideByPower (parameterOrder curve + 1) table.val) parameter := by
  have evaluation := parameterPolynomial_eval retained parameter
  rewrite [← table.property] at evaluation
  have original := primitive.split parameter nonzero
  rewrite [evaluation, parameterOrder_succ] at original
  exact original

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

end
