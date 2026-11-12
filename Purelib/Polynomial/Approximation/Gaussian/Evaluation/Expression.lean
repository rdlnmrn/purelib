module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Expression.Basic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

namespace Purelib.Polynomial.Approximation.Gaussian.Evaluation.Expression

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Polynomial

public section

/-!
# Projective rational-function evaluation on CCL names

Numerator and denominator are evaluated as a pair of coherent progressive CCL
processes.  This pair remains meaningful at a pole; affine division is exposed
only after the caller supplies finite denominator apartness.  No completed
input or root is selected.
-/

open Purelib.Approximation

/-- Expression-tree form of polynomial Horner evaluation. -/
@[expose] def polynomialExpression (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Expression) : Expression :=
  polynomial.coeffs.foldl
    (fun accumulator coefficient =>
      Expression.add
        (Expression.mul accumulator input)
        (Expression.exact coefficient))
    (Expression.exact 0)

section
/-- Reading the output of a finite expression Horner fold gives the same coherent Horner fold. -/
private theorem expressionHorner_output (input accumulator :
  Expression) :
    (coefficients : List Gaussian.Basic.Canonical) →
      (coefficients.foldl
        (fun current coefficient =>
          Expression.add
            (Expression.mul current input)
            (Expression.exact coefficient))
        accumulator).output =
      Horner.horner input.output accumulator.output coefficients
  | [] => rfl
  | coefficient :: coefficients => by
      simpa only [List.foldl_cons, Horner.horner_cons,
        Expression.add,
        Expression.mul,
        Expression.exact,
        Expression.leaf] using

          Expression.expressionHorner_output
          input
          (Expression.add
            (Expression.mul
              accumulator input)
            (Expression.exact coefficient))
          coefficients
end

/-- The polynomial expression's output is exactly its coherent Horner evaluation. -/
theorem polynomialExpression_output (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Expression) :
    (polynomialExpression polynomial input).output =
      Horner.polynomialEval polynomial input.output := by
  exact expressionHorner_output
    input
    (Expression.exact 0)
    polynomial.coeffs

/-- Exact rational specialization of the public expression-tree evaluator. -/
@[expose] def polynomialExpression_exact (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Gaussian.Basic.Canonical) :
    Equivalence.NamedEquivalent
      (polynomialExpression polynomial
        (Expression.exact input)).output.name
      (Name.Basic.Named.exact
        (polynomial.eval input)) := by
  rw [polynomialExpression_output]
  simpa only [Expression.exact,
    Expression.leaf] using
    Horner.polynomialEval_exact polynomial input

end

end Purelib.Polynomial.Approximation.Gaussian.Evaluation.Expression
