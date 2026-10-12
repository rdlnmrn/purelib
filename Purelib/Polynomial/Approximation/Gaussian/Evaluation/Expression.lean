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
    (input : Approximation.Gaussian.Expression) : Approximation.Gaussian.Expression :=
  polynomial.coeffs.foldl
    (fun accumulator coefficient =>
      Approximation.Gaussian.Expression.add
        (Approximation.Gaussian.Expression.mul accumulator input)
        (Approximation.Gaussian.Expression.exact coefficient))
    (Approximation.Gaussian.Expression.exact 0)

section
/-- Reading the output of a finite expression Horner fold gives the same coherent Horner fold. -/
private theorem expressionHorner_output (input accumulator :
  Approximation.Gaussian.Expression) :
    (coefficients : List Gaussian.Basic.Canonical) →
      (coefficients.foldl
        (fun current coefficient =>
          Approximation.Gaussian.Expression.add
            (Approximation.Gaussian.Expression.mul current input)
            (Approximation.Gaussian.Expression.exact coefficient))
        accumulator).output =
      Approximation.Gaussian.Evaluation.Horner.horner input.output accumulator.output coefficients
  | [] => rfl
  | coefficient :: coefficients => by
      simpa only [List.foldl_cons, Approximation.Gaussian.Evaluation.Horner.horner,
        Approximation.Gaussian.Expression.add,
        Approximation.Gaussian.Expression.mul,
        Approximation.Gaussian.Expression.exact,
        Approximation.Gaussian.Expression.leaf] using

          Purelib.Polynomial.Approximation.Gaussian.Evaluation.Expression.expressionHorner_output
          input
          (Approximation.Gaussian.Expression.add
            (Approximation.Gaussian.Expression.mul
              accumulator input)
            (Approximation.Gaussian.Expression.exact coefficient))
          coefficients
end

/-- The polynomial expression's output is exactly its coherent Horner evaluation. -/
theorem polynomialExpression_output (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Approximation.Gaussian.Expression) :
    (Approximation.Gaussian.Evaluation.Expression.polynomialExpression polynomial input).output =
      Approximation.Gaussian.Evaluation.Horner.polynomialEval polynomial input.output := by
  exact Purelib.Polynomial.Approximation.Gaussian.Evaluation.Expression.expressionHorner_output
    input
    (Approximation.Gaussian.Expression.exact 0)
    polynomial.coeffs

/-- Exact rational specialization of the public expression-tree evaluator. -/
@[expose] def polynomialExpression_exact (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (input : Gaussian.Basic.Canonical) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.Evaluation.Expression.polynomialExpression polynomial
        (Approximation.Gaussian.Expression.exact input)).output.name
      (Name.Basic.Named.exact
        (polynomial.eval input)) := by
  rw [Approximation.Gaussian.Evaluation.Expression.polynomialExpression_output]
  simpa only [Approximation.Gaussian.Expression.exact,
    Approximation.Gaussian.Expression.leaf] using
    Approximation.Gaussian.Evaluation.Horner.polynomialEval_exact polynomial input

end

end Purelib.Polynomial.Approximation.Gaussian.Evaluation.Expression
