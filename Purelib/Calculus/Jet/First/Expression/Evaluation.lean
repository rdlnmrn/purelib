module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sample
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Sequence
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.Sample
import Purelib.Approximation.Gaussian.Sequence.Constant
public import Purelib.Calculus.Jet.First.Arithmetic
import Purelib.Calculus.Jet.First.Basic
public import Purelib.Calculus.Jet.First.Expression.Basic
import Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Executable first jets and forward differentiation

A `FirstJet` is just two displayed Gaussian rationals: a value and its
first-order coefficient.  It is not a function graph, germ, infinitesimal,
or equivalence class.  The operations below are finite programs implementing
the sum, product, chain, reciprocal, and quotient rules.

`JetExpression` is finite syntax.  Its evaluator computes the value and
first-order coefficient together.  Exponential and logarithm nodes call the
finite sample programs from the preceding calculus modules at the requested
natural depth.
-/

namespace Purelib.Calculus.Jet.First.Expression.Basic
namespace JetExpression

section
open Purelib.Calculus.Jet.First
open Purelib.Data
section
open Purelib.Approximation.Gaussian
/-- Evaluate an expression using displayed Gaussian rational arithmetic.

Every transcendental node uses the same supplied natural depth. Inversion is total; this evaluator does not perform the
separate admissibility checks. -/
def eval : Expression.Basic.JetExpression →
  Canonical → Nat → Canonical
  | .constant value, _, _ => value
  | .input, point, _ => point
  | .add left right, point, index =>
      left.eval point index + right.eval point index
  | .neg expression, point, index => -expression.eval point index
  | .mul left right, point, index =>
      left.eval point index * right.eval point index
  | .reciprocal expression, point, index =>
      (expression.eval point index)⁻¹
  | .exponential expression, point, index =>
      Exponential.Horner.Sample.sample (expression.eval point index) index
  | .logarithm1p expression, point, index =>
      Logarithm.OnePlus.Sample.log1pSample
        (expression.eval point index) index

/-- Evaluate the displayed value and first-order coefficient together.

Arithmetic nodes use the finite first-order rules. Exponential nodes reuse the finite exponential sample as their
primitive coefficient; logarithm nodes use the finite geometric derivative sample. No function-valued derivative is
constructed. -/
def jet : Expression.Basic.JetExpression →
  Canonical → Nat → Basic.FirstJet
  | .constant value, _, _ => Basic.FirstJet.constant value
  | .input, point, _ => Basic.FirstJet.independent point
  | .add left right, point, index =>
      Basic.FirstJet.add (left.jet point index) (right.jet point index)
  | .neg expression, point, index =>
      Basic.FirstJet.neg (expression.jet point index)
  | .mul left right, point, index =>
      Basic.FirstJet.mul (left.jet point index) (right.jet point index)
  | .reciprocal expression, point, index =>
      Basic.FirstJet.reciprocal (expression.jet point index)
  | .exponential expression, point, index =>
      let inner := expression.jet point index
      Basic.FirstJet.compose
        ⟨Exponential.Horner.Sample.sample inner.value index,
          Exponential.Horner.Sample.sample inner.value index⟩ inner
  | .logarithm1p expression, point, index =>
      let inner := expression.jet point index
      Basic.FirstJet.compose
        ⟨Logarithm.OnePlus.Sample.log1pSample inner.value index,
          Logarithm.OnePlus.Derivative.Sample.log1pDerivativeSample
            inner.value index⟩ inner

end

/-- The value component of forward evaluation equals ordinary finite-depth evaluation. -/
theorem jet_value (expression :
  Expression.Basic.JetExpression) (point : Canonical)
    (index : Nat) :
    (expression.jet point index).value = expression.eval point index := by
  induction expression with
  | constant value => rfl
  | input => rfl
  | add left right leftInduction rightInduction =>
      simp only [jet, eval, Basic.FirstJet.add]
      rw [leftInduction, rightInduction]
  | neg expression inductionHypothesis =>
      simp only [jet, eval, Basic.FirstJet.neg]
      rw [inductionHypothesis]
  | mul left right leftInduction rightInduction =>
      simp only [jet, eval, Basic.FirstJet.mul]
      rw [leftInduction, rightInduction]
  | reciprocal expression inductionHypothesis =>
      simp only [jet, eval, Basic.FirstJet.reciprocal]
      rw [inductionHypothesis]
  | exponential expression inductionHypothesis =>
      simp only [jet, eval, Basic.FirstJet.compose]
      rw [inductionHypothesis]
  | logarithm1p expression inductionHypothesis =>
      simp only [jet, eval, Basic.FirstJet.compose]
      rw [inductionHypothesis]

/-- The displayed coefficient of an expression sum is the sum of its coefficients. -/
@[simp] theorem jet_add_slope (left right :
  Expression.Basic.JetExpression)
    (input : Canonical) (index : Nat) :
    ((left.add right).jet input index).slope =
      (left.jet input index).slope + (right.jet input index).slope := rfl

/-- The displayed product coefficient satisfies the first-order product rule.

Each cross term uses the ordinary finite-depth value of the other subexpression at the same input and depth. -/
@[simp] theorem jet_mul_slope (left right :
  Expression.Basic.JetExpression)
    (input : Canonical) (index : Nat) :
    ((left.mul right).jet input index).slope =
      (left.jet input index).slope * right.eval input index +
        left.eval input index * (right.jet input index).slope := by
  simp only [jet, Basic.FirstJet.mul]
  rw [jet_value, jet_value]

/-- The displayed reciprocal coefficient is the negative coefficient times the squared inverse value. -/
@[simp] theorem jet_reciprocal_slope (expression :
  Expression.Basic.JetExpression)
    (input : Canonical) (index : Nat) :
    (expression.reciprocal.jet input index).slope =
      -((expression.jet input index).slope *
        ((expression.eval input index)⁻¹ *
          (expression.eval input index)⁻¹)) := by
  simp only [jet, Basic.FirstJet.reciprocal]
  rw [jet_value]

open Purelib.Approximation.Gaussian
/-- The exponential node multiplies the inner coefficient by its finite exponential sample.

The inner value is evaluated at the same input and depth as the coefficient. -/
theorem jet_exponential_slope (expression :
  Expression.Basic.JetExpression)
    (input : Canonical) (index : Nat) :
    (expression.exponential.jet input index).slope =
      (expression.jet input index).slope *
        Exponential.Horner.Sample.sample
          (expression.eval input index) index := by
  simp only [jet, Basic.FirstJet.compose]
  rw [jet_value]

/-- The logarithm-of-one-plus node uses the finite geometric derivative sample.

Its coefficient is the inner coefficient times that sample at the ordinary finite-depth inner value. -/
theorem jet_logarithm1p_slope (expression :
  Expression.Basic.JetExpression)
    (input : Canonical) (index : Nat) :
    (expression.logarithm1p.jet input index).slope =
      (expression.jet input index).slope *
        Logarithm.OnePlus.Derivative.Sample.log1pDerivativeSample
          (expression.eval input index) index := by
  simp only [jet, Basic.FirstJet.compose]
  rw [jet_value]

/-- Relate the logarithm derivative approximation to the exact reciprocal target.

The displayed inner value must have squared norm at most one quarter. The resulting equivalence compares its finite
derivative approximation with the constant approximation to the inverse of one plus that value. -/
def logarithm1p_primitive_derivative_equivalent
    (expression : Expression.Basic.JetExpression) (input : Canonical) (index : Nat)
    (disk : Gaussian.Norm.Basic.normSq (expression.eval input index) ≤ 1 / 4) :
    Equivalence.Equivalent
      (Logarithm.OnePlus.Derivative.Sequence.log1pDerivativeApproximation
        (expression.eval input index) disk)
      (Sequence.Constant.constantApproximation
        ((1 + expression.eval input index)⁻¹)) :=
  Logarithm.OnePlus.Derivative.Equivalence.log1p_derivative_equivalent_inverse
    (expression.eval input index) disk
end

end JetExpression

end Purelib.Calculus.Jet.First.Expression.Basic

end
