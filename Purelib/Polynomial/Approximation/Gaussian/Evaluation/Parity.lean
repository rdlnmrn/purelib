module
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.Low
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Coherent evaluation through an operational square law

Inserting zero odd coefficients transports a finite polynomial evaluation
through the supplied square comparison. The resulting primitive comparison
retains the input channel, factor coefficients and exact parameter.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Evaluation.Parity

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Polynomial
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)

/-- Inserting zero odd coefficients transports evaluation through the retained square law of the input name.

The resulting named equivalence uses the supplied operational square certificate; individual rational samples need not
satisfy that equality. -/
@[expose] def low_square (input : Name.Coherent.CoherentNamed) (point : Gaussian.Basic.Canonical)
    (square : Equivalence.NamedEquivalent (Name.Coherent.CoherentNamed.mul input input).name (exact point).name)
      (coefficients : List Gaussian.Basic.Canonical) :
    Equivalence.NamedEquivalent (Horner.Low.low (Dense.Gaussian.Primitive.Parity.spread coefficients) input).name
      (Horner.Low.low coefficients (exact point)).name := by
  induction coefficients with
  | nil => exact Equivalence.NamedEquivalent.refl _
  | cons coefficient remaining previous =>
      let left := Horner.Low.low (Dense.Gaussian.Primitive.Parity.spread remaining) input
      let right := Horner.Low.low remaining (exact point)
      have products : Equivalence.NamedEquivalent (Name.Coherent.CoherentNamed.mul (Name.Coherent.CoherentNamed.add
        (Name.Coherent.CoherentNamed.mul left input) (exact 0)) input).name
          (Name.Coherent.CoherentNamed.mul right (exact point)).name :=
        (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects (Name.Coherent.CoherentNamed.add
          (Name.Coherent.CoherentNamed.mul left input) (exact 0)) (Name.Coherent.CoherentNamed.mul left input) input
          input
          (Arithmetic.Add.coherentAdd_zero_right (Name.Coherent.CoherentNamed.mul left input))
            (Equivalence.NamedEquivalent.refl _)).trans
          ((Name.Coherent.Arithmetic.Product.Laws.coherentMul_assoc left input input).trans
            (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects left right
              (Name.Coherent.CoherentNamed.mul input input) (exact point) previous square))
      simp only [Dense.Gaussian.Primitive.Parity.spread, Horner.Low.low_cons]
      exact Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects (Name.Coherent.CoherentNamed.mul
        (Name.Coherent.CoherentNamed.add (Name.Coherent.CoherentNamed.mul left input) (exact 0)) input)
        (Name.Coherent.CoherentNamed.mul right (exact point)) (exact coefficient) (exact coefficient) products
          (Equivalence.NamedEquivalent.refl _)

/-- A factored dense primitive evaluates through the supplied operational square law.

The retained coefficient identity expresses the primitive as the coordinate
times its cached factor at the squared parameter. The comparison uses that
same factor and coordinate name without replacing their numerical readings. -/
@[expose] def square {value factor : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (coefficients : value.coeffs = Dense.Gaussian.Primitive.Parity.valueCoefficients factor true)
    (input : Name.Coherent.CoherentNamed) (point : Gaussian.Basic.Canonical)
    (square : Equivalence.NamedEquivalent (Name.Coherent.CoherentNamed.mul input input).name (exact point).name) :
    Equivalence.NamedEquivalent (Approximation.Gaussian.Evaluation.Horner.polynomialEval value input).name
      (Name.Coherent.CoherentNamed.mul input (exact (factor.eval point))).name := by
  have factorValue : Equivalence.NamedEquivalent (Horner.Low.low (Dense.Gaussian.Primitive.Parity.spread
    factor.coeffs.reverse) input).name
      (exact (factor.eval point)).name := by
    have transported := low_square input point square factor.coeffs.reverse
    rw [Horner.Low.low_coeffs] at transported
    exact transported.trans (Approximation.Gaussian.Evaluation.Horner.polynomialEval_exact factor point)
  change Equivalence.NamedEquivalent (Approximation.Gaussian.Evaluation.Horner.horner input (exact 0) value.coeffs).name
    _
  rw [coefficients]
  change Equivalence.NamedEquivalent (Horner.Low.low (0 :: Dense.Gaussian.Primitive.Parity.spread factor.coeffs.reverse)
    input).name _
  rw [Horner.Low.low_cons]
  exact (Arithmetic.Add.coherentAdd_zero_right (Name.Coherent.CoherentNamed.mul (Horner.Low.low
    (Dense.Gaussian.Primitive.Parity.spread factor.coeffs.reverse) input) input)).trans
    ((Name.Coherent.Arithmetic.Product.Laws.coherentMul_comm (Horner.Low.low (Dense.Gaussian.Primitive.Parity.spread
      factor.coeffs.reverse) input) input).trans
      (Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects input input (Horner.Low.low
        (Dense.Gaussian.Primitive.Parity.spread factor.coeffs.reverse) input) (exact (factor.eval point))
        (Equivalence.NamedEquivalent.refl _) factorValue))

end Purelib.Polynomial.Approximation.Gaussian.Evaluation.Parity
