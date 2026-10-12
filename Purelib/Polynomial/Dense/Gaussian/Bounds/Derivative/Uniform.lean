module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.List.NormBounds
import Purelib.Data.Gaussian.List.Proximity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Perturbation.Derivative
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Bounds.Horner

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Derivative.Uniform
open Purelib.Data.Gaussian

/-- A common coefficient quadrance bound gives coefficientwise proximity to the zero table of the same length. -/
private theorem coefficientsClose_zero_of_normLe : ∀
    {coefficients : List Gaussian.Basic.Canonical} {bound : Fraction.Rational},
    Gaussian.List.NormBounds.CoefficientsNormLe coefficients bound →
    Purelib.Data.Gaussian.List.Proximity.CoefficientsClose coefficients (coefficients.map fun _ => 0) bound
  | [], bound, _bounded => trivial
  | coefficient :: remaining, bound, bounded => by
      change Data.Gaussian.Norm.Basic.normSq (coefficient - 0) ≤ bound ∧
        Purelib.Data.Gaussian.List.Proximity.CoefficientsClose remaining
          (remaining.map fun _ => 0) bound
      constructor
      · simpa only [Gaussian.Basic.sub_zero] using bounded.1
      · exact coefficientsClose_zero_of_normLe bounded.2
end Purelib.Polynomial.Dense.Gaussian.Bounds.Derivative.Uniform

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Derivative.Uniform
open Purelib.Data.Gaussian

/-- Automatic Horner evaluation of an all-zero coefficient table returns zero value and zero derivative. -/
private theorem evalDerivativeCoeffs_zero : ∀
    (coefficients : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical),
    Dense.Derivative.evalDerivativeCoeffs input
      (coefficients.map fun _ => 0) = (0, 0)
  | [], input => rfl
  | _ :: remaining, input => by
      change (0 :: remaining.map (fun _ => 0)).foldl
        (Dense.Derivative.evalDerivativeStep input) (0, 0) = (0, 0)
      rw [List.foldl_cons]
      simp only [Dense.Derivative.evalDerivativeStep,
        Gaussian.Basic.zero_mul,
        Gaussian.Basic.zero_add]
      exact evalDerivativeCoeffs_zero remaining input
end Purelib.Polynomial.Dense.Gaussian.Bounds.Derivative.Uniform

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Derivative.Uniform
open Purelib.Data.Gaussian

/-- A common coefficient quadrance bound controls the automatic derivative
at every input with the displayed norm bound. -/
theorem normSq_evalDerivativeCoeffs_le_uniform
    (coefficients : List Gaussian.Basic.Canonical) (input : Gaussian.Basic.Canonical)
    (coefficientBound inputNormSq : Fraction.Rational)
    (bounded : Gaussian.List.NormBounds.CoefficientsNormLe coefficients coefficientBound)
    (inputBound : Data.Gaussian.Norm.Basic.normSq input ≤ inputNormSq)
    (coefficientNonnegative : 0 ≤ coefficientBound)
    (inputNonnegative : 0 ≤ inputNormSq) :
    Data.Gaussian.Norm.Basic.normSq
        (Dense.Derivative.evalDerivativeCoeffs input coefficients).2 ≤
      (Dense.Gaussian.Bounds.Perturbation.Derivative.coefficientPerturbationBounds coefficients.length coefficientBound
        inputNormSq).slope := by
  have close := coefficientsClose_zero_of_normLe bounded
  have result := Dense.Gaussian.Bounds.Perturbation.Derivative.normSq_evalDerivative_sub_le coefficients
    (coefficients.map fun _ => 0) input coefficientBound inputNormSq close
    inputBound coefficientNonnegative inputNonnegative
  rw [evalDerivativeCoeffs_zero coefficients input] at result
  simpa only [Gaussian.Basic.sub_zero] using result.2

end Purelib.Polynomial.Dense.Gaussian.Bounds.Derivative.Uniform

end
