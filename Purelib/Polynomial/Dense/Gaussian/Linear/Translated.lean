module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Data.Gaussian.Field
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

/-!
# Translated Gaussian coordinates

The retained two-entry coefficient table `[1, -c]` represents `Z - c`.
-/

open Purelib.Data
open Purelib.Polynomial

public section

namespace Purelib.Polynomial.Dense.Gaussian.Linear.Translated

/-- Exact dense program for `Z-c`. -/
@[expose] def translatedCoordinate (c :
  Gaussian.Basic.Canonical) : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) := ⟨[1, -c]⟩

/-- The polynomial with coefficients `[1, -c]` evaluates to the point minus `c`. -/
@[simp] theorem translatedCoordinate_eval (c z :
  Gaussian.Basic.Canonical) :
    (translatedCoordinate c).eval z = z - c := by
  simp only [translatedCoordinate, Dense.Basic.DensePolynomial.eval,
    Dense.Basic.DensePolynomial.evalCoeffs, List.foldl_cons,
    List.foldl_nil, MulZeroClass.zero_mul, _root_.zero_add, _root_.one_mul]
  exact (_root_.sub_eq_add_neg z c).symm

/-- The original translated-coordinate polynomial derivative evaluates to one at every original point.

The unchanged two-entry coefficient spine feeds the existing automatic
Horner derivative. Its constant entry has zero spatial derivative.
-/
theorem derivative_eval (center point : Gaussian.Basic.Canonical) :
    (GCD.derivative (translatedCoordinate center)).eval point = 1 := by
  unfold GCD.derivative
  rewrite [Dense.Derivative.eval_derivative]
  unfold translatedCoordinate Dense.Derivative.evalDerivativeCoeffs Dense.Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

end Purelib.Polynomial.Dense.Gaussian.Linear.Translated
