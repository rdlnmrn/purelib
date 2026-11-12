module

public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # One finite Horner secant traversal for original coefficient evaluators -/

public section

namespace Purelib.Polynomial.Ascending.Gaussian.Secant

open Purelib.Data.Gaussian.Basic (Canonical)

universe u

/-- Construct the finite secant kernel using the same retained tail evaluator.

The constant entry disappears structurally. Each successor branch consumes
its original coefficient tail through the supplied original evaluator.
-/
@[expose] def coefficientsKernel {Coefficient : Type u}
    (evaluate : Canonical → List Coefficient → Canonical) (x y : Canonical) : List Coefficient → Canonical
  | [] => 0
  | _ :: remaining => evaluate x remaining + y * coefficientsKernel evaluate x y remaining

/-- The original Horner branches factor their value difference through the shared finite secant traversal.

The displayed readback laws concern those same original evaluator branches;
no division by the argument difference or semantic coefficient equality is
used, including on the diagonal.
-/
theorem evalCoefficients_sub_factor {Coefficient : Type u}
    (evaluate : Canonical → List Coefficient → Canonical) (read : Coefficient → Canonical)
    (empty : ∀ point, evaluate point [] = 0)
    (step : ∀ point head tail, evaluate point (head :: tail) = read head + point * evaluate point tail)
    (x y : Canonical) : ∀ coefficients,
    evaluate x coefficients - evaluate y coefficients = (x - y) * coefficientsKernel evaluate x y coefficients
  | [] => by rw [empty, empty, coefficientsKernel]; ring1
  | head :: tail => by
      rw [step, step, coefficientsKernel]
      calc
        _ = (x - y) * evaluate x tail + y * (evaluate x tail - evaluate y tail) := by ring1
        _ = (x - y) * (evaluate x tail + y * coefficientsKernel evaluate x y tail) := by
          rw [evalCoefficients_sub_factor evaluate read empty step x y tail]
          ring1

end Purelib.Polynomial.Ascending.Gaussian.Secant

end
