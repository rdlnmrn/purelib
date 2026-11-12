module

public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Approximation.Rational.Budget.Product
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Operand allowances below the original coherent product allowance

The actual paired product state retains both original operand states.
Nonnegativity of the original five-term allowance polynomial bounds each
operand's magnitude-weighted allowance by the same full product allowance.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

/-- The full original product allowance bounds the original left operand allowance at its actual paired state. -/
theorem leftAllowance_le (left right : CoherentNamed) (state : (left.mul right).name.process.State) :
    4 * right.name.process.centerBound * left.coherent.allowance state.1 ≤
      (left.mul right).coherent.allowance state := by
  let first := left.coherent.allowance state.1
  let last := right.coherent.allowance state.2
  have remaining : 0 ≤ first * last + first * first + last * last + left.name.process.centerBound * last :=
    Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct
          (Order.Arithmetic.mul_nonneg_direct (left.coherent.allowance_nonneg state.1)
            (right.coherent.allowance_nonneg state.2))
          (Order.Arithmetic.mul_nonneg_direct (left.coherent.allowance_nonneg state.1)
            (left.coherent.allowance_nonneg state.1)))
        (Order.Arithmetic.mul_nonneg_direct (right.coherent.allowance_nonneg state.2)
          (right.coherent.allowance_nonneg state.2)))
      (Order.Arithmetic.mul_nonneg_direct left.name.process.centerBound_nonneg
        (right.coherent.allowance_nonneg state.2))
  calc
    _ = 4 * (first * right.name.process.centerBound + 0) := by dsimp only [first]; ring1
    _ ≤ 4 * (first * right.name.process.centerBound +
        (first * last + first * first + last * last + left.name.process.centerBound * last)) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) remaining) (by decide +kernel)
    _ = (left.mul right).coherent.allowance state := by
      change _ = Process.Coherence.Basic.Coherent.productAllowance left.name.process.centerBound
        right.name.process.centerBound first last
      unfold Process.Coherence.Basic.Coherent.productAllowance Process.Coherence.Basic.Coherent.productBase
      ring1

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
