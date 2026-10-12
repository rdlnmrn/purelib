module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rat.Logarithm.Horner.Basic
public import Purelib.Data.Nat.Odd
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Compatibility

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
public section

/-! Approximation Rat Logarithm Horner Coefficient and its finite structural certificates. -/

namespace Purelib.Approximation.Rat.Logarithm.Horner.Coefficient

open Purelib
open Purelib.Approximation.Rat.Logarithm.Horner.Basic
open Purelib.Data.Nat
open Purelib.Data.Rat

/-- At a positive index, the shared logarithm coefficient is the ratio of consecutive displayed odd numbers. -/
theorem logCoefficient_eq_priorOdd_ratio {index : Nat}
    (positive : 1 ≤ index) :
    ComplexLog.coefficient index =
      (Purelib.Data.Nat.Odd.priorOdd index : Fraction.Rational) / (Purelib.Data.Nat.Odd.priorOdd (index + 1) :
        Fraction.Rational) := by
  rw [ComplexLog.coefficient,
    Log.coefficient]
  unfold Odd.priorOdd
  rw [Purelib.Algebra.NatCast.sub (by omega : 1 ≤ 2 * index),
    Purelib.Algebra.NatCast.sub (by omega : 1 ≤ 2 * (index + 1)), Purelib.Algebra.NatCast.mul,
    Purelib.Algebra.NatCast.mul, Purelib.Algebra.NatCast.add, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  ring1

/-- The logarithm coefficient cancels the shared odd-number factor in the displayed finite ratio. -/
theorem logCoefficient_telescope {index : Nat} (positive : 1 ≤ index)
    (degree : Nat) :
    ComplexLog.coefficient index *
        ((Odd.priorOdd (index + 1) : Fraction.Rational) /
          (Odd.priorOdd (index + 1 + degree) : Fraction.Rational)) =
      (Odd.priorOdd index : Fraction.Rational) /
        (Odd.priorOdd (index + (degree + 1)) : Fraction.Rational) := by
  rw [Approximation.Rat.Logarithm.Horner.Coefficient.logCoefficient_eq_priorOdd_ratio positive]
  have middleNonzero : (Odd.priorOdd (index + 1) : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (Odd.priorOdd_pos (positive.trans (Nat.le_add_right index 1)))).ne'
  have denominatorNonzero :
      (Odd.priorOdd (index + 1 + degree) : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (Odd.priorOdd_pos
        ((positive.trans (Nat.le_add_right index 1)).trans
          (Nat.le_add_right (index + 1) degree)))).ne'
  rw [Fraction.Compatibility.div_mul_div_telescope _ _ _ middleNonzero denominatorNonzero]
  congr 2
  congr 1
  ring1
end Purelib.Approximation.Rat.Logarithm.Horner.Coefficient

end
