module
import Purelib.Algebra.NatCast
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational

open Purelib.Data.Rat
open Purelib.Algebra

@[expose] public section

/-!
# Finite primitive comparison for actual path samples

Telescoping is supplied by the geometry of a connected path.  The comparison
then uses finite Cauchy--Schwarz, retaining both occurrences of the cell count
when each cell has a uniform squared-error bound.  Dyadic cancellation pays
that count exactly; it is not a fixed-list convergence argument.
-/

namespace Purelib.Approximation.Rational.Geometric.DyadicCount

/-- The squared dyadic cell count exactly cancels one squared movement factor, for arbitrary rational scales, including
zero. -/
theorem dyadic_count_cancel (movement : Fraction.Rational) (depth : Nat) :
    ((2 ^ depth : Nat) : Fraction.Rational) *
      (((2 ^ depth : Nat) : Fraction.Rational) * Geometric.Basic.quarterRadius movement depth) = movement := by
  rw [Geometric.Basic.quarterRadius]
  have castPower : ((2 ^ depth : Nat) : Fraction.Rational) = (2 : Fraction.Rational) ^ depth :=
    NatCast.pow 2 depth
  rw [castPower]
  have square : (2 : Fraction.Rational) ^ depth * 2 ^ depth = 4 ^ depth := by
    rewrite [← Semiring.Normalization.product_pow]
    exact congrArg (fun value : Fraction.Rational => value ^ depth)
      (show (2 : Fraction.Rational) * 2 = 4 by decide)
  calc
    _ = (movement / (4 : Fraction.Rational) ^ depth) * ((2 : Fraction.Rational) ^ depth * 2 ^ depth) := by ring1
    _ = (movement / (4 : Fraction.Rational) ^ depth) * (4 : Fraction.Rational) ^ depth := by rw [square]
    _ = movement := Fraction.Field.div_mul_cancel_of_ne _ _
      (Fraction.Order.Arithmetic.pow_pos_direct (by decide) depth).ne'
end Purelib.Approximation.Rational.Geometric.DyadicCount
