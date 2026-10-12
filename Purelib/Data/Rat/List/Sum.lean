module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Rational.Squares
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Finite primitive comparison for actual path samples

Telescoping is supplied by the geometry of a connected path.  The comparison
then uses finite Cauchy--Schwarz, retaining both occurrences of the cell count
when each cell has a uniform squared-error bound.  Dyadic cancellation pays
that count exactly; it is not a fixed-list convergence argument.
-/

namespace Purelib.Data.Rat.List.Sum

open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)

open Purelib in
open Purelib.Algebra in
open Purelib.Data.Rat in
/-- Summing a constant rational over the retained finite cell list gives its length cast times that constant.

The original cell list is traversed in order. The exact natural length is cast through the same rational operation
record, and each retained occurrence contributes the supplied scalar once. -/
theorem constantSum (budget : Fraction.Rational) (cells : List Integration.Polynomial.Gaussian.Cell.Basic.CellModel) :
    FiniteSum.Rational.Squares.coordinateSum (cells.map fun _ => budget) = (cells.length : Fraction.Rational) * budget
      := by
  induction cells with
  | nil => change (0 : Fraction.Rational) = 0 * budget; ring1
  | cons cell cells ih =>
      change budget + coordinateSum (cells.map fun _ => budget) =
        ((cells.length + 1 : Nat) : Fraction.Rational) * budget
      rw [ih, NatCast.add, Nat.cast_one]
      ring1

end Purelib.Data.Rat.List.Sum
