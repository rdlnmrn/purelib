module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite primitive comparison for actual path samples

Telescoping is supplied by the geometry of a connected path.  The comparison
then uses finite Cauchy--Schwarz, retaining both occurrences of the cell count
when each cell has a uniform squared-error bound.  Dyadic cancellation pays
that count exactly; it is not a fixed-list convergence argument.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A retained dyadic cell count cancels the count factors in the original primitive integral-error bound.

The original per-cell Taylor and coefficient-error terms retain their separate movement and quarter-radius factors at
the supplied depth. -/
theorem dyadic_integral_error_le (primitive :
  Basic.Canonical → Basic.Canonical) (path : Basic.PathModel)
    {start finish : Basic.Canonical}
    (telescopes : Primitive.incrementSum primitive path.cells = primitive finish - primitive start)
    (depth : Nat) (count : path.cells.length = 2 ^ depth)
    (movement taylor coefficientError : Fraction.Rational)
    (bounded : ∀ cell ∈ path.cells,
      Basic.Canonical.normSq (primitive cell.finish - primitive cell.start - cell.integralSample) ≤
        taylor * Geometric.Basic.quarterRadius movement depth ^ 2 + coefficientError * Geometric.Basic.quarterRadius
          movement depth) :
    Basic.Canonical.normSq (primitive finish - primitive start - path.integralSample) ≤
      taylor * movement * Geometric.Basic.quarterRadius movement depth + coefficientError * movement := by
  have bound := Primitive.integral_error_le_uniform primitive path telescopes _ bounded
  rw [count] at bound
  have identity : ((2 ^ depth : Nat) : Fraction.Rational) *
      (((2 ^ depth : Nat) : Fraction.Rational) *
        (taylor * Geometric.Basic.quarterRadius movement depth ^ 2 + coefficientError * Geometric.Basic.quarterRadius
          movement depth)) =
      taylor * movement * Geometric.Basic.quarterRadius movement depth + coefficientError * movement := by
    calc
      _ = (taylor * Geometric.Basic.quarterRadius movement depth + coefficientError) *
        (((2 ^ depth : Nat) : Fraction.Rational) *
          (((2 ^ depth : Nat) : Fraction.Rational) * Geometric.Basic.quarterRadius movement depth)) := by ring1
      _ = _ := by rw [Geometric.DyadicCount.dyadic_count_cancel]; ring1
  exact identity ▸ bound

end Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic

end
