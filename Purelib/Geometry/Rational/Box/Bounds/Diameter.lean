module
import Purelib.Geometry.Rational.Box.Dimensions
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

section
@[expose] public section

/-!
# Choice-free finite packing of winding-one tracks

A finite rational grid assigns every sufficiently refined track to one
explicit cell.  Equal assignments contradict local Taylor uniqueness.  The
final pigeonhole bound is proved by direct recursion on `Fin`, avoiding the
choice-dependent generic finite-cardinality theorem.
-/

namespace Purelib.Geometry.Rational.Box.Bounds.Diameter

/-- A nonnegative upper bound on the box diagonal also bounds each side length. -/
theorem widths_le_of_diagonal
    {box : Rational.Box} {side : Fraction.Rational} (sideNonnegative : 0 ≤ side)
    (diagonal : box.diagonalSq ≤ side ^ 2) :
    box.widthX ≤ side ∧ box.widthY ≤ side := by
  let dimensions : Data.Gaussian.Basic.Canonical := ⟨box.widthX, box.widthY⟩
  have dimensionsNorm : Data.Gaussian.Norm.Basic.normSq dimensions =
      box.diagonalSq := rfl
  have bounds := Data.Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le
    (z := dimensions) sideNonnegative (by
      rw [dimensionsNorm]
      exact diagonal)
  exact ⟨bounds.2.1, bounds.2.2.2⟩
end Purelib.Geometry.Rational.Box.Bounds.Diameter

end
