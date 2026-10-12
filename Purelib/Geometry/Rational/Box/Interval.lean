module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Cast
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry

section
@[expose] public section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace Purelib.Geometry.Rational.Box.Interval

/-- The degenerate Gaussian box occupied by one coordinate interval. -/
def intervalBox (interval : Data.Rat.Interval.Bounds) :
  Rational.Box where
  xLower := interval.lower
  xUpper := interval.upper
  yLower := 0
  yUpper := 0
  x_valid := interval.valid
  y_valid := le_rfl

/-- Embedding a rational interval member on the real axis places it in the corresponding degenerate box. -/
theorem ofCoordinate_mem_intervalBox
    {interval : Data.Rat.Interval.Bounds} {point : Fraction.Rational}
    (inside : interval.Contains point) :
    (intervalBox interval).Contains (CoordinateTaylor.ofCoordinate point) :=
  ⟨inside.1, inside.2, le_rfl, le_rfl⟩

/-- The squared diagonal of the degenerate interval box is the squared interval width. -/
@[simp] theorem intervalBox_diagonalSq (interval :
  Data.Rat.Interval.Bounds) :
    (intervalBox interval).diagonalSq =
      (interval.upper - interval.lower) ^ 2 := by
  simp only [Rational.Box.diagonalSq, intervalBox]
  ring1

/-- Any two displayed points of one coordinate interval are no farther apart than its displayed width, in squared
distance. -/
theorem point_sub_center_sq_le_width_sq
    {interval : Data.Rat.Interval.Bounds} {point center : Fraction.Rational}
    (pointInside : interval.Contains point)
    (centerInside : interval.Contains center) :
    (point - center) ^ 2 ≤
      (interval.upper - interval.lower) ^ 2 := by
  have bound := (intervalBox interval).normSq_sub_le_diagonalSq
    (ofCoordinate_mem_intervalBox pointInside)
    (ofCoordinate_mem_intervalBox centerInside)
  rw [← Cast.ofCoordinate_sub] at bound
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Cast.ofCoordinate_normSq,
    intervalBox_diagonalSq] at bound
  exact bound
end Purelib.Geometry.Rational.Box.Interval

end
