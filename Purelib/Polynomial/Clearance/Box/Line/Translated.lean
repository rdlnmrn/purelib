module
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

namespace Purelib.Polynomial.Clearance.Box.Line.Translated

open Purelib.Algebra.Group
attribute [local instance high] Negation.subNegZeroMonoid

/-- Quantitative clearance of the original translated coordinate on a displayed vertical line.

The fixed nonzero real-coordinate difference supplies a strictly positive squared lower bound throughout the original
ambient vertical interval. The polynomial and line retain their original coordinate and box owners. -/
@[expose] def translatedCoordinate_verticalLineClearance
    (c : Gaussian.Basic.Canonical) (ambient : Box) (x : Fraction.Rational)
    (apart : x ≠ c.re) :
    Clearance.Box.Line.Basic.VerticalLineClearance
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) ambient x where
  bound := (x - c.re) ^ 2
  positive := by
    have nonzero : x - c.re ≠ 0 := by
      intro zero
      apply apart
      calc
        x = (x - c.re) + c.re := by ring1
        _ = 0 + c.re := congrArg (fun value => value + c.re) zero
        _ = c.re := by ring1
    have squareNonzero : (x - c.re) ^ 2 ≠ 0 := by
      intro zero
      exact nonzero ((Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_eq_zero_direct _).mp zero)
    exact lt_of_le_of_ne
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _) (Ne.symm squareNonzero)
  lower := by
    intro y lower upper
    rw [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    change (x - c.re) ^ 2 <=
      (x - c.re) ^ 2 + (y - c.im) ^ 2
    exact le_add_of_nonneg_right
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- Quantitative clearance of the original translated coordinate on a displayed horizontal line.

The fixed nonzero imaginary-coordinate difference supplies a strictly positive squared lower bound throughout the
original ambient horizontal interval. The polynomial and line retain their original coordinate and box owners. -/
@[expose] def translatedCoordinate_horizontalLineClearance
    (c : Gaussian.Basic.Canonical) (ambient : Box) (y : Fraction.Rational)
    (apart : y ≠ c.im) :
    Clearance.Box.Line.Basic.HorizontalLineClearance
      (Dense.Gaussian.Linear.Translated.translatedCoordinate c) ambient y where
  bound := (y - c.im) ^ 2
  positive := by
    have nonzero : y - c.im ≠ 0 := by
      intro zero
      apply apart
      calc
        y = (y - c.im) + c.im := by ring1
        _ = 0 + c.im := congrArg (fun value => value + c.im) zero
        _ = c.im := by ring1
    have squareNonzero : (y - c.im) ^ 2 ≠ 0 := by
      intro zero
      exact nonzero ((Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_eq_zero_direct _).mp zero)
    exact lt_of_le_of_ne
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _) (Ne.symm squareNonzero)
  lower := by
    intro x lower upper
    rw [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    change (y - c.im) ^ 2 <=
      (x - c.re) ^ 2 + (y - c.im) ^ 2
    exact le_add_of_nonneg_left
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
end Purelib.Polynomial.Clearance.Box.Line.Translated
