module
-- Exposed weight construction retains the exact natural-cast increment proof.
public import Purelib.Algebra.NatCast

public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularClippedSeamBounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat.Fraction.Order

public section

/-! A finite reading allowance pays the full coarse seam and corner counts.
Its slope ceiling and geometry are fixed before numerical refinement. -/

namespace Purelib.Integration.Polynomial.Rectangle

open Purelib.Riemann.Normalization in
set_option genInjectivity false in
/-- A positive error cap paying for the exact rectangular seam-and-corner shape weight.

The retained cap is at most one, and its product with the explicit count-and-slope weight is bounded by the original
target. -/
structure ClippedExteriorTolerance (columns rows : Nat) (slope target : InverseRootPolynomial.Coordinate) where
  /-- The retained rectangular seam-and-corner error weight. -/ weight : InverseRootPolynomial.Coordinate
  /-- The weight equals the explicit column, row and slope formula. -/ weight_eq : weight =
    1024 * ((columns : InverseRootPolynomial.Coordinate) ^ 2 * ((rows + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2
      +
      ((columns + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * (rows : InverseRootPolynomial.Coordinate) ^ 2) *
        slope +
    512 * ((columns : InverseRootPolynomial.Coordinate) * (rows : InverseRootPolynomial.Coordinate)) ^ 2
  /-- The retained common upper bound for each input error. -/ cap : InverseRootPolynomial.Coordinate
  /-- The common error cap is strictly positive. -/ positive : 0 < cap
  /-- The error cap is at most one. -/ le_one : cap ≤ 1
  /-- The exact retained weight times the cap is at most the target. -/ paid : weight * cap ≤ target

constructive_injectivity ClippedExteriorTolerance

end Purelib.Integration.Polynomial.Rectangle

namespace Purelib.Integration.Polynomial.Rectangle.ClippedExteriorTolerance

variable {columns rows : Nat} {slope target : Riemann.Normalization.InverseRootPolynomial.Coordinate}

open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- The rectangular seam-count shape factor is nonnegative.

Both summands multiply squares of the retained column and row coordinates.
Their individual nonnegativity therefore supplies the exact shape bound. -/
theorem shape_nonnegative (columns rows : Nat) :
    0 ≤ (columns : InverseRootPolynomial.Coordinate) ^ 2 * ((rows + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 +
      ((columns + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * (rows : InverseRootPolynomial.Coordinate) ^ 2 :=
  add_nonneg (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
    (Arithmetic.sq_nonneg_direct _))
    (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
      (Arithmetic.sq_nonneg_direct _))

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Normalization in
/-- Construct a positive cap by clipping the weighted target allowance at one.

The exact column, row and slope weight is retained with its defining equation and payment certificate. -/
@[expose] def build (columns rows : Nat) (slope target : InverseRootPolynomial.Coordinate) (slopeNonnegative : 0 ≤
  slope) (positive : 0 < target) :
    ClippedExteriorTolerance columns rows slope target := by
  let c := Budget.Aggregate.countCoordinate columns
  let r := Budget.Aggregate.countCoordinate rows
  let weight := 1024 * (c ^ 2 * (r + 1) ^ 2 + (c + 1) ^ 2 * r ^ 2) * slope + 512 * (c * r) ^ 2
  have equal : weight =
      1024 * ((columns : InverseRootPolynomial.Coordinate) ^ 2 * ((rows + 1 : Nat) : InverseRootPolynomial.Coordinate) ^
        2 +
        ((columns + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * (rows : InverseRootPolynomial.Coordinate) ^ 2) *
          slope +
      512 * ((columns : InverseRootPolynomial.Coordinate) * (rows : InverseRootPolynomial.Coordinate)) ^ 2 := by
    dsimp only [weight, c, r]
    rewrite [Budget.Aggregate.countCoordinate_eq, Budget.Aggregate.countCoordinate_eq,
      Algebra.NatCast.add, Algebra.NatCast.add, Nat.cast_one]
    exact Eq.refl _
  have nonnegative : 0 ≤ weight := by
    rw [equal]
    exact add_nonneg (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by
      decide +kernel) (shape_nonnegative columns rows)) slopeNonnegative)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.sq_nonneg_direct _))
  let cap := min 1 (Budget.Weighted.allowance target weight)
  exact ⟨weight, equal, cap,
    Basic.lt_min (by decide) (Budget.Weighted.allowance_positive positive nonnegative),
    Basic.min_le_left _ _,
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Basic.min_le_right _ _)
      nonnegative).trans
      (Budget.Weighted.mul_allowance_le positive.le nonnegative)⟩

open Purelib in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Normalization in
/-- Two capped error bounds and two bounded slopes satisfy the full seam-and-corner target estimate.

The calculation retains both error and slope maxima, then pays them through the original rectangular shape weight. -/
theorem pair_bound (budget : ClippedExteriorTolerance columns rows slope target)
    {firstError secondError firstSlope secondSlope : InverseRootPolynomial.Coordinate}
    (firstNonnegative : 0 ≤ firstError) (firstLe : firstError ≤ budget.cap) (secondLe : secondError ≤ budget.cap)
    (slopeNonnegative : 0 ≤ firstSlope) (firstSlopeLe : firstSlope ≤ slope) (secondSlopeLe : secondSlope ≤ slope) :
    4 * ((columns : InverseRootPolynomial.Coordinate) ^ 2 * ((rows + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 +
      ((columns + 1 : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * (rows : InverseRootPolynomial.Coordinate) ^ 2) *
      (8 * max (4 * firstError) (4 * secondError) *
        (4 * max firstSlope secondSlope + max (4 * firstSlope) (4 * secondSlope))) +
      512 * ((columns : InverseRootPolynomial.Coordinate) * (rows : InverseRootPolynomial.Coordinate)) ^ 2 * (max
        firstError secondError) ^ 2 ≤ target := by
  have globalLe : max firstError secondError ≤ budget.cap := Basic.max_le firstLe secondLe
  have globalNonnegative : 0 ≤ max firstError secondError := firstNonnegative.trans (Basic.le_max_left _
    _)
  have fourErrorLe : max (4 * firstError) (4 * secondError) ≤ 4 * budget.cap :=
    Basic.max_le (Arithmetic.mul_le_mul_of_nonneg_left_direct firstLe (by decide))
      (Arithmetic.mul_le_mul_of_nonneg_left_direct secondLe (by decide))
  have factorLe : 4 * max firstSlope secondSlope + max (4 * firstSlope) (4 * secondSlope) ≤ 4 * slope + 4 * slope :=
    add_le_add (Arithmetic.mul_le_mul_of_nonneg_left_direct (Basic.max_le firstSlopeLe
      secondSlopeLe) (by decide))
      (Basic.max_le (Arithmetic.mul_le_mul_of_nonneg_left_direct firstSlopeLe (by decide))
        (Arithmetic.mul_le_mul_of_nonneg_left_direct secondSlopeLe (by decide)))
  have factorNonnegative : 0 ≤ 4 * max firstSlope secondSlope + max (4 * firstSlope) (4 * secondSlope) :=
    add_nonneg (Arithmetic.mul_nonneg_direct (by decide) (slopeNonnegative.trans
      (Basic.le_max_left _ _)))
      ((Arithmetic.mul_nonneg_direct (by decide) slopeNonnegative).trans
        (Basic.le_max_left _ _))
  have seamLe : 8 * max (4 * firstError) (4 * secondError) *
      (4 * max firstSlope secondSlope + max (4 * firstSlope) (4 * secondSlope)) ≤ 256 * budget.cap * slope :=
    ((Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct fourErrorLe (by decide)) factorNonnegative).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct factorLe (Arithmetic.mul_nonneg_direct
        (by decide) (Arithmetic.mul_nonneg_direct (by decide) budget.positive.le)))).trans_eq (by ring1)
  have squareLe : (max firstError secondError) ^ 2 ≤ budget.cap :=
    (Arithmetic.pow_le_pow_direct globalNonnegative globalLe 2).trans
      ((show budget.cap ^ 2 = budget.cap * budget.cap by ring1).le.trans
        ((Arithmetic.mul_le_mul_of_nonneg_right_direct budget.le_one budget.positive.le).trans_eq (by
          ring1)))
  have bound := add_le_add
    (Arithmetic.mul_le_mul_of_nonneg_left_direct seamLe (Arithmetic.mul_nonneg_direct
      (show (0 : InverseRootPolynomial.Coordinate) ≤ 4 by decide) (shape_nonnegative columns
      rows)))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
      (Arithmetic.mul_nonneg_direct (show (0 : InverseRootPolynomial.Coordinate) ≤ 512 by decide +kernel)
        (Arithmetic.sq_nonneg_direct ((columns : InverseRootPolynomial.Coordinate) * (rows :
          InverseRootPolynomial.Coordinate)))))
  apply bound.trans
  apply le_trans (le_of_eq ?_) budget.paid
  rw [budget.weight_eq]
  ring1

end Purelib.Integration.Polynomial.Rectangle.ClippedExteriorTolerance

end
