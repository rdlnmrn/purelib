module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Normalization.RectangularInverseModels
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

/-!
# Uniform rectangular coordinates from an actual cleared box

The axes cache their cuts once. Every cell refines the original box, has the
specified squared diameter, and shares its boundary coordinates literally
with its neighbours. This connects a computed geometric subdivision budget
to the rectangular model and sewing APIs without another mesh certificate.
-/

public section

namespace Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Axis Geometry)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

namespace Axis

/-- The rational cast of the positive cell count is positive. -/
private theorem count_positive (steps : Nat) : (0 : InverseRootPolynomial.Coordinate) < (steps + 1 : Nat) :=
  Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ steps)

/-- Materialize the uniform coordinate cuts in their original finite vector.

The divided endpoint width determines each stored coordinate. Its positivity
and the natural-cast increment certify the strict ordering of consecutive
retained cuts, so later geometry reads the same cache. -/
@[expose] def uniform (steps : Nat) (lower upper : InverseRootPolynomial.Coordinate) (proper : lower < upper) :
  RectangularInverseModels.Axis steps :=
  let width := (upper - lower) / (steps + 1 : Nat)
  have positive : 0 < width := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.sub_pos_direct proper)
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ steps))
  { coordinates := vectorOfFn fun index => lower + (index.val : InverseRootPolynomial.Coordinate) * width
    ordered := fun index => by
      rw [vectorOfFn_apply, vectorOfFn_apply]
      change lower + (index.val : InverseRootPolynomial.Coordinate) * width < lower + (index.val + 1 : Nat) * width
      rw [Algebra.NatCast.add, Nat.cast_one]
      have increase := Fraction.Order.Arithmetic.add_lt_add_left_direct positive
        (lower + (index.val : InverseRootPolynomial.Coordinate) * width)
      rewrite [_root_.add_zero] at increase
      exact increase.trans_eq (by ring1) }

/-- Read the cached uniform coordinate as lower endpoint plus index times width. -/
theorem uniform_coordinate (steps : Nat) (lower upper : InverseRootPolynomial.Coordinate) (proper : lower < upper)
    (index : Fin (steps + 2)) :
    (Axis.uniform steps lower upper proper).coordinates index =
      lower + (index.val : InverseRootPolynomial.Coordinate) * ((upper - lower) / (steps + 1 : Nat)) := by
  unfold Axis.uniform
  rw [vectorOfFn_apply]

/-- The first cached uniform coordinate is the lower endpoint. -/
theorem uniform_first (steps : Nat) (lower upper : InverseRootPolynomial.Coordinate) (proper : lower < upper) :
    (Axis.uniform steps lower upper proper).coordinates 0 = lower := by
  rw [uniform_coordinate]
  change lower + (0 : InverseRootPolynomial.Coordinate) * _ = lower
  ring1

/-- The last cached uniform coordinate is the upper endpoint. -/
theorem uniform_last (steps : Nat) (lower upper : InverseRootPolynomial.Coordinate) (proper : lower < upper) :
    (Axis.uniform steps lower upper proper).coordinates (Fin.last (steps + 1)) = upper := by
  rw [uniform_coordinate]
  change lower + (steps + 1 : Nat) * ((upper - lower) / (steps + 1 : Nat)) = upper
  rw [Fraction.Field.mul_comm,
    Fraction.Field.div_mul_cancel_of_ne _ _ (count_positive steps).ne']
  ring1

/-- All cached uniform coordinates lie between the original endpoints. -/
theorem uniform_between (steps : Nat) (lower upper : InverseRootPolynomial.Coordinate) (proper : lower < upper)
    (index : Fin (steps + 2)) :
    lower ≤ (Axis.uniform steps lower upper proper).coordinates index ∧
      (Axis.uniform steps lower upper proper).coordinates index ≤ upper := by
  rw [uniform_coordinate]
  have widthNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ (upper - lower) / (steps + 1 : Nat) :=
    (Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.sub_pos_direct proper) (count_positive steps)).le
  refine ⟨le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index.val)) widthNonnegative), ?_⟩
  have indexBound : (index.val : InverseRootPolynomial.Coordinate) ≤ (steps + 1 : Nat) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.le_of_lt_succ index.isLt)
  calc
    _ ≤ lower + (steps + 1 : Nat) * ((upper - lower) / (steps + 1 : Nat)) :=
      add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct indexBound widthNonnegative)
    _ = upper := by
      rw [Fraction.Field.mul_comm (steps + 1 : Nat),
        Fraction.Field.div_mul_cancel_of_ne _ _ (count_positive steps).ne']
      ring1

/-- Every consecutive uniform interval has the same divided width.

The natural-cast successor equation isolates one retained coordinate increment; scalar ring transport preserves the
cached axis readbacks. -/
theorem uniform_width (steps : Nat) (lower upper : InverseRootPolynomial.Coordinate) (proper : lower < upper)
    (index : Fin (steps + 1)) :
    (Axis.uniform steps lower upper proper).coordinates index.succ -
      (Axis.uniform steps lower upper proper).coordinates index.castSucc =
        (upper - lower) / (steps + 1 : Nat) := by
  rw [uniform_coordinate, uniform_coordinate]
  change lower + (index.val + 1 : Nat) * _ - (lower + (index.val : InverseRootPolynomial.Coordinate) * _) = _
  rw [Algebra.NatCast.add, Nat.cast_one]
  ring1

set_option genInjectivity false in
/-- A concrete interval and its endpoint certificates, not merely a claim that the union of the intervals covers the
query. -/
structure Located {steps : Nat} (axis : RectangularInverseModels.Axis steps) (point : InverseRootPolynomial.Coordinate)
  where
  /-- The index of a containing cached axis interval. -/ index : Fin (steps + 1)
  /-- The query lies between the selected consecutive cached coordinates. -/ inside : axis.coordinates index.castSucc ≤
    point ∧ point ≤ axis.coordinates index.succ

constructive_injectivity Located

/-- Search a finite cached axis prefix for a closed interval containing the point.

The retained lower bound and last-coordinate upper bound ensure a containing interval is returned with its original
finite index. -/
@[expose] def locatePrefix {steps : Nat} (axis : Purelib.Riemann.Normalization.RectangularInverseModels.Axis steps)
  (point : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate)
    (lower : axis.coordinates 0 ≤ point) :
    (last : Nat) → (bounded : last ≤ steps) →
    point ≤ axis.coordinates ⟨last + 1, by omega⟩ →
      Located axis point
  | 0, _, upper => ⟨0, lower, upper⟩
  | last + 1, bounded, upper =>
      if earlier : point ≤ axis.coordinates ⟨last + 1, by omega⟩ then
        locatePrefix axis point lower last (by
          omega) earlier
      else
        ⟨⟨last + 1, by omega⟩, (le_of_not_ge earlier), upper⟩

/-- Total finite location on the closed axis, including both outer ends. This scan reads cached cuts and allocates no
list of rectangles. -/
@[expose] def locate {steps : Nat} (axis : RectangularInverseModels.Axis steps) (point :
  InverseRootPolynomial.Coordinate)
    (lower : axis.coordinates 0 ≤ point)
    (upper : point ≤ axis.coordinates (Fin.last (steps + 1))) : Located axis point :=
  locatePrefix axis point lower steps (Nat.le_refl _) upper

end Axis

section Geometry

/-- Build a uniform rectangular grid by caching the two uniform axes. -/
@[expose] def uniform (box : InverseRootPolynomial.Box) (proper : box.Proper) (steps : Nat) :
  RectangularInverseModels.Geometry steps steps :=
  ⟨Axis.uniform steps box.xLower box.xUpper proper.1, Axis.uniform steps box.yLower box.yUpper proper.2⟩

/-- Every cell of the uniform rectangular grid refines the original box. -/
theorem uniform_refines (box : InverseRootPolynomial.Box) (proper : box.Proper) (steps : Nat)
    (column row : Fin (steps + 1)) : ((uniform box proper steps).box column row).Refines box :=
  ⟨(Axis.uniform_between steps _ _ proper.1 column.castSucc).1,
    (Axis.uniform_between steps _ _ proper.1 column.succ).2,
    (Axis.uniform_between steps _ _ proper.2 row.castSucc).1,
    (Axis.uniform_between steps _ _ proper.2 row.succ).2⟩

/-- The first uniform cell has the original box's anchor. -/
theorem uniform_anchor (box : InverseRootPolynomial.Box) (proper : box.Proper) (steps : Nat) :
    ((uniform box proper steps).box 0 0).anchor = box.anchor := by
  apply Data.Gaussian.Basic.ext
  · exact Axis.uniform_first steps _ _ proper.1
  · exact Axis.uniform_first steps _ _ proper.2

set_option genInjectivity false in
/-- A retained pair of cell indices containing the point.

The containment certificate refers to the exact box read from the supplied rectangular geometry. -/
structure Located {columns rows : Nat} (geometry : RectangularInverseModels.Geometry columns rows) (point :
  InverseRootPolynomial.Gaussian) where
  /-- The retained containing column index. -/ column : Fin (columns + 1)
  /-- The retained containing row index. -/ row : Fin (rows + 1)
  /-- The point lies in the closed box selected by these indices. -/ inside : (geometry.box column row).Contains point

constructive_injectivity Located

/-- An actual cell covering any point of the original face; generated locations can instead supply their indices and
four exact inequalities. -/
@[expose] def locateUniform (box : InverseRootPolynomial.Box) (proper : box.Proper) (steps : Nat) (point :
  InverseRootPolynomial.Gaussian)
    (inside : box.Contains point) : Located (uniform box proper steps) point :=
  let horizontal := Axis.locate (Axis.uniform steps box.xLower box.xUpper proper.1) point.re
    ((Axis.uniform_first steps _ _ proper.1).trans_le inside.1)
    (inside.2.1.trans_eq (Axis.uniform_last steps _ _ proper.1).symm)
  let vertical := Axis.locate (Axis.uniform steps box.yLower box.yUpper proper.2) point.im
    ((Axis.uniform_first steps _ _ proper.2).trans_le inside.2.2.1)
    (inside.2.2.2.trans_eq (Axis.uniform_last steps _ _ proper.2).symm)
  ⟨horizontal.index, vertical.index, horizontal.inside.1, horizontal.inside.2,
    vertical.inside.1, vertical.inside.2⟩

/-- Uniform cell squared diagonals equal the original divided by the square of the cell count. -/
theorem uniform_diagonalSq (box : InverseRootPolynomial.Box) (proper : box.Proper) (steps : Nat)
    (column row : Fin (steps + 1)) :
    ((uniform box proper steps).box column row).diagonalSq =
      box.diagonalSq / (steps + 1 : Nat) ^ (2 : Nat) := by
  change (_ - _) ^ 2 + (_ - _) ^ 2 = _
  dsimp only [uniform, Geometry.box]
  rw [Axis.uniform_width, Axis.uniform_width]
  change (box.widthX / _) ^ 2 + (box.widthY / _) ^ 2 = (box.widthX ^ 2 + box.widthY ^ 2) / _
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.inv_pow_direct]
  ring1

/-- Count the interior cuts at the displayed dyadic spatial depth.

The original natural power gives one more cell than interior cuts. Natural
subtraction retains exactly that interior count, including the zero-depth case. -/
@[expose] def dyadicSteps (depth : Nat) : Nat := Nat.pow 2 depth - 1

/-- The dyadic interior-cut count plus one is exactly two to the depth.

Positivity of the displayed natural power ensures that the preceding natural subtraction reconstructs the full cell
count. -/
theorem dyadicSteps_count (depth : Nat) : dyadicSteps depth + 1 = Nat.pow 2 depth := by
  have positive : 0 < Nat.pow 2 depth := Nat.pow_pos (by decide)
  unfold dyadicSteps
  omega

/-- At dyadic depth, every uniform cell has the specified quarter-radius squared diagonal.

The explicit natural power is cast through its multiplication recurrence. The retained width formula then identifies
exactly the original quarter-radius value. -/
theorem uniform_dyadic_diagonalSq (box : InverseRootPolynomial.Box) (proper : box.Proper) (depth : Nat)
    (column row : Fin (dyadicSteps depth + 1)) :
    ((uniform box proper (dyadicSteps depth)).box column row).diagonalSq =
      Geometric.Basic.quarterRadius box.diagonalSq depth := by
  rw [uniform_diagonalSq, dyadicSteps_count]
  have castPower : ((Nat.pow 2 depth : Nat) : InverseRootPolynomial.Coordinate) =
      (2 : InverseRootPolynomial.Coordinate) ^ depth := by
    clear column row
    induction depth with
    | zero => rfl
    | succ depth ih =>
        change ((Nat.pow 2 depth * 2 : Nat) : InverseRootPolynomial.Coordinate) = _
        rewrite [Algebra.NatCast.mul, ih, pow_succ]
        rfl
  rw [castPower]
  have powers : ((2 : InverseRootPolynomial.Coordinate) ^ depth) ^ 2 = (4 : InverseRootPolynomial.Coordinate) ^ depth :=
    by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    rw [show (2 : InverseRootPolynomial.Coordinate) ^ 2 = 4 by decide]
  rw [powers]
  rfl

end Geometry

end Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry

end
