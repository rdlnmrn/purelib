module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
public import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Shifted Legendre polynomial clearance on the identical original patch

One quarter of the existing whole-box increment allocation pays the
original affine parameter coefficient uniformly. The shifted cubic then
retains one quarter of the original radicand floor throughout that same
closed box. This constructs polynomial clearance, without choosing a
shifted sheet, continuation radius, source query or geometric cycle.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Bounds
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)

/-- Quarter the original whole-box parameter allocation to retain a positive shifted polynomial floor. -/
@[expose] def shiftedBound : Rational := range.bound / 4

/-- The computed shifted-polynomial parameter allocation is strictly positive. -/
theorem shiftedBound_positive : 0 < range.shiftedBound := Quarter.quarter_pos range.bound_positive

/-- The tighter shifted-polynomial allocation also admits the original point continuation. -/
theorem shiftedBound_le_bound : range.shiftedBound ≤ range.bound :=
  Order.Field.divide_le_self range.bound_positive.le (by decide +kernel : (1 : Rational) ≤ 4)

/-- The identical box and cached affine coefficient pay a quarter of its original radicand floor.

The bound holds at every point in the closed original box, independently
of observation stage or selected node. Both polynomial evaluations retain
the exact original parameter and its admitted increment.
-/
theorem movement_lt_quarter (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.shiftedBound) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point) < (patch.base.site.denominatorValue / 4) / 4 := by
  have identity : (Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point = increment * Polynomials.baseValue point := by
    rewrite [radicand_eq, radicand_eq, Variation.radicand_step]
    ring1
  have paid : range.coefficient * range.bound < patch.base.site.denominatorValue / 4 := by
    have allocated := Order.Field.mul_min_one_div_lt range.coefficient_nonnegative
      (Order.Basic.lt_min range.contour_positive
        (Quarter.quarter_pos patch.base.site.denominatorValue_positive))
    change range.coefficient * range.bound < min range.contour (patch.base.site.denominatorValue / 4) at allocated
    exact allocated.trans_le (Order.Basic.min_le_right _ _)
  have quarterPaid : (range.coefficient * range.bound) / 4 < (patch.base.site.denominatorValue / 4) / 4 := by
    apply (Order.Field.lt_div_iff_pos (by decide +kernel : (0 : Rational) < 4)).mpr
    rewrite [Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (4 : Rational) ≠ 0)]
    exact paid
  have product := Order.Arithmetic.mul_le_mul_direct admitted (range.coefficient_upper inside)
    (Norm.Basic.normSq_nonneg (Polynomials.baseValue point)) range.shiftedBound_positive.le
  rewrite [identity, Norm.Basic.normSq_mul]
  calc
    _ ≤ range.shiftedBound * range.coefficient := product
    _ = (range.coefficient * range.bound) / 4 := by
      unfold shiftedBound
      rewrite [Field.div_eq_mul_inv_direct, Field.div_eq_mul_inv_direct]
      ring1
    _ < _ := quarterPaid

/-- The shifted cubic retains a positive quarter of the original denominator floor throughout the same physical box. -/
theorem shifted_lower (inside : patch.box.Contains point) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.shiftedBound) :
    (patch.base.site.denominatorValue / 4) / 4 ≤
      Norm.Basic.normSq ((Paths.polynomial (parameter + increment)).eval point) := by
  let floor := patch.base.site.denominatorValue / 4
  have original : floor ≤ Norm.Basic.normSq ((Paths.polynomial parameter).eval point) := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact patch.parameter_lower inside
  have half := Order.Field.divide_mono original (by decide +kernel : (0 : Rational) < 2)
  have movement := range.movement_lt_quarter inside increment admitted
  have comparison := Order.Arithmetic.sub_le_sub_direct half movement.le
  have estimate := Norm.Bounds.half_normSq_sub_le_normSq_sub ((Paths.polynomial parameter).eval point)
    ((Paths.polynomial parameter).eval point - (Paths.polynomial (parameter + increment)).eval point)
  rewrite [show (Paths.polynomial parameter).eval point -
    ((Paths.polynomial parameter).eval point - (Paths.polynomial (parameter + increment)).eval point) =
      (Paths.polynomial (parameter + increment)).eval point by ring1] at estimate
  have quarterIdentity : floor / 4 = floor / 2 - floor / 4 := by
    calc
      _ = (floor / 4 + floor / 4) - floor / 4 := by ring1
      _ = _ := congrArg (fun value : Rational => value - floor / 4) (Quarter.two_quarters floor)
  exact quarterIdentity.trans_le (comparison.trans estimate)

/-- Construct quantitative clearance for the actual changed polynomial on the identical original closed box.

The original site's denominator floor and retained coefficient allocation
supply all data and inequalities. No shifted query, root owner, signed
continuation or equality of period programmes is an input or conclusion.
-/
def shiftedClearance (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.shiftedBound) :
    RegionClearance (Paths.polynomial (parameter + increment)) patch.box :=
  { bound := (patch.base.site.denominatorValue / 4) / 4
    positive := Quarter.quarter_pos (Quarter.quarter_pos patch.base.site.denominatorValue_positive)
    lower := fun _ inside => range.shifted_lower inside increment admitted }

/-- The shifted region certificate retains the computed floor from the identical original observation site. -/
theorem shiftedClearance_bound (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.shiftedBound) :
    (range.shiftedClearance increment admitted).bound = (patch.base.site.denominatorValue / 4) / 4 := by
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
