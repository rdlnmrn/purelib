module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Banks
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Bounds
import Purelib.Data.Gaussian.Components.Projection.Negation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Quantified cap geometry at the original Legendre branch endpoints

The original first quarter leaves the moving labelled branch and the original
third quarter leaves the fixed labelled branch. Their exact conic geometry
gives fourth-power squared base displacement and second-power squared
normalized ordinate bounds. Reflection retains the same original cubic base
and negates its normalized ordinate, so both signed banks pay the same bounds.
These bounds pay local cap geometry; canonical cut/homotopy comparisons remain
separate obligations.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.BranchCaps

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle

/-- The original first-quarter direction has the identical original stereographic reading. -/
private theorem first_direction (time : Fraction.Rational) :
    (direction .first time).value = Stereographic.unitQuarterPoint time := by
  rewrite [direction_value]
  change (1 : Canonical) * Stereographic.unitQuarterPoint time = _
  exact Basic.one_mul _

/-- The original third-quarter direction negates the identical original stereographic reading. -/
private theorem third_direction (time : Fraction.Rational) :
    (direction .third time).value = -Stereographic.unitQuarterPoint time := by
  rewrite [direction_value]
  change (-1 : Canonical) * Stereographic.unitQuarterPoint time = _
  ring1

variable (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
variable (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))

/-- The actual moving-branch cap base displacement retains the original half-gap and real projection. -/
theorem moving_base (time : Fraction.Rational) :
    (point site parameter (direction .first time) regular bound).base - Paths.branchPoint parameter 1 =
      halfGap site parameter * (Components.Projection.realPart (Stereographic.unitQuarterPoint time) - 1) := by
  rewrite [point_base, first_direction, ← center_add_halfGap site parameter]
  ring1

/-- The actual moving-branch cap normalized ordinate retains the original half-gap and imaginary projection. -/
theorem moving_ordinate (time : Fraction.Rational) :
    (point site parameter (direction .first time) regular bound).ordinate =
      halfGap site parameter * Components.Projection.imaginaryPart (Stereographic.unitQuarterPoint time) := by
  rewrite [point_ordinate, first_direction]
  rfl

/-- The actual fixed-branch cap base displacement is the opposite signed original real displacement. -/
theorem fixed_base (time : Fraction.Rational) :
    (point site parameter (direction .third time) regular bound).base -
        Paths.branchPoint parameter (fixedLabel site) =
      -(halfGap site parameter * (Components.Projection.realPart (Stereographic.unitQuarterPoint time) - 1)) := by
  rewrite [point_base, third_direction, Components.Projection.realPart_neg, ← center_sub_halfGap site parameter]
  ring1

/-- The actual fixed-branch cap normalized ordinate is the opposite signed original imaginary displacement. -/
theorem fixed_ordinate (time : Fraction.Rational) :
    (point site parameter (direction .third time) regular bound).ordinate =
      -(halfGap site parameter * Components.Projection.imaginaryPart (Stereographic.unitQuarterPoint time)) := by
  rewrite [point_ordinate, third_direction, Components.Projection.imaginaryPart_neg]
  ring1

/-- The moving-branch cap has a quantified fourth-power squared base-displacement bound. -/
theorem moving_base_normSq_le (time : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter (direction .first time) regular bound).base -
      Paths.branchPoint parameter 1) ≤ 4 * Norm.Basic.normSq (halfGap site parameter) * time ^ 4 := by
  rewrite [moving_base, Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * (4 * time ^ 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Stereographic.real_displacement_normSq_le time) (Norm.Basic.normSq_nonneg _)
    _ = _ := by ring1

/-- The moving-branch cap has a quantified second-power squared normalized-ordinate bound. -/
theorem moving_ordinate_normSq_le (time : Fraction.Rational) :
    Norm.Basic.normSq (point site parameter (direction .first time) regular bound).ordinate ≤
      4 * Norm.Basic.normSq (halfGap site parameter) * time ^ 2 := by
  rewrite [moving_ordinate, Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * (4 * time ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Stereographic.imaginary_normSq_le time) (Norm.Basic.normSq_nonneg _)
    _ = _ := by ring1

/-- The fixed-branch cap has the same quantified fourth-power squared base-displacement bound. -/
theorem fixed_base_normSq_le (time : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter (direction .third time) regular bound).base -
      Paths.branchPoint parameter (fixedLabel site)) ≤ 4 * Norm.Basic.normSq (halfGap site parameter) * time ^ 4 := by
  rewrite [fixed_base, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * (4 * time ^ 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Stereographic.real_displacement_normSq_le time) (Norm.Basic.normSq_nonneg _)
    _ = _ := by ring1

/-- The fixed-branch cap has the same quantified second-power squared normalized-ordinate bound. -/
theorem fixed_ordinate_normSq_le (time : Fraction.Rational) :
    Norm.Basic.normSq (point site parameter (direction .third time) regular bound).ordinate ≤
      4 * Norm.Basic.normSq (halfGap site parameter) * time ^ 2 := by
  rewrite [fixed_ordinate, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul]
  calc
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * (4 * time ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Stereographic.imaginary_normSq_le time) (Norm.Basic.normSq_nonneg _)
    _ = _ := by ring1

/-- Reflection preserves each actual cap's original base displacement to its retained branch endpoint. -/
theorem mirrored_base (original : Basic.UnitVertex) (endpoint : Canonical) :
    (point site parameter (Banks.mirror original) regular bound).base - endpoint =
      (point site parameter original regular bound).base - endpoint := by
  rewrite [Banks.point_mirror, Point.exchange_base]
  rfl

/-- Reflection preserves each actual cap's squared normalized ordinate on the same original conic owner. -/
theorem mirrored_ordinate_normSq (original : Basic.UnitVertex) :
    Norm.Basic.normSq (point site parameter (Banks.mirror original) regular bound).ordinate =
      Norm.Basic.normSq (point site parameter original regular bound).ordinate := by
  rewrite [Banks.point_mirror, Point.exchange_ordinate, Norm.Basic.normSq_neg]
  rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.BranchCaps
