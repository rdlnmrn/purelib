module
public import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Protected-boundary scalar thresholds

The fixed rational scale and nested threshold retain the displayed box widths,
clearance and Lipschitz inputs.
-/

namespace Purelib.Geometry.Rational.Box.Boundary.Budget

open Purelib.Data.Rat
open Purelib.Geometry.Rational

/-- The exact rational scale used by the protected-boundary radius cap.

The exact rational factor is eight times eight times eight. This retained
scale converts the displayed quadratic displacement estimates into the
same linear radius cap used by the protected-boundary thresholds. -/
@[expose] public def protectedBoundaryScale : Fraction.Rational := (8 : Fraction.Rational) * 8 * 8

/-- The fixed protected-boundary scale is positive.

Each of the three retained rational factors is positive. Direct scalar
multiplication positivity therefore certifies the exact displayed scale
without replacing its factors or numeral operations. -/
public theorem protectedBoundaryScale_pos :
    0 < protectedBoundaryScale := by
  unfold protectedBoundaryScale
  have eightPositive : (0 : Fraction.Rational) < 8 :=
    Fraction.Cast.Order.natCast_pos_direct (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct eightPositive eightPositive)
    eightPositive

/-- The radius threshold determined by a box, clearance and Lipschitz value.

The same reciprocal scale cap, clearance-to-Lipschitz quotient and two
one-sixteenth side widths are retained in their original nested minima.
Only the displayed finite box and scalar inputs determine the value. -/
@[expose] public def predictedProtectedRadiusData
    (ambient : Box) (clearanceBound lipschitz : Fraction.Rational) : Fraction.Rational :=
  min (1 / protectedBoundaryScale)
    (min (clearanceBound / (2 * lipschitz))
      (min (ambient.widthX / 16) (ambient.widthY / 16)))

/-- Positive side lengths, clearance and Lipschitz bound give a positive protected radius.

A proper box has positive side widths, and the supplied clearance and
Lipschitz quantities are positive. These conditions make every retained
quotient positive and hence certify the same nested minimum. -/
public theorem predictedProtectedRadiusData_pos
    {ambient : Box} {clearanceBound lipschitz : Fraction.Rational}
    (proper : ambient.Proper) (clearancePositive : 0 < clearanceBound)
    (lipschitzPositive : 0 < lipschitz) :
    0 < predictedProtectedRadiusData ambient clearanceBound lipschitz := by
  have scalePositive : 0 < protectedBoundaryScale := by
    unfold protectedBoundaryScale
    exact Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide) (by decide))
      (by decide)
  exact Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct (by decide) scalePositive)
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Field.div_pos_direct clearancePositive
        (Fraction.Order.Arithmetic.mul_pos_direct
          (by decide) lipschitzPositive))
      (Fraction.Order.Basic.lt_min
        (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Arithmetic.sub_pos_direct proper.1) (by decide))
        (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Arithmetic.sub_pos_direct proper.2) (by decide))))

end Purelib.Geometry.Rational.Box.Boundary.Budget
