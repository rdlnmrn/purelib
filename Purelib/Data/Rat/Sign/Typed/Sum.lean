module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
public import Purelib.Data.Sign.Sum
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

namespace Purelib.Data.Sign

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open _root_.Purelib.Data renaming Sign -> FiniteSign

-- The established finite-sign method namespace repeats its subject's basename.
/-- The finite signs of two rationals and their sum satisfy the exact finite addition compatibility relation.

The original rational classifier assigns the three finite signs to both
summands and their retained sum. Equal nonzero signs are preserved by
direct strict translations; opposite signs keep the formal sum unrestricted. -/
public theorem sumCompatible_ofCoordinate (x y : Fraction.Rational) :
    FiniteSign.SumCompatible (FiniteSign.ofCoordinate x) (FiniteSign.ofCoordinate y)
      (FiniteSign.ofCoordinate (x + y)) := by
  rcases lt_trichotomy x 0 with negativeX | rfl | positiveX <;>
    rcases lt_trichotomy y 0 with negativeY | rfl | positiveY
  · have sumNegative : x + y < 0 := by
      calc
        x + y < 0 + y := Arithmetic.add_lt_add_right_direct negativeX y
        _ = y := zero_add y
        _ < 0 := negativeY
    rw [FiniteSign.ofCoordinate_of_neg negativeX, FiniteSign.ofCoordinate_of_neg negativeY,
      FiniteSign.ofCoordinate_of_neg sumNegative]
    trivial
  · rw [add_zero, FiniteSign.ofCoordinate_of_neg negativeX]
    trivial
  · rw [FiniteSign.ofCoordinate_of_neg negativeX, FiniteSign.ofCoordinate_of_pos positiveY]
    trivial
  · rw [zero_add, FiniteSign.ofCoordinate_of_neg negativeY]
    trivial
  · trivial
  · rw [zero_add, FiniteSign.ofCoordinate_of_pos positiveY]
    trivial
  · rw [FiniteSign.ofCoordinate_of_pos positiveX, FiniteSign.ofCoordinate_of_neg negativeY]
    trivial
  · rw [add_zero, FiniteSign.ofCoordinate_of_pos positiveX]
    trivial
  · have sumPositive : 0 < x + y :=
      Arithmetic.add_pos_of_pos_of_nonneg_direct positiveX positiveY.le
    rw [FiniteSign.ofCoordinate_of_pos positiveX, FiniteSign.ofCoordinate_of_pos positiveY,
      FiniteSign.ofCoordinate_of_pos sumPositive]
    trivial

end Purelib.Data.Sign
