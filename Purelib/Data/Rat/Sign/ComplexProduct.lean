module

public import Purelib.Data.Rat.Sign.Typed
public import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Rat.Sign.Typed.Sum
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.Sum
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Rational readback of formal complex-product signs

Multiplication and addition of the original rational coordinates retain the
formal sign compatibility conditions for both complex-product coordinates.
-/

namespace Purelib.Data.Rat.Sign.ComplexProduct

open Purelib.Data.Rat
open _root_.Purelib.Data renaming Sign -> FiniteSign

/-- Rational complex-product signs satisfy the formal coordinate compatibility relation.

The real output is the sign of AC minus BD and the imaginary output is the
sign of AD plus BC. The retained coordinate products satisfy the corresponding
formal sum restrictions without requiring their magnitudes. -/
public theorem sign_complexProductCompatible
    (A B C D : Fraction.Rational) :
    FiniteSign.ComplexProductCompatible
      (FiniteSign.ofCoordinate A) (FiniteSign.ofCoordinate B)
      (FiniteSign.ofCoordinate C) (FiniteSign.ofCoordinate D)
      (FiniteSign.ofCoordinate (A * C - B * D))
      (FiniteSign.ofCoordinate (A * D + B * C)) := by
  constructor
  · change FiniteSign.SumCompatible
      (FiniteSign.mul (FiniteSign.ofCoordinate A)
        (FiniteSign.ofCoordinate C))
      (FiniteSign.neg (FiniteSign.mul (FiniteSign.ofCoordinate B)
        (FiniteSign.ofCoordinate D)))
      (FiniteSign.ofCoordinate (A * C + -(B * D)))
    rw [← FiniteSign.ofCoordinate_mul A C,
      ← FiniteSign.ofCoordinate_mul B D,
      ← FiniteSign.ofCoordinate_neg]
    exact FiniteSign.sumCompatible_ofCoordinate (A * C) (-(B * D))
  · rw [← FiniteSign.ofCoordinate_mul A D,
      ← FiniteSign.ofCoordinate_mul B C]
    exact FiniteSign.sumCompatible_ofCoordinate (A * D) (B * C)

end Purelib.Data.Rat.Sign.ComplexProduct
