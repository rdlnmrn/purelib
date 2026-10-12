module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Sign.Jump
public import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Positive rational factors and finite sign jumps

A strictly positive rational factor preserves the finite sign used by a
Cauchy-index jump. The displayed jump identity retains both original factors.
-/

namespace Purelib.Data.Rat.Sign.CauchyIndex.HalfPlane

open Purelib.Data.Rat in
open _root_.Purelib.Data renaming Sign -> FiniteSign in
/-- A positive rational factor identifies the finite jump from the positive sign with the jump to the product sign. -/
public theorem jump_positive_eq_signJump_mul
    {r s : Fraction.Rational} (positive : 0 < r) :
    FiniteSign.jump .positive (FiniteSign.ofCoordinate s) =
      Sign.Jump.signJump 1 (r * s) := by
  rw [← FiniteSign.jump_ofCoordinate]
  rw [FiniteSign.ofCoordinate_of_pos (by decide : (0 : Fraction.Rational) < 1),
    FiniteSign.ofCoordinate_mul r s,
    FiniteSign.ofCoordinate_of_pos positive]
  cases FiniteSign.ofCoordinate s <;> rfl

end Purelib.Data.Rat.Sign.CauchyIndex.HalfPlane

end
