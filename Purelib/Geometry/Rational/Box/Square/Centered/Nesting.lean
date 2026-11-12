module

public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Translated equal-radius squares in one fixed doubled square

The original contained center and original radius bound all four translated
endpoints. The conclusion is refinement of the original rational boxes;
neither their points nor any preparation owners are identified or replaced.
-/

public section

namespace Purelib.Geometry.Rational.Box.Square.Centered

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- Moving a square's center inside the original equal-radius square keeps it inside that fixed doubled square. -/
theorem translated_refines_double {first last : Canonical} {radius : Fraction.Rational}
    (nonnegative : 0 ≤ radius) (inside : (Affine.centeredSquare first radius nonnegative).Contains last) :
    (Affine.centeredSquare last radius nonnegative).Refines
      (Affine.centeredSquare first (2 * radius)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl) nonnegative)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (show first.re - 2 * radius = (first.re - radius) - radius by ring1).trans_le
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.1 radius)
  · exact (Fraction.Order.Arithmetic.add_le_add_direct inside.2.1 (Fraction.Order.Basic.le_refl radius)).trans_eq
      (show (first.re + radius) + radius = first.re + 2 * radius by ring1)
  · exact (show first.im - 2 * radius = (first.im - radius) - radius by ring1).trans_le
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.1 radius)
  · exact (Fraction.Order.Arithmetic.add_le_add_direct inside.2.2.2 (Fraction.Order.Basic.le_refl radius)).trans_eq
      (show (first.im + radius) + radius = first.im + 2 * radius by ring1)

end Purelib.Geometry.Rational.Box.Square.Centered

end
