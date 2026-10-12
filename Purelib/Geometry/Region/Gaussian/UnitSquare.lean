module

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Square
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# The half-open Gaussian unit square

The original four rational coordinate inequalities specify the half-open
unit square. They directly bound the retained Gaussian quadrance by two.
-/

namespace Purelib.Geometry.Region.Gaussian.UnitSquare

open Purelib
open Purelib.Data.Rat

/-- The half-open Gaussian coordinate unit square.

The original real and imaginary coordinates are each nonnegative and strictly
less than one; the four inequalities retain those exact coordinates. -/
@[expose] public def Sq (z : Data.Gaussian.Basic.Canonical) : Prop :=
  0 ≤ z.re ∧ z.re < 1 ∧ 0 ≤ z.im ∧ z.im < 1

/-- Every Gaussian point in the half-open unit square has quadrance below two.

Both coordinates lie in `[0,1)`, so each coordinate square is strictly below one. -/
public theorem normSq_lt_two_of_sq {z : Data.Gaussian.Basic.Canonical} (inside : Geometry.Region.Gaussian.UnitSquare.Sq
  z) :
    Data.Gaussian.Norm.Basic.normSq z < 2 := by
  rcases inside with ⟨realNonnegative, realSmall,
    imagNonnegative, imagSmall⟩
  have realSquare := Fraction.Order.Square.square_lt_one_of_unit realNonnegative realSmall
  have imagSquare := Fraction.Order.Square.square_lt_one_of_unit imagNonnegative imagSmall
  have sum := Fraction.Order.Arithmetic.add_lt_add_direct
    realSquare imagSquare
  calc
    Data.Gaussian.Norm.Basic.normSq z = z.re ^ 2 + z.im ^ 2 := rfl
    _ < 1 + 1 := sum
    _ = 2 := by ring1

end Purelib.Geometry.Region.Gaussian.UnitSquare
