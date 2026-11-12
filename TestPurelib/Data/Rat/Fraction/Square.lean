module

import Purelib.Data.Rat.Fraction.Square.Check
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast

/-!
# Exact square admission and canonical-coordinate obstructions

Closed computations exercise zero, signs, normalization and denominator-only
obstructions. The same retained inspections exclude every rational candidate,
including candidates whose numerators and denominators are not bounded by the
original inspected coordinates.
-/

namespace TestPurelib.Data.Rat.Fraction.Square

open Purelib.Data.Rat.Fraction

example : (Square.inspect 0).root? = some 0 := by decide +kernel
example : (Square.inspect 1).root? = some 1 := by decide +kernel
example : (Square.inspect (4 / 9)).root? = some (2 / 3) := by decide +kernel
example : (Square.inspect (9 / 4)).root? = some (3 / 2) := by decide +kernel
example : (Square.inspect (4 / 16)).root? = some (1 / 2) := by decide +kernel
example : (Square.inspect (Cast.fromInt 11025)).root? = some (Cast.fromInt 105) := by decide +kernel

example (candidate : Rational) : candidate * candidate ≠ 2 :=
  (Square.inspect 2).not_square_of_missing (by decide +kernel) candidate

example (candidate : Rational) : candidate * candidate ≠ 1 / 2 :=
  (Square.inspect (1 / 2)).not_square_of_missing (by decide +kernel) candidate

example (candidate : Rational) : candidate * candidate ≠ -4 :=
  (Square.inspect (-4)).not_square_of_missing (by decide +kernel) candidate

example : (Square.inspect (4 / 16)).value = (4 / 16 : Rational) := rfl

/-- The denominator obstruction retains the completed numerator floor and its own original floor. -/
private def denominatorFloors {value : Rational} : Square.Outcome value → Option (Nat × Nat)
  | .denominator numerator _ denominator _ _ => some (numerator.root, denominator.root)
  | _ => none

example : denominatorFloors (Square.inspect (1 / 2)).result = some (1, 1) := by decide +kernel

end TestPurelib.Data.Rat.Fraction.Square
