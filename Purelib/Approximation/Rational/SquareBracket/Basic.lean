module

public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite dyadic square brackets

A bounded natural recursion selects a positive dyadic rational whose square
lies immediately above a displayed target in `(0, 1)`.  It then performs a
coefficient-computed finite number of rational bisections.  Given any
displayed rational factor greater than one, the returned square lies above
the target and at most that factor times it.  No square root or limiting
object is used.
-/

namespace Purelib.Approximation.Rational.SquareBracket.Basic

set_option genInjectivity false in
/-- A positive dyadic scale whose square brackets a positive target from above, within the factor four caused by one
halving step. -/
structure Bracket (target : Fraction.Rational) where
  /-- The retained rational radius of the square bracket. -/ radius : Fraction.Rational
  /-- The retained radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- The radius squared strictly exceeds the target. -/ target_lt_square : target < radius ^ 2
  /-- The radius squared is at most four times the target. -/ square_le_four_target : radius ^ 2 <= 4 * target

constructive_injectivity Bracket

end Purelib.Approximation.Rational.SquareBracket.Basic

end
