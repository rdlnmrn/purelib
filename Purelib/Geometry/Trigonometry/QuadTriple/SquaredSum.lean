module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Exercise 5.9

The braces in the source are treated as an unordered triple: any one entry
may be `(a+b)²`, with the other two equal to `a²` and `b²`.  The explicit
quad triple `{3,3,12}` is not of that form over the constructive rationals,
because its two repeated entries would require a rational square root of
three.  The nonsquare certificate comes from the computable reduced fraction,
not from real-number completeness or an infinite descent object.
-/

namespace Purelib.Geometry.Trigonometry.QuadTriple.SquaredSum

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The unordered triple `{first, second, third}` has the special squared-sum form `{a²,b²,(a+b)²}` requested in
Exercise 5.9. -/
def IsSquaredSumTriple (first second third : K) : Prop :=
  ∃ a b : K,
    (first = a ^ 2 ∧ second = b ^ 2 ∧ third = (a + b) ^ 2) ∨
    (first = a ^ 2 ∧ third = b ^ 2 ∧ second = (a + b) ^ 2) ∨
    (second = a ^ 2 ∧ third = b ^ 2 ∧ first = (a + b) ^ 2)

/-- Generic finite core of Exercise 5.9: in any explicit field where `3` is not a square, `{3,3,12}` is a quad triple
but not a squared-sum triple. -/
theorem exercise_5_9_of_three_not_square
    (threeNotSquare : ∀ value : K, value ^ 2 ≠ 3) :
    Trigonometry.QuadTriple (3 : K) 3 12 ∧ ¬ IsSquaredSumTriple (3 : K)
      3 12 := by
  constructor
  · unfold Trigonometry.QuadTriple QuadTriple.Basic.archimedesFunction
    ring1
  · rintro ⟨a, b, ordered | firstAndThird | secondAndThird⟩
    · exact threeNotSquare a ordered.1.symm
    · exact threeNotSquare a firstAndThird.1.symm
    · exact threeNotSquare a secondAndThird.1.symm

end Purelib.Geometry.Trigonometry.QuadTriple.SquaredSum

end
