import DivineProportions.Trigonometry.QuadTripleExercises
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Exercise 5.9

The braces in the source are treated as an unordered triple: any one entry
may be `(a+b)²`, with the other two equal to `a²` and `b²`.  The explicit
quad triple `{3,3,12}` is not of that form over the constructive rationals,
because its two repeated entries would require a rational square root of
three.  The nonsquare certificate comes from the computable reduced fraction,
not from real-number completeness or an infinite descent object.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The unordered triple `{first, second, third}` has the special squared-sum
form `{a²,b²,(a+b)²}` requested in Exercise 5.9. -/
def IsSquaredSumTriple (first second third : K) : Prop :=
  ∃ a b : K,
    (first = a ^ 2 ∧ second = b ^ 2 ∧ third = (a + b) ^ 2) ∨
    (first = a ^ 2 ∧ third = b ^ 2 ∧ second = (a + b) ^ 2) ∨
    (second = a ^ 2 ∧ third = b ^ 2 ∧ first = (a + b) ^ 2)

/-- Generic finite core of Exercise 5.9: in any explicit field where `3` is
not a square, `{3,3,12}` is a quad triple but not a squared-sum triple. -/
theorem exercise_5_9_of_three_not_square
    (threeNotSquare : ∀ value : K, value ^ 2 ≠ 3) :
    QuadTriple (3 : K) 3 12 ∧ ¬ IsSquaredSumTriple (3 : K) 3 12 := by
  constructor
  · unfold QuadTriple archimedesFunction
    ring1
  · rintro ⟨a, b, ordered | firstAndThird | secondAndThird⟩
    · exact threeNotSquare a ordered.1.symm
    · exact threeNotSquare a firstAndThird.1.symm
    · exact threeNotSquare a secondAndThird.1.symm

namespace ExerciseFiveNine

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- Exercise 5.9's closed constructive-rational counterexample. -/
theorem exercise_5_9 :
    QuadTriple (3 : Rational) 3 12 ∧
      ¬ IsSquaredSumTriple (3 : Rational) 3 12 := by
  apply exercise_5_9_of_three_not_square
  exact RFAP.ConstructiveFraction.square_ne_three

end ExerciseFiveNine

end DivineProportions
