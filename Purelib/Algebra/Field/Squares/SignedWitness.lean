module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

section
public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Algebra.Field.Squares.SignedWitness

section ThreeDimensionalProblems

variable {K : Type*} [ExplicitField K]

/-- A candidate is a signed height when its square equals the supplied height square. -/
@[expose] def IsSignedHeight (height candidate : K) : Prop :=
  candidate ^ 2 = height ^ 2

open Purelib.Algebra.Field.Squares in
/-- A nonzero height has exactly its two distinct signed square roots.

Decidable equality and nonzero two show that the height and its negative are distinct and exhaust all candidates with
the same square. -/
theorem exercise_22_3_two_completions [DecidableEq K]
    (height : K) (heightNonzero : height ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    IsSignedHeight height height ∧
      IsSignedHeight height (-height) ∧
      height ≠ -height ∧
      ∀ candidate : K,
        IsSignedHeight height candidate →
          candidate = height ∨ candidate = -height := by
  have signsDistinct : height ≠ -height := by
    intro signsEqual
    have productZero : (2 : K) * height = 0 := by
      calc
        2 * height = height + height := by ring1
        _ = -height + height := congrArg (fun value => value + height) signsEqual
        _ = 0 := by ring1
    exact (ExplicitField.mul_ne_zero twoNonzero heightNonzero) productZero
  refine ⟨rfl, ?_, signsDistinct, ?_⟩
  · unfold IsSignedHeight
    ring1
  · intro candidate candidateSquare
    unfold IsSignedHeight at candidateSquare
    have productZero : (candidate - height) * (candidate + height) = 0 := by
      calc
        (candidate - height) * (candidate + height) =
            candidate ^ 2 - height ^ 2 := by ring1
        _ = 0 := by rw [candidateSquare]; ring1
    by_cases firstFactor : candidate - height = 0
    · left
      calc
        candidate = (candidate - height) + height := by ring1
        _ = height := by rw [firstFactor]; ring1
    · right
      have secondFactor : candidate + height = 0 := by
        by_cases secondZero : candidate + height = 0
        · exact secondZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero firstFactor secondZero)
              productZero)
      calc
        candidate = (candidate + height) - height := by ring1
        _ = -height := by rw [secondFactor]; ring1
end ThreeDimensionalProblems
end Purelib.Algebra.Field.Squares.SignedWitness

end

end
