module

public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Rational rotations, Theorem 61: the quadrance class

Square classes are represented quotient-free.  Equality carries an explicit
nonzero square factor, so invariance and multiplicativity remain executable
finite field calculations.
-/

namespace Purelib.Algebra.Field.SquareClass.Basic

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A displayed nonzero scalar representing a square class.

The value and its nonzero certificate are retained directly, without a quotient or a selected canonical representative.
-/
@[ext]
structure SquareClassRepresentative (K : Type*) [ExplicitField K] where
  /-- The retained representative scalar. -/ value : K
  /-- The representative scalar is nonzero. -/ nonzero : value ≠ 0

constructive_injectivity SquareClassRepresentative

namespace SquareClassRepresentative

open Purelib.Algebra.Field.SquareClass.Basic
/-- Two representatives differ by multiplication by a nonzero square.

The witness retains a nonzero scalar factor whose square takes the left value to the right value. -/
def Equivalent (left right :
  SquareClassRepresentative K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧ right.value = factor ^ 2 * left.value

/-- A nonzero representative forces the unit of its explicit field to be nonzero. -/
theorem one_ne_zero (representative :
  SquareClassRepresentative K) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply representative.nonzero
  calc
    representative.value = representative.value * 1 := by rw [mul_one]
    _ = representative.value * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

/-- Each square-class representative is equivalent to itself using unit factor. -/
theorem equivalent_refl (representative :
  SquareClassRepresentative K) :
    representative.Equivalent representative := by
  refine ⟨1, representative.one_ne_zero, ?_⟩
  ring1

/-- Square-class equivalence reverses by inverting its nonzero factor. -/
theorem equivalent_symm {left right :
  SquareClassRepresentative K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := cancel
  refine ⟨factor⁻¹, ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  calc
    left.value = (factor⁻¹ * factor) ^ 2 * left.value := by
      rw [reverseCancel]
      ring1
    _ = factor⁻¹ ^ 2 * (factor ^ 2 * left.value) := by ring1
    _ = factor⁻¹ ^ 2 * right.value := by rw [rightValue]

/-- Square-class equivalence composes by multiplying its nonzero factors. -/
theorem equivalent_trans {first second third :
  SquareClassRepresentative K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstFactorNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondFactorNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    ExplicitField.mul_ne_zero secondFactorNonzero firstFactorNonzero, ?_⟩
  calc
    third.value = secondFactor ^ 2 * second.value := thirdValue
    _ = secondFactor ^ 2 * (firstFactor ^ 2 * first.value) := by
      rw [secondValue]
    _ = (secondFactor * firstFactor) ^ 2 * first.value := by ring1

/-- Multiply two displayed square-class representatives.

The result retains their product and the nonzero certificate obtained from both inputs. -/
def mul (left right : SquareClassRepresentative
  K) :
    SquareClassRepresentative K where
  value := left.value * right.value
  nonzero := ExplicitField.mul_ne_zero left.nonzero right.nonzero

/-- Multiplication preserves equivalence of displayed square-class representatives.

The product of the two supplied nonzero factors witnesses the resulting equivalence. -/
theorem mul_respects_equivalent
    {left left' right right' : SquareClassRepresentative K}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    (mul left right).Equivalent (mul left' right') := by
  rcases leftEquivalent with ⟨leftFactor, leftFactorNonzero, leftValue⟩
  rcases rightEquivalent with ⟨rightFactor, rightFactorNonzero, rightValue⟩
  refine ⟨leftFactor * rightFactor,
    ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
  change left'.value * right'.value =
    (leftFactor * rightFactor) ^ 2 * (left.value * right.value)
  rw [leftValue, rightValue]
  ring1

end SquareClassRepresentative

end Purelib.Algebra.Field.SquareClass.Basic

end

public section

namespace Purelib.Algebra.Field.SquareClass.Basic.SquareClassRepresentative

variable {K : Type*} [ExplicitField K]

/-- A nonzero square-class representative is equivalent to one exactly when its value has a square root.

The inverse of the retained equivalence factor is the root in one direction; the original root gives the reverse
equivalence factor. -/
theorem equivalent_one_iff_square (representative : SquareClassRepresentative K) :
    representative.Equivalent ⟨1, representative.one_ne_zero⟩ ↔
      ∃ root : K, root ^ 2 = representative.value := by
  constructor
  · intro trivial
    rcases equivalent_symm trivial with ⟨factor, _, valueEqual⟩
    refine ⟨factor, ?_⟩
    change representative.value = factor ^ 2 * 1 at valueEqual
    exact (valueEqual.trans (mul_one _)).symm
  · rintro ⟨root, square⟩
    have rootNonzero : root ≠ 0 := by
      intro zero
      apply representative.nonzero
      calc
        representative.value = root ^ 2 := square.symm
        _ = 0 := by rw [zero]; ring1
    apply equivalent_symm
    refine ⟨root, rootNonzero, ?_⟩
    change representative.value = root ^ 2 * 1
    rw [mul_one]
    exact square.symm

/-- Equivalent nonzero representatives have square roots simultaneously.

The same square-factor equivalence transports membership in the unit square class, without selecting a canonical
root. -/
theorem square_iff_of_equivalent {left right : SquareClassRepresentative K}
    (equivalent : left.Equivalent right) :
    (∃ root : K, root ^ 2 = left.value) ↔ (∃ root : K, root ^ 2 = right.value) := by
  constructor
  · intro square
    have trivial := (equivalent_one_iff_square left).mpr square
    exact (equivalent_one_iff_square right).mp (equivalent_trans (equivalent_symm equivalent) trivial)
  · intro square
    have trivial := (equivalent_one_iff_square right).mpr square
    exact (equivalent_one_iff_square left).mp (equivalent_trans equivalent trivial)

end Purelib.Algebra.Field.SquareClass.Basic.SquareClassRepresentative
