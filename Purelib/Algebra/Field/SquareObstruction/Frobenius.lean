module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace Purelib.Algebra.Field.SquareObstruction.Frobenius

section ChapterFourteenExamples

/-- A negative power certificate obstructs being a nonzero square.

Two is nonzero, the displayed value raised to the supplied exponent is negative one, and every scalar is fixed by twice
that exponent plus one. -/
theorem not_nonzeroSquare_of_frobenius_neg
    {K : Type*} [ExplicitField K] [DecidableEq K]
    (value : K) (exponent : Nat) (twoNonzero : (2 : K) ≠ 0)
    (valuePower : value ^ exponent = -1)
    (frobenius : ∀ root : K, root ^ (2 * exponent + 1) = root) :
    ¬ Squares.IsNonzeroSquare value := by
  rintro ⟨root, rootNonzero, valueSquare⟩
  have oddPower : root ^ (2 * exponent + 1) = -root := by
    calc
      root ^ (2 * exponent + 1) = root ^ (2 * exponent) * root := by
        rw [pow_add, pow_one]
      _ = (root ^ 2) ^ exponent * root := by rw [pow_mul]
      _ = value ^ exponent * root := by rw [← valueSquare]
      _ = -root := by rw [valuePower]; ring1
  have rootEqNegative : root = -root :=
    (frobenius root).symm.trans oddPower
  have addRoot := congrArg (fun value : K => value + root) rootEqNegative
  have twiceRootZero : (2 : K) * root = 0 := by
    calc
      (2 : K) * root = root + root := by ring1
      _ = -root + root := addRoot
      _ = 0 := by ring1
  exact (ExplicitField.mul_ne_zero twoNonzero rootNonzero)
    twiceRootZero

end ChapterFourteenExamples

end Purelib.Algebra.Field.SquareObstruction.Frobenius

end
