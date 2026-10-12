module

-- Exposed powers retain the same natural operations with structural monoid laws.
public import Purelib.Algebra.Semiring.Nat
-- The exposed root builder retains the original quotient/remainder certificate.
public import Purelib.Data.Nat.Division
import Mathlib.Algebra.Ring.MinimalAxioms
import Purelib.Tactic.Ring
public import Batteries.Data.Nat.Basic
public import Mathlib.Algebra.Group.Nat.Defs
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Natural square root

This module computes an integer square root by a displayed base-four
recursion.  Dividing the input by four recursively supplies a root `q`; the
only remaining decision is whether `2q + 1` still fits.  The recursion is
logarithmic in the input and returns both defining inequalities as cached
data.  It deliberately does not use Mathlib or Lean core square-root
correctness theorems, whose current proof closure introduces quotient
soundness and choice.
-/

public section

namespace Purelib.Data.Nat.SquareRoot

set_option genInjectivity false in
/-- The floor of a natural square root together with its two defining inequalities.

The retained root has square at most value, while the square of its successor is
strictly greater than value. -/
structure Output (value : Nat) where
  /-- The computed natural floor square root. -/ root : Nat
  /-- The square of the retained root does not exceed the input. -/ square_le : root ^ 2 ≤ value
  /-- The input is strictly below the square of the successor of the retained root. -/ lt_succ_square : value < (root +
    1) ^ 2

constructive_injectivity Output

/-- Compute a certified natural square-root floor by base-four recursion.

Recursing on the original value / 4 produces a smaller certified root. The
retained quotient/remainder equation proves its bounds directly. Doubling the
same root leaves only the original odd-candidate comparison; both output
inequalities are retained. -/
@[expose] def compute : (value : Nat) → Output value :=
  Nat.strongRec (motive := fun value => Output value)
    fun value recurse => by
      by_cases valueZero : value = 0
      · subst value
        exact
          { root := 0
            square_le := by decide
            lt_succ_square := by decide }
      · let quarter := value / 4
        have valuePositive : 0 < value := Nat.pos_of_ne_zero valueZero
        have quarterEquation : value % 4 + 4 * quarter = value :=
          Division.mod_add_div value 4
        have quarterCleared : 4 * quarter ≤ value := by
          calc
            4 * quarter ≤ value % 4 + 4 * quarter := Nat.le_add_left _ _
            _ = value := quarterEquation
        have quarterBelow : quarter < value := by
          by_cases quarterZero : quarter = 0
          · rw [quarterZero]
            exact valuePositive
          · have quarterPositive : 0 < quarter := Nat.pos_of_ne_zero quarterZero
            have belowProduct : quarter < 4 * quarter := by
              calc
                quarter = 1 * quarter := (Nat.one_mul _).symm
                _ < 4 * quarter :=
                  Nat.mul_lt_mul_of_pos_right (by decide : 1 < (4 : Nat)) quarterPositive
            exact Nat.lt_of_lt_of_le belowProduct quarterCleared
        let previous := recurse quarter quarterBelow
        let evenRoot := 2 * previous.root
        have evenRootSquareLe : evenRoot ^ 2 ≤ value := by
          calc
            evenRoot ^ 2 = 4 * previous.root ^ 2 := by
              unfold evenRoot
              ring1
            _ ≤ 4 * quarter :=
              Nat.mul_le_mul_left 4 previous.square_le
            _ ≤ value := quarterCleared
        have valueLtNextEvenSquare : value < (evenRoot + 2) ^ 2 := by
          have valueLtQuarterSuccessor : value < 4 * (quarter + 1) := by
            calc
              value = value % 4 + 4 * quarter := quarterEquation.symm
              _ < 4 + 4 * quarter :=
                Nat.add_lt_add_right (Nat.mod_lt value (by decide : 0 < (4 : Nat))) _
              _ = 4 * (quarter + 1) := by rw [Nat.mul_succ, Nat.add_comm]
          have quarterSuccessorLe :
              quarter + 1 ≤ (previous.root + 1) ^ 2 := by
            exact Nat.succ_le_of_lt previous.lt_succ_square
          calc
            value < 4 * (quarter + 1) := valueLtQuarterSuccessor
            _ ≤ 4 * (previous.root + 1) ^ 2 :=
              Nat.mul_le_mul_left 4 quarterSuccessorLe
            _ = (evenRoot + 2) ^ 2 := by
              unfold evenRoot
              ring1
        by_cases nextFits : (evenRoot + 1) ^ 2 ≤ value
        · exact
            { root := evenRoot + 1
              square_le := nextFits
              lt_succ_square := by
                simpa only [Nat.add_assoc] using valueLtNextEvenSquare }
        · exact
            { root := evenRoot
              square_le := evenRootSquareLe
              lt_succ_square := Nat.lt_of_not_ge nextFits }

/-- The executable floor projection. -/
@[expose] def floor (value : Nat) : Nat := (compute value).root

/-- The computed floor's square lies beneath its input. -/
theorem floor_square_le (value : Nat) : floor value ^ 2 ≤ value :=
  (compute value).square_le

/-- The input lies strictly beneath the square after the computed floor. -/
theorem lt_floor_succ_square (value : Nat) :
    value < (floor value + 1) ^ 2 :=
  (compute value).lt_succ_square

end Purelib.Data.Nat.SquareRoot
