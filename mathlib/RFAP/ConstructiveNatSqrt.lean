import mathlib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Constructive natural square root

This module computes an integer square root by a displayed base-four
recursion.  Dividing the input by four recursively supplies a root `q`; the
only remaining decision is whether `2q + 1` still fits.  The recursion is
logarithmic in the input and returns both defining inequalities as cached
data.  It deliberately does not use Mathlib or Lean core square-root
correctness theorems, whose current proof closure introduces quotient
soundness and choice.
-/

namespace RFAP.ConstructiveNatSqrt

/-- A computed square-root floor together with its two defining bounds. -/
structure Output (value : Nat) where
  root : Nat
  square_le : root ^ 2 ≤ value
  lt_succ_square : value < (root + 1) ^ 2

/-- Logarithmic base-four recursion for the natural square-root floor. -/
def compute : (value : Nat) → Output value :=
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
        have quarterBelow : quarter < value := by
          unfold quarter
          omega0
        let previous := recurse quarter quarterBelow
        let evenRoot := 2 * previous.root
        have quarterCleared : 4 * quarter ≤ value := by
          unfold quarter
          omega0
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
            unfold quarter
            omega0
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
def floor (value : Nat) : Nat := (compute value).root

/-- The computed floor's square lies beneath its input. -/
theorem floor_square_le (value : Nat) : floor value ^ 2 ≤ value :=
  (compute value).square_le

/-- The input lies strictly beneath the square after the computed floor. -/
theorem lt_floor_succ_square (value : Nat) :
    value < (floor value + 1) ^ 2 :=
  (compute value).lt_succ_square

end RFAP.ConstructiveNatSqrt
