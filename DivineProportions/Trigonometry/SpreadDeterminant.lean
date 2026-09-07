import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadPolynomial

/-!
# Divine Proportions, Chapter 8: bordered-tridiagonal determinants

The determinant family in Exercise 8.8 is evaluated by its finite continuant
and last-column cofactor expansion.  The first four literal determinants from
the source are also checked independently.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Determinant of the symmetric tridiagonal block with diagonal `d` and
adjacent entries `-1`. -/
def symmetricContinuant {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 1
  | 1, diagonal => diagonal
  | index + 2, diagonal =>
      diagonal * symmetricContinuant (index + 1) diagonal -
        symmetricContinuant index diagonal

@[simp] theorem symmetricContinuant_zero
    {R : Type*} [CommRing R] (diagonal : R) :
    symmetricContinuant 0 diagonal = 1 := rfl

@[simp] theorem symmetricContinuant_one
    {R : Type*} [CommRing R] (diagonal : R) :
    symmetricContinuant 1 diagonal = diagonal := rfl

@[simp] theorem symmetricContinuant_succ_succ
    {R : Type*} [CommRing R] (index : Nat) (diagonal : R) :
    symmetricContinuant (index + 2) diagonal =
      diagonal * symmetricContinuant (index + 1) diagonal -
        symmetricContinuant index diagonal := rfl

/-- Sum the first `count` continuants by appending one final cofactor at each
finite step. -/
def continuantPrefix {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 0
  | count + 1, diagonal =>
      continuantPrefix count diagonal +
        symmetricContinuant count diagonal

@[simp] theorem continuantPrefix_zero
    {R : Type*} [CommRing R] (diagonal : R) :
    continuantPrefix 0 diagonal = 0 := rfl

@[simp] theorem continuantPrefix_succ
    {R : Type*} [CommRing R] (count : Nat) (diagonal : R) :
    continuantPrefix (count + 1) diagonal =
      continuantPrefix count diagonal +
        symmetricContinuant count diagonal := rfl

/-- The cofactor evaluation of the source's `dimension × dimension`
bordered-tridiagonal determinant. -/
def borderedSpreadDeterminant
    {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 0
  | blockSize + 1, value =>
      value * symmetricContinuant blockSize (2 - 4 * value) +
        2 * value * continuantPrefix blockSize (2 - 4 * value)

/-- Entry function for the complete matrix family printed in Exercise 8.8.
The final column of every nonfinal row is `1`; the final row ends in
`[-2s,s]`; the remaining leading block is symmetric tridiagonal. -/
def borderedSpreadEntry
    {R : Type*} [CommRing R]
    (dimension row column : Nat) (value : R) : R :=
  if row + 1 < dimension then
    if column + 1 = dimension then 1
    else if column = row then 2 - 4 * value
    else if column + 1 = row ∨ row + 1 = column then -1
    else 0
  else if row + 1 = dimension then
    if column + 2 = dimension then -2 * value
    else if column + 1 = dimension then value
    else 0
  else 0

private theorem continuantPrefix_recurrence
    {R : Type*} [CommRing R] (index : Nat) (diagonal : R) :
    diagonal * continuantPrefix (index + 1) diagonal -
      continuantPrefix index diagonal + 1 =
      continuantPrefix (index + 2) diagonal := by
  induction index with
  | zero =>
      simp only [Nat.zero_add, continuantPrefix_succ,
        continuantPrefix_zero, symmetricContinuant_zero,
        symmetricContinuant_one]
      ring1
  | succ index inductionHypothesis =>
      rw [show Nat.succ index + 1 = (index + 1) + 1 by omega0]
      rw [show Nat.succ index + 2 = (index + 2) + 1 by omega0]
      calc
        diagonal * continuantPrefix (index + 2) diagonal -
              continuantPrefix (index + 1) diagonal + 1 =
            (diagonal * continuantPrefix (index + 1) diagonal -
                continuantPrefix index diagonal + 1) +
              (diagonal * symmetricContinuant (index + 1) diagonal -
                symmetricContinuant index diagonal) := by
                  rw [continuantPrefix_succ, continuantPrefix_succ]
                  ring1
        _ = continuantPrefix (index + 2) diagonal +
              symmetricContinuant (index + 2) diagonal := by
                rw [inductionHypothesis,
                  symmetricContinuant_succ_succ]
        _ = continuantPrefix ((index + 2) + 1) diagonal :=
          (continuantPrefix_succ (index + 2) diagonal).symm
        _ = continuantPrefix (index + 3) diagonal := rfl

/-- Cofactor recurrence of the complete bordered determinant family. -/
theorem borderedSpreadDeterminant_recurrence
    (index : Nat) (value : K) :
    borderedSpreadDeterminant (index + 2) value =
      (2 - 4 * value) * borderedSpreadDeterminant (index + 1) value -
        borderedSpreadDeterminant index value + 2 * value := by
  cases index with
  | zero =>
      simp only [borderedSpreadDeterminant, symmetricContinuant,
        continuantPrefix]
      ring1
  | succ index =>
      simp only [borderedSpreadDeterminant]
      change
        value * symmetricContinuant (index + 2) (2 - 4 * value) +
              2 * value * continuantPrefix (index + 2)
                (2 - 4 * value) =
          (2 - 4 * value) *
              (value * symmetricContinuant (index + 1) (2 - 4 * value) +
                2 * value * continuantPrefix (index + 1)
                  (2 - 4 * value)) -
            (value * symmetricContinuant index (2 - 4 * value) +
              2 * value * continuantPrefix index (2 - 4 * value)) +
            2 * value
      rw [symmetricContinuant_succ_succ]
      have prefixRecurrence :=
        continuantPrefix_recurrence index (2 - 4 * value)
      rw [← prefixRecurrence]
      ring1

private theorem two_sub_four_mul (value : K) :
    2 - 4 * value = 2 * (1 - 2 * value) := by
  ring1

private theorem borderedSpreadDeterminant_agrees_zero (value : K) :
    borderedSpreadDeterminant 0 value = spreadPolynomial 0 value :=
  rfl

private theorem borderedSpreadDeterminant_agrees_one (value : K) :
    borderedSpreadDeterminant 1 value = spreadPolynomial 1 value := by
  change value * 1 + 2 * value * 0 = value
  rw [mul_one, mul_zero, add_zero]

private theorem borderedSpreadDeterminant_agrees_step (value : K)
    (current : Nat)
    (previousEquality :
      borderedSpreadDeterminant current value =
        spreadPolynomial current value)
    (currentEquality :
      borderedSpreadDeterminant (current + 1) value =
        spreadPolynomial (current + 1) value) :
    borderedSpreadDeterminant (current + 2) value =
      spreadPolynomial (current + 2) value := by
  rw [borderedSpreadDeterminant_recurrence,
    spreadPolynomial_succ_succ, previousEquality, currentEquality]
  rw [two_sub_four_mul]

/-- Exercise 8.8 for every requested finite dimension. -/
theorem exercise_8_8 (dimension : Nat) (value : K) :
    borderedSpreadDeterminant dimension value =
      spreadPolynomial dimension value := by
  exact Nat.twoStepInduction (motive := fun current =>
      borderedSpreadDeterminant current value =
        spreadPolynomial current value)
    (borderedSpreadDeterminant_agrees_zero value)
    (borderedSpreadDeterminant_agrees_one value)
    (borderedSpreadDeterminant_agrees_step value)
    dimension

/-- Ordinary two-by-two determinant, used to check the second displayed
matrix literally. -/
def determinantTwo {R : Type*} [CommRing R]
    (a₀₀ a₀₁ a₁₀ a₁₁ : R) : R :=
  a₀₀ * a₁₁ - a₀₁ * a₁₀

/-- Ordinary three-by-three determinant in its six-term expansion. -/
def determinantThree {R : Type*} [CommRing R]
    (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : R) : R :=
  a₀₀ * a₁₁ * a₂₂ + a₀₁ * a₁₂ * a₂₀ + a₀₂ * a₁₀ * a₂₁ -
    a₀₂ * a₁₁ * a₂₀ - a₀₁ * a₁₀ * a₂₂ - a₀₀ * a₁₂ * a₂₁

/-- Four-by-four determinant by its finite first-row cofactor expansion. -/
def determinantFour {R : Type*} [CommRing R]
    (a₀₀ a₀₁ a₀₂ a₀₃
      a₁₀ a₁₁ a₁₂ a₁₃
      a₂₀ a₂₁ a₂₂ a₂₃
      a₃₀ a₃₁ a₃₂ a₃₃ : R) : R :=
  a₀₀ * determinantThree a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ -
    a₀₁ * determinantThree a₁₀ a₁₂ a₁₃ a₂₀ a₂₂ a₂₃ a₃₀ a₃₂ a₃₃ +
    a₀₂ * determinantThree a₁₀ a₁₁ a₁₃ a₂₀ a₂₁ a₂₃ a₃₀ a₃₁ a₃₃ -
    a₀₃ * determinantThree a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ a₃₀ a₃₁ a₃₂

/-- The four literal determinant displays in Exercise 8.8 evaluate to the
same general family. -/
theorem exercise_8_8_first_four (value : K) :
    borderedSpreadDeterminant 1 value = value ∧
      borderedSpreadDeterminant 2 value =
        determinantTwo (2 - 4 * value) 1 (-2 * value) value ∧
      borderedSpreadDeterminant 3 value =
        determinantThree
          (2 - 4 * value) (-1) 1
          (-1) (2 - 4 * value) 1
          0 (-2 * value) value ∧
      borderedSpreadDeterminant 4 value =
        determinantFour
          (2 - 4 * value) (-1) 0 1
          (-1) (2 - 4 * value) (-1) 1
          0 (-1) (2 - 4 * value) 1
          0 0 (-2 * value) value := by
  simp only [borderedSpreadDeterminant, symmetricContinuant,
    continuantPrefix, determinantTwo, determinantThree, determinantFour]
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

end DivineProportions
