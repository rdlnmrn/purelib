module
public import Purelib.LinearAlgebra.Coordinates2.Determinant
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Ring.Affine
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.LinearAlgebra.Coordinates4.Determinant
public import Purelib.Polynomial.Recurrence.Continuant.Basic
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.LinearAlgebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: bordered-tridiagonal determinants

The determinant family in Exercise 8.8 is evaluated by its finite continuant
and last-column cofactor expansion.  The first four literal determinants from
the source are also checked independently.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Continuant

variable {K : Type*} [ExplicitField K]

/-- The cofactor evaluation of the source's `dimension × dimension`
bordered-tridiagonal determinant. -/
def borderedSpreadDeterminant
    {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 0
  | blockSize + 1, value =>
      value * Recurrence.Continuant.Basic.symmetricContinuant blockSize (2 - 4 * value) +
        2 * value * Recurrence.Continuant.Basic.continuantPrefix blockSize (2 - 4 * value)

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

/-- Cofactor recurrence of the complete bordered determinant family. -/
theorem borderedSpreadDeterminant_recurrence
    (index : Nat) (value : K) :
    Recurrence.Spread.Continuant.borderedSpreadDeterminant (index + 2) value =
      (2 - 4 * value) * Recurrence.Spread.Continuant.borderedSpreadDeterminant (index + 1) value -
        Recurrence.Spread.Continuant.borderedSpreadDeterminant index value + 2 * value := by
  cases index with
  | zero =>
      simp only [Recurrence.Spread.Continuant.borderedSpreadDeterminant,
        Recurrence.Continuant.Basic.symmetricContinuant,
        Recurrence.Continuant.Basic.continuantPrefix]
      ring1
  | succ index =>
      simp only [Recurrence.Spread.Continuant.borderedSpreadDeterminant]
      change
        value * Recurrence.Continuant.Basic.symmetricContinuant (index + 2) (2 - 4 * value) +
              2 * value * Recurrence.Continuant.Basic.continuantPrefix (index + 2)
                (2 - 4 * value) =
          (2 - 4 * value) *
              (value * Recurrence.Continuant.Basic.symmetricContinuant (index + 1) (2 - 4 * value) +
                2 * value * Recurrence.Continuant.Basic.continuantPrefix (index + 1)
                  (2 - 4 * value)) -
            (value * Recurrence.Continuant.Basic.symmetricContinuant index (2 - 4 * value) +
              2 * value * Recurrence.Continuant.Basic.continuantPrefix index (2 - 4 * value)) +
            2 * value
      rw [Recurrence.Continuant.Basic.symmetricContinuant_succ_succ]
      have prefixRecurrence :=
        Purelib.Polynomial.Recurrence.Continuant.Basic.continuantPrefix_recurrence index (2 - 4 *
          value)
      rw [← prefixRecurrence]
      ring1

section
/-- The bordered determinant and spread polynomial agree at dimension zero. -/
private theorem
  borderedSpreadDeterminant_agrees_zero
  (value : K) :
    Recurrence.Spread.Continuant.borderedSpreadDeterminant 0 value = Recurrence.Spread.Basic.spreadPolynomial 0 value :=
  rfl
/-- The bordered determinant and spread polynomial agree at dimension one. -/
private theorem
  borderedSpreadDeterminant_agrees_one
  (value : K) :
    Recurrence.Spread.Continuant.borderedSpreadDeterminant 1 value = Recurrence.Spread.Basic.spreadPolynomial 1 value :=
      by
  change value * 1 + 2 * value * 0 = value
  rw [mul_one, mul_zero, add_zero]
/-- Transport two consecutive determinant identities through the spread recurrence.

Agreement at the preceding two indices gives agreement at the next index over the supplied explicit field. -/
private theorem
  borderedSpreadDeterminant_agrees_step
  (value : K)
    (current : Nat)
    (previousEquality :
      Recurrence.Spread.Continuant.borderedSpreadDeterminant current value =
        Recurrence.Spread.Basic.spreadPolynomial current value)
    (currentEquality :
      Recurrence.Spread.Continuant.borderedSpreadDeterminant (current + 1) value =
        Recurrence.Spread.Basic.spreadPolynomial (current + 1) value) :
    Recurrence.Spread.Continuant.borderedSpreadDeterminant (current + 2) value =
      Recurrence.Spread.Basic.spreadPolynomial (current + 2) value := by
  rw [Recurrence.Spread.Continuant.borderedSpreadDeterminant_recurrence,
    Recurrence.Spread.Basic.spreadPolynomial_succ_succ, previousEquality, currentEquality]
  rw [Purelib.Algebra.Ring.Affine.two_sub_four_mul]
end

/-- The bordered tridiagonal determinant equals the spread polynomial.

The identity holds for every finite dimension and every scalar in the supplied explicit field. -/
theorem exercise_8_8 (dimension : Nat) (value : K) :
    Recurrence.Spread.Continuant.borderedSpreadDeterminant dimension value =
      Recurrence.Spread.Basic.spreadPolynomial dimension value := by
  exact Nat.twoStepInduction (motive := fun current =>
      Recurrence.Spread.Continuant.borderedSpreadDeterminant current value =
        Recurrence.Spread.Basic.spreadPolynomial current value)
    (Purelib.Polynomial.Recurrence.Spread.Continuant.borderedSpreadDeterminant_agrees_zero value)
    (Purelib.Polynomial.Recurrence.Spread.Continuant.borderedSpreadDeterminant_agrees_one value)
    (Purelib.Polynomial.Recurrence.Spread.Continuant.borderedSpreadDeterminant_agrees_step value)
    dimension

/-- The first four bordered determinants have their explicit small-matrix formulas.

The conjunction identifies dimensions one through four with scalar, two-, three-, and four-dimensional determinant
expressions. -/
theorem exercise_8_8_first_four (value : K) :
    Recurrence.Spread.Continuant.borderedSpreadDeterminant 1 value = value ∧
      Recurrence.Spread.Continuant.borderedSpreadDeterminant 2 value =
        LinearAlgebra.Coordinates2.Determinant.SpreadDeterminant.determinantTwo (2 - 4 * value) 1 (-2 * value) value ∧
      Recurrence.Spread.Continuant.borderedSpreadDeterminant 3 value =
        Coordinates3.Matrix.determinantThree
          (2 - 4 * value) (-1) 1
          (-1) (2 - 4 * value) 1
          0 (-2 * value) value ∧
      Recurrence.Spread.Continuant.borderedSpreadDeterminant 4 value =
        LinearAlgebra.Coordinates4.Determinant.determinantFour
          (2 - 4 * value) (-1) 0 1
          (-1) (2 - 4 * value) (-1) 1
          0 (-1) (2 - 4 * value) 1
          0 0 (-2 * value) value := by
  simp only [Recurrence.Spread.Continuant.borderedSpreadDeterminant, Recurrence.Continuant.Basic.symmetricContinuant,
    Recurrence.Continuant.Basic.continuantPrefix,
      LinearAlgebra.Coordinates2.Determinant.SpreadDeterminant.determinantTwo, Coordinates3.Matrix.determinantThree,
      LinearAlgebra.Coordinates4.Determinant.determinantFour]
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

end Purelib.Polynomial.Recurrence.Spread.Continuant

end
