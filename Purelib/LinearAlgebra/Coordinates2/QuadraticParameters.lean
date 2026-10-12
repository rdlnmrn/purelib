module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra.Field
open Purelib

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

section

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.LinearAlgebra.Coordinates2.QuadraticParameters.Quadrola

/-- Algebraic core of Exercise 15.10.  Two focal-difference vectors giving
the same three normalized quadratic coefficients are equal up to sign when
`-1` has no square root; their associated quadrances are then equal. -/
theorem parameters_unique_of_quadratic_coefficients [DecidableEq K]
    (firstX firstY secondX secondY : K)
    (firstAssociated secondAssociated : K)
    (noNegativeOneSquare : Algebra.Field.Squares.NoSquareRootOfNegativeOne (K := K))
    (dEqual :
      firstAssociated - firstX ^ 2 =
        secondAssociated - secondX ^ 2)
    (mixedEqual : firstX * firstY = secondX * secondY)
    (fEqual :
      firstAssociated - firstY ^ 2 =
        secondAssociated - secondY ^ 2) :
    firstAssociated = secondAssociated ∧
      ((firstX = secondX ∧ firstY = secondY) ∨
        (firstX = -secondX ∧ firstY = -secondY)) := by
  have firstDifference :
      firstAssociated - secondAssociated = firstX ^ 2 - secondX ^ 2 := by
    calc
      firstAssociated - secondAssociated =
          (firstAssociated - firstX ^ 2) -
            (secondAssociated - secondX ^ 2) +
            (firstX ^ 2 - secondX ^ 2) := by ring1
      _ = firstX ^ 2 - secondX ^ 2 := by rw [dEqual]; ring1
  have secondDifference :
      firstAssociated - secondAssociated = firstY ^ 2 - secondY ^ 2 := by
    calc
      firstAssociated - secondAssociated =
          (firstAssociated - firstY ^ 2) -
            (secondAssociated - secondY ^ 2) +
            (firstY ^ 2 - secondY ^ 2) := by ring1
      _ = firstY ^ 2 - secondY ^ 2 := by rw [fEqual]; ring1
  have differenceProduct :
      (firstAssociated - secondAssociated) ^ 2 =
        (firstX ^ 2 - secondX ^ 2) *
          (firstY ^ 2 - secondY ^ 2) := by
    rw [← firstDifference, ← secondDifference]
    ring1
  let cross := firstX * secondY - firstY * secondX
  have negativeSquareIdentity :
      (firstAssociated - secondAssociated) ^ 2 + cross ^ 2 = 0 := by
    calc
      (firstAssociated - secondAssociated) ^ 2 + cross ^ 2 =
          (firstX ^ 2 - secondX ^ 2) *
              (firstY ^ 2 - secondY ^ 2) + cross ^ 2 := by
        rw [differenceProduct]
      _ = (firstX * firstY - secondX * secondY) ^ 2 := by
        unfold cross
        ring1
      _ = 0 := by rw [mixedEqual]; ring1
  have associatedDifferenceZero :
      firstAssociated - secondAssociated = 0 := by
    by_cases differenceZero : firstAssociated - secondAssociated = 0
    · exact differenceZero
    · have differenceCancel :
          (firstAssociated - secondAssociated) *
              (firstAssociated - secondAssociated)⁻¹ = (1 : K) :=
        ExplicitField.mul_inv_cancel _ differenceZero
      have candidateSquare :
          (cross / (firstAssociated - secondAssociated)) ^ 2 = -1 := by
        simp only [ExplicitField.div_eq_mul_inv]
        calc
          (cross * (firstAssociated - secondAssociated)⁻¹) ^ 2 =
              cross ^ 2 *
                (firstAssociated - secondAssociated)⁻¹ ^ 2 := by ring1
          _ = -(firstAssociated - secondAssociated) ^ 2 *
                (firstAssociated - secondAssociated)⁻¹ ^ 2 := by
            have crossSquare :
                cross ^ 2 = -(firstAssociated - secondAssociated) ^ 2 := by
              calc
                cross ^ 2 =
                    ((firstAssociated - secondAssociated) ^ 2 + cross ^ 2) -
                      (firstAssociated - secondAssociated) ^ 2 := by ring1
                _ = -(firstAssociated - secondAssociated) ^ 2 := by
                  rw [negativeSquareIdentity]
                  ring1
            rw [crossSquare]
          _ = -((firstAssociated - secondAssociated) *
                (firstAssociated - secondAssociated)⁻¹) ^ 2 := by ring1
          _ = -1 := by rw [differenceCancel]; ring1
      exact False.elim
        ((noNegativeOneSquare
          (cross / (firstAssociated - secondAssociated))) candidateSquare)
  have associatedEqual : firstAssociated = secondAssociated := by
    calc
      firstAssociated =
          (firstAssociated - secondAssociated) + secondAssociated := by ring1
      _ = secondAssociated := by rw [associatedDifferenceZero]; ring1
  have firstSquaresEqual : firstX ^ 2 = secondX ^ 2 := by
    have squareDifferenceZero : firstX ^ 2 - secondX ^ 2 = 0 := by
      calc
        firstX ^ 2 - secondX ^ 2 =
            firstAssociated - secondAssociated := firstDifference.symm
        _ = 0 := associatedDifferenceZero
    calc
      firstX ^ 2 = (firstX ^ 2 - secondX ^ 2) + secondX ^ 2 := by ring1
      _ = secondX ^ 2 := by rw [squareDifferenceZero]; ring1
  have secondSquaresEqual : firstY ^ 2 = secondY ^ 2 := by
    have squareDifferenceZero : firstY ^ 2 - secondY ^ 2 = 0 := by
      calc
        firstY ^ 2 - secondY ^ 2 =
            firstAssociated - secondAssociated := secondDifference.symm
        _ = 0 := associatedDifferenceZero
    calc
      firstY ^ 2 = (firstY ^ 2 - secondY ^ 2) + secondY ^ 2 := by ring1
      _ = secondY ^ 2 := by rw [squareDifferenceZero]; ring1
  refine ⟨associatedEqual, ?_⟩
  by_cases firstXZero : firstX = 0
  · have secondXSquareZero : secondX ^ 2 = 0 := by
      rw [← firstSquaresEqual, firstXZero]
      ring1
    have secondXZero : secondX = 0 := by
      by_cases secondXZero : secondX = 0
      · exact secondXZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero secondXZero secondXZero)
            (by simpa only [pow_two] using secondXSquareZero))
    rcases Algebra.Field.Squares.eq_or_eq_neg_of_square_eq secondSquaresEqual with
      secondYEqual | secondYNegative
    · left
      exact ⟨by rw [firstXZero, secondXZero], secondYEqual⟩
    · right
      exact ⟨by rw [firstXZero, secondXZero]; ring1, secondYNegative⟩
  · rcases Algebra.Field.Squares.eq_or_eq_neg_of_square_eq firstSquaresEqual with
      firstXEqual | firstXNegative
    · left
      refine ⟨firstXEqual, ?_⟩
      have productZero : firstX * (firstY - secondY) = 0 := by
        calc
          firstX * (firstY - secondY) =
              firstX * firstY - secondX * secondY := by
            rw [← firstXEqual]
            ring1
          _ = 0 := by rw [mixedEqual]; ring1
      have differenceZero :=
        ExplicitField.eq_zero_of_mul_eq_zero_left firstXZero productZero
      calc
        firstY = (firstY - secondY) + secondY := by ring1
        _ = secondY := by rw [differenceZero]; ring1
    · right
      refine ⟨firstXNegative, ?_⟩
      have secondXEqualsNegative : secondX = -firstX := by
        calc
          secondX = -(-secondX) := by ring1
          _ = -firstX := by rw [firstXNegative]
      have productZero : firstX * (firstY + secondY) = 0 := by
        calc
          firstX * (firstY + secondY) =
              firstX * firstY - secondX * secondY := by
            rw [secondXEqualsNegative]
            ring1
          _ = 0 := by rw [mixedEqual]; ring1
      have sumZero := ExplicitField.eq_zero_of_mul_eq_zero_left firstXZero productZero
      calc
        firstY = (firstY + secondY) - secondY := by ring1
        _ = -secondY := by rw [sumZero]; ring1

end Purelib.LinearAlgebra.Coordinates2.QuadraticParameters.Quadrola

end

end

end

end
