module

public import Mathlib.Algebra.Ring.Defs
public import Purelib.Algebra.Group.Basic
public import Purelib.Algebra.Group.Negation

namespace Purelib.Algebra.Ring

open Purelib.Algebra

attribute [local instance high] Group.Negation.subNegZeroMonoid

/-- Build a commutative ring from its left identities and a displayed subtraction.

Associativity, left additive inverses, commutative multiplication and left
distributivity determine the remaining ring laws. Scalar multiplication,
powers and casts retain the standard recursive operations of the minimal-
axiom construction; subtraction is the supplied operation with its equation.
The original additive group is retained as the ring's parent. -/
@[expose, reducible] public def commRingOfAxioms {R : Type*}
    [Add R] [Mul R] [Neg R] [Zero R] [One R]
    (addAssoc : ∀ first second third : R,
      first + second + third = first + (second + third))
    (zeroAdd : ∀ value : R, 0 + value = value)
    (negAddCancel : ∀ value : R, -value + value = 0)
    (mulAssoc : ∀ first second third : R,
      first * second * third = first * (second * third))
    (mulComm : ∀ left right : R, left * right = right * left)
    (oneMul : ∀ value : R, 1 * value = value)
    (leftDistrib : ∀ factor left right : R,
      factor * (left + right) = factor * left + factor * right)
    (subtract : R → R → R)
    (subEquation : ∀ left right : R, subtract left right = left + -right) :
    CommRing R := by
  letI : AddGroup R := Group.addGroupOfLeftAxioms addAssoc zeroAdd negAddCancel
  have mulOne : ∀ value : R, value * 1 = value := fun value =>
    (mulComm value 1).trans (oneMul value)
  have rightDistrib : ∀ left right factor : R,
      (left + right) * factor = left * factor + right * factor := by
    intro left right factor
    rw [mulComm, leftDistrib, mulComm factor left, mulComm factor right]
  have addComm : ∀ left right : R, left + right = right + left := by
    intro left right
    have first : (1 + 1 : R) * (left + right) = left + (left + right) + right := by
      rw [leftDistrib, rightDistrib, rightDistrib, oneMul, oneMul,
        addAssoc left left (right + right), ← addAssoc left right right]
      exact (addAssoc left (left + right) right).symm
    have second : (1 + 1 : R) * (left + right) = left + (right + left) + right := by
      rw [rightDistrib, leftDistrib, oneMul, oneMul, addAssoc]
      rw [← addAssoc right left right]
      exact (addAssoc left (right + left) right).symm
    exact add_left_cancel (add_right_cancel (first.symm.trans second))
  have zeroMul : ∀ value : R, 0 * value = 0 := by
    intro value
    have doubles : (0 : R) * value = 0 * value + 0 * value :=
      calc
        0 * value = (0 + 0) * value := congrArg (· * value) (zeroAdd 0).symm
        _ = 0 * value + 0 * value := rightDistrib 0 0 value
    exact add_left_cancel (doubles.symm.trans (add_zero (0 * value)).symm)
  have mulZero : ∀ value : R, value * 0 = 0 := fun value =>
    (mulComm value 0).trans (zeroMul value)
  exact {
    add_comm := addComm
    left_distrib := leftDistrib
    right_distrib := rightDistrib
    zero_mul := zeroMul
    mul_zero := mulZero
    mul_assoc := mulAssoc
    mul_comm := mulComm
    one_mul := oneMul
    mul_one := mulOne
    neg_add_cancel := negAddCancel
    sub := subtract
    sub_eq_add_neg := subEquation }

end Purelib.Algebra.Ring
