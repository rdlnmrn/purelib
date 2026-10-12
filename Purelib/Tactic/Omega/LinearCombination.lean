module
import Purelib.Tactic.Ring

import Purelib.Data.Int.Arithmetic

import Lean.Elab.Tactic.Omega
meta import Lean.Elab.Tactic.Omega.Frontend
meta import Lean.Elab.Tactic.Omega.OmegaM
public import Purelib.Tactic.Omega.Coefficients

section

/-!
# Quotient-free Omega proof reconstruction

Lean's Omega procedure computes a finite contradiction certificate.  Some of
the small checker lemmas used to turn that certificate into a kernel proof
currently inherit `Quot.sound` through generic list and function
extensionality.  This module gives those finite lemmas direct structural
proofs and substitutes them into the generated certificate.
-/

public section

namespace Purelib.Tactic.Omega.LinearCombination

open Lean.Omega
open Purelib.Data.Int
open Purelib.Tactic.Omega

/-- Reduce a finite coordinate evaluation by its explicit list and integer equations.

This local tactic unfolds only the displayed coefficient constructors, dot product and scalar zero/one identities. -/
local macro "coordinate_rfl" : tactic =>
  `(tactic|
    (dsimp only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.ofList,
      Coeffs.set, Coeffs.dot, IntList.set, IntList.dot, IntList.mul_def,
      IntList.sum, List.foldr, List.zipWith]
     repeat first
       | rw [Int.one_mul]
       | rw [Arithmetic.zero_mul]
       | rw [Int.add_zero]
       | rw [Arithmetic.zero_add]
     try rfl))

/-- Coordinate 0 evaluates to the coefficient stored at that position.

The displayed list contains at least 1 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_0 :
    (LinearCombo.coordinate 0).eval (.ofList (a0 :: tail)) = a0 := by
  coordinate_rfl

/-- Coordinate 1 evaluates to the coefficient stored at that position.

The displayed list contains at least 2 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_1 :
    (LinearCombo.coordinate 1).eval (.ofList (a0 :: a1 :: tail)) = a1 := by
  coordinate_rfl

/-- Coordinate 2 evaluates to the coefficient stored at that position.

The displayed list contains at least 3 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_2 :
    (LinearCombo.coordinate 2).eval (.ofList (a0 :: a1 :: a2 :: tail)) = a2 := by
  coordinate_rfl

/-- Coordinate 3 evaluates to the coefficient stored at that position.

The displayed list contains at least 4 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_3 :
    (LinearCombo.coordinate 3).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: tail)) = a3 := by
  coordinate_rfl

/-- Coordinate 4 evaluates to the coefficient stored at that position.

The displayed list contains at least 5 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_4 :
    (LinearCombo.coordinate 4).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: tail)) = a4 := by
  coordinate_rfl

/-- Coordinate 5 evaluates to the coefficient stored at that position.

The displayed list contains at least 6 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_5 :
    (LinearCombo.coordinate 5).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: tail)) = a5 := by
  coordinate_rfl

/-- Coordinate 6 evaluates to the coefficient stored at that position.

The displayed list contains at least 7 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_6 :
    (LinearCombo.coordinate 6).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: tail)) = a6 := by
  coordinate_rfl

/-- Coordinate 7 evaluates to the coefficient stored at that position.

The displayed list contains at least 8 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_7 :
    (LinearCombo.coordinate 7).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: tail)) = a7 := by
  coordinate_rfl

/-- Coordinate 8 evaluates to the coefficient stored at that position.

The displayed list contains at least 9 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_8 :
    (LinearCombo.coordinate 8).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: tail)) = a8 := by
  coordinate_rfl

/-- Coordinate 9 evaluates to the coefficient stored at that position.

The displayed list contains at least 10 entries; its remaining tail
contributes zero to this coordinate. -/
theorem coordinate_eval_9 :
    (LinearCombo.coordinate 9).eval
      (.ofList
        (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: tail)) = a9 := by
  coordinate_rfl

section
open Purelib.Tactic
/-- Every coordinate combination evaluates to the corresponding coefficient lookup.

Structural recursion handles both displayed entries and indices beyond the finite list, where lookup is zero. -/
theorem coordinate_eval (index : Nat) (values : Coeffs) :
    (LinearCombo.coordinate index).eval values = Omega.Coefficients.get values index := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil =>
          exact Eq.refl (0 : Int)
      | cons head tail =>
          exact coordinate_eval_0
  | succ index inductionHypothesis =>
      cases values with
      | nil =>
          exact Eq.refl (0 : Int)
      | cons head tail =>
          change 0 + (0 * head + IntList.dot (IntList.set [] index 1) tail) =
            Omega.Coefficients.get tail index
          rw [Arithmetic.zero_mul, Arithmetic.zero_add, Arithmetic.zero_add]
          have tailEvaluation := inductionHypothesis tail
          change 0 + IntList.dot (IntList.set [] index 1) tail =
            Omega.Coefficients.get tail index at tailEvaluation
          rw [Arithmetic.zero_add] at tailEvaluation
          exact tailEvaluation

/-- Evaluation commutes with addition of finite linear combinations. -/
theorem add_eval (left right : LinearCombo) (values : Coeffs) :
    (left + right).eval values = left.eval values + right.eval values := by
  rcases left with ⟨leftConstant, leftCoefficients⟩
  rcases right with ⟨rightConstant, rightCoefficients⟩
  change (leftConstant + rightConstant) +
      IntList.dot (leftCoefficients + rightCoefficients) values =
    (leftConstant + IntList.dot leftCoefficients values) +
      (rightConstant + IntList.dot rightCoefficients values)
  rw [Omega.Coefficients.intList_dot_distrib_left]
  ring1

end

/-- Negating a finite linear combination negates its evaluation.

The original constant and retained coefficient list are negated separately.
Structural dot-product negation and scalar sum negation recover the negative
of their unchanged evaluation. -/
theorem neg_eval
    (combination : LinearCombo) (values : Coeffs) :
    (-combination).eval values = -combination.eval values := by
  rcases combination with ⟨constant, coefficients⟩
  change -constant + IntList.dot (-coefficients) values =
    -(constant + IntList.dot coefficients values)
  rw [Coefficients.intList_dot_neg_left, Arithmetic.neg_add]

/-- Evaluation commutes with subtraction of finite linear combinations.

The constants and the two retained coefficient lists are subtracted in their
original representation, with dot-product negation proved structurally. -/
theorem sub_eval (left right : LinearCombo) (values : Coeffs) :
    (left - right).eval values = left.eval values - right.eval values := by
  rcases left with ⟨leftConstant, leftCoefficients⟩
  rcases right with ⟨rightConstant, rightCoefficients⟩
  change (leftConstant - rightConstant) +
      IntList.dot (leftCoefficients - rightCoefficients) values =
    (leftConstant + IntList.dot leftCoefficients values) -
      (rightConstant + IntList.dot rightCoefficients values)
  rw [Omega.Coefficients.intList_sub_eq_add_neg, Omega.Coefficients.intList_dot_distrib_left,
    Coefficients.intList_dot_neg_left]
  ring1

/-- Scaling a finite linear combination scales its evaluation.

The constant and every coefficient retain the same integer factor. The direct
finite dot-product scaling identity and scalar distributivity recover the
scaled original evaluation. -/
theorem smul_eval
    (combination : LinearCombo) (factor : Int) (values : Coeffs) :
    (factor * combination).eval values = factor * combination.eval values := by
  rcases combination with ⟨constant, coefficients⟩
  change factor * constant + IntList.dot (factor * coefficients) values =
    factor * (constant + IntList.dot coefficients values)
  rw [Coefficients.intList_dot_smul_left, Arithmetic.mul_add]

open Purelib.Tactic
/-- Evaluation of linear-combination multiplication agrees with scalar multiplication when the left coefficient vector
is zero.

The original zero-entry witness removes that factor's finite dot product.
Direct scalar evaluation and the unchanged linearized multiplication then give
the product of the two original evaluations. -/
theorem mul_eval_of_const_left (left right : LinearCombo) (values :
  Coeffs)
    (constantLeft : left.coeffs.isZero) :
    (LinearCombo.mul left right).eval values =
      left.eval values * right.eval values := by
  have zeroDot : IntList.dot left.coeffs values = 0 :=
    Coefficients.intList_dot_of_left_zero _ _ constantLeft
  change left.coeffs.dot values = 0 at zeroDot
  unfold LinearCombo.mul
  rw [sub_eval, add_eval, smul_eval,
    smul_eval]
  simp only [LinearCombo.eval, IntList.dot_nil_left, Int.add_zero]
  rw [zeroDot]
  ring1

/-- Evaluation of linear-combination multiplication agrees with scalar multiplication when the right coefficient vector
is zero.

The original zero-entry witness removes that factor's finite dot product.
Direct scalar evaluation and the unchanged linearized multiplication then give
the product of the two original evaluations. -/
theorem mul_eval_of_const_right (left right : LinearCombo) (values :
  Coeffs)
    (constantRight : right.coeffs.isZero) :
    (LinearCombo.mul left right).eval values =
      left.eval values * right.eval values := by
  have zeroDot : IntList.dot right.coeffs values = 0 :=
    Coefficients.intList_dot_of_left_zero _ _ constantRight
  change right.coeffs.dot values = 0 at zeroDot
  unfold LinearCombo.mul
  rw [sub_eval, add_eval, smul_eval,
    smul_eval]
  simp only [LinearCombo.eval, IntList.dot_nil_left, Int.add_zero]
  rw [zeroDot]
  ring1

/-- Multiplication of finite linear combinations is sound when either coefficient vector is zero.

The displayed disjunction selects a constant factor, so the linearized product evaluates to the product of the original
evaluations. -/
theorem mul_eval (left right : LinearCombo) (values : Coeffs)
    (oneConstant : left.coeffs.isZero ∨ right.coeffs.isZero) :
    (LinearCombo.mul left right).eval values =
      left.eval values * right.eval values := by
  rcases oneConstant with constantLeft | constantRight
  · exact mul_eval_of_const_left left right values constantLeft
  · exact mul_eval_of_const_right left right values constantRight
end Purelib.Tactic.Omega.LinearCombination

end

end
