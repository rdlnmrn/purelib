module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Additive.TriangleBounds
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.PositiveMul
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Additive

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Rational.Roots

section

/-- The finite ordered-field content of being a nonzero triangle spread. -/
@[expose] def PositiveUnitSpread (spread :
  Fraction.Rational) : Prop :=
  0 < spread ∧ spread ≤ 1

/-- An explicit nonnegative square root for the discriminant in the normal form of the Triple spread formula. This
replaces any completed square-root operation by finite rational data. -/
@[expose] def SpreadRootWitness
    (first second root : Fraction.Rational) : Prop :=
  0 ≤ root ∧
    root ^ 2 = first * second * (1 - first) * (1 - second)

/-- The lower of the two displayed roots in §20.5, relative to an explicit rational square-root witness. -/
@[expose] def littleSpread (first second root :
  Fraction.Rational) : Fraction.Rational :=
  first + second - 2 * first * second - 2 * root

/-- The upper of the two displayed roots in §20.5, relative to an explicit rational square-root witness. -/
@[expose] def bigSpread (first second root :
  Fraction.Rational) : Fraction.Rational :=
  first + second - 2 * first * second + 2 * root

/-- The Triple spread equation has exactly the two displayed finite roots once a square-root witness is supplied. -/
theorem spreadTriple_eq_little_or_big
    (first second third root : Fraction.Rational)
    (triple : TripleSpread.SpreadTriple first second third)
    (rootWitness : SpreadRootWitness first second root) :
    third = littleSpread first second root ∨
      third = bigSpread first second root := by
  have normalForm := (Triple.exercise_7_6 triple).2.2.2.2
  have equalSquares :
      (third - (first + second - 2 * first * second)) ^ 2 =
        (2 * root) ^ 2 := by
    calc
      (third - (first + second - 2 * first * second)) ^ 2 =
          4 * first * second * (1 - first) * (1 - second) := normalForm
      _ = 4 * (first * second * (1 - first) * (1 - second)) := by
        ring1
      _ = 4 * root ^ 2 := by rw [← rootWitness.2]
      _ = (2 * root) ^ 2 := by ring1
  have factorProduct :
      (third - (first + second - 2 * first * second) - 2 * root) *
          (third - (first + second - 2 * first * second) + 2 * root) =
        0 := by
    calc
      (third - (first + second - 2 * first * second) - 2 * root) *
            (third - (first + second - 2 * first * second) + 2 * root) =
          (third - (first + second - 2 * first * second)) ^ 2 -
            (2 * root) ^ 2 := by ring1
      _ = 0 := by rw [equalSquares]; ring1
  by_cases upperRoot :
      third - (first + second - 2 * first * second) - 2 * root = 0
  · right
    unfold bigSpread
    apply Group.eq_of_sub_eq_zero
    calc
      third - (first + second - 2 * first * second + 2 * root) =
          third - (first + second - 2 * first * second) - 2 * root := by
            ring1
      _ = 0 := upperRoot
  · by_cases lowerRoot :
        third - (first + second - 2 * first * second) + 2 * root = 0
    · left
      unfold littleSpread
      apply Group.eq_of_sub_eq_zero
      calc
        third - (first + second - 2 * first * second - 2 * root) =
            third - (first + second - 2 * first * second) + 2 * root := by
              ring1
        _ = 0 := lowerRoot
    · exact False.elim
        ((Algebra.Field.ExplicitField.mul_ne_zero upperRoot lowerRoot) factorProduct)

/-- The big root automatically makes the first two sectors acute. -/
theorem bigSpread_first_second_acute
    (first second root : Fraction.Rational)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (firstAtMostOne : first ≤ 1) (secondAtMostOne : second ≤ 1)
    (rootNonnegative : 0 ≤ root) :
    first ≤ bigSpread first second root + second ∧
      second ≤ bigSpread first second root + first := by
  have twoNonnegative : (0 : Fraction.Rational) ≤ 2 := by decide
  have firstComplementNonnegative : 0 ≤ 1 - first :=
    Fraction.Order.Arithmetic.sub_nonneg_direct firstAtMostOne
  have secondComplementNonnegative : 0 ≤ 1 - second :=
    Fraction.Order.Arithmetic.sub_nonneg_direct secondAtMostOne
  have firstTermNonnegative :
      0 ≤ 2 * second * (1 - first) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct twoNonnegative
        secondNonnegative)
      firstComplementNonnegative
  have secondTermNonnegative :
      0 ≤ 2 * first * (1 - second) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct twoNonnegative
        firstNonnegative)
      secondComplementNonnegative
  have rootTermNonnegative : 0 ≤ 2 * root :=
    Fraction.Order.Arithmetic.mul_nonneg_direct twoNonnegative
      rootNonnegative
  constructor
  · apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      bigSpread first second root + second - first =
          2 * second * (1 - first) + 2 * root := by
            unfold bigSpread
            ring1
      _ ≥ 0 := Fraction.Order.add_nonnegative firstTermNonnegative rootTermNonnegative
  · apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      bigSpread first second root + first - second =
          2 * first * (1 - second) + 2 * root := by
            unfold bigSpread
            ring1
      _ ≥ 0 := Fraction.Order.add_nonnegative secondTermNonnegative rootTermNonnegative

/-- Triangle spread rule 1: among the two finite roots of the Triple spread formula, the third spread is the big root
exactly when the first two sectors are acute. The hypotheses state explicitly the positivity and unit bounds that come
from a nondegenerate rational triangle. -/
theorem triangle_spread_rule_1
    (first second third root : Fraction.Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (thirdRange : PositiveUnitSpread third)
    (triple : TripleSpread.SpreadTriple first second third)
    (rootWitness : SpreadRootWitness first second root) :
    third = bigSpread first second root ↔
      first ≤ third + second ∧ second ≤ third + first := by
  have firstNonnegative : 0 ≤ first :=
    Fraction.Order.Arithmetic.le_of_lt_direct firstRange.1
  have secondNonnegative : 0 ≤ second :=
    Fraction.Order.Arithmetic.le_of_lt_direct secondRange.1
  have firstComplementNonnegative : 0 ≤ 1 - first :=
    Fraction.Order.Arithmetic.sub_nonneg_direct firstRange.2
  have secondComplementNonnegative : 0 ≤ 1 - second :=
    Fraction.Order.Arithmetic.sub_nonneg_direct secondRange.2
  constructor
  · intro thirdBig
    rw [thirdBig]
    exact bigSpread_first_second_acute first second root
      firstNonnegative
      secondNonnegative firstRange.2 secondRange.2 rootWitness.1
  · rintro ⟨firstAcute, secondAcute⟩
    rcases spreadTriple_eq_little_or_big first second third root
      triple
      rootWitness with thirdLittle | thirdBig
    · by_cases rootZero : root = 0
      · calc
          third = littleSpread first second root := thirdLittle
          _ = bigSpread first second root := by
            unfold littleSpread bigSpread
            rw [rootZero]
            ring1
      · have rootPositive : 0 < root :=
          lt_of_le_of_ne rootWitness.1 (Ne.symm rootZero)
        have rootSquareProduct :
            root ^ 2 =
              (second * (1 - first)) * (first * (1 - second)) := by
          calc
            root ^ 2 =
                first * second * (1 - first) * (1 - second) :=
              rootWitness.2
            _ = (second * (1 - first)) *
                (first * (1 - second)) := by ring1
        have firstArmNonnegative : 0 ≤ second * (1 - first) :=
          Fraction.Order.Arithmetic.mul_nonneg_direct secondNonnegative
            firstComplementNonnegative
        have secondArmNonnegative : 0 ≤ first * (1 - second) :=
          Fraction.Order.Arithmetic.mul_nonneg_direct firstNonnegative
            secondComplementNonnegative
        have rootSquarePositive : 0 < root ^ 2 :=
          Fraction.Order.Arithmetic.pow_pos_direct rootPositive 2
        have armProductPositive :
            0 < (second * (1 - first)) * (first * (1 - second)) := by
          rw [← rootSquareProduct]
          exact rootSquarePositive
        have secondArmPositive : 0 < first * (1 - second) :=
          Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
            armProductPositive firstArmNonnegative
        have firstArmPositive : 0 < second * (1 - first) := by
          exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
            (by simpa only [mul_comm] using armProductPositive)
            secondArmNonnegative
        have rootLeFirstArm : root ≤ second * (1 - first) := by
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
            (c := (2 : Fraction.Rational))
          · have acuteDifference : 0 ≤ third + second - first :=
              Fraction.Order.Arithmetic.sub_nonneg_direct firstAcute
            have scaled :
                root * 2 ≤ (second * (1 - first)) * 2 := by
              apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
              calc
                (second * (1 - first)) * 2 - root * 2 =
                    third + second - first := by
                      rw [thirdLittle]
                      unfold littleSpread
                      ring1
                _ ≥ 0 := acuteDifference
            exact scaled
          · decide
        have rootLeSecondArm : root ≤ first * (1 - second) := by
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
            (c := (2 : Fraction.Rational))
          · have acuteDifference : 0 ≤ third + first - second :=
              Fraction.Order.Arithmetic.sub_nonneg_direct secondAcute
            have scaled :
                root * 2 ≤ (first * (1 - second)) * 2 := by
              apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
              calc
                (first * (1 - second)) * 2 - root * 2 =
                    third + first - second := by
                      rw [thirdLittle]
                      unfold littleSpread
                      ring1
                _ ≥ 0 := acuteDifference
            exact scaled
          · decide
        have rootSquareLeFirstArmSquare :
            root ^ 2 ≤ (second * (1 - first)) ^ 2 :=
          Fraction.Order.Arithmetic.pow_le_pow_direct rootWitness.1
            rootLeFirstArm 2
        have rootSquareLeSecondArmSquare :
            root ^ 2 ≤ (first * (1 - second)) ^ 2 :=
          Fraction.Order.Arithmetic.pow_le_pow_direct rootWitness.1
            rootLeSecondArm 2
        have secondArmLeFirstArm :
            first * (1 - second) ≤ second * (1 - first) := by
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
            (c := second * (1 - first))
          · calc
              (first * (1 - second)) * (second * (1 - first)) =
                  root ^ 2 := by rw [mul_comm, rootSquareProduct]
              _ ≤ (second * (1 - first)) ^ 2 :=
                rootSquareLeFirstArmSquare
              _ = (second * (1 - first)) *
                  (second * (1 - first)) := by ring1
          · exact firstArmPositive
        have firstArmLeSecondArm :
            second * (1 - first) ≤ first * (1 - second) := by
          apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
            (c := first * (1 - second))
          · calc
              (second * (1 - first)) * (first * (1 - second)) =
                  root ^ 2 := rootSquareProduct.symm
              _ ≤ (first * (1 - second)) ^ 2 :=
                rootSquareLeSecondArmSquare
              _ = (first * (1 - second)) *
                  (first * (1 - second)) := by ring1
          · exact secondArmPositive
        have armsEqual :
            second * (1 - first) = first * (1 - second) :=
          le_antisymm firstArmLeSecondArm secondArmLeFirstArm
        have firstEqualsSecond : first = second := by
          apply Group.eq_of_sub_eq_zero
          calc
            first - second =
                first * (1 - second) - second * (1 - first) := by ring1
            _ = 0 := by rw [← armsEqual]; ring1
        have firstArmSquareEqualsRootSquare :
            (second * (1 - first)) ^ 2 = root ^ 2 := by
          calc
            (second * (1 - first)) ^ 2 =
                (second * (1 - first)) * (first * (1 - second)) := by
                  rw [armsEqual]
                  ring1
            _ = root ^ 2 := rootSquareProduct.symm
        have firstArmLeRoot : second * (1 - first) ≤ root :=
          Fraction.Order.Arithmetic.le_of_sq_le_sq_direct rootWitness.1
            (by rw [firstArmSquareEqualsRootSquare])
        have rootEqualsFirstArm : root = second * (1 - first) :=
          le_antisymm rootLeFirstArm firstArmLeRoot
        have thirdZero : third = 0 := by
          calc
            third = littleSpread first second root := thirdLittle
            _ = 0 := by
              unfold littleSpread
              rw [rootEqualsFirstArm, firstEqualsSecond]
              ring1
        exact False.elim
          ((Fraction.Order.rational_ne_zero_of_positive thirdRange.1) thirdZero)
    · exact thirdBig

/-- Comparing the explicit square root with `s₁s₂` is equivalent to comparing `s₁+s₂` with one. This is the finite
algebraic sign calculation underlying the second Triangle spread rule. -/
theorem spreadRoot_product_le_iff_sum_le_one
    (first second root : Fraction.Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (rootWitness : SpreadRootWitness first second root) :
    first * second ≤ root ↔ first + second ≤ 1 := by
  have firstNonnegative : 0 ≤ first :=
    Fraction.Order.Arithmetic.le_of_lt_direct firstRange.1
  have secondNonnegative : 0 ≤ second :=
    Fraction.Order.Arithmetic.le_of_lt_direct secondRange.1
  have productPositive : 0 < first * second :=
    Fraction.Order.Arithmetic.mul_pos_direct firstRange.1 secondRange.1
  have productNonnegative : 0 ≤ first * second :=
    Fraction.Order.Arithmetic.le_of_lt_direct productPositive
  constructor
  · intro productLeRoot
    have squareOrder :
        (first * second) ^ 2 ≤ root ^ 2 :=
      Fraction.Order.Arithmetic.pow_le_pow_direct productNonnegative
        productLeRoot 2
    have factoredNonnegative :
        0 ≤ (first * second) * (1 - (first + second)) := by
      calc
        (first * second) * (1 - (first + second)) =
            root ^ 2 - (first * second) ^ 2 := by
              rw [rootWitness.2]
              ring1
        _ ≥ 0 := Fraction.Order.Arithmetic.sub_nonneg_direct squareOrder
    have complementNonnegative : 0 ≤ 1 - (first + second) :=
      (Fraction.Order.PositiveMul.nonnegative_mul_iff_of_positive (first * second)
        (1 - (first + second)) productPositive).1 factoredNonnegative
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      complementNonnegative
  · intro sumLeOne
    have complementNonnegative : 0 ≤ 1 - (first + second) :=
      Fraction.Order.Arithmetic.sub_nonneg_direct sumLeOne
    have factoredNonnegative :
        0 ≤ (first * second) * (1 - (first + second)) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct productNonnegative
        complementNonnegative
    have squareOrder : (first * second) ^ 2 ≤ root ^ 2 := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        root ^ 2 - (first * second) ^ 2 =
            (first * second) * (1 - (first + second)) := by
              rw [rootWitness.2]
              ring1
        _ ≥ 0 := factoredNonnegative
    exact Fraction.Order.Arithmetic.le_of_sq_le_sq_direct rootWitness.1
      squareOrder

/-- For the big root, being at least `s₁+s₂` is equivalent to `s₁+s₂≤1`. -/
theorem bigSpread_obtuse_iff_sum_le_one
    (first second root : Fraction.Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (rootWitness : SpreadRootWitness first second root) :
    first + second ≤ bigSpread first second root ↔
      first + second ≤ 1 := by
  have twoPositive : (0 : Fraction.Rational) < 2 := by decide
  have rootComparison := spreadRoot_product_le_iff_sum_le_one
    first second root firstRange secondRange rootWitness
  constructor
  · intro bigObtuse
    apply rootComparison.1
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (2 : Fraction.Rational))
    · apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        root * 2 - (first * second) * 2 =
            bigSpread first second root - (first + second) := by
              unfold bigSpread
              ring1
        _ ≥ 0 := Fraction.Order.Arithmetic.sub_nonneg_direct bigObtuse
    · exact twoPositive
  · intro sumLeOne
    have productLeRoot := rootComparison.2 sumLeOne
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      bigSpread first second root - (first + second) =
          (root - first * second) * 2 := by
            unfold bigSpread
            ring1
      _ ≥ 0 :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.sub_nonneg_direct productLeRoot)
          (Fraction.Order.Arithmetic.le_of_lt_direct twoPositive)

/-- Triangle spread rule 2: the third sector is obtuse exactly when the first two are acute and their spreads sum to at
most one. -/
theorem triangle_spread_rule_2
    (first second third root : Fraction.Rational)
    (firstRange : PositiveUnitSpread first)
    (secondRange : PositiveUnitSpread second)
    (thirdRange : PositiveUnitSpread third)
    (triple : TripleSpread.SpreadTriple first second third)
    (rootWitness : SpreadRootWitness first second root) :
    first + second ≤ third ↔
      (first ≤ third + second ∧ second ≤ third + first) ∧
        first + second ≤ 1 := by
  have noTwoObtuse := TriangleBounds.exercise_20_4 first second third
    firstRange.1 secondRange.1 thirdRange.1
  have ruleOne := triangle_spread_rule_1 first second third root
    firstRange secondRange thirdRange triple rootWitness
  have bigCriterion := bigSpread_obtuse_iff_sum_le_one
    first second root firstRange secondRange rootWitness
  constructor
  · intro thirdObtuseBound
    have thirdObtuse : TriangleBounds.ObtuseAtFirst third first second :=
      thirdObtuseBound
    have firstAcute : first ≤ third + second := by
      by_cases acute : first ≤ third + second
      · exact acute
      · have strictObtuse : third + second < first :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct acute
        have firstObtuse : TriangleBounds.ObtuseAtFirst first third second :=
          Fraction.Order.Arithmetic.le_of_lt_direct strictObtuse
        exact False.elim (noTwoObtuse.2.2 ⟨thirdObtuse, firstObtuse⟩)
    have secondAcute : second ≤ third + first := by
      by_cases acute : second ≤ third + first
      · exact acute
      · have strictObtuse : third + first < second :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct acute
        have secondObtuse : TriangleBounds.ObtuseAtFirst second third first :=
          Fraction.Order.Arithmetic.le_of_lt_direct strictObtuse
        have reorderedThirdObtuse : TriangleBounds.ObtuseAtFirst third second first := by
          unfold TriangleBounds.ObtuseAtFirst at thirdObtuse ⊢
          simpa only [add_comm] using thirdObtuse
        exact False.elim
          (noTwoObtuse.2.1 ⟨secondObtuse, reorderedThirdObtuse⟩)
    have thirdBig : third = bigSpread first second root :=
      ruleOne.2 ⟨firstAcute, secondAcute⟩
    have bigObtuseBound :
        first + second ≤ bigSpread first second root := by
      calc
        first + second ≤ third := thirdObtuseBound
        _ = bigSpread first second root := thirdBig
    exact ⟨⟨firstAcute, secondAcute⟩, bigCriterion.1 bigObtuseBound⟩
  · rintro ⟨⟨firstAcute, secondAcute⟩, sumLeOne⟩
    have thirdBig : third = bigSpread first second root :=
      ruleOne.2 ⟨firstAcute, secondAcute⟩
    have bigObtuseBound :
        first + second ≤ bigSpread first second root :=
      bigCriterion.2 sumLeOne
    calc
      first + second ≤ bigSpread first second root := bigObtuseBound
      _ = third := thirdBig.symm

end
end Purelib.Geometry.Trigonometry.Spread.Triple.Rational.Roots

end

end
