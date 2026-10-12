module

import Purelib.Algebra.Field.Characteristic.Nonzero
public import Purelib.Algebra.Group.Basic
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.QuadraticFragment.Imaginary
import Purelib.Algebra.Field.Ratio.Finite
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Triple
public import Purelib.Geometry.Plane.Line.Twist
import Purelib.Geometry.Plane.Line.Twist.Triple
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Triangles

open Purelib.Algebra

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7 field-fragment examples

The book's two complex examples need only one explicitly supplied element
`i` satisfying `i²=-1`.  Keeping that finite field fragment abstract makes the
same proofs usable in admissible finite fields and in the constructive
Gaussian rationals; no completed complex carrier is introduced.
-/

namespace formalisations.DivineProportions.Chapters.Examples

namespace ChapterSevenFieldFragments

variable {K : Type*} [ExplicitField K]
namespace ExampleSevenOne

/-- The first displayed quadrance, equal to one in the original explicit field. -/
def q₁ : K := QuadraticFragment.Imaginary.complexValue (K := K) 0 1 0
/-- The second displayed quadrance, equal to minus one in the original explicit field. -/
def q₂ : K := QuadraticFragment.Imaginary.complexValue (K := K) 0 (-1) 0

/-- The abstract `i` is supplied separately as the third quadrance. -/
def crossNumerator₁ (i : K) : K := QuadraticFragment.Imaginary.complexValue i 4 3
/-- The second cross-law numerator 4 − 3i in the supplied quadratic field fragment. -/
def crossNumerator₂ (i : K) : K := QuadraticFragment.Imaginary.complexValue i 4 (-3)
/-- The third cross-law numerator one in the supplied quadratic field fragment. -/
def crossNumerator₃ (i : K) : K := QuadraticFragment.Imaginary.complexValue i 1 0

/-- Example 7.1's three Cross-law calculations and printed component forms. -/
theorem cross_values
    [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : K) ≠ 0) :
    (((-1 : K) + i - 1) ^ 2) / (4 * (-1) * i) =
        QuadraticFragment.Imaginary.complexValue i 1 (3 / 4) ∧
      ((i + 1 - (-1 : K)) ^ 2) / (4 * i * 1) =
        QuadraticFragment.Imaginary.complexValue i 1 (-(3 / 4)) ∧
      (((1 : K) + (-1) - i) ^ 2) / (4 * 1 * (-1)) =
        QuadraticFragment.Imaginary.complexValue i (1 / 4) 0 := by
  have iNonzero := QuadraticFragment.Imaginary.i_nonzero i iSquare
  have fourNonzero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
    (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero (K := K) twoNonzero : (4 : K) ≠ 0)) twoNonzero
  have firstDenominatorNonzero : (4 : K) * (-1) * i ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero (Group.neg_ne_zero one_ne_zero))
      iNonzero
  have secondDenominatorNonzero : (4 : K) * i * 1 ≠ 0 := by
    simpa only [mul_one] using ExplicitField.mul_ne_zero fourNonzero iNonzero
  have thirdDenominatorNonzero : (4 : K) * 1 * (-1) ≠ 0 := by
    simpa only [mul_one] using
      ExplicitField.mul_ne_zero fourNonzero (Group.neg_ne_zero one_ne_zero)
  constructor
  · calc
      (((-1 : K) + i - 1) ^ 2) / (4 * (-1) * i) =
          crossNumerator₁ i / 4 := by
        apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero fourNonzero
        unfold crossNumerator₁ QuadraticFragment.Imaginary.complexValue
        calc
          (((-1 : K) + i - 1) ^ 2) * 4 =
              (4 + 3 * i) * (4 * (-1) * i) + 16 * (i ^ 2 + 1) := by ring1
          _ = (4 + 3 * i) * (4 * (-1) * i) := by rw [iSquare]; ring1
      _ = QuadraticFragment.Imaginary.complexValue i (4 / 4) (3 / 4) :=
        QuadraticFragment.Imaginary.complexValue_div i 4 3 4 fourNonzero
      _ = QuadraticFragment.Imaginary.complexValue i 1 (3 / 4) := by
        apply congrArg (fun value : K => QuadraticFragment.Imaginary.complexValue i value (3 / 4))
        apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
        rw [ExplicitField.div_mul_cancel 4 fourNonzero]
        ring1
  constructor
  · calc
      ((i + 1 - (-1 : K)) ^ 2) / (4 * i * 1) =
          crossNumerator₂ i / 4 := by
        apply Ratio.ratio_eq_of_cross_product secondDenominatorNonzero fourNonzero
        unfold crossNumerator₂ QuadraticFragment.Imaginary.complexValue
        calc
          ((i + 1 - (-1 : K)) ^ 2) * 4 =
              (4 + (-3) * i) * (4 * i * 1) + 16 * (i ^ 2 + 1) := by ring1
          _ = (4 + (-3) * i) * (4 * i * 1) := by rw [iSquare]; ring1
      _ = QuadraticFragment.Imaginary.complexValue i (4 / 4) ((-3) / 4) :=
        QuadraticFragment.Imaginary.complexValue_div i 4 (-3) 4 fourNonzero
      _ = QuadraticFragment.Imaginary.complexValue i 1 (-(3 / 4)) := by
        unfold QuadraticFragment.Imaginary.complexValue
        have selfDivision : (4 : K) / 4 = 1 := by
          apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
          rw [ExplicitField.div_mul_cancel 4 fourNonzero]
          ring1
        rw [selfDivision]
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  · calc
      (((1 : K) + (-1) - i) ^ 2) / (4 * 1 * (-1)) =
          crossNumerator₃ i / 4 := by
        apply Ratio.ratio_eq_of_cross_product thirdDenominatorNonzero fourNonzero
        unfold crossNumerator₃ QuadraticFragment.Imaginary.complexValue
        calc
          (((1 : K) + (-1) - i) ^ 2) * 4 =
              (1 + 0 * i) * (4 * 1 * (-1)) + 4 * (i ^ 2 + 1) := by ring1
          _ = (1 + 0 * i) * (4 * 1 * (-1)) := by rw [iSquare]; ring1
      _ = QuadraticFragment.Imaginary.complexValue i (1 / 4) (0 / 4) :=
        QuadraticFragment.Imaginary.complexValue_div i 1 0 4 fourNonzero
      _ = QuadraticFragment.Imaginary.complexValue i (1 / 4) 0 := by
        rw [ExplicitField.zero_div]

/-- Both sides of the Triple cross formula reduce to `25/16`. -/
theorem triple_cross_value
    (i : K) (iSquare : i ^ 2 = -1) (twoNonzero : (2 : K) ≠ 0) :
    let c₁ := QuadraticFragment.Imaginary.complexValue i 1 (3 / 4)
    let c₂ := QuadraticFragment.Imaginary.complexValue i 1 (-(3 / 4))
    let c₃ := QuadraticFragment.Imaginary.complexValue i (1 / 4) 0
    (c₁ + c₂ + c₃ - 1) ^ 2 = 25 / 16 ∧
      4 * c₁ * c₂ * c₃ = 25 / 16 := by
  dsimp only
  have fourNonzero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
    (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero (K := K) twoNonzero : (4 : K) ≠ 0)) twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 * 4 by ring1]
    exact ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have fourCancel := ExplicitField.mul_inv_cancel (4 : K) fourNonzero
  have sixteenCancel := ExplicitField.mul_inv_cancel (16 : K) sixteenNonzero
  have rightScaled : ((25 : K) * 16⁻¹) * 16 = 25 := by
    calc
      ((25 : K) * 16⁻¹) * 16 = 25 * (16 * 16⁻¹) := by ring1
      _ = 25 := by rw [sixteenCancel]; ring1
  simp only [ExplicitField.div_eq_mul_inv]
  constructor
  · unfold QuadraticFragment.Imaginary.complexValue
    apply ExplicitField.eq_of_mul_eq_mul_right sixteenNonzero
    rw [rightScaled]
    calc
      ((1 + 3 * 4⁻¹ * i + (1 + -(3 * 4⁻¹) * i) +
            (1 * 4⁻¹ + 0 * i) - 1) ^ 2) * 16 =
          25 + (4 * 4⁻¹ - 1) * (4 * 4⁻¹ + 9) := by ring1
      _ = 25 := by rw [fourCancel]; ring1
  · unfold QuadraticFragment.Imaginary.complexValue
    apply ExplicitField.eq_of_mul_eq_mul_right sixteenNonzero
    rw [rightScaled]
    calc
      (4 * (1 + 3 * 4⁻¹ * i) * (1 + -(3 * 4⁻¹) * i) *
          (1 * 4⁻¹ + 0 * i)) * 16 =
        25 + (4 * 4⁻¹ - 1) *
            (144 * (4⁻¹) ^ 2 + 36 * 4⁻¹ + 25) -
          576 * (4⁻¹) ^ 3 * (i ^ 2 + 1) := by ring1
      _ = 25 := by rw [fourCancel, iSquare]; ring1

end ExampleSevenOne

namespace ExampleSevenFour

/-- Exactly the prime-characteristic exclusions needed by the denominators in
Example 7.4.  They hold in the constructive Gaussian rationals and in every
finite field fragment whose characteristic avoids these six primes. -/
structure AdmissibleCharacteristic (K : Type*) [ExplicitField K] : Prop where
  /-- The field characteristic does not divide two. -/ twoNonzero : (2 : K) ≠ 0
  /-- The field characteristic does not divide three. -/ threeNonzero : (3 : K) ≠ 0
  /-- The field characteristic does not divide five. -/ fiveNonzero : (5 : K) ≠ 0
  /-- The field characteristic does not divide thirteen. -/ thirteenNonzero : (13 : K) ≠ 0
  /-- The field characteristic does not divide seventeen. -/ seventeenNonzero : (17 : K) ≠ 0
  /-- The field characteristic does not divide forty-one. -/ fortyOneNonzero : (41 : K) ≠ 0

/-- Eight is nonzero under the retained characteristic exclusions. -/
private theorem eight_nonzero
    (admissible : AdmissibleCharacteristic K) : (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.twoNonzero

/-- Twenty is nonzero under the retained characteristic exclusions. -/
private theorem twenty_nonzero
    (admissible : AdmissibleCharacteristic K) : (20 : K) ≠ 0 := by
  rw [show (20 : K) = 2 * 2 * 5 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.fiveNonzero

/-- Thirty-four is nonzero under the retained characteristic exclusions. -/
private theorem thirtyFour_nonzero
    (admissible : AdmissibleCharacteristic K) : (34 : K) ≠ 0 := by
  rw [show (34 : K) = 2 * 17 by ring1]
  exact ExplicitField.mul_ne_zero admissible.twoNonzero
    admissible.seventeenNonzero

/-- Forty is nonzero under the retained characteristic exclusions. -/
private theorem forty_nonzero
    (admissible : AdmissibleCharacteristic K) : (40 : K) ≠ 0 := by
  rw [show (40 : K) = 2 * 2 * 2 * 5 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.twoNonzero admissible.fiveNonzero

/-- Fifty-two is nonzero under the retained characteristic exclusions. -/
private theorem fiftyTwo_nonzero
    (admissible : AdmissibleCharacteristic K) : (52 : K) ≠ 0 := by
  rw [show (52 : K) = 2 * 2 * 13 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.thirteenNonzero

/-- Sixty-five is nonzero under the retained characteristic exclusions. -/
private theorem sixtyFive_nonzero
    (admissible : AdmissibleCharacteristic K) : (65 : K) ≠ 0 := by
  rw [show (65 : K) = 5 * 13 by ring1]
  exact ExplicitField.mul_ne_zero admissible.fiveNonzero
    admissible.thirteenNonzero

/-- Eighty-two is nonzero under the retained characteristic exclusions. -/
private theorem eightyTwo_nonzero
    (admissible : AdmissibleCharacteristic K) : (82 : K) ≠ 0 := by
  rw [show (82 : K) = 2 * 41 by ring1]
  exact ExplicitField.mul_ne_zero admissible.twoNonzero
    admissible.fortyOneNonzero

/-- One hundred four is nonzero under the retained characteristic exclusions. -/
private theorem oneHundredFour_nonzero
    (admissible : AdmissibleCharacteristic K) : (104 : K) ≠ 0 := by
  rw [show (104 : K) = 2 * 2 * 2 * 13 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
    admissible.twoNonzero admissible.thirteenNonzero

/-- One hundred thirty is nonzero under the retained characteristic exclusions. -/
private theorem oneHundredThirty_nonzero
    (admissible : AdmissibleCharacteristic K) : (130 : K) ≠ 0 := by
  rw [show (130 : K) = 2 * 5 * 13 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.twoNonzero admissible.fiveNonzero
    admissible.thirteenNonzero

/-- Nine is nonzero under the retained characteristic exclusions. -/
private theorem nine_nonzero
    (admissible : AdmissibleCharacteristic K) : (9 : K) ≠ 0 := by
  rw [show (9 : K) = 3 * 3 by ring1]
  exact ExplicitField.mul_ne_zero admissible.threeNonzero
    admissible.threeNonzero

/-- Eighteen is nonzero under the retained characteristic exclusions. -/
private theorem eighteen_nonzero
    (admissible : AdmissibleCharacteristic K) : (18 : K) ≠ 0 := by
  rw [show (18 : K) = 2 * 3 * 3 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.twoNonzero admissible.threeNonzero
    admissible.threeNonzero

/-- Two hundred eighty-nine is nonzero under the retained characteristic exclusions. -/
private theorem twoHundredEightyNine_nonzero
    (admissible : AdmissibleCharacteristic K) : (289 : K) ≠ 0 := by
  rw [show (289 : K) = 17 * 17 by ring1]
  exact ExplicitField.mul_ne_zero admissible.seventeenNonzero
    admissible.seventeenNonzero

/-- Five hundred twenty is nonzero under the retained characteristic exclusions. -/
private theorem fiveHundredTwenty_nonzero
    (admissible : AdmissibleCharacteristic K) : (520 : K) ≠ 0 := by
  rw [show (520 : K) = (2 * 2 * 2 * 5) * 13 by ring1]
  exact ExplicitField.mul_ne_zero
    (Purelib.Algebra.Field.ExplicitField.mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
      admissible.twoNonzero admissible.fiveNonzero)
    admissible.thirteenNonzero

/-- One thousand forty is nonzero under the retained characteristic exclusions. -/
private theorem oneThousandForty_nonzero
    (admissible : AdmissibleCharacteristic K) : (1040 : K) ≠ 0 := by
  rw [show (1040 : K) = 2 * (2 * 2 * 2 * 5) * 13 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.twoNonzero
    (Purelib.Algebra.Field.ExplicitField.mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
      admissible.twoNonzero admissible.fiveNonzero)
    admissible.thirteenNonzero

/-- One thousand six hundred eighty-one is nonzero under the retained characteristic exclusions. -/
private theorem oneThousandSixHundredEightyOne_nonzero
    (admissible : AdmissibleCharacteristic K) : (1681 : K) ≠ 0 := by
  rw [show (1681 : K) = 41 * 41 by ring1]
  exact ExplicitField.mul_ne_zero admissible.fortyOneNonzero
    admissible.fortyOneNonzero

/-- Two thousand ninety-one is nonzero under the retained characteristic exclusions. -/
private theorem twoThousandNinetyOne_nonzero
    (admissible : AdmissibleCharacteristic K) : (2091 : K) ≠ 0 := by
  rw [show (2091 : K) = 3 * 17 * 41 by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.threeNonzero
    admissible.seventeenNonzero admissible.fortyOneNonzero

/-- Four thousand two hundred twenty-five is nonzero under the retained characteristic exclusions. -/
private theorem fourThousandTwoHundredTwentyFive_nonzero
    (admissible : AdmissibleCharacteristic K) : (4225 : K) ≠ 0 := by
  rw [show (4225 : K) = (5 * 5) * (13 * 13) by ring1]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero admissible.fiveNonzero
      admissible.fiveNonzero)
    (ExplicitField.mul_ne_zero admissible.thirteenNonzero
      admissible.thirteenNonzero)

/-- The denominator 135200 is nonzero under the retained characteristic exclusions. -/
private theorem oneHundredThirtyFiveThousandTwoHundred_nonzero
    (admissible : AdmissibleCharacteristic K) : (135200 : K) ≠ 0 := by
  rw [show (135200 : K) =
      (2 * 2 * 2 * 2 * 2) * (5 * 5) * (13 * 13) by ring1]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (Purelib.Algebra.Field.ExplicitField.mul_four_ne_zero admissible.twoNonzero admissible.twoNonzero
          admissible.twoNonzero admissible.twoNonzero)
        admissible.twoNonzero)
      (ExplicitField.mul_ne_zero admissible.fiveNonzero
        admissible.fiveNonzero))
    (ExplicitField.mul_ne_zero admissible.thirteenNonzero
      admissible.thirteenNonzero)

/-- The denominator 1457427 is nonzero under the retained characteristic exclusions. -/
private theorem oneMillionFourHundredFiftySevenThousandFourHundredTwentySeven_nonzero
    (admissible : AdmissibleCharacteristic K) : (1457427 : K) ≠ 0 := by
  rw [show (1457427 : K) = 3 * (17 * 17) * (41 * 41) by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero admissible.threeNonzero
    (ExplicitField.mul_ne_zero admissible.seventeenNonzero
      admissible.seventeenNonzero)
    (ExplicitField.mul_ne_zero admissible.fortyOneNonzero
      admissible.fortyOneNonzero)

/-- The denominator 4372281 is nonzero under the retained characteristic exclusions. -/
private theorem fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
    (admissible : AdmissibleCharacteristic K) : (4372281 : K) ≠ 0 := by
  rw [show (4372281 : K) = (3 * 3) * (17 * 17) * (41 * 41) by ring1]
  exact Purelib.Algebra.Field.ExplicitField.mul_three_ne_zero
    (ExplicitField.mul_ne_zero admissible.threeNonzero
      admissible.threeNonzero)
    (ExplicitField.mul_ne_zero admissible.seventeenNonzero
      admissible.seventeenNonzero)
    (ExplicitField.mul_ne_zero admissible.fortyOneNonzero
      admissible.fortyOneNonzero)

/-- The origin vertex `A₁=[0,0]`. -/
def point₁ : Purelib.Geometry.Plane.Point K := ⟨0, 0⟩

/-- The second vertex `A₂=[3,-i]`. -/
def point₂ (i : K) : Purelib.Geometry.Plane.Point K := ⟨3, -i⟩

/-- The third vertex `A₃=[1+i,2i]`. -/
def point₃ (i : K) : Purelib.Geometry.Plane.Point K := ⟨1 + i, 2 * i⟩

/-- The side `A₂A₃`, with the exact coefficient triple
`⟨-3i:-2+i:-1+7i⟩`. -/
def line₁ (i : K) (threeNonzero : (3 : K) ≠ 0) (iNonzero : i ≠ 0) :
    Purelib.Geometry.Plane.Line K where
  a := -3 * i
  b := -2 + i
  c := QuadraticFragment.Imaginary.complexValue i (-1) 7
  direction_nonzero := Or.inl
    (ExplicitField.mul_ne_zero (Group.neg_ne_zero threeNonzero) iNonzero)

/-- The side `A₁A₃`, represented by `⟨-2i:1+i:0⟩`. -/
def line₂ (i : K) (twoNonzero : (2 : K) ≠ 0) (iNonzero : i ≠ 0) :
    Purelib.Geometry.Plane.Line K where
  a := -2 * i
  b := 1 + i
  c := 0
  direction_nonzero := Or.inl
    (ExplicitField.mul_ne_zero (Group.neg_ne_zero twoNonzero) iNonzero)

/-- The side `A₁A₂`, represented by `⟨i:3:0⟩`. -/
def line₃ (i : K) (iNonzero : i ≠ 0) : Purelib.Geometry.Plane.Line K where
  a := i
  b := 3
  c := 0
  direction_nonzero := Or.inl iNonzero

/-- The three quadrances printed in Example 7.4. -/
theorem quadrance_values
    (i : K) (iSquare : i ^ 2 = -1) :
    Point.Quadrance.quadrance (point₂ i) (point₃ i) = QuadraticFragment.Imaginary.complexValue i (-6) (-4) ∧
      Point.Quadrance.quadrance point₁ (point₃ i) = QuadraticFragment.Imaginary.complexValue i (-4) 2 ∧
      Point.Quadrance.quadrance point₁ (point₂ i) = 8 := by
  constructor
  · unfold Point.Quadrance.quadrance point₂ point₃ QuadraticFragment.Imaginary.complexValue
    calc
      ((1 + i - 3) ^ 2 + (2 * i - -i) ^ 2) =
          (-6 + -4 * i) + 10 * (i ^ 2 + 1) := by ring1
      _ = -6 + -4 * i := by rw [iSquare]; ring1
  constructor
  · unfold Point.Quadrance.quadrance point₁ point₃ QuadraticFragment.Imaginary.complexValue
    calc
      ((1 + i - 0) ^ 2 + (2 * i - 0) ^ 2) =
          (-4 + 2 * i) + 5 * (i ^ 2 + 1) := by ring1
      _ = -4 + 2 * i := by rw [iSquare]; ring1
  · unfold Point.Quadrance.quadrance point₁ point₂
    calc
      ((3 : K) - 0) ^ 2 + (-i - 0) ^ 2 = 8 + (i ^ 2 + 1) := by ring1
      _ = 8 := by rw [iSquare]; ring1

/-- The printed quadrea `-192-56i`. -/
theorem quadrea_value (i : K) (iSquare : i ^ 2 = -1) :
    Quadrea.Basic.quadrea point₁ (point₂ i) (point₃ i) =
      QuadraticFragment.Imaginary.complexValue i (-192) (-56) := by
  rw [Quadrea.Basic.quadrea_coordinate_formula]
  have determinantValue :
      Line.Incidence.pointDeterminant point₁ (point₂ i) (point₃ i) =
        QuadraticFragment.Imaginary.complexValue i (-1) 7 := by
    unfold Line.Incidence.pointDeterminant point₁ point₂ point₃ QuadraticFragment.Imaginary.complexValue
    change
      0 * (-i) - 0 * (2 * i) + 3 * (2 * i) - (1 + i) * (-i) +
          (1 + i) * 0 - 3 * 0 = -1 + 7 * i
    calc
      0 * (-i) - 0 * (2 * i) + 3 * (2 * i) - (1 + i) * (-i) +
          (1 + i) * 0 - 3 * 0 =
        i ^ 2 + 7 * i := by ring1
      _ = -1 + 7 * i := by rw [iSquare]
  rw [determinantValue, QuadraticFragment.Imaginary.complexValue_square i (-1) 7 iSquare]
  unfold QuadraticFragment.Imaginary.complexValue
  ring1

/-- Each displayed side contains its two defining vertices. -/
theorem line_incidence [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    (line₁ i admissible.threeNonzero iNonzero).Contains (point₂ i) ∧
      (line₁ i admissible.threeNonzero iNonzero).Contains (point₃ i) ∧
      (line₂ i admissible.twoNonzero iNonzero).Contains point₁ ∧
      (line₂ i admissible.twoNonzero iNonzero).Contains (point₃ i) ∧
      (line₃ i iNonzero).Contains point₁ ∧
      (line₃ i iNonzero).Contains (point₂ i) := by
  dsimp only
  unfold Purelib.Geometry.Plane.Line.Contains line₁ line₂ line₃ point₁ point₂ point₃
  unfold QuadraticFragment.Imaginary.complexValue
  constructor
  · calc
      (-3 * i) * 3 + (-2 + i) * -i + (-1 + 7 * i) =
          -(i ^ 2 + 1) := by ring1
      _ = 0 := by rw [iSquare]; ring1
  constructor
  · calc
      (-3 * i) * (1 + i) + (-2 + i) * (2 * i) + (-1 + 7 * i) =
          -(i ^ 2 + 1) := by ring1
      _ = 0 := by rw [iSquare]; ring1
  exact ⟨by ring1, by ring1, by ring1, by ring1⟩

/-- The side norms are the opposite quadrances, as printed. -/
theorem line_norm_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    Line.Basic.lineNorm (line₁ i admissible.threeNonzero iNonzero) =
        QuadraticFragment.Imaginary.complexValue i (-6) (-4) ∧
      Line.Basic.lineNorm (line₂ i admissible.twoNonzero iNonzero) =
        QuadraticFragment.Imaginary.complexValue i (-4) 2 ∧
      Line.Basic.lineNorm (line₃ i iNonzero) = 8 := by
  dsimp only
  unfold Line.Basic.lineNorm line₁ line₂ line₃ QuadraticFragment.Imaginary.complexValue
  constructor
  · calc
      (-3 * i) ^ 2 + (-2 + i) ^ 2 =
          (-6 + -4 * i) + 10 * (i ^ 2 + 1) := by ring1
      _ = -6 + -4 * i := by rw [iSquare]; ring1
  constructor
  · calc
      (-2 * i) ^ 2 + (1 + i) ^ 2 =
          (-4 + 2 * i) + 5 * (i ^ 2 + 1) := by ring1
      _ = -4 + 2 * i := by rw [iSquare]; ring1
  · calc
      i ^ 2 + (3 : K) ^ 2 = 8 + (i ^ 2 + 1) := by ring1
      _ = 8 := by rw [iSquare]; ring1

/-- The displayed first quadrance −6 − 4i is nonzero when the retained characteristic exclusions hold. -/
private theorem firstQuadrance_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    QuadraticFragment.Imaginary.complexValue i (-6) (-4) ≠ 0 := by
  intro valueZero
  apply fiftyTwo_nonzero admissible
  calc
    (52 : K) = QuadraticFragment.Imaginary.complexValue i (-6) (-4) * QuadraticFragment.Imaginary.complexValue i (-6) 4
      := by
      rw [QuadraticFragment.Imaginary.complexValue_mul i (-6) (-4) (-6) 4 iSquare]
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

/-- The displayed second quadrance −4 + 2i is nonzero when the retained characteristic exclusions hold. -/
private theorem secondQuadrance_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    QuadraticFragment.Imaginary.complexValue i (-4) 2 ≠ 0 := by
  intro valueZero
  apply twenty_nonzero admissible
  calc
    (20 : K) = QuadraticFragment.Imaginary.complexValue i (-4) 2 * QuadraticFragment.Imaginary.complexValue i (-4) (-2)
      := by
      rw [QuadraticFragment.Imaginary.complexValue_mul i (-4) 2 (-4) (-2) iSquare]
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

/-- The three side lines are non-null, with constructive witnesses obtained
from the small integer norms `52`, `20`, and `8`. -/
theorem side_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    ¬ (line₁ i admissible.threeNonzero iNonzero).IsNull ∧
      ¬ (line₂ i admissible.twoNonzero iNonzero).IsNull ∧
      ¬ (line₃ i iNonzero).IsNull := by
  dsimp only
  have norms := line_norm_values i iSquare admissible
  constructor
  · intro firstNull
    exact firstQuadrance_nonzero i iSquare admissible (norms.1.symm.trans firstNull)
  constructor
  · intro secondNull
    exact secondQuadrance_nonzero i iSquare admissible
      (norms.2.1.symm.trans secondNull)
  · intro thirdNull
    exact eight_nonzero admissible (norms.2.2.symm.trans thirdNull)

/-- The displayed first side has nonzero line norm in the admissible quadratic fragment. -/
theorem line₁_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    ¬ (line₁ i admissible.threeNonzero (iNonzero)).IsNull :=
  (side_nonNull i iSquare admissible).1

/-- The displayed second side has nonzero line norm in the admissible quadratic fragment. -/
theorem line₂_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    ¬ (line₂ i admissible.twoNonzero (iNonzero)).IsNull :=
  (side_nonNull i iSquare admissible).2.1

/-- The displayed third side has nonzero line norm in the admissible quadratic fragment. -/
theorem line₃_nonNull [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    ¬ (line₃ i (iNonzero)).IsNull :=
  (side_nonNull i iSquare admissible).2.2

/-- All three oriented side-pair determinants equal `1-7i`; their square is
the common spread numerator `-48-14i`. -/
theorem determinant_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    second.a * third.b - third.a * second.b = QuadraticFragment.Imaginary.complexValue i 1 (-7) ∧
      first.a * third.b - third.a * first.b = QuadraticFragment.Imaginary.complexValue i 1 (-7) ∧
      first.a * second.b - second.a * first.b = QuadraticFragment.Imaginary.complexValue i 1 (-7) := by
  dsimp only
  unfold line₁ line₂ line₃ QuadraticFragment.Imaginary.complexValue
  constructor
  · calc
      (-2 * i) * 3 - i * (1 + i) =
          (1 + -7 * i) - (i ^ 2 + 1) := by ring1
      _ = 1 + -7 * i := by rw [iSquare]; ring1
  constructor
  · calc
      (-3 * i) * 3 - i * (-2 + i) =
          (1 + -7 * i) - (i ^ 2 + 1) := by ring1
      _ = 1 + -7 * i := by rw [iSquare]; ring1
  · calc
      (-3 * i) * (1 + i) - (-2 * i) * (-2 + i) =
          (1 + -7 * i) - (i ^ 2 + 1) := by ring1
      _ = 1 + -7 * i := by rw [iSquare]; ring1

/-- The squares of all three displayed side determinants equal −48 − 14i. -/
private theorem determinant_square_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := QuadraticFragment.Imaginary.i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    (second.a * third.b - third.a * second.b) ^ 2 =
        QuadraticFragment.Imaginary.complexValue i (-48) (-14) ∧
      (first.a * third.b - third.a * first.b) ^ 2 =
        QuadraticFragment.Imaginary.complexValue i (-48) (-14) ∧
      (first.a * second.b - second.a * first.b) ^ 2 =
        QuadraticFragment.Imaginary.complexValue i (-48) (-14) := by
  dsimp only
  have determinants := determinant_values i iSquare admissible
  rw [determinants.1, determinants.2.1, determinants.2.2,
    QuadraticFragment.Imaginary.complexValue_square i 1 (-7) iSquare]
  unfold QuadraticFragment.Imaginary.complexValue
  exact ⟨by ring1, by ring1, by ring1⟩

/-- The three dot products used by the twists are `5+3i`, `-3+3i`, and
`-9-i`. -/
theorem dot_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    second.a * third.a + second.b * third.b = QuadraticFragment.Imaginary.complexValue i 5 3 ∧
      first.a * third.a + first.b * third.b = QuadraticFragment.Imaginary.complexValue i (-3) 3 ∧
      first.a * second.a + first.b * second.b = QuadraticFragment.Imaginary.complexValue i (-9) (-1) := by
  dsimp only
  unfold line₁ line₂ line₃ QuadraticFragment.Imaginary.complexValue
  constructor
  · calc
      (-2 * i) * i + (1 + i) * 3 =
          (5 + 3 * i) - 2 * (i ^ 2 + 1) := by ring1
      _ = 5 + 3 * i := by rw [iSquare]; ring1
  constructor
  · calc
      (-3 * i) * i + (-2 + i) * 3 =
          (-3 + 3 * i) - 3 * (i ^ 2 + 1) := by ring1
      _ = -3 + 3 * i := by rw [iSquare]; ring1
  · calc
      (-3 * i) * (-2 * i) + (-2 + i) * (1 + i) =
          (-9 + -1 * i) + 7 * (i ^ 2 + 1) := by ring1
      _ = -9 + -1 * i := by rw [iSquare]; ring1

/-- The three spreads in a single-denominator component form. -/
theorem spread_common_denominator_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    Line.Spread.spread second third (line₂_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          QuadraticFragment.Imaginary.complexValue i 41 38 / 40 ∧
      Line.Spread.spread first third (line₁_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          QuadraticFragment.Imaginary.complexValue i 86 (-27) / 104 ∧
      Line.Spread.spread first second (line₁_nonNull i iSquare admissible)
        (line₂_nonNull i iSquare admissible) =
          QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 130 := by
  dsimp only
  have norms := line_norm_values i iSquare admissible
  have determinants := determinant_square_value i iSquare admissible
  constructor
  · unfold Line.Spread.spread
    rw [determinants.1, norms.2.1, norms.2.2]
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero
        (secondQuadrance_nonzero i iSquare admissible)
        (eight_nonzero admissible))
      (forty_nonzero admissible)
    have denominatorValue :
        QuadraticFragment.Imaginary.complexValue i (-4) 2 * 8 = QuadraticFragment.Imaginary.complexValue i (-32) 16 :=
          by
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    rw [denominatorValue,
      QuadraticFragment.Imaginary.complexValue_mul i 41 38 (-32) 16 iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  constructor
  · unfold Line.Spread.spread
    rw [determinants.2.1, norms.1, norms.2.2]
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero
        (firstQuadrance_nonzero i iSquare admissible)
        (eight_nonzero admissible))
      (oneHundredFour_nonzero admissible)
    have denominatorValue :
        QuadraticFragment.Imaginary.complexValue i (-6) (-4) * 8 = QuadraticFragment.Imaginary.complexValue i (-48)
          (-32) := by
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    rw [denominatorValue,
      QuadraticFragment.Imaginary.complexValue_mul i 86 (-27) (-48) (-32) iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  · unfold Line.Spread.spread
    rw [determinants.2.2, norms.1, norms.2.1]
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero
        (firstQuadrance_nonzero i iSquare admissible)
        (secondQuadrance_nonzero i iSquare admissible))
      (oneHundredThirty_nonzero admissible)
    rw [QuadraticFragment.Imaginary.complexValue_mul i (-6) (-4) (-4) 2 iSquare]
    have denominatorValue :
        QuadraticFragment.Imaginary.complexValue i (-6 * -4 - -4 * 2) (-6 * 2 + -4 * -4) =
          QuadraticFragment.Imaginary.complexValue i 32 4 := by
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    rw [denominatorValue,
      QuadraticFragment.Imaginary.complexValue_mul i (-199) (-32) 32 4 iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1

/-- Example 7.4's three spreads in precisely the reduced component form
printed in the book. -/
theorem spread_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    Line.Spread.spread second third (line₂_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          QuadraticFragment.Imaginary.complexValue i (41 / 40) (19 / 20) ∧
      Line.Spread.spread first third (line₁_nonNull i iSquare admissible)
        (line₃_nonNull i iSquare admissible) =
          QuadraticFragment.Imaginary.complexValue i (43 / 52) (-(27 / 104)) ∧
      Line.Spread.spread first second (line₁_nonNull i iSquare admissible)
        (line₂_nonNull i iSquare admissible) =
          QuadraticFragment.Imaginary.complexValue i (-(199 / 130)) (-(16 / 65)) := by
  dsimp only
  have common := spread_common_denominator_values i iSquare admissible
  have firstImaginary : (38 : K) / 40 = 19 / 20 := by
    apply Ratio.ratio_eq_of_cross_product (forty_nonzero admissible)
      (twenty_nonzero admissible)
    ring1
  have secondReal : (86 : K) / 104 = 43 / 52 := by
    apply Ratio.ratio_eq_of_cross_product (oneHundredFour_nonzero admissible)
      (fiftyTwo_nonzero admissible)
    ring1
  have thirdImaginary : ((-32 : K) / 130) = -(16 / 65) := by
    calc
      ((-32 : K) / 130) = (-16) / 65 := by
        apply Ratio.ratio_eq_of_cross_product (oneHundredThirty_nonzero admissible)
          (sixtyFive_nonzero admissible)
        ring1
      _ = -(16 / 65) := by
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  constructor
  · calc
      Line.Spread.spread (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) =
        QuadraticFragment.Imaginary.complexValue i 41 38 / 40 := common.1
      _ = QuadraticFragment.Imaginary.complexValue i (41 / 40) (38 / 40) :=
        QuadraticFragment.Imaginary.complexValue_div i 41 38 40 (forty_nonzero admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (41 / 40) (19 / 20) := by rw [firstImaginary]
  constructor
  · calc
      Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₁_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) =
        QuadraticFragment.Imaginary.complexValue i 86 (-27) / 104 := common.2.1
      _ = QuadraticFragment.Imaginary.complexValue i (86 / 104) ((-27) / 104) :=
        QuadraticFragment.Imaginary.complexValue_div i 86 (-27) 104 (oneHundredFour_nonzero admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (43 / 52) (-(27 / 104)) := by
        rw [secondReal]
        unfold QuadraticFragment.Imaginary.complexValue
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  · calc
      Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible) =
        QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 130 := common.2.2
      _ = QuadraticFragment.Imaginary.complexValue i ((-199) / 130) ((-32) / 130) :=
        QuadraticFragment.Imaginary.complexValue_div i (-199) (-32) 130
          (oneHundredThirty_nonzero admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (-(199 / 130)) (-(16 / 65)) := by
        rw [thirdImaginary]
        unfold QuadraticFragment.Imaginary.complexValue
        simp only [ExplicitField.div_eq_mul_inv]
        ring1

/-- The three quotients in the Spread law have the common single-denominator
value `(-199-32i)/1040`. -/
theorem spread_law_common_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let s₁ := Line.Spread.spread second third (line₂_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₂ := Line.Spread.spread first third (line₁_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₃ := Line.Spread.spread first second (line₁_nonNull i iSquare admissible)
      (line₂_nonNull i iSquare admissible)
    s₁ / QuadraticFragment.Imaginary.complexValue i (-6) (-4) = QuadraticFragment.Imaginary.complexValue i (-199) (-32)
      / 1040 ∧
      s₂ / QuadraticFragment.Imaginary.complexValue i (-4) 2 = QuadraticFragment.Imaginary.complexValue i (-199) (-32) /
        1040 ∧
      s₃ / 8 = QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 1040 := by
  dsimp only
  have spreads := spread_common_denominator_values i iSquare admissible
  constructor
  · rw [spreads.1]
    calc
      (QuadraticFragment.Imaginary.complexValue i 41 38 / 40) / QuadraticFragment.Imaginary.complexValue i (-6) (-4) =
          QuadraticFragment.Imaginary.complexValue i 41 38 /
            (40 * QuadraticFragment.Imaginary.complexValue i (-6) (-4)) :=
        Ratio.Finite.fraction_div _ _ _ (forty_nonzero admissible)
          (firstQuadrance_nonzero i iSquare admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 1040 := by
        apply Ratio.ratio_eq_of_cross_product
          (ExplicitField.mul_ne_zero (forty_nonzero admissible)
            (firstQuadrance_nonzero i iSquare admissible))
          (oneThousandForty_nonzero admissible)
        have scaledQuadrance :
            (40 : K) * QuadraticFragment.Imaginary.complexValue i (-6) (-4) =
              QuadraticFragment.Imaginary.complexValue i (-240) (-160) := by
          unfold QuadraticFragment.Imaginary.complexValue
          ring1
        rw [scaledQuadrance,
          QuadraticFragment.Imaginary.complexValue_mul i (-199) (-32) (-240) (-160) iSquare]
        unfold QuadraticFragment.Imaginary.complexValue
        ring1
  constructor
  · rw [spreads.2.1]
    calc
      (QuadraticFragment.Imaginary.complexValue i 86 (-27) / 104) / QuadraticFragment.Imaginary.complexValue i (-4) 2 =
          QuadraticFragment.Imaginary.complexValue i 86 (-27) /
            (104 * QuadraticFragment.Imaginary.complexValue i (-4) 2) :=
        Ratio.Finite.fraction_div _ _ _ (oneHundredFour_nonzero admissible)
          (secondQuadrance_nonzero i iSquare admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 1040 := by
        apply Ratio.ratio_eq_of_cross_product
          (ExplicitField.mul_ne_zero
            (oneHundredFour_nonzero admissible)
            (secondQuadrance_nonzero i iSquare admissible))
          (oneThousandForty_nonzero admissible)
        have scaledQuadrance :
            (104 : K) * QuadraticFragment.Imaginary.complexValue i (-4) 2 =
              QuadraticFragment.Imaginary.complexValue i (-416) 208 := by
          unfold QuadraticFragment.Imaginary.complexValue
          ring1
        rw [scaledQuadrance,
          QuadraticFragment.Imaginary.complexValue_mul i (-199) (-32) (-416) 208 iSquare]
        unfold QuadraticFragment.Imaginary.complexValue
        ring1
  · rw [spreads.2.2]
    calc
      (QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 130) / 8 =
          QuadraticFragment.Imaginary.complexValue i (-199) (-32) / (130 * 8) :=
        Ratio.Finite.fraction_div _ _ _ (oneHundredThirty_nonzero admissible)
          (eight_nonzero admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 1040 := by
        congr 1
        ring1

/-- The common Spread-law value in the two reduced components printed by the
book. -/
theorem spread_law_value
    (i : K) (admissible : AdmissibleCharacteristic K) :
    QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 1040 =
      QuadraticFragment.Imaginary.complexValue i (-(199 / 1040)) (-(2 / 65)) := by
  have imaginaryReduction : ((-32 : K) / 1040) = -(2 / 65) := by
    calc
      ((-32 : K) / 1040) = (-2) / 65 := by
        apply Ratio.ratio_eq_of_cross_product (oneThousandForty_nonzero admissible)
          (sixtyFive_nonzero admissible)
        ring1
      _ = -(2 / 65) := by
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  calc
    QuadraticFragment.Imaginary.complexValue i (-199) (-32) / 1040 =
        QuadraticFragment.Imaginary.complexValue i ((-199) / 1040) ((-32) / 1040) :=
      QuadraticFragment.Imaginary.complexValue_div i (-199) (-32) 1040
        (oneThousandForty_nonzero admissible)
    _ = QuadraticFragment.Imaginary.complexValue i (-(199 / 1040)) (-(2 / 65)) := by
      rw [imaginaryReduction]
      unfold QuadraticFragment.Imaginary.complexValue
      simp only [ExplicitField.div_eq_mul_inv]
      ring1

/-- The sum of the three spreads, before squaring, is `(167+231i)/520`. -/
private theorem spread_sum_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := QuadraticFragment.Imaginary.i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    Line.Spread.spread second third (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        Line.Spread.spread first third (line₁_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        Line.Spread.spread first second (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible) =
      QuadraticFragment.Imaginary.complexValue i 167 231 / 520 := by
  dsimp only
  rw [(spread_common_denominator_values i iSquare admissible).1,
    (spread_common_denominator_values i iSquare admissible).2.1,
    (spread_common_denominator_values i iSquare admissible).2.2]
  apply Ratio.Finite.three_fraction_sum_eq
    (QuadraticFragment.Imaginary.complexValue i 41 38) (QuadraticFragment.Imaginary.complexValue i 86 (-27))
    (QuadraticFragment.Imaginary.complexValue i (-199) (-32)) (QuadraticFragment.Imaginary.complexValue i 167 231)
    40 104 130 520 (forty_nonzero admissible)
    (oneHundredFour_nonzero admissible) (oneHundredThirty_nonzero admissible)
    (fiveHundredTwenty_nonzero admissible)
  unfold QuadraticFragment.Imaginary.complexValue
  ring1

/-- The square common to both sides of the Triple spread formula, using one
component denominator. -/
private theorem triple_spread_common_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := QuadraticFragment.Imaginary.i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    (Line.Spread.spread second third (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        Line.Spread.spread first third (line₁_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible) +
        Line.Spread.spread first second (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible)) ^ 2 =
      QuadraticFragment.Imaginary.complexValue i (-12736) 38577 / 135200 := by
  dsimp only
  rw [spread_sum_value i iSquare admissible]
  apply Ratio.Finite.square_fraction_eq
    (QuadraticFragment.Imaginary.complexValue i 167 231) 520 (QuadraticFragment.Imaginary.complexValue i (-12736) 38577)
      135200
    (fiveHundredTwenty_nonzero admissible)
    (oneHundredThirtyFiveThousandTwoHundred_nonzero admissible)
  rw [QuadraticFragment.Imaginary.complexValue_square i 167 231 iSquare]
  unfold QuadraticFragment.Imaginary.complexValue
  ring1

/-- Both sides of the Triple spread formula have the exact value printed in
Example 7.4. -/
theorem triple_spread_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let s₁ := Line.Spread.spread second third (line₂_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₂ := Line.Spread.spread first third (line₁_nonNull i iSquare admissible)
      (line₃_nonNull i iSquare admissible)
    let s₃ := Line.Spread.spread first second (line₁_nonNull i iSquare admissible)
      (line₂_nonNull i iSquare admissible)
    (s₁ + s₂ + s₃) ^ 2 =
        QuadraticFragment.Imaginary.complexValue i (-(398 / 4225)) (38577 / 135200) ∧
      2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ =
        QuadraticFragment.Imaginary.complexValue i (-(398 / 4225)) (38577 / 135200) := by
  dsimp only
  have common := triple_spread_common_value i iSquare admissible
  have realReduction : ((-12736 : K) / 135200) = -(398 / 4225) := by
    calc
      ((-12736 : K) / 135200) = (-398) / 4225 := by
        apply Ratio.ratio_eq_of_cross_product
          (oneHundredThirtyFiveThousandTwoHundred_nonzero admissible)
          (fourThousandTwoHundredTwentyFive_nonzero admissible)
        ring1
      _ = -(398 / 4225) := by
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  have printedValue :
      QuadraticFragment.Imaginary.complexValue i (-12736) 38577 / 135200 =
        QuadraticFragment.Imaginary.complexValue i (-(398 / 4225)) (38577 / 135200) := by
    calc
      QuadraticFragment.Imaginary.complexValue i (-12736) 38577 / 135200 =
          QuadraticFragment.Imaginary.complexValue i ((-12736) / 135200) (38577 / 135200) :=
        QuadraticFragment.Imaginary.complexValue_div i (-12736) 38577 135200
          (oneHundredThirtyFiveThousandTwoHundred_nonzero admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (-(398 / 4225)) (38577 / 135200) := by
        rw [realReduction]
  constructor
  · exact common.trans printedValue
  · calc
      2 *
            (Line.Spread.spread (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                  (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                  (line₂_nonNull i iSquare admissible)
                  (line₃_nonNull i iSquare admissible) ^ 2 +
              Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i
                iSquare))
                  (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                  (line₁_nonNull i iSquare admissible)
                  (line₃_nonNull i iSquare admissible) ^ 2 +
              Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i
                iSquare))
                  (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                  (line₁_nonNull i iSquare admissible)
                  (line₂_nonNull i iSquare admissible) ^ 2) +
          4 *
            Line.Spread.spread (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
              (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
              (line₂_nonNull i iSquare admissible)
              (line₃_nonNull i iSquare admissible) *
            Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i
              iSquare))
              (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
              (line₁_nonNull i iSquare admissible)
              (line₃_nonNull i iSquare admissible) *
            Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i
              iSquare))
              (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
              (line₁_nonNull i iSquare admissible)
              (line₂_nonNull i iSquare admissible) =
          (Line.Spread.spread (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                (line₂_nonNull i iSquare admissible)
                (line₃_nonNull i iSquare admissible) +
            Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i
              iSquare))
                (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                (line₁_nonNull i iSquare admissible)
                (line₃_nonNull i iSquare admissible) +
            Line.Spread.spread (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i
              iSquare))
                (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
                (line₁_nonNull i iSquare admissible)
                (line₂_nonNull i iSquare admissible)) ^ 2 :=
        (Line.Spread.Triple.triple_spread_formula
          (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
          (line₁_nonNull i iSquare admissible)
          (line₂_nonNull i iSquare admissible)
          (line₃_nonNull i iSquare admissible)).symm
      _ = QuadraticFragment.Imaginary.complexValue i (-(398 / 4225)) (38577 / 135200) :=
        common.trans printedValue

/-- The displayed dot product 5 + 3i is nonzero in the admissible quadratic fragment. -/
private theorem firstDot_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    QuadraticFragment.Imaginary.complexValue i 5 3 ≠ 0 := by
  intro valueZero
  apply thirtyFour_nonzero admissible
  calc
    (34 : K) = QuadraticFragment.Imaginary.complexValue i 5 3 * QuadraticFragment.Imaginary.complexValue i 5 (-3) := by
      rw [QuadraticFragment.Imaginary.complexValue_mul i 5 3 5 (-3) iSquare]
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

/-- The displayed dot product −3 + 3i is nonzero in the admissible quadratic fragment. -/
private theorem secondDot_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    QuadraticFragment.Imaginary.complexValue i (-3) 3 ≠ 0 := by
  intro valueZero
  apply eighteen_nonzero admissible
  calc
    (18 : K) = QuadraticFragment.Imaginary.complexValue i (-3) 3 * QuadraticFragment.Imaginary.complexValue i (-3) (-3)
      := by
      rw [QuadraticFragment.Imaginary.complexValue_mul i (-3) 3 (-3) (-3) iSquare]
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

/-- The displayed dot product −9 − i is nonzero in the admissible quadratic fragment. -/
private theorem thirdDot_nonzero
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    QuadraticFragment.Imaginary.complexValue i (-9) (-1) ≠ 0 := by
  intro valueZero
  apply eightyTwo_nonzero admissible
  calc
    (82 : K) = QuadraticFragment.Imaginary.complexValue i (-9) (-1) * QuadraticFragment.Imaginary.complexValue i (-9) 1
      := by
      rw [QuadraticFragment.Imaginary.complexValue_mul i (-9) (-1) (-9) 1 iSquare]
      unfold QuadraticFragment.Imaginary.complexValue
      ring1
    _ = 0 := by rw [valueZero]; ring1

/-- The second and third displayed sides are not perpendicular under the retained characteristic exclusions. -/
theorem line₂_line₃_notPerpendicular [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    ¬ (line₂ i admissible.twoNonzero (iNonzero)).Perpendicular
      (line₃ i (iNonzero)) := by
  dsimp only
  intro perpendicular
  apply firstDot_nonzero i iSquare admissible
  calc
    QuadraticFragment.Imaginary.complexValue i 5 3 =
        (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).a *
            (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare)).a +
          (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).b *
            (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare)).b :=
      (dot_values i iSquare admissible).1.symm
    _ = 0 := perpendicular

/-- The first and third displayed sides are not perpendicular under the retained characteristic exclusions. -/
theorem line₁_line₃_notPerpendicular [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    ¬ (line₁ i admissible.threeNonzero (iNonzero)).Perpendicular
      (line₃ i (iNonzero)) := by
  dsimp only
  intro perpendicular
  apply secondDot_nonzero i iSquare admissible
  calc
    QuadraticFragment.Imaginary.complexValue i (-3) 3 =
        (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).a *
            (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare)).a +
          (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).b *
            (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare)).b :=
      (dot_values i iSquare admissible).2.1.symm
    _ = 0 := perpendicular

/-- The first and second displayed sides are not perpendicular under the retained characteristic exclusions. -/
theorem line₁_line₂_notPerpendicular [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    ¬ (line₁ i admissible.threeNonzero (iNonzero)).Perpendicular
      (line₂ i admissible.twoNonzero (iNonzero)) := by
  dsimp only
  intro perpendicular
  apply thirdDot_nonzero i iSquare admissible
  calc
    QuadraticFragment.Imaginary.complexValue i (-9) (-1) =
        (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).a *
            (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).a +
          (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).b *
            (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare)).b :=
      (dot_values i iSquare admissible).2.2.symm
    _ = 0 := perpendicular

/-- The three twists in the single-denominator component forms used to check
the final formula. -/
theorem twist_values [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    Line.Twist.twist second third (line₂_line₃_notPerpendicular i iSquare admissible) =
        QuadraticFragment.Imaginary.complexValue i (-297) 304 / 289 ∧
      Line.Twist.twist first third (line₁_line₃_notPerpendicular i iSquare admissible) =
        QuadraticFragment.Imaginary.complexValue i 7 (-24) / 9 ∧
      Line.Twist.twist first second (line₁_line₂_notPerpendicular i iSquare admissible) =
        QuadraticFragment.Imaginary.complexValue i (-1023) (-64) / 1681 := by
  dsimp only
  have determinants := determinant_square_value i iSquare admissible
  have dots := dot_values i iSquare admissible
  have firstDotSquare :
      QuadraticFragment.Imaginary.complexValue i 5 3 ^ 2 = QuadraticFragment.Imaginary.complexValue i 16 30 := by
    rw [QuadraticFragment.Imaginary.complexValue_square i 5 3 iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  have secondDotSquare :
      QuadraticFragment.Imaginary.complexValue i (-3) 3 ^ 2 = QuadraticFragment.Imaginary.complexValue i 0 (-18) := by
    rw [QuadraticFragment.Imaginary.complexValue_square i (-3) 3 iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  have thirdDotSquare :
      QuadraticFragment.Imaginary.complexValue i (-9) (-1) ^ 2 = QuadraticFragment.Imaginary.complexValue i 80 18 := by
    rw [QuadraticFragment.Imaginary.complexValue_square i (-9) (-1) iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  constructor
  · unfold Line.Twist.twist
    rw [determinants.1, dots.1, firstDotSquare]
    apply Ratio.ratio_eq_of_cross_product
      (by
        rw [← firstDotSquare]
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero
            (firstDot_nonzero i iSquare admissible)
            (firstDot_nonzero i iSquare admissible))
      (twoHundredEightyNine_nonzero admissible)
    rw [QuadraticFragment.Imaginary.complexValue_mul i (-297) 304 16 30 iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  constructor
  · unfold Line.Twist.twist
    rw [determinants.2.1, dots.2.1, secondDotSquare]
    apply Ratio.ratio_eq_of_cross_product
      (by
        rw [← secondDotSquare]
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero
            (secondDot_nonzero i iSquare admissible)
            (secondDot_nonzero i iSquare admissible))
      (nine_nonzero admissible)
    rw [QuadraticFragment.Imaginary.complexValue_mul i 7 (-24) 0 (-18) iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  · unfold Line.Twist.twist
    rw [determinants.2.2, dots.2.2, thirdDotSquare]
    apply Ratio.ratio_eq_of_cross_product
      (by
        rw [← thirdDotSquare]
        simpa only [pow_two] using
          ExplicitField.mul_ne_zero
            (thirdDot_nonzero i iSquare admissible)
            (thirdDot_nonzero i iSquare admissible))
      (oneThousandSixHundredEightyOne_nonzero admissible)
    rw [QuadraticFragment.Imaginary.complexValue_mul i (-1023) (-64) 80 18 iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1

/-- Before squaring, the Triple-twist expression is `(474+1232i)/2091`. -/
private theorem twist_expression_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := QuadraticFragment.Imaginary.i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let t₁ := Line.Twist.twist second third
      (line₂_line₃_notPerpendicular i iSquare admissible)
    let t₂ := Line.Twist.twist first third
      (line₁_line₃_notPerpendicular i iSquare admissible)
    let t₃ := Line.Twist.twist first second
      (line₁_line₂_notPerpendicular i iSquare admissible)
    t₁ + t₂ + t₃ - t₁ * t₂ * t₃ =
      QuadraticFragment.Imaginary.complexValue i 474 1232 / 2091 := by
  dsimp only
  rw [(twist_values i iSquare admissible).1,
    (twist_values i iSquare admissible).2.1,
    (twist_values i iSquare admissible).2.2]
  apply Ratio.Finite.three_fraction_sum_sub_product_eq
    (QuadraticFragment.Imaginary.complexValue i (-297) 304) (QuadraticFragment.Imaginary.complexValue i 7 (-24))
    (QuadraticFragment.Imaginary.complexValue i (-1023) (-64)) (QuadraticFragment.Imaginary.complexValue i 474 1232)
    289 9 1681 2091 (twoHundredEightyNine_nonzero admissible)
    (nine_nonzero admissible) (oneThousandSixHundredEightyOne_nonzero admissible)
    (twoThousandNinetyOne_nonzero admissible)
  have firstProduct :
      QuadraticFragment.Imaginary.complexValue i (-297) 304 * QuadraticFragment.Imaginary.complexValue i 7 (-24) =
        QuadraticFragment.Imaginary.complexValue i 5217 9256 := by
    rw [QuadraticFragment.Imaginary.complexValue_mul i (-297) 304 7 (-24) iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  have productValue :
      QuadraticFragment.Imaginary.complexValue i (-297) 304 * QuadraticFragment.Imaginary.complexValue i 7 (-24) *
          QuadraticFragment.Imaginary.complexValue i (-1023) (-64) =
        QuadraticFragment.Imaginary.complexValue i (-4744607) (-9802776) := by
    rw [firstProduct,
      QuadraticFragment.Imaginary.complexValue_mul i 5217 9256 (-1023) (-64) iSquare]
    unfold QuadraticFragment.Imaginary.complexValue
    ring1
  rw [productValue]
  unfold QuadraticFragment.Imaginary.complexValue
  ring1

/-- The squared triple-twist expression equals (−1293148 + 1167936i)/4372281 in the admissible quadratic fragment. -/
private theorem triple_twist_common_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero := QuadraticFragment.Imaginary.i_nonzero i iSquare
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let t₁ := Line.Twist.twist second third
      (line₂_line₃_notPerpendicular i iSquare admissible)
    let t₂ := Line.Twist.twist first third
      (line₁_line₃_notPerpendicular i iSquare admissible)
    let t₃ := Line.Twist.twist first second
      (line₁_line₂_notPerpendicular i iSquare admissible)
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
      QuadraticFragment.Imaginary.complexValue i (-1293148) 1167936 / 4372281 := by
  dsimp only
  rw [twist_expression_value i iSquare admissible]
  apply Ratio.Finite.square_fraction_eq
    (QuadraticFragment.Imaginary.complexValue i 474 1232) 2091
    (QuadraticFragment.Imaginary.complexValue i (-1293148) 1167936) 4372281
    (twoThousandNinetyOne_nonzero admissible)
    (fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
      admissible)
  rw [QuadraticFragment.Imaginary.complexValue_square i 474 1232 iSquare]
  unfold QuadraticFragment.Imaginary.complexValue
  ring1

/-- Both sides of the Triple twist formula have the exact value printed in
Example 7.4. -/
theorem triple_twist_value [Nontrivial K]
    (i : K) (iSquare : i ^ 2 = -1)
    (admissible : AdmissibleCharacteristic K) :
    let iNonzero : i ≠ 0 := by
      intro iZero
      have negativeOneZero : (-1 : K) = 0 := by
        calc
          (-1 : K) = i ^ 2 := iSquare.symm
          _ = 0 := by rw [iZero]; ring1
      exact one_ne_zero (by
        calc
          (1 : K) = -(-1) := by ring1
          _ = 0 := by rw [negativeOneZero]; ring1)
    let first := line₁ i admissible.threeNonzero iNonzero
    let second := line₂ i admissible.twoNonzero iNonzero
    let third := line₃ i iNonzero
    let t₁ := Line.Twist.twist second third
      (line₂_line₃_notPerpendicular i iSquare admissible)
    let t₂ := Line.Twist.twist first third
      (line₁_line₃_notPerpendicular i iSquare admissible)
    let t₃ := Line.Twist.twist first second
      (line₁_line₂_notPerpendicular i iSquare admissible)
    (t₁ + t₂ + t₃ - t₁ * t₂ * t₃) ^ 2 =
        QuadraticFragment.Imaginary.complexValue i (-(1293148 / 4372281)) (389312 / 1457427) ∧
      4 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃ +
          2 * t₁ * t₂ * t₃) =
        QuadraticFragment.Imaginary.complexValue i (-(1293148 / 4372281)) (389312 / 1457427) := by
  dsimp only
  have common := triple_twist_common_value i iSquare admissible
  have imaginaryReduction :
      (1167936 : K) / 4372281 = 389312 / 1457427 := by
    apply Ratio.ratio_eq_of_cross_product
      (fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
        admissible)
      (oneMillionFourHundredFiftySevenThousandFourHundredTwentySeven_nonzero
        admissible)
    ring1
  have printedValue :
      QuadraticFragment.Imaginary.complexValue i (-1293148) 1167936 / 4372281 =
        QuadraticFragment.Imaginary.complexValue i (-(1293148 / 4372281)) (389312 / 1457427) := by
    calc
      QuadraticFragment.Imaginary.complexValue i (-1293148) 1167936 / 4372281 =
          QuadraticFragment.Imaginary.complexValue i ((-1293148) / 4372281) (1167936 / 4372281) :=
        QuadraticFragment.Imaginary.complexValue_div i (-1293148) 1167936 4372281
          (fourMillionThreeHundredSeventyTwoThousandTwoHundredEightyOne_nonzero
            admissible)
      _ = QuadraticFragment.Imaginary.complexValue i (-(1293148 / 4372281)) (389312 / 1457427) := by
        rw [imaginaryReduction]
        unfold QuadraticFragment.Imaginary.complexValue
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
  have formula := Line.Twist.Triple.triple_twist_formula
    (line₁ i admissible.threeNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
    (line₂ i admissible.twoNonzero (QuadraticFragment.Imaginary.i_nonzero i iSquare))
    (line₃ i (QuadraticFragment.Imaginary.i_nonzero i iSquare))
    (line₁_line₂_notPerpendicular i iSquare admissible)
    (line₁_line₃_notPerpendicular i iSquare admissible)
    (line₂_line₃_notPerpendicular i iSquare admissible)
  exact ⟨common.trans printedValue,
    formula.symm.trans (common.trans printedValue)⟩

end ExampleSevenFour

end ChapterSevenFieldFragments

end formalisations.DivineProportions.Chapters.Examples

end
