module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Choice-free finite eight-sector table

The predicates and selector are the exact finite table from the CCL-1 paper,
specialized to explicit constructive fractions.  The geometric estimates are
proved from displayed polynomial identities and direct order lemmas; no
linear-programming tactic or inherited ordered-field compatibility theorem is
part of their dependency closure.
-/

public section

namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector

section
open Purelib.Data.Rat
/-- An axial-sector point with squared norm at most two has squared distance below one half from its axial
representative.

The retained axial bounds give nonnegative horizontal factors and strictly positive vertical factors. Their exact
polynomial identity yields the strict half-unit distance bound under the original upper norm constraint. -/
private theorem axial_contraction (x y : Fraction.Rational)
    (xLower : 1 / 2 ≤ x) (yLower : -1 / 2 < y) (yUpper : y < 1 / 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 2) :
    (x - 1) ^ 2 + y ^ 2 < 1 / 2 := by
  have halfPositive : (0 : Fraction.Rational) < 1 / 2 := by decide
  have xNonnegative : 0 ≤ x := halfPositive.le.trans xLower
  have xUpper : x < 3 / 2 := by
    by_cases upper : x < 3 / 2
    · exact upper
    · have threeHalvesLe : (3 / 2 : Fraction.Rational) ≤ x := le_of_not_gt upper
      have squareLower : (3 / 2 : Fraction.Rational) ^ 2 ≤ x ^ 2 := by
        rw [pow_two, pow_two]
        exact Fraction.Order.Arithmetic.mul_le_mul_direct threeHalvesLe
          threeHalvesLe (by decide) xNonnegative
      have impossible : (9 / 4 : Fraction.Rational) ≤ 2 := by
        calc
          (9 / 4 : Fraction.Rational) = (3 / 2 : Fraction.Rational) ^ 2 := by decide
          _ ≤ x ^ 2 := squareLower
          _ ≤ x ^ 2 + y ^ 2 := by
            have bound := Fraction.Order.Arithmetic.add_le_add_direct
              (le_refl (x ^ 2)) (Fraction.Order.Arithmetic.sq_nonneg_direct y)
            calc
              x ^ 2 = x ^ 2 + 0 := by ring1
              _ ≤ x ^ 2 + y ^ 2 := bound
          _ ≤ 2 := normUpper
      exact ((by decide : ¬ ((9 / 4 : Fraction.Rational) ≤ 2)) impossible).elim
  have leftNonnegative : 0 ≤ x - 1 / 2 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct xLower
  have rightNonnegative : 0 ≤ 3 / 2 - x :=
    Fraction.Order.Arithmetic.sub_nonneg_direct xUpper.le
  have yLeftPositive : 0 < y + 1 / 2 := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      yLower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < y + 1 / 2 := shifted
  have yRightPositive : 0 < 1 / 2 - y :=
    Fraction.Order.Arithmetic.sub_pos_direct yUpper
  have firstNonnegative :
      0 ≤ (x - 1 / 2) * (3 / 2 - x) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct leftNonnegative rightNonnegative
  have secondPositive : 0 < (y + 1 / 2) * (1 / 2 - y) :=
    Fraction.Order.Arithmetic.mul_pos_direct yLeftPositive yRightPositive
  have differencePositive :
      0 < 1 / 2 - ((x - 1) ^ 2 + y ^ 2) := by
    calc
      0 < (x - 1 / 2) * (3 / 2 - x) +
          (y + 1 / 2) * (1 / 2 - y) :=
        Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
          firstNonnegative secondPositive
      _ = 1 / 2 - ((x - 1) ^ 2 + y ^ 2) +
          (2 * (1 / 2 : Fraction.Rational) - 1) * (x - 1) := by
        rw [show (3 / 2 : Fraction.Rational) = 1 + 1 / 2 by decide]
        ring1
      _ = 1 / 2 - ((x - 1) ^ 2 + y ^ 2) := by
        rw [show (2 : Fraction.Rational) * (1 / 2) - 1 = 0 by decide]
        ring1
  exact Fraction.Order.Arithmetic.lt_of_sub_pos_direct differencePositive

/-- A diagonal-sector point with squared norm between one and two has squared distance below one half from its diagonal
representative.

The original nonnegative half-coordinate differences determine their sum and squared sum. The retained norm band forces
the strict comparison between those two quantities and hence the exact distance bound. -/
private theorem diagonal_contraction (x y : Fraction.Rational)
    (xLower : 1 / 2 ≤ x) (yLower : 1 / 2 ≤ y)
    (normLower : 1 ≤ x ^ 2 + y ^ 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 2) :
    (x - 1) ^ 2 + (y - 1) ^ 2 < 1 / 2 := by
  let a := x - 1 / 2
  let b := y - 1 / 2
  let p := a + b
  let q := a ^ 2 + b ^ 2
  have aNonnegative : 0 ≤ a :=
    Fraction.Order.Arithmetic.sub_nonneg_direct xLower
  have bNonnegative : 0 ≤ b :=
    Fraction.Order.Arithmetic.sub_nonneg_direct yLower
  have pNonnegative : 0 ≤ p := add_nonneg aNonnegative bNonnegative
  have normIdentity : x ^ 2 + y ^ 2 = p + q + 1 / 2 := by
    have linearZero : (1 : Fraction.Rational) - 2 * (1 / 2) = 0 := by decide
    have constantZero :
        (2 : Fraction.Rational) * (1 / 2) ^ 2 - 1 / 2 = 0 := by decide
    calc
      x ^ 2 + y ^ 2 = x ^ 2 + y ^ 2 +
          ((1 : Fraction.Rational) - 2 * (1 / 2)) * (x + y) +
          (2 * (1 / 2 : Fraction.Rational) ^ 2 - 1 / 2) := by
        rw [linearZero, constantZero]
        ring1
      _ = p + q + 1 / 2 := by
        dsimp only [a, b, p, q]
        ring1
  have lowerPQ : (1 / 2 : Fraction.Rational) ≤ p + q := by
    apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
      (c := (1 / 2 : Fraction.Rational))
    calc
      (1 / 2 : Fraction.Rational) + 1 / 2 = 1 := by decide
      _ ≤ x ^ 2 + y ^ 2 := normLower
      _ = (p + q) + 1 / 2 := normIdentity
  have upperPQ : p + q ≤ (3 / 2 : Fraction.Rational) := by
    apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
      (c := (1 / 2 : Fraction.Rational))
    calc
      (p + q) + 1 / 2 = x ^ 2 + y ^ 2 := normIdentity.symm
      _ ≤ 2 := normUpper
      _ = (3 / 2 : Fraction.Rational) + 1 / 2 := by decide
  have qLeSquareP : q ≤ p ^ 2 := by
    have twiceProductNonnegative : 0 ≤ 2 * (a * b) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct aNonnegative bNonnegative)
    calc
      q = q + 0 := by ring1
      _ ≤ q + 2 * (a * b) := add_le_add le_rfl twiceProductNonnegative
      _ = p ^ 2 := by
        dsimp only [p, q]
        ring1
  have pPositive : 0 < p := by
    by_cases pZero : p = 0
    · have aZero : a = 0 := by
        apply le_antisymm
        · calc
            a ≤ a + b := le_add_of_nonneg_right bNonnegative
            _ = 0 := pZero
        · exact aNonnegative
      have bZero : b = 0 := by
        apply le_antisymm
        · calc
            b ≤ a + b := le_add_of_nonneg_left aNonnegative
            _ = 0 := pZero
        · exact bNonnegative
      have impossible : (1 / 2 : Fraction.Rational) ≤ 0 := by
        calc
          (1 / 2 : Fraction.Rational) ≤ p + q := lowerPQ
          _ = 0 := by
            rw [pZero]
            dsimp only [q]
            rw [aZero, bZero]
            ring1
      exact ((by decide : ¬ ((1 / 2 : Fraction.Rational) ≤ 0)) impossible).elim
    · exact lt_of_le_of_ne pNonnegative (Ne.symm pZero)
  have qLtP : q < p := by
    by_cases qLess : q < p
    · exact qLess
    · have pLeQ : p ≤ q := le_of_not_gt qLess
      have oneLeP : (1 : Fraction.Rational) ≤ p := by
        by_cases pLessOne : p < 1
        · have oneMinusPositive : 0 < 1 - p :=
            Fraction.Order.Arithmetic.sub_pos_direct pLessOne
          have productPositive : 0 < p * (1 - p) :=
            Fraction.Order.Arithmetic.mul_pos_direct pPositive oneMinusPositive
          have squareLt : p ^ 2 < p := by
            apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
            calc
              0 < p * (1 - p) := productPositive
              _ = p - p ^ 2 := by ring1
          have qLessP : q < p := qLeSquareP.trans_lt squareLt
          exact (not_lt_of_ge pLeQ qLessP).elim
        · exact le_of_not_gt pLessOne
      have twoLeTwoP : (2 : Fraction.Rational) ≤ 2 * p :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (a := (1 : Fraction.Rational)) (b := p) (c := 2)
          oneLeP (by decide)
      have twoPLePQ : 2 * p ≤ p + q := by
        calc
          2 * p = p + p := by ring1
          _ ≤ p + q := add_le_add le_rfl pLeQ
      have impossible : (2 : Fraction.Rational) ≤ 3 / 2 :=
        twoLeTwoP.trans (twoPLePQ.trans upperPQ)
      exact ((by decide : ¬ ((2 : Fraction.Rational) ≤ 3 / 2)) impossible).elim
  apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
  calc
    0 < p - q := Fraction.Order.Arithmetic.sub_pos_direct qLtP
    _ = 1 / 2 - ((x - 1) ^ 2 + (y - 1) ^ 2) +
        (2 * (1 / 2 : Fraction.Rational) - 1) * (x + y) +
        (2 - 3 * (1 / 2 : Fraction.Rational) - 2 * (1 / 2 : Fraction.Rational) ^ 2) := by
      dsimp only [a, b, p, q]
      ring1
    _ = 1 / 2 - ((x - 1) ^ 2 + (y - 1) ^ 2) := by
      rw [show (2 : Fraction.Rational) * (1 / 2) - 1 = 0 by decide,
        show (2 : Fraction.Rational) - 3 * (1 / 2) - 2 * (1 / 2) ^ 2 = 0 by decide]
      ring1

end

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every point in the closed unit-to-two norm band lies within squared distance one half of its retained containing
sector representative.

The sector membership hypothesis retains the exact strict axial and weak diagonal boundaries. Rotating the original
scalar estimates handles all eight representatives without changing the selected sector. -/
theorem contraction {z : Basic.Canonical} (band : Band z) (sector : Sector)
    (holds : Holds sector z) : Gaussian.Norm.Basic.normSq (z - rep sector) < 1 /
      2 := by
  rcases band with ⟨normLower, normUpper⟩
  have normLower : 1 ≤ Gaussian.Norm.Basic.normSq z := by
    simpa only [Norm.Basic.normSq_eq_canonical] using normLower
  have normUpper : Gaussian.Norm.Basic.normSq z ≤ 2 := by
    simpa only [Norm.Basic.normSq_eq_canonical] using normUpper
  cases sector with
  | east =>
      rcases holds with ⟨xLower, yLower, yUpper⟩
      have contracted :=
        axial_contraction z.re z.im xLower yLower yUpper normUpper
      change (z.re - 1) ^ 2 + (z.im - 0) ^ 2 < 1 / 2
      calc
        (z.re - 1) ^ 2 + (z.im - 0) ^ 2 =
            (z.re - 1) ^ 2 + z.im ^ 2 := by ring1
        _ < 1 / 2 := contracted
  | northEast =>
      rcases holds with ⟨xLower, yLower⟩
      exact diagonal_contraction z.re z.im xLower yLower normLower normUpper
  | north =>
      rcases holds with ⟨xLower, xUpper, yLower⟩
      have rotatedUpper : z.im ^ 2 + (-z.re) ^ 2 ≤ 2 := by
        calc
          z.im ^ 2 + (-z.re) ^ 2 = Gaussian.Norm.Basic.normSq z := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := axial_contraction z.im (-z.re) yLower
        (Fraction.Order.Arithmetic.neg_lt_neg_direct xUpper)
        (Fraction.Order.Arithmetic.neg_lt_neg_direct xLower)
        rotatedUpper
      change (z.re - 0) ^ 2 + (z.im - 1) ^ 2 < 1 / 2
      calc
        (z.re - 0) ^ 2 + (z.im - 1) ^ 2 =
            (z.im - 1) ^ 2 + (-z.re) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | northWest =>
      rcases holds with ⟨xUpper, yLower⟩
      have rotatedLower : 1 ≤ z.im ^ 2 + (-z.re) ^ 2 := by
        calc
          1 ≤ Gaussian.Norm.Basic.normSq z := normLower
          _ = z.im ^ 2 + (-z.re) ^ 2 := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
      have rotatedUpper : z.im ^ 2 + (-z.re) ^ 2 ≤ 2 := by
        calc
          z.im ^ 2 + (-z.re) ^ 2 = Gaussian.Norm.Basic.normSq z := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := diagonal_contraction z.im (-z.re) yLower
        (Fraction.Order.Arithmetic.neg_le_neg_direct xUpper)
        rotatedLower rotatedUpper
      change (z.re - -1) ^ 2 + (z.im - 1) ^ 2 < 1 / 2
      calc
        (z.re - -1) ^ 2 + (z.im - 1) ^ 2 =
            (z.im - 1) ^ 2 + (-z.re - 1) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | west =>
      rcases holds with ⟨xUpper, yLower, yUpper⟩
      have rotatedUpper : (-z.re) ^ 2 + (-z.im) ^ 2 ≤ 2 := by
        calc
          (-z.re) ^ 2 + (-z.im) ^ 2 = Gaussian.Norm.Basic.normSq z := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := axial_contraction (-z.re) (-z.im)
        (Fraction.Order.Arithmetic.neg_le_neg_direct xUpper)
        (Fraction.Order.Arithmetic.neg_lt_neg_direct yUpper)
        (Fraction.Order.Arithmetic.neg_lt_neg_direct yLower)
        rotatedUpper
      change (z.re - -1) ^ 2 + (z.im - 0) ^ 2 < 1 / 2
      calc
        (z.re - -1) ^ 2 + (z.im - 0) ^ 2 =
            (-z.re - 1) ^ 2 + (-z.im) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | southWest =>
      rcases holds with ⟨xUpper, yUpper⟩
      have rotatedLower : 1 ≤ (-z.re) ^ 2 + (-z.im) ^ 2 := by
        calc
          1 ≤ Gaussian.Norm.Basic.normSq z := normLower
          _ = (-z.re) ^ 2 + (-z.im) ^ 2 := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
      have rotatedUpper : (-z.re) ^ 2 + (-z.im) ^ 2 ≤ 2 := by
        calc
          (-z.re) ^ 2 + (-z.im) ^ 2 = Gaussian.Norm.Basic.normSq z := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := diagonal_contraction (-z.re) (-z.im)
        (Fraction.Order.Arithmetic.neg_le_neg_direct xUpper)
        (Fraction.Order.Arithmetic.neg_le_neg_direct yUpper)
        rotatedLower rotatedUpper
      change (z.re - -1) ^ 2 + (z.im - -1) ^ 2 < 1 / 2
      calc
        (z.re - -1) ^ 2 + (z.im - -1) ^ 2 =
            (-z.re - 1) ^ 2 + (-z.im - 1) ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | south =>
      rcases holds with ⟨xLower, xUpper, yUpper⟩
      have rotatedUpper : (-z.im) ^ 2 + z.re ^ 2 ≤ 2 := by
        calc
          (-z.im) ^ 2 + z.re ^ 2 = Gaussian.Norm.Basic.normSq z := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := axial_contraction (-z.im) z.re
        (Fraction.Order.Arithmetic.neg_le_neg_direct yUpper)
        xLower xUpper rotatedUpper
      change (z.re - 0) ^ 2 + (z.im - -1) ^ 2 < 1 / 2
      calc
        (z.re - 0) ^ 2 + (z.im - -1) ^ 2 =
            (-z.im - 1) ^ 2 + z.re ^ 2 := by ring1
        _ < 1 / 2 := rotated
  | southEast =>
      rcases holds with ⟨xLower, yUpper⟩
      have rotatedLower : 1 ≤ (-z.im) ^ 2 + z.re ^ 2 := by
        calc
          1 ≤ Gaussian.Norm.Basic.normSq z := normLower
          _ = (-z.im) ^ 2 + z.re ^ 2 := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
      have rotatedUpper : (-z.im) ^ 2 + z.re ^ 2 ≤ 2 := by
        calc
          (-z.im) ^ 2 + z.re ^ 2 = Gaussian.Norm.Basic.normSq z := by
            dsimp only [Gaussian.Norm.Basic.normSq]
            ring1
          _ ≤ 2 := normUpper
      have rotated := diagonal_contraction (-z.im) z.re
        (Fraction.Order.Arithmetic.neg_le_neg_direct yUpper) xLower
        rotatedLower rotatedUpper
      change (z.re - 1) ^ 2 + (z.im - -1) ^ 2 < 1 / 2
      calc
        (z.re - 1) ^ 2 + (z.im - -1) ^ 2 =
            (-z.im - 1) ^ 2 + (z.re - 1) ^ 2 := by ring1
        _ < 1 / 2 := rotated

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- The deterministically selected sector contracts every point in the closed norm band to squared distance below one
half.

The original selector retains its exact eight-case sector table. Its membership certificate supplies the boundaries
needed by the corresponding axial or diagonal contraction estimate. -/
theorem select_contraction {z : Basic.Canonical} (band : Band z) :
    Gaussian.Norm.Basic.normSq (z - rep (select z)) < 1 / 2 :=
  contraction band (select z) (select_spec z band.1)

end Purelib.Data.ComplexContinuedFraction.Encoding.Sector
