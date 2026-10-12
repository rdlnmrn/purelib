module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

namespace Purelib.Geometry.Rational.Sector.Eight.Margin

open Purelib
open Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
open Purelib.Data.Rat

/-- Uniform version of the axial sector calculation. The rational constant `7/16` is deliberately a little weaker than
the sharp algebraic maximum; its strict gap below `1/2` supplies a finite enclosure margin.

The supplied axial coordinate bounds and enlarged annulus bounds control the same squared residual. The rational
seven-sixteenths allowance remains strictly below one half. -/
private theorem axial_residual_le_seven_sixteenths
    (x y : Fraction.Rational)
    (xLower : 1 / 2 ≤ x) (yLower : -1 / 2 < y) (yUpper : y < 1 / 2)
    (normLower : 1 ≤ x ^ 2 + y ^ 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 13 / 6) :
    (x - 1) ^ 2 + y ^ 2 ≤ 7 / 16 := by
  have xNonnegative : 0 ≤ x := (by decide : (0 : Fraction.Rational) ≤ 1 / 2).trans xLower
  have ySquareLt : y ^ 2 < 1 / 4 :=
    Bounds.Square.square_lt_quarter_of_half_bounds yLower yUpper
  have xAboveThreeQuarters : 3 / 4 < x := by
    by_cases above : 3 / 4 < x
    · exact above
    · have xUpper : x ≤ 3 / 4 := le_of_not_gt above
      have xSquareUpper : x ^ 2 ≤ (3 / 4 : Fraction.Rational) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct xNonnegative xUpper 2
      have normTooSmall : x ^ 2 + y ^ 2 < 1 := by
        calc
          x ^ 2 + y ^ 2 < (3 / 4 : Fraction.Rational) ^ 2 + 1 / 4 :=
            (Fraction.Order.Arithmetic.add_lt_add_left_direct
              ySquareLt _).trans_le
              (Fraction.Order.Arithmetic.add_le_add_right_direct xSquareUpper _)
          _ = 13 / 16 := by decide
          _ < 1 := by decide
      exact ((not_lt_of_ge normLower) normTooSmall).elim
  by_cases moderate : x ≤ 11 / 8
  · have differenceLower : -(3 / 8 : Fraction.Rational) ≤ x - 1 := by
      exact (show -(3 / 8 : Fraction.Rational) < x - 1 from by
        calc
        -(3 / 8 : Fraction.Rational) < -1 / 4 := by decide
        _ < x - 1 := by
          apply Fraction.Order.Arithmetic.add_lt_add_right_direct
            xAboveThreeQuarters (-1)).le
    have differenceUpper : x - 1 ≤ (3 / 8 : Fraction.Rational) := by
      calc
        x - 1 = -1 + x := by ring1
        _ ≤ -1 + 11 / 8 := Fraction.Order.Arithmetic.add_le_add_direct le_rfl moderate
        _ = 3 / 8 := by decide
    have differenceSquare : (x - 1) ^ 2 ≤ (3 / 8 : Fraction.Rational) ^ 2 :=
      Bounds.Square.square_le_of_two_sided differenceLower differenceUpper
    apply LT.lt.le
    have squareStrict : (3 / 8 : Fraction.Rational) ^ 2 < 3 / 16 := by decide
    calc
      (x - 1) ^ 2 + y ^ 2 <
          (3 / 8 : Fraction.Rational) ^ 2 + 1 / 4 :=
        (Fraction.Order.Arithmetic.add_lt_add_left_direct
              ySquareLt _).trans_le
              (Fraction.Order.Arithmetic.add_le_add_right_direct differenceSquare _)
      _ < 3 / 16 + 1 / 4 :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct
          squareStrict (1 / 4)
      _ = 7 / 16 := by decide
  · have xAbove : 11 / 8 < x := lt_of_not_ge moderate
    have doubled : (2 : Fraction.Rational) * (11 / 8 : Fraction.Rational) < 2 * x :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide) xAbove
    have residualIdentity :
        (x - 1) ^ 2 + y ^ 2 = (x ^ 2 + y ^ 2) - 2 * x + 1 := by
      ring1
    rw [residualIdentity]
    have negDoubled : -(2 * x) < -(2 * (11 / 8 : Fraction.Rational)) :=
      Fraction.Order.Arithmetic.neg_lt_neg_direct doubled
    have beforeOne :
        (x ^ 2 + y ^ 2) + -(2 * x) <
          13 / 6 + -(2 * (11 / 8 : Fraction.Rational)) :=
      (Fraction.Order.Arithmetic.add_lt_add_left_direct
              negDoubled _).trans_le
              (Fraction.Order.Arithmetic.add_le_add_right_direct normUpper _)
    exact (show (x ^ 2 + y ^ 2) - 2 * x + 1 < 7 / 16 from by
      calc
        (x ^ 2 + y ^ 2) - 2 * x + 1 <
            13 / 6 - 2 * (11 / 8 : Fraction.Rational) + 1 := by
          calc
            (x ^ 2 + y ^ 2) - 2 * x + 1 =
                1 + ((x ^ 2 + y ^ 2) + -(2 * x)) := by ring1
            _ < 1 + (13 / 6 + -(2 * (11 / 8 : Fraction.Rational))) :=
              Fraction.Order.Arithmetic.add_lt_add_left_direct beforeOne 1
            _ = 13 / 6 - 2 * (11 / 8 : Fraction.Rational) + 1 := by ring1
        _ = 5 / 12 := by decide
        _ < 7 / 16 := by decide).le

/-- The two affine slack terms sum to the translated diagonal difference minus one twelfth.

The two rational constants and the supplied translated coordinates retain this scalar additive identity. -/
private theorem high_slack_identity (p q : Fraction.Rational) :
    (2 * p - 7 / 4) + (5 / 3 - (p + q)) =
      (p - q) - 1 / 12 := by
  have constants :
      (5 / 3 : Fraction.Rational) - 7 / 4 = -1 / 12 := by decide
  have negative : (-1 / 12 : Fraction.Rational) = -(1 / 12) := by decide
  calc
    (2 * p - 7 / 4) + (5 / 3 - (p + q)) =
        (2 * p - (p + q)) + (5 / 3 - 7 / 4) := by ring1
    _ = (2 * p - (p + q)) + (-1 / 12) := by rw [constants]
    _ = (2 * p - (p + q)) + -(1 / 12) := by rw [negative]
    _ = (p - q) - 1 / 12 := by ring1

/-- Rewrite the translated diagonal gap as the residual allowance below seven sixteenths.

Both sides retain the same two translated coordinates. The one-sixteenth difference is the seven-sixteenths allowance
after its one-half residual translation. -/
private theorem diagonal_gap_identity (p q : Fraction.Rational) :
    (p - q) - 1 / 16 = 7 / 16 - (q - p + 1 / 2) := by
  have constants :
      (7 / 16 : Fraction.Rational) - 1 / 2 = -1 / 16 := by decide
  have negative : (-1 / 16 : Fraction.Rational) = -(1 / 16) := by decide
  calc
    (p - q) - 1 / 16 = (p - q) + -(1 / 16) := by ring1
    _ = (p - q) + (-1 / 16) := by rw [negative]
    _ = (p - q) + (7 / 16 - 1 / 2) := by rw [constants]
    _ = 7 / 16 - (q - p + 1 / 2) := by ring1

/-- Nonnegative p with q bounded by its square and p plus q at least one half must exceed one third.

The retained lower sum bound and quadratic upper bound on q exclude every nonnegative p at most one third by direct
rational square comparison. -/
private theorem translated_p_above_third
    (p q : Fraction.Rational) (pNonnegative : 0 ≤ p)
    (lowerPQ : (1 / 2 : Fraction.Rational) ≤ p + q)
    (qLeSquareP : q ≤ p ^ 2) :
    (1 / 3 : Fraction.Rational) < p := by
  by_cases above : (1 / 3 : Fraction.Rational) < p
  · exact above
  · have pUpper : p ≤ 1 / 3 := le_of_not_gt above
    have pSquareUpper : p ^ 2 ≤ (1 / 3 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.pow_le_pow_direct pNonnegative pUpper 2
    have pqUpper : p + q ≤ (4 / 9 : Fraction.Rational) := by
      calc
        p + q ≤ (1 / 3 : Fraction.Rational) + (1 / 3 : Fraction.Rational) ^ 2 :=
          add_le_add pUpper (qLeSquareP.trans pSquareUpper)
        _ = 4 / 9 := by decide
    have impossible : (1 / 2 : Fraction.Rational) ≤ 4 / 9 :=
      lowerPQ.trans pqUpper
    exact ((by decide : ¬ ((1 / 2 : Fraction.Rational) ≤ 4 / 9)) impossible).elim

/-- An upper bound on q by p squared gives the corresponding lower bound on p minus q.

Negating the supplied weak comparison and adding the same retained p transports that bound to the two displayed
differences. -/
private theorem translated_difference_order
    (p q : Fraction.Rational) (qLeSquareP : q ≤ p ^ 2) :
    p - p ^ 2 ≤ p - q := by
  have negated := Fraction.Order.Arithmetic.neg_le_neg_direct qLeSquareP
  calc
    p - p ^ 2 = p + -(p ^ 2) := by ring1
    _ ≤ p + -q := Fraction.Order.Arithmetic.add_le_add_direct le_rfl negated
    _ = p - q := by ring1

/-- The translated annulus inequalities force p minus q to be at least one sixteenth.

The proof retains nonnegativity of p, lower and upper bounds on p plus q, and the quadratic comparison of q with p
squared. -/
private theorem translated_diagonal_gap
    (p q : Fraction.Rational) (pNonnegative : 0 ≤ p)
    (lowerPQ : (1 / 2 : Fraction.Rational) ≤ p + q)
    (upperPQ : p + q ≤ (5 / 3 : Fraction.Rational))
    (qLeSquareP : q ≤ p ^ 2) :
    (1 / 16 : Fraction.Rational) ≤ p - q := by
  have pAboveThird :=
    translated_p_above_third p q pNonnegative lowerPQ qLeSquareP
  have differenceOrder := translated_difference_order p q qLeSquareP
  match Fraction.Decide.rationalDecLE
      (7 : Fraction.Rational) (8 * p) with
  | isTrue highScaled =>
    have doubled : (7 / 4 : Fraction.Rational) ≤ 2 * p := by
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := (4 : Fraction.Rational)) _ (by decide)
      calc
        (7 / 4 : Fraction.Rational) * 4 = 7 :=
          Fraction.Field.div_mul_cancel_of_ne 7 4 (by decide)
        _ ≤ 8 * p := highScaled
        _ = (2 * p) * 4 := by ring1
    have upperSlack : 0 ≤ 5 / 3 - (p + q) :=
      Fraction.Order.Arithmetic.sub_nonneg_direct upperPQ
    have highSlack : 0 ≤ 2 * p - 7 / 4 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct doubled
    have twelfthLower : (1 / 12 : Fraction.Rational) ≤ p - q := by
      have differenceNonnegative : 0 ≤ (p - q) - 1 / 12 := by
        calc
          0 ≤ (2 * p - 7 / 4) + (5 / 3 - (p + q)) :=
            add_nonneg highSlack upperSlack
          _ = (p - q) - 1 / 12 := high_slack_identity p q
      apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
        (c := -(1 / 12 : Fraction.Rational))
      calc
        (1 / 12 : Fraction.Rational) + -(1 / 12) = 0 := by ring1
        _ ≤ (p - q) - 1 / 12 := differenceNonnegative
        _ = (p - q) + -(1 / 12) := by ring1
    exact (by decide : (1 / 16 : Fraction.Rational) ≤ 1 / 12).trans twelfthLower
  | isFalse notHighScaled =>
    have belowScaled : 8 * p < (7 : Fraction.Rational) :=
      lt_of_not_ge notHighScaled
    have below : p < 7 / 8 := by
      apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
        (c := (8 : Fraction.Rational)) _ (by decide)
      calc
        p * 8 = 8 * p := by ring1
        _ < 7 := belowScaled
        _ = (7 / 8 : Fraction.Rational) * 8 :=
          (Fraction.Field.div_mul_cancel_of_ne 7 8
            (by decide)).symm
    have oneMinusEighth : (1 / 8 : Fraction.Rational) < 1 - p := by
      have negated : -(7 / 8 : Fraction.Rational) < -p :=
        Fraction.Order.Arithmetic.neg_lt_neg_direct below
      calc
        (1 / 8 : Fraction.Rational) = 1 + -(7 / 8) := by decide
        _ < 1 + -p := Fraction.Order.Arithmetic.add_lt_add_left_direct negated 1
        _ = 1 - p := by ring1
    by_cases half : 1 / 2 ≤ p
    · have productLower : (1 / 16 : Fraction.Rational) < p * (1 - p) := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            (by decide : (0 : Fraction.Rational) < 1 / 2) oneMinusEighth
        calc
          (1 / 16 : Fraction.Rational) = (1 / 2) * (1 / 8) := by decide
          _ < (1 / 2) * (1 - p) := scaled
          _ ≤ p * (1 - p) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              half ((by decide : (0 : Fraction.Rational) < 1 / 8).trans
                oneMinusEighth).le
      exact (show (1 / 16 : Fraction.Rational) < p - q from by
        calc
          (1 / 16 : Fraction.Rational) < p * (1 - p) := productLower
          _ = p - p ^ 2 := by ring1
          _ ≤ p - q := differenceOrder).le
    · have pBelowHalf : p < 1 / 2 := lt_of_not_ge half
      have halfBelowOneMinus : (1 / 2 : Fraction.Rational) < 1 - p := by
        have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct pBelowHalf
        calc
          (1 / 2 : Fraction.Rational) = 1 + -(1 / 2) := by decide
          _ < 1 + -p := Fraction.Order.Arithmetic.add_lt_add_left_direct negated 1
          _ = 1 - p := by ring1
      have productLower : (1 / 6 : Fraction.Rational) < p * (1 - p) := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            (by decide : (0 : Fraction.Rational) < 1 / 3) halfBelowOneMinus
        have rightPositive : 0 < 1 - p :=
          (by decide : (0 : Fraction.Rational) < 1 / 2).trans halfBelowOneMinus
        calc
          (1 / 6 : Fraction.Rational) = (1 / 3) * (1 / 2) := by decide
          _ < (1 / 3) * (1 - p) := scaled
          _ < p * (1 - p) :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
              pAboveThird rightPositive
      exact (show (1 / 16 : Fraction.Rational) < p - q from by
        calc
          (1 / 16 : Fraction.Rational) < 1 / 6 := by decide
          _ < p * (1 - p) := productLower
          _ = p - p ^ 2 := by ring1
          _ ≤ p - q := differenceOrder).le

/-- Uniform diagonal-sector estimate in translated nonnegative coordinates.

The supplied diagonal coordinate and enlarged annulus bounds give nonnegative translated coordinates. Their retained
linear and squared sums bound the same sector residual by seven sixteenths. -/
private theorem diagonal_residual_le_seven_sixteenths
    (x y : Fraction.Rational)
    (xLower : 1 / 2 ≤ x) (yLower : 1 / 2 ≤ y)
    (normLower : 1 ≤ x ^ 2 + y ^ 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 13 / 6) :
    (x - 1) ^ 2 + (y - 1) ^ 2 ≤ 7 / 16 := by
  let a := x - 1 / 2
  let b := y - 1 / 2
  generalize pDefinition : a + b = p
  generalize qDefinition : a ^ 2 + b ^ 2 = q
  have aNonnegative : 0 ≤ a :=
    Fraction.Order.Arithmetic.sub_nonneg_direct xLower
  have bNonnegative : 0 ≤ b :=
    Fraction.Order.Arithmetic.sub_nonneg_direct yLower
  have pNonnegative : 0 ≤ p := by
    rw [← pDefinition]
    exact add_nonneg aNonnegative bNonnegative
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
        rw [← pDefinition, ← qDefinition]
        dsimp only [a, b]
        ring1
  have lowerPQ : (1 / 2 : Fraction.Rational) ≤ p + q := by
    apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
      (c := (1 / 2 : Fraction.Rational))
    calc
      (1 / 2 : Fraction.Rational) + 1 / 2 = 1 := by decide
      _ ≤ x ^ 2 + y ^ 2 := normLower
      _ = (p + q) + 1 / 2 := normIdentity
  have upperPQ : p + q ≤ (5 / 3 : Fraction.Rational) := by
    apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
      (c := (1 / 2 : Fraction.Rational))
    calc
      (p + q) + 1 / 2 = x ^ 2 + y ^ 2 := normIdentity.symm
      _ ≤ 13 / 6 := normUpper
      _ = (5 / 3 : Fraction.Rational) + 1 / 2 := by decide
  have qLeSquareP : q ≤ p ^ 2 := by
    have twiceProductNonnegative : 0 ≤ 2 * (a * b) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          aNonnegative bNonnegative)
    calc
      q = q + 0 := by ring1
      _ ≤ q + 2 * (a * b) := add_le_add le_rfl twiceProductNonnegative
      _ = p ^ 2 := by
        rw [← pDefinition, ← qDefinition]
        ring1
  have gapLower : (1 / 16 : Fraction.Rational) ≤ p - q :=
    translated_diagonal_gap p q pNonnegative lowerPQ upperPQ qLeSquareP
  have sumIdentity : p = x + y - 1 := by
    rw [← pDefinition]
    dsimp only [a, b]
    have halves : (1 / 2 : Fraction.Rational) + 1 / 2 = 1 := by decide
    calc
      (x - 1 / 2) + (y - 1 / 2) = x + y - (1 / 2 + 1 / 2) := by
        ring1
      _ = x + y - 1 := by rw [halves]
  have residualIdentity :
      (x - 1) ^ 2 + (y - 1) ^ 2 = q - p + 1 / 2 := by
    calc
      (x - 1) ^ 2 + (y - 1) ^ 2 =
          (x ^ 2 + y ^ 2) - 2 * (x + y) + 2 := by ring1
      _ = (p + q + 1 / 2) - 2 * (p + 1) + 2 := by
        rw [normIdentity]
        have sumFromP : x + y = p + 1 := by
          calc
            x + y = (x + y - 1) + 1 := by ring1
            _ = p + 1 := by rw [← sumIdentity]
        rw [sumFromP]
      _ = q - p + 1 / 2 := by ring1
  rw [residualIdentity]
  have differenceNonnegative : 0 ≤ 7 / 16 - (q - p + 1 / 2) := by
    calc
      0 ≤ (p - q) - 1 / 16 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct gapLower
      _ = 7 / 16 - (q - p + 1 / 2) := diagonal_gap_identity p q
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := -(q - p + 1 / 2))
  calc
    q - p + 1 / 2 + -(q - p + 1 / 2) = 0 := by ring1
    _ ≤ 7 / 16 - (q - p + 1 / 2) := differenceNonnegative
    _ = 7 / 16 + -(q - p + 1 / 2) := by ring1

/-- The slightly enlarged closed normalization band used by the redundant controller. Its overlap above norm `2` is what
separates safe-sector output from the next-unary output without an equality test.

The exact Gaussian value retains squared norm between one and thirteen sixths. This closed rational band includes the
canonical normalization band. -/
@[expose] public def ExtendedBand (value : Data.Gaussian.Basic.Canonical) : Prop :=
  1 ≤ Data.Gaussian.Norm.Basic.normSq value ∧ Data.Gaussian.Norm.Basic.normSq value ≤ 13 / 6

/-- Decide membership in the enlarged normalization band by its two rational quadrance comparisons.

The two original rational comparisons determine the same conjunction decision on the retained Gaussian value. -/
public instance extendedBandDecidable (value : Data.Gaussian.Basic.Canonical) :
    Decidable (ExtendedBand value) := by
  unfold ExtendedBand
  infer_instance

/-- The selected canonical representative has a uniform rational residual bound `7/16` throughout the enlarged band. Its
remaining gap below `1/2` is the finite margin used by the redundant arithmetic controller.

The original eight-sector selection table and supplied enlarged band determine the retained representative. Axial and
diagonal scalar certificates bound its same Gaussian residual. -/
public theorem extendedBand_residual_le_seven_sixteenths
    {value : Data.Gaussian.Basic.Canonical} (band : ExtendedBand value) :
    Data.Gaussian.Norm.Basic.normSq (value - (Data.ComplexContinuedFraction.Encoding.Sector.select value).rep) ≤ 7 / 16
      := by
  have normLower := band.1
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical value] at normLower
  have holds := Data.ComplexContinuedFraction.Encoding.Sector.select_spec value normLower
  rcases band with ⟨normLower, normUpper⟩
  generalize selected : Data.ComplexContinuedFraction.Encoding.Sector.select value = sector at holds ⊢
  cases sector with
  | east =>
      rcases holds with ⟨xLower, yLower, yUpper⟩
      change (value.re - 1) ^ 2 + (value.im - 0) ^ 2 ≤ 7 / 16
      calc
        (value.re - 1) ^ 2 + (value.im - 0) ^ 2 =
            (value.re - 1) ^ 2 + value.im ^ 2 := by ring1
        _ ≤ 7 / 16 := axial_residual_le_seven_sixteenths
          value.re value.im xLower yLower yUpper normLower normUpper
  | northEast =>
      rcases holds with ⟨xLower, yLower⟩
      exact diagonal_residual_le_seven_sixteenths value.re value.im
        xLower yLower normLower normUpper
  | north =>
      rcases holds with ⟨xLower, xUpper, yLower⟩
      have rotatedLower : 1 ≤ value.im ^ 2 + (-value.re) ^ 2 := by
        calc
          1 ≤ value.re ^ 2 + value.im ^ 2 := normLower
          _ = value.im ^ 2 + (-value.re) ^ 2 := by ring1
      have rotatedUpper : value.im ^ 2 + (-value.re) ^ 2 ≤ 13 / 6 := by
        calc
          value.im ^ 2 + (-value.re) ^ 2 =
              value.re ^ 2 + value.im ^ 2 := by ring1
          _ ≤ 13 / 6 := normUpper
      have result := axial_residual_le_seven_sixteenths
        value.im (-value.re)
        yLower (Fraction.Order.Arithmetic.neg_lt_neg_direct xUpper)
        (Fraction.Order.Arithmetic.neg_lt_neg_direct xLower)
        rotatedLower rotatedUpper
      change (value.re - 0) ^ 2 + (value.im - 1) ^ 2 ≤ 7 / 16
      calc
        (value.re - 0) ^ 2 + (value.im - 1) ^ 2 =
            (value.im - 1) ^ 2 + (-value.re) ^ 2 := by ring1
        _ ≤ 7 / 16 := result
  | northWest =>
      rcases holds with ⟨xUpper, yLower⟩
      have rotatedLower : 1 ≤ value.im ^ 2 + (-value.re) ^ 2 := by
        calc
          1 ≤ value.re ^ 2 + value.im ^ 2 := normLower
          _ = value.im ^ 2 + (-value.re) ^ 2 := by ring1
      have rotatedUpper : value.im ^ 2 + (-value.re) ^ 2 ≤ 13 / 6 := by
        calc
          value.im ^ 2 + (-value.re) ^ 2 =
              value.re ^ 2 + value.im ^ 2 := by ring1
          _ ≤ 13 / 6 := normUpper
      have result := diagonal_residual_le_seven_sixteenths
        value.im (-value.re) yLower
        (Fraction.Order.Arithmetic.neg_le_neg_direct xUpper)
        rotatedLower rotatedUpper
      change (value.re - -1) ^ 2 + (value.im - 1) ^ 2 ≤ 7 / 16
      calc
        (value.re - -1) ^ 2 + (value.im - 1) ^ 2 =
            (value.im - 1) ^ 2 + (-value.re - 1) ^ 2 := by ring1
        _ ≤ 7 / 16 := result
  | west =>
      rcases holds with ⟨xUpper, yLower, yUpper⟩
      have rotatedLower : 1 ≤ (-value.re) ^ 2 + (-value.im) ^ 2 := by
        calc
          1 ≤ value.re ^ 2 + value.im ^ 2 := normLower
          _ = (-value.re) ^ 2 + (-value.im) ^ 2 := by ring1
      have rotatedUpper : (-value.re) ^ 2 + (-value.im) ^ 2 ≤ 13 / 6 := by
        calc
          (-value.re) ^ 2 + (-value.im) ^ 2 =
              value.re ^ 2 + value.im ^ 2 := by ring1
          _ ≤ 13 / 6 := normUpper
      have result := axial_residual_le_seven_sixteenths
        (-value.re) (-value.im)
        (Fraction.Order.Arithmetic.neg_le_neg_direct xUpper)
        (Fraction.Order.Arithmetic.neg_lt_neg_direct yUpper)
        (Fraction.Order.Arithmetic.neg_lt_neg_direct yLower)
        rotatedLower rotatedUpper
      change (value.re - -1) ^ 2 + (value.im - 0) ^ 2 ≤ 7 / 16
      calc
        (value.re - -1) ^ 2 + (value.im - 0) ^ 2 =
            (-value.re - 1) ^ 2 + (-value.im) ^ 2 := by ring1
        _ ≤ 7 / 16 := result
  | southWest =>
      rcases holds with ⟨xUpper, yUpper⟩
      have rotatedLower : 1 ≤ (-value.re) ^ 2 + (-value.im) ^ 2 := by
        calc
          1 ≤ value.re ^ 2 + value.im ^ 2 := normLower
          _ = (-value.re) ^ 2 + (-value.im) ^ 2 := by ring1
      have rotatedUpper : (-value.re) ^ 2 + (-value.im) ^ 2 ≤ 13 / 6 := by
        calc
          (-value.re) ^ 2 + (-value.im) ^ 2 =
              value.re ^ 2 + value.im ^ 2 := by ring1
          _ ≤ 13 / 6 := normUpper
      have result := diagonal_residual_le_seven_sixteenths
        (-value.re) (-value.im)
        (Fraction.Order.Arithmetic.neg_le_neg_direct xUpper)
        (Fraction.Order.Arithmetic.neg_le_neg_direct yUpper)
        rotatedLower rotatedUpper
      change (value.re - -1) ^ 2 + (value.im - -1) ^ 2 ≤ 7 / 16
      calc
        (value.re - -1) ^ 2 + (value.im - -1) ^ 2 =
            (-value.re - 1) ^ 2 + (-value.im - 1) ^ 2 := by ring1
        _ ≤ 7 / 16 := result
  | south =>
      rcases holds with ⟨xLower, xUpper, yUpper⟩
      have rotatedLower : 1 ≤ (-value.im) ^ 2 + value.re ^ 2 := by
        calc
          1 ≤ value.re ^ 2 + value.im ^ 2 := normLower
          _ = (-value.im) ^ 2 + value.re ^ 2 := by ring1
      have rotatedUpper : (-value.im) ^ 2 + value.re ^ 2 ≤ 13 / 6 := by
        calc
          (-value.im) ^ 2 + value.re ^ 2 =
              value.re ^ 2 + value.im ^ 2 := by ring1
          _ ≤ 13 / 6 := normUpper
      have result := axial_residual_le_seven_sixteenths
        (-value.im) value.re
        (Fraction.Order.Arithmetic.neg_le_neg_direct yUpper)
        xLower xUpper rotatedLower rotatedUpper
      change (value.re - 0) ^ 2 + (value.im - -1) ^ 2 ≤ 7 / 16
      calc
        (value.re - 0) ^ 2 + (value.im - -1) ^ 2 =
            (-value.im - 1) ^ 2 + value.re ^ 2 := by ring1
        _ ≤ 7 / 16 := result
  | southEast =>
      rcases holds with ⟨xLower, yUpper⟩
      have rotatedLower : 1 ≤ (-value.im) ^ 2 + value.re ^ 2 := by
        calc
          1 ≤ value.re ^ 2 + value.im ^ 2 := normLower
          _ = (-value.im) ^ 2 + value.re ^ 2 := by ring1
      have rotatedUpper : (-value.im) ^ 2 + value.re ^ 2 ≤ 13 / 6 := by
        calc
          (-value.im) ^ 2 + value.re ^ 2 =
              value.re ^ 2 + value.im ^ 2 := by ring1
          _ ≤ 13 / 6 := normUpper
      have result := diagonal_residual_le_seven_sixteenths
        (-value.im) value.re
        (Fraction.Order.Arithmetic.neg_le_neg_direct yUpper) xLower
        rotatedLower rotatedUpper
      change (value.re - 1) ^ 2 + (value.im - -1) ^ 2 ≤ 7 / 16
      calc
        (value.re - 1) ^ 2 + (value.im - -1) ^ 2 =
            (-value.im - 1) ^ 2 + (value.re - 1) ^ 2 := by ring1
        _ ≤ 7 / 16 := result

/-- The original normalization band embeds into the enlarged redundant band.

The canonical squared-norm upper bound of two is below thirteen sixths. The same selected sector representative
therefore satisfies the enlarged-band residual certificate. -/
public theorem canonical_residual_le_seven_sixteenths
    {value : Data.Gaussian.Basic.Canonical} (band : Data.ComplexContinuedFraction.Encoding.Sector.Band value) :
    Data.Gaussian.Norm.Basic.normSq (value - (Data.ComplexContinuedFraction.Encoding.Sector.select value).rep) ≤ 7 / 16
      := by
  have normLower := band.1
  have normUpper := band.2
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical value] at normLower normUpper
  exact extendedBand_residual_le_seven_sixteenths
    ⟨normLower, normUpper.trans (by decide)⟩
end Purelib.Geometry.Rational.Sector.Eight.Margin
