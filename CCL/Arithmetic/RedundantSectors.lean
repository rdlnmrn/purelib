import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Decoder

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

namespace CCL.RedundantSectors

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors

/-- The overlapping contraction predicate needed by a redundant sector
choice.  Unlike `Sector.Holds`, different representatives may safely hold at
the same displayed point. -/
def Safe (sector : Sector) (value : Gaussian) : Prop :=
  normSq (value - sector.rep) < 1 / 2

instance safeDecidable (sector : Sector) (value : Gaussian) :
    Decidable (Safe sector value) := by
  unfold Safe
  infer_instance

/-- A strict axis-aligned unit cell centred at one sector representative.
The strict inequalities are essential: a closed cell corner has residual
quadrance exactly `1/2`. -/
def InOpenCell (sector : Sector) (value : Gaussian) : Prop :=
  -1 / 2 < (value - sector.rep).re ∧
    (value - sector.rep).re < 1 / 2 ∧
    -1 / 2 < (value - sector.rep).im ∧
    (value - sector.rep).im < 1 / 2

instance inOpenCellDecidable (sector : Sector) (value : Gaussian) :
    Decidable (InOpenCell sector value) := by
  unfold InOpenCell
  infer_instance

private theorem square_lt_quarter {x : Coordinate}
    (lower : -1 / 2 < x) (upper : x < 1 / 2) :
    x ^ 2 < 1 / 4 := by
  have leftPositive : 0 < x + 1 / 2 := by
    have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      lower (1 / 2)
    calc
      0 = -1 / 2 + 1 / 2 := by decide
      _ < x + 1 / 2 := shifted
  have rightPositive : 0 < 1 / 2 - x :=
    RFAP.ConstructiveFraction.sub_pos_direct upper
  apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
  calc
    0 < (x + 1 / 2) * (1 / 2 - x) :=
      RFAP.ConstructiveFraction.mul_pos_direct leftPositive rightPositive
    _ = (1 / 2 : Coordinate) ^ 2 - x ^ 2 := by ring1
    _ = 1 / 4 - x ^ 2 := by
      rw [show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]

/-- Strict containment in the displayed unit cell is a direct local
contraction certificate; no annulus membership is involved. -/
theorem safe_of_openCell {sector : Sector} {value : Gaussian}
    (inside : InOpenCell sector value) : Safe sector value := by
  rcases inside with ⟨realLower, realUpper, imaginaryLower, imaginaryUpper⟩
  have realSquare := square_lt_quarter realLower realUpper
  have imaginarySquare := square_lt_quarter imaginaryLower imaginaryUpper
  unfold Safe normSq
  exact (RFAP.ConstructiveFraction.add_lt_add_direct
    realSquare imaginarySquare).trans_eq (by decide)

/-- Every canonical annulus-sector choice is also a redundant safe choice.
This embeds the original bitstream semantics into the stronger arithmetic
layer without changing the original definitions. -/
theorem safe_of_canonical {sector : Sector} {value : Gaussian}
    (band : Sector.Band value) (holds : sector.Holds value) :
    Safe sector value :=
  Sector.contraction band sector holds

private theorem square_le_of_two_sided
    {value radius : Coordinate}
    (lower : -radius ≤ value) (upper : value ≤ radius) :
    value ^ 2 ≤ radius ^ 2 := by
  have first : 0 ≤ radius - value :=
    RFAP.ConstructiveFraction.sub_nonneg_direct upper
  have second : 0 ≤ radius + value := by
    calc
      0 = radius + -radius := by ring1
      _ ≤ radius + value := add_le_add_right lower radius
  have differenceNonnegative : 0 ≤ radius ^ 2 - value ^ 2 := by
    calc
      0 ≤ (radius - value) * (radius + value) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct first second
      _ = radius ^ 2 - value ^ 2 := by ring1
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := -(value ^ 2))
  calc
    value ^ 2 + -(value ^ 2) = 0 := by ring1
    _ ≤ radius ^ 2 - value ^ 2 := differenceNonnegative
    _ = radius ^ 2 + -(value ^ 2) := by ring1

private theorem square_lt_quarter_of_half_bounds {value : Coordinate}
    (lower : -1 / 2 < value) (upper : value < 1 / 2) :
    value ^ 2 < 1 / 4 :=
  square_lt_quarter lower upper

/-- Uniform version of the axial sector calculation.  The rational constant
`7/16` is deliberately a little weaker than the sharp algebraic maximum; its
strict gap below `1/2` supplies a finite enclosure margin. -/
private theorem axial_residual_le_seven_sixteenths
    (x y : Coordinate)
    (xLower : 1 / 2 ≤ x) (yLower : -1 / 2 < y) (yUpper : y < 1 / 2)
    (normLower : 1 ≤ x ^ 2 + y ^ 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 13 / 6) :
    (x - 1) ^ 2 + y ^ 2 ≤ 7 / 16 := by
  have xNonnegative : 0 ≤ x := (by decide : (0 : Coordinate) ≤ 1 / 2).trans xLower
  have ySquareLt : y ^ 2 < 1 / 4 :=
    square_lt_quarter_of_half_bounds yLower yUpper
  have xAboveThreeQuarters : 3 / 4 < x := by
    by_cases above : 3 / 4 < x
    · exact above
    · have xUpper : x ≤ 3 / 4 := le_of_not_gt above
      have xSquareUpper : x ^ 2 ≤ (3 / 4 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct xNonnegative xUpper 2
      have normTooSmall : x ^ 2 + y ^ 2 < 1 := by
        calc
          x ^ 2 + y ^ 2 < (3 / 4 : Coordinate) ^ 2 + 1 / 4 :=
            add_lt_add_of_le_of_lt xSquareUpper ySquareLt
          _ = 13 / 16 := by decide
          _ < 1 := by decide
      exact ((not_lt_of_ge normLower) normTooSmall).elim
  by_cases moderate : x ≤ 11 / 8
  · have differenceLower : -(3 / 8 : Coordinate) ≤ x - 1 := by
      exact (show -(3 / 8 : Coordinate) < x - 1 from by
        calc
        -(3 / 8 : Coordinate) < -1 / 4 := by decide
        _ < x - 1 := by
          apply RFAP.ConstructiveFraction.add_lt_add_right_direct
            xAboveThreeQuarters (-1)).le
    have differenceUpper : x - 1 ≤ (3 / 8 : Coordinate) := by
      calc
        x - 1 = -1 + x := by ring1
        _ ≤ -1 + 11 / 8 := add_le_add_right moderate (-1)
        _ = 3 / 8 := by decide
    have differenceSquare : (x - 1) ^ 2 ≤ (3 / 8 : Coordinate) ^ 2 :=
      square_le_of_two_sided differenceLower differenceUpper
    apply LT.lt.le
    have squareStrict : (3 / 8 : Coordinate) ^ 2 < 3 / 16 := by decide
    calc
      (x - 1) ^ 2 + y ^ 2 <
          (3 / 8 : Coordinate) ^ 2 + 1 / 4 :=
        add_lt_add_of_le_of_lt differenceSquare ySquareLt
      _ < 3 / 16 + 1 / 4 :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          squareStrict (1 / 4)
      _ = 7 / 16 := by decide
  · have xAbove : 11 / 8 < x := lt_of_not_ge moderate
    have doubled : (2 : Coordinate) * (11 / 8 : Coordinate) < 2 * x :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide) xAbove
    have residualIdentity :
        (x - 1) ^ 2 + y ^ 2 = (x ^ 2 + y ^ 2) - 2 * x + 1 := by
      ring1
    rw [residualIdentity]
    have negDoubled : -(2 * x) < -(2 * (11 / 8 : Coordinate)) :=
      RFAP.ConstructiveFraction.neg_lt_neg_direct doubled
    have beforeOne :
        (x ^ 2 + y ^ 2) + -(2 * x) <
          13 / 6 + -(2 * (11 / 8 : Coordinate)) :=
      add_lt_add_of_le_of_lt normUpper negDoubled
    exact (show (x ^ 2 + y ^ 2) - 2 * x + 1 < 7 / 16 from by
      calc
        (x ^ 2 + y ^ 2) - 2 * x + 1 <
            13 / 6 - 2 * (11 / 8 : Coordinate) + 1 := by
          calc
            (x ^ 2 + y ^ 2) - 2 * x + 1 =
                1 + ((x ^ 2 + y ^ 2) + -(2 * x)) := by ring1
            _ < 1 + (13 / 6 + -(2 * (11 / 8 : Coordinate))) :=
              add_lt_add_right beforeOne 1
            _ = 13 / 6 - 2 * (11 / 8 : Coordinate) + 1 := by ring1
        _ = 5 / 12 := by decide
        _ < 7 / 16 := by decide).le

private theorem high_slack_identity (p q : Coordinate) :
    (2 * p - 7 / 4) + (5 / 3 - (p + q)) =
      (p - q) - 1 / 12 := by
  have constants :
      (5 / 3 : Coordinate) - 7 / 4 = -1 / 12 := by decide
  have negative : (-1 / 12 : Coordinate) = -(1 / 12) := by decide
  calc
    (2 * p - 7 / 4) + (5 / 3 - (p + q)) =
        (2 * p - (p + q)) + (5 / 3 - 7 / 4) := by ring1
    _ = (2 * p - (p + q)) + (-1 / 12) := by rw [constants]
    _ = (2 * p - (p + q)) + -(1 / 12) := by rw [negative]
    _ = (p - q) - 1 / 12 := by ring1

private theorem diagonal_gap_identity (p q : Coordinate) :
    (p - q) - 1 / 16 = 7 / 16 - (q - p + 1 / 2) := by
  have constants :
      (7 / 16 : Coordinate) - 1 / 2 = -1 / 16 := by decide
  have negative : (-1 / 16 : Coordinate) = -(1 / 16) := by decide
  calc
    (p - q) - 1 / 16 = (p - q) + -(1 / 16) := by ring1
    _ = (p - q) + (-1 / 16) := by rw [negative]
    _ = (p - q) + (7 / 16 - 1 / 2) := by rw [constants]
    _ = 7 / 16 - (q - p + 1 / 2) := by ring1

private theorem translated_p_above_third
    (p q : Coordinate) (pNonnegative : 0 ≤ p)
    (lowerPQ : (1 / 2 : Coordinate) ≤ p + q)
    (qLeSquareP : q ≤ p ^ 2) :
    (1 / 3 : Coordinate) < p := by
  by_cases above : (1 / 3 : Coordinate) < p
  · exact above
  · have pUpper : p ≤ 1 / 3 := le_of_not_gt above
    have pSquareUpper : p ^ 2 ≤ (1 / 3 : Coordinate) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct pNonnegative pUpper 2
    have pqUpper : p + q ≤ (4 / 9 : Coordinate) := by
      calc
        p + q ≤ (1 / 3 : Coordinate) + (1 / 3 : Coordinate) ^ 2 :=
          add_le_add pUpper (qLeSquareP.trans pSquareUpper)
        _ = 4 / 9 := by decide
    have impossible : (1 / 2 : Coordinate) ≤ 4 / 9 :=
      lowerPQ.trans pqUpper
    exact ((by decide : ¬ ((1 / 2 : Coordinate) ≤ 4 / 9)) impossible).elim

private theorem translated_difference_order
    (p q : Coordinate) (qLeSquareP : q ≤ p ^ 2) :
    p - p ^ 2 ≤ p - q := by
  have negated := RFAP.ConstructiveFraction.neg_le_neg_direct qLeSquareP
  calc
    p - p ^ 2 = p + -(p ^ 2) := by ring1
    _ ≤ p + -q := add_le_add_right negated p
    _ = p - q := by ring1

private theorem translated_diagonal_gap
    (p q : Coordinate) (pNonnegative : 0 ≤ p)
    (lowerPQ : (1 / 2 : Coordinate) ≤ p + q)
    (upperPQ : p + q ≤ (5 / 3 : Coordinate))
    (qLeSquareP : q ≤ p ^ 2) :
    (1 / 16 : Coordinate) ≤ p - q := by
  have pAboveThird :=
    translated_p_above_third p q pNonnegative lowerPQ qLeSquareP
  have differenceOrder := translated_difference_order p q qLeSquareP
  match RFAP.ConstructiveFraction.rationalDecLE
      (7 : Coordinate) (8 * p) with
  | isTrue highScaled =>
    have doubled : (7 / 4 : Coordinate) ≤ 2 * p := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := (4 : Coordinate)) _ (by decide)
      calc
        (7 / 4 : Coordinate) * 4 = 7 :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne 7 4 (by decide)
        _ ≤ 8 * p := highScaled
        _ = (2 * p) * 4 := by ring1
    have upperSlack : 0 ≤ 5 / 3 - (p + q) :=
      RFAP.ConstructiveFraction.sub_nonneg_direct upperPQ
    have highSlack : 0 ≤ 2 * p - 7 / 4 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct doubled
    have twelfthLower : (1 / 12 : Coordinate) ≤ p - q := by
      have differenceNonnegative : 0 ≤ (p - q) - 1 / 12 := by
        calc
          0 ≤ (2 * p - 7 / 4) + (5 / 3 - (p + q)) :=
            add_nonneg highSlack upperSlack
          _ = (p - q) - 1 / 12 := high_slack_identity p q
      apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
        (c := -(1 / 12 : Coordinate))
      calc
        (1 / 12 : Coordinate) + -(1 / 12) = 0 := by ring1
        _ ≤ (p - q) - 1 / 12 := differenceNonnegative
        _ = (p - q) + -(1 / 12) := by ring1
    exact (by decide : (1 / 16 : Coordinate) ≤ 1 / 12).trans twelfthLower
  | isFalse notHighScaled =>
    have belowScaled : 8 * p < (7 : Coordinate) :=
      lt_of_not_ge notHighScaled
    have below : p < 7 / 8 := by
      apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
        (c := (8 : Coordinate)) _ (by decide)
      calc
        p * 8 = 8 * p := by ring1
        _ < 7 := belowScaled
        _ = (7 / 8 : Coordinate) * 8 :=
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 7 8
            (by decide)).symm
    have oneMinusEighth : (1 / 8 : Coordinate) < 1 - p := by
      have negated : -(7 / 8 : Coordinate) < -p :=
        RFAP.ConstructiveFraction.neg_lt_neg_direct below
      calc
        (1 / 8 : Coordinate) = 1 + -(7 / 8) := by decide
        _ < 1 + -p := add_lt_add_right negated 1
        _ = 1 - p := by ring1
    by_cases half : 1 / 2 ≤ p
    · have productLower : (1 / 16 : Coordinate) < p * (1 - p) := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (by decide : (0 : Coordinate) < 1 / 2) oneMinusEighth
        calc
          (1 / 16 : Coordinate) = (1 / 2) * (1 / 8) := by decide
          _ < (1 / 2) * (1 - p) := scaled
          _ ≤ p * (1 - p) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              half ((by decide : (0 : Coordinate) < 1 / 8).trans
                oneMinusEighth).le
      exact (show (1 / 16 : Coordinate) < p - q from by
        calc
          (1 / 16 : Coordinate) < p * (1 - p) := productLower
          _ = p - p ^ 2 := by ring1
          _ ≤ p - q := differenceOrder).le
    · have pBelowHalf : p < 1 / 2 := lt_of_not_ge half
      have halfBelowOneMinus : (1 / 2 : Coordinate) < 1 - p := by
        have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct pBelowHalf
        calc
          (1 / 2 : Coordinate) = 1 + -(1 / 2) := by decide
          _ < 1 + -p := add_lt_add_right negated 1
          _ = 1 - p := by ring1
      have productLower : (1 / 6 : Coordinate) < p * (1 - p) := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (by decide : (0 : Coordinate) < 1 / 3) halfBelowOneMinus
        have rightPositive : 0 < 1 - p :=
          (by decide : (0 : Coordinate) < 1 / 2).trans halfBelowOneMinus
        calc
          (1 / 6 : Coordinate) = (1 / 3) * (1 / 2) := by decide
          _ < (1 / 3) * (1 - p) := scaled
          _ < p * (1 - p) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
              pAboveThird rightPositive
      exact (show (1 / 16 : Coordinate) < p - q from by
        calc
          (1 / 16 : Coordinate) < 1 / 6 := by decide
          _ < p * (1 - p) := productLower
          _ = p - p ^ 2 := by ring1
          _ ≤ p - q := differenceOrder).le

/-- Uniform diagonal-sector estimate in translated nonnegative coordinates. -/
private theorem diagonal_residual_le_seven_sixteenths
    (x y : Coordinate)
    (xLower : 1 / 2 ≤ x) (yLower : 1 / 2 ≤ y)
    (normLower : 1 ≤ x ^ 2 + y ^ 2)
    (normUpper : x ^ 2 + y ^ 2 ≤ 13 / 6) :
    (x - 1) ^ 2 + (y - 1) ^ 2 ≤ 7 / 16 := by
  let a := x - 1 / 2
  let b := y - 1 / 2
  generalize pDefinition : a + b = p
  generalize qDefinition : a ^ 2 + b ^ 2 = q
  have aNonnegative : 0 ≤ a :=
    RFAP.ConstructiveFraction.sub_nonneg_direct xLower
  have bNonnegative : 0 ≤ b :=
    RFAP.ConstructiveFraction.sub_nonneg_direct yLower
  have pNonnegative : 0 ≤ p := by
    rw [← pDefinition]
    exact add_nonneg aNonnegative bNonnegative
  have normIdentity : x ^ 2 + y ^ 2 = p + q + 1 / 2 := by
    have linearZero : (1 : Coordinate) - 2 * (1 / 2) = 0 := by decide
    have constantZero :
        (2 : Coordinate) * (1 / 2) ^ 2 - 1 / 2 = 0 := by decide
    calc
      x ^ 2 + y ^ 2 = x ^ 2 + y ^ 2 +
          ((1 : Coordinate) - 2 * (1 / 2)) * (x + y) +
          (2 * (1 / 2 : Coordinate) ^ 2 - 1 / 2) := by
        rw [linearZero, constantZero]
        ring1
      _ = p + q + 1 / 2 := by
        rw [← pDefinition, ← qDefinition]
        dsimp only [a, b]
        ring1
  have lowerPQ : (1 / 2 : Coordinate) ≤ p + q := by
    apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
      (c := (1 / 2 : Coordinate))
    calc
      (1 / 2 : Coordinate) + 1 / 2 = 1 := by decide
      _ ≤ x ^ 2 + y ^ 2 := normLower
      _ = (p + q) + 1 / 2 := normIdentity
  have upperPQ : p + q ≤ (5 / 3 : Coordinate) := by
    apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
      (c := (1 / 2 : Coordinate))
    calc
      (p + q) + 1 / 2 = x ^ 2 + y ^ 2 := normIdentity.symm
      _ ≤ 13 / 6 := normUpper
      _ = (5 / 3 : Coordinate) + 1 / 2 := by decide
  have qLeSquareP : q ≤ p ^ 2 := by
    have twiceProductNonnegative : 0 ≤ 2 * (a * b) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          aNonnegative bNonnegative)
    calc
      q = q + 0 := by ring1
      _ ≤ q + 2 * (a * b) := add_le_add le_rfl twiceProductNonnegative
      _ = p ^ 2 := by
        rw [← pDefinition, ← qDefinition]
        ring1
  have gapLower : (1 / 16 : Coordinate) ≤ p - q :=
    translated_diagonal_gap p q pNonnegative lowerPQ upperPQ qLeSquareP
  have sumIdentity : p = x + y - 1 := by
    rw [← pDefinition]
    dsimp only [a, b]
    have halves : (1 / 2 : Coordinate) + 1 / 2 = 1 := by decide
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
        RFAP.ConstructiveFraction.sub_nonneg_direct gapLower
      _ = 7 / 16 - (q - p + 1 / 2) := diagonal_gap_identity p q
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := -(q - p + 1 / 2))
  calc
    q - p + 1 / 2 + -(q - p + 1 / 2) = 0 := by ring1
    _ ≤ 7 / 16 - (q - p + 1 / 2) := differenceNonnegative
    _ = 7 / 16 + -(q - p + 1 / 2) := by ring1

/-- The slightly enlarged closed normalization band used by the redundant
controller.  Its overlap above norm `2` is what separates safe-sector output
from the next-unary output without an equality test. -/
def ExtendedBand (value : Gaussian) : Prop :=
  1 ≤ normSq value ∧ normSq value ≤ 13 / 6

instance extendedBandDecidable (value : Gaussian) :
    Decidable (ExtendedBand value) := by
  unfold ExtendedBand
  infer_instance

/-- The selected canonical representative has a uniform rational residual
bound `7/16` throughout the enlarged band.  Its remaining gap below `1/2`
is the finite margin used by the redundant arithmetic controller. -/
theorem extendedBand_residual_le_seven_sixteenths
    {value : Gaussian} (band : ExtendedBand value) :
    normSq (value - (Sector.select value).rep) ≤ 7 / 16 := by
  have holds := Sector.select_spec value band.1
  rcases band with ⟨normLower, normUpper⟩
  generalize selected : Sector.select value = sector at holds ⊢
  cases sector with
  | east =>
      rcases holds with ⟨xLower, yLower, yUpper⟩
      change (value.re - 1) ^ 2 + (value.im - 0) ^ 2 ≤ 7 / 16
      simpa only [_root_.sub_zero] using
        axial_residual_le_seven_sixteenths
          value.re value.im xLower yLower
          yUpper normLower normUpper
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
        yLower (RFAP.ConstructiveFraction.neg_lt_neg_direct xUpper)
        (RFAP.ConstructiveFraction.neg_lt_neg_direct xLower)
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
        (RFAP.ConstructiveFraction.neg_le_neg_direct xUpper)
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
        (RFAP.ConstructiveFraction.neg_le_neg_direct xUpper)
        (RFAP.ConstructiveFraction.neg_lt_neg_direct yUpper)
        (RFAP.ConstructiveFraction.neg_lt_neg_direct yLower)
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
        (RFAP.ConstructiveFraction.neg_le_neg_direct xUpper)
        (RFAP.ConstructiveFraction.neg_le_neg_direct yUpper)
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
        (RFAP.ConstructiveFraction.neg_le_neg_direct yUpper)
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
        (RFAP.ConstructiveFraction.neg_le_neg_direct yUpper) xLower
        rotatedLower rotatedUpper
      change (value.re - 1) ^ 2 + (value.im - -1) ^ 2 ≤ 7 / 16
      calc
        (value.re - 1) ^ 2 + (value.im - -1) ^ 2 =
            (-value.im - 1) ^ 2 + (value.re - 1) ^ 2 := by ring1
        _ ≤ 7 / 16 := result

/-- The original normalization band embeds into the enlarged redundant band. -/
theorem canonical_residual_le_seven_sixteenths
    {value : Gaussian} (band : Sector.Band value) :
    normSq (value - (Sector.select value).rep) ≤ 7 / 16 :=
  extendedBand_residual_le_seven_sixteenths
    ⟨band.1, band.2.trans (by decide)⟩

/-- Local safety alone gives the strict post-inversion lower norm.  The old
annulus upper bound was used only to derive this local inequality. -/
theorem postInversion_norm_gt_one {sector : Sector} {value : Gaussian}
    (safe : Safe sector value) (residualNonzero : value - sector.rep ≠ 0) :
    1 < normSq ((gamma * (value - sector.rep))⁻¹) := by
  have gammaNonzero : gamma ≠ 0 := by decide
  have productNonzero : gamma * (value - sector.rep) ≠ 0 :=
    mul_ne_zero_direct gammaNonzero residualNonzero
  have productNormPositive := normSq_pos productNonzero
  have productNormLtOne : normSq (gamma * (value - sector.rep)) < 1 := by
    rw [normSq_mul, normSq_gamma]
    calc
      2 * normSq (value - sector.rep) < 2 * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide) safe
      _ = 1 := by decide
  rw [inv_eq, normSq_inv _ productNonzero]
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := normSq (gamma * (value - sector.rep))) _ productNormPositive
  calc
    1 * normSq (gamma * (value - sector.rep)) =
        normSq (gamma * (value - sector.rep)) :=
      RFAP.ConstructiveFraction.one_mul _
    _ < 1 := productNormLtOne
    _ = (normSq (gamma * (value - sector.rep)))⁻¹ *
          normSq (gamma * (value - sector.rep)) :=
      (RFAP.ConstructiveFraction.inv_mul_cancel _
        productNormPositive.ne').symm

/-- The difference-of-inverses identity proved by cancellation in the
constructive Gaussian field.  This named form keeps later error estimates
away from Mathlib's generic field identity. -/
theorem inverse_sub_inverse_direct {left right : Gaussian}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    inv left - inv right =
      inv left * (right - left) * inv right := by
  have productNonzero : left * right ≠ 0 :=
    mul_ne_zero_direct leftNonzero rightNonzero
  apply mul_right_cancel_of_ne productNonzero
  have leftCancel := inv_mul left leftNonzero
  have rightCancel := inv_mul right rightNonzero
  calc
    (inv left - inv right) * (left * right) = right - left := by
      calc
        (inv left - inv right) * (left * right) =
            (inv left * left) * right -
              (inv right * right) * left := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
        _ = right - left := by
          rw [leftCancel, rightCancel]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, mul_re, mul_im, one_re, one_im] <;>
            ring1
    _ = (inv left * (right - left) * inv right) * (left * right) := by
      calc
        right - left =
            (right - left) *
              ((inv left * left) * (inv right * right)) := by
          rw [leftCancel, rightCancel,
            RFAP.ConstructiveGaussian.Gaussian.one_mul,
            RFAP.ConstructiveGaussian.Gaussian.mul_one]
        _ = (inv left * (right - left) * inv right) *
              (left * right) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1

/-- Squared norm of the numerator created by the safe inverse chart. -/
theorem transformed_difference_normSq
    {sector : Sector} (left right : Gaussian) :
    normSq
        ((gamma * (right - sector.rep)) -
          (gamma * (left - sector.rep))) =
      2 * normSq (left - right) := by
  have numeratorIdentity :
      (gamma * (right - sector.rep)) -
          (gamma * (left - sector.rep)) =
        -(gamma * (left - right)) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im, neg_re, neg_im, gamma] <;>
      ring1
  rw [numeratorIdentity, normSq_neg, normSq_mul, normSq_gamma]

/-- Rewrite the three inverse factors into two explicit fractions. -/
theorem inverse_product_as_fractions_direct (a b c : Coordinate) :
    (2 * a)⁻¹ * (2 * b) * (2 * c)⁻¹ =
      ((2 * b) / (2 * a)) * (1 / (2 * c)) := by
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.one_mul]
  rw [RFAP.ConstructiveFraction.mul_comm (2 * a)⁻¹ (2 * b)]

/-- Combine the two explicit fractions without a generic field instance. -/
theorem combine_scaled_fractions_direct (a b c : Coordinate) :
    ((2 * b) / (2 * a)) * (1 / (2 * c)) =
      (2 * b) / (2 * (2 * a * c)) := by
  calc
    ((2 * b) / (2 * a)) * (1 / (2 * c)) =
        ((2 * b) * 1) / ((2 * a) * (2 * c)) :=
      RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
    _ = (2 * b) / (2 * (2 * a * c)) := by
      rw [RFAP.ConstructiveFraction.mul_one_direct]
      have denominatorIdentity :
          (2 * a) * (2 * c) = 2 * (2 * a * c) := by ring1
      rw [denominatorIdentity]

/-- The rational cancellation at the end of the inverse-error calculation,
kept explicit so it cannot select Mathlib's generic division lemmas. -/
theorem inverse_error_fraction_direct (a b c : Coordinate) :
    (2 * a)⁻¹ * (2 * b) * (2 * c)⁻¹ = b / (2 * a * c) := by
  rw [inverse_product_as_fractions_direct,
    combine_scaled_fractions_direct]
  have twoNonzero : (2 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 2) (by decide)).ne'
  exact RFAP.ConstructiveFraction.mul_div_mul_left_direct
    2 b (2 * a * c) twoNonzero

/-- Explicit-inverse form of the affine error calculation. -/
private theorem inversion_difference_normSq_explicit
    {sector : Sector} {left right : Gaussian}
    (leftNonzero : left - sector.rep ≠ 0)
    (rightNonzero : right - sector.rep ≠ 0) :
    normSq
        (inv (gamma * (left - sector.rep)) -
          inv (gamma * (right - sector.rep))) =
      normSq (left - right) /
        (2 * normSq (left - sector.rep) * normSq (right - sector.rep)) := by
  have gammaNonzero : gamma ≠ 0 := by decide
  have leftProductNonzero : gamma * (left - sector.rep) ≠ 0 :=
    mul_ne_zero_direct gammaNonzero leftNonzero
  have rightProductNonzero : gamma * (right - sector.rep) ≠ 0 :=
    mul_ne_zero_direct gammaNonzero rightNonzero
  let leftProduct := gamma * (left - sector.rep)
  let rightProduct := gamma * (right - sector.rep)
  have inverseDifference :
      inv leftProduct - inv rightProduct =
        inv leftProduct * (rightProduct - leftProduct) * inv rightProduct :=
    inverse_sub_inverse_direct leftProductNonzero rightProductNonzero
  rw [inverseDifference,
    normSq_mul, normSq_mul, normSq_inv _ leftProductNonzero,
    normSq_inv _ rightProductNonzero]
  have numeratorNorm :
      normSq (rightProduct - leftProduct) =
        2 * normSq (left - right) := by
    exact transformed_difference_normSq left right
  have leftProductNorm : normSq leftProduct =
      2 * normSq (left - sector.rep) := by
    dsimp only [leftProduct]
    rw [normSq_mul, normSq_gamma]
  have rightProductNorm : normSq rightProduct =
      2 * normSq (right - sector.rep) := by
    dsimp only [rightProduct]
    rw [normSq_mul, normSq_gamma]
  rw [leftProductNorm, rightProductNorm]
  rw [numeratorNorm]
  exact inverse_error_fraction_direct
    (normSq (left - sector.rep))
    (normSq (left - right))
    (normSq (right - sector.rep))

/-- Exact affine error propagation through the safe inverse chart.  This
identity explains why a scalar error bound must be accompanied by residual
separation before the projective tail is converted back to an affine box. -/
theorem inversion_difference_normSq
    {sector : Sector} {left right : Gaussian}
    (leftNonzero : left - sector.rep ≠ 0)
    (rightNonzero : right - sector.rep ≠ 0) :
    normSq
        ((gamma * (left - sector.rep))⁻¹ -
          (gamma * (right - sector.rep))⁻¹) =
      normSq (left - right) /
        (2 * normSq (left - sector.rep) * normSq (right - sector.rep)) := by
  rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq]
  exact inversion_difference_normSq_explicit leftNonzero rightNonzero

end CCL.RedundantSectors
