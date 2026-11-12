module

import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Algebra.NatCast
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Semiring.Normalization
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

/-!
# Finite rational contraction depths

A rational ceiling supplies sufficient fuel for a bounded contraction scan.
The scan retains each width and returns the first depth whose scalar test
meets the positive tolerance.
-/

namespace Purelib.Approximation.Rational.Contraction

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Rounding
open Purelib.Algebra.Semiring

/-- The inverse contraction power dominates one plus half its finite depth.

At each successor, multiplication by three halves enlarges the retained
linear lower bound by a nonnegative rational remainder. -/
public theorem inverseContraction_linear_lower (depth : Nat) :
    (1 : Fraction.Rational) + (depth : Fraction.Rational) * (1 / 2) ≤
      (3 / 2 : Fraction.Rational) ^ depth := by
  induction depth with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero]
      exact le_rfl
  | succ depth inductionHypothesis =>
      have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := by decide
      have depthNonnegative : (0 : Fraction.Rational) ≤ (depth : Fraction.Rational) :=
        Fraction.Cast.Order.natCast_le_direct (Nat.zero_le depth)
      have remainderNonnegative : 0 ≤
          (depth : Fraction.Rational) * (1 / 2) * (1 / 2) :=
        Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct
            depthNonnegative halfNonnegative)
          halfNonnegative
      have ratioNonnegative : (0 : Fraction.Rational) ≤ 3 / 2 := by decide
      have scaled :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          inductionHypothesis ratioNonnegative
      calc
        (1 : Fraction.Rational) + (Nat.succ depth : Fraction.Rational) * (1 / 2) ≤
            (1 + (depth : Fraction.Rational) * (1 / 2)) * (3 / 2) := by
          apply Arithmetic.le_of_sub_nonneg_direct
          calc
            0 ≤ (depth : Fraction.Rational) * (1 / 2) * (1 / 2) :=
              remainderNonnegative
            _ = (1 + (depth : Fraction.Rational) * (1 / 2)) * (3 / 2) -
                (1 + (Nat.succ depth : Fraction.Rational) * (1 / 2)) := by
              have threeHalves : (3 / 2 : Fraction.Rational) = 1 + 1 / 2 := by
                decide
              rw [threeHalves, Nat.cast_succ]
              ring1
        _ ≤ (3 / 2 : Fraction.Rational) ^ depth * (3 / 2) := scaled
        _ = (3 / 2 : Fraction.Rational) ^ Nat.succ depth := by
          rw [pow_succ]

/-- Compute a finite contraction depth bound from the rational ceiling.

The rational ceiling bounds the requested ratio by a natural depth.
Its retained quotient, integer ceiling and natural readback are unchanged. -/
@[expose] public def geometricDepthBound (width epsilon : Fraction.Rational) : Nat :=
  Floor.ceilNat (2 * width / epsilon)

/-- The computed ceiling depth contracts a nonnegative width to at most the positive tolerance.

The width is nonnegative and the tolerance is positive. The ceiling
ratio and inverse-power bound certify the same finite contraction factor. -/
public theorem geometricDepthBound_sufficient {width epsilon : Fraction.Rational}
    (widthNonnegative : 0 ≤ width) (epsilonPositive : 0 < epsilon) :
    (2 / 3 : Fraction.Rational) ^ geometricDepthBound width epsilon * width ≤
      epsilon := by
  let depth := geometricDepthBound width epsilon
  have ratioNonnegative : 0 ≤ 2 * width / epsilon := by
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv]
    exact Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        widthNonnegative)
      (Field.inv_pos_direct epsilonPositive).le
  have ceiling : 2 * width / epsilon ≤ (depth : Fraction.Rational) := by
    exact Floor.le_natCast_ceilNat_of_nonneg
      ratioNonnegative
  have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := by decide
  have halfScaled :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      ceiling halfNonnegative
  have widthRatio : width / epsilon ≤
      (depth : Fraction.Rational) * (1 / 2) := by
    calc
      width / epsilon = (2 * width / epsilon) * (1 / 2) := by
        rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
          Algebra.Field.ExplicitField.div_eq_mul_inv]
        have twoHalf : (2 : Fraction.Rational) * (1 / 2) = 1 := by decide
        calc
          width * epsilon⁻¹ = width * epsilon⁻¹ * 1 :=
            (Fraction.Field.mul_one_direct _).symm
          _ = width * epsilon⁻¹ * (2 * (1 / 2)) := by rw [twoHalf]
          _ = 2 * width * epsilon⁻¹ * (1 / 2) := by ring1
      _ ≤ (depth : Fraction.Rational) * (1 / 2) := halfScaled
  have linear := inverseContraction_linear_lower depth
  have depthHalfLeLinear : (depth : Fraction.Rational) * (1 / 2) ≤
      1 + (depth : Fraction.Rational) * (1 / 2) := by
    calc
      (depth : Fraction.Rational) * (1 / 2) =
          0 + (depth : Fraction.Rational) * (1 / 2) := by ring1
      _ ≤ 1 + (depth : Fraction.Rational) * (1 / 2) :=
        add_le_add (by decide) (le_refl _)
  have ratioPower : width / epsilon ≤
      (3 / 2 : Fraction.Rational) ^ depth :=
    widthRatio.trans (depthHalfLeLinear.trans linear)
  have widthBound : width ≤
      epsilon * (3 / 2 : Fraction.Rational) ^ depth := by
    have divided :=
      (Field.div_le_iff_pos epsilonPositive).mp ratioPower
    simpa only [Fraction.Field.mul_comm] using divided
  have contractionNonnegative :
      0 ≤ (2 / 3 : Fraction.Rational) ^ depth :=
    Arithmetic.pow_nonneg_direct (by decide) depth
  have inverseProduct :
      (2 / 3 : Fraction.Rational) ^ depth * (3 / 2 : Fraction.Rational) ^ depth = 1 := by
    rw [← Normalization.product_pow (2 / 3 : Fraction.Rational) (3 / 2) depth]
    have inverseBase : (2 / 3 : Fraction.Rational) * (3 / 2) = 1 := by decide
    rw [inverseBase, one_pow]
  change (2 / 3 : Fraction.Rational) ^ depth * width ≤ epsilon
  calc
    (2 / 3 : Fraction.Rational) ^ depth * width ≤
        (2 / 3 : Fraction.Rational) ^ depth *
          (epsilon * (3 / 2 : Fraction.Rational) ^ depth) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        widthBound contractionNonnegative
    _ = epsilon := by
      rw [show (2 / 3 : Fraction.Rational) ^ depth *
          (epsilon * (3 / 2 : Fraction.Rational) ^ depth) =
        epsilon * ((2 / 3 : Fraction.Rational) ^ depth *
          (3 / 2 : Fraction.Rational) ^ depth) by ring1,
        inverseProduct]
      ring1

/-- Scan at most the displayed fuel for the first sufficient geometric contraction. The recursive width is an exact
rational, so every stop test is decidable and the construction remains a bounded finite calculation.

Each successor tests the retained width against the tolerance. A failed
test passes the same contracted width to the recursive call with one less fuel. -/
@[expose] public def geometricDepthSearch (width epsilon : Fraction.Rational) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      if width ≤ epsilon then 0
      else 1 + geometricDepthSearch ((2 / 3 : Fraction.Rational) * width) epsilon fuel

section
/-- A bounded contraction scan succeeds whenever its terminal depth satisfies the displayed width bound.

The supplied terminal inequality bounds the last permitted depth.
Induction transports it through each retained stop test and successor width. -/
private theorem geometricDepthSearch_sufficient
    {width epsilon : Fraction.Rational} (fuel : Nat)
    (terminal : (2 / 3 : Fraction.Rational) ^ fuel * width ≤ epsilon) :
    (2 / 3 : Fraction.Rational) ^ geometricDepthSearch width epsilon fuel * width ≤
      epsilon := by
  induction fuel generalizing width with
  | zero =>
      simpa only [geometricDepthSearch, pow_zero, one_mul] using terminal
  | succ fuel inductionHypothesis =>
      by_cases small : width ≤ epsilon
      · rw [geometricDepthSearch, if_pos small, pow_zero, one_mul]
        exact small
      · let next := (2 / 3 : Fraction.Rational) * width
        have nextTerminal :
            (2 / 3 : Fraction.Rational) ^ fuel * next ≤ epsilon := by
          calc
            (2 / 3 : Fraction.Rational) ^ fuel * next =
                (2 / 3 : Fraction.Rational) ^ (fuel + 1) * width := by
              dsimp only [next]
              rw [pow_succ]
              ring1
            _ ≤ epsilon := terminal
        have recursive := inductionHypothesis nextTerminal
        rw [geometricDepthSearch, if_neg small]
        calc
          (2 / 3 : Fraction.Rational) ^
                (1 + geometricDepthSearch next epsilon fuel) * width =
              (2 / 3 : Fraction.Rational) ^
                  geometricDepthSearch next epsilon fuel * next := by
            dsimp only [next]
            rw [Nat.add_comm 1, pow_succ]
            ring1
          _ ≤ epsilon := recursive
end

/-- Compute the first sufficient contraction depth within the retained ceiling fuel.

The scan consumes the computed ceiling as its fuel. It returns the same
first successful depth, or the exhausted depth when no earlier test succeeds. -/
@[expose] public def geometricDepth (width epsilon : Fraction.Rational) : Nat :=
  geometricDepthSearch width epsilon (geometricDepthBound width epsilon)

/-- The computed finite contraction depth reduces a nonnegative width to at most the positive tolerance.

Nonnegative width and positive tolerance give a sufficient terminal
ceiling. The bounded scan transports that certificate to its computed depth. -/
public theorem geometricDepth_sufficient {width epsilon : Fraction.Rational}
    (widthNonnegative : 0 ≤ width) (epsilonPositive : 0 < epsilon) :
    (2 / 3 : Fraction.Rational) ^ geometricDepth width epsilon * width ≤
      epsilon := by
  exact geometricDepthSearch_sufficient _
    (geometricDepthBound_sufficient widthNonnegative epsilonPositive)

/-- Increasing a natural exponent decreases powers of a rational rate between zero and one. -/
public theorem power_antitone {rate : Fraction.Rational} (nonnegative : 0 ≤ rate) (atMostOne : rate ≤ 1)
    {first second : Nat} (ordered : first ≤ second) : rate ^ second ≤ rate ^ first := by
  have reconstruct : first + (second - first) = second := Nat.add_sub_of_le ordered
  have extra := Arithmetic.pow_le_pow_direct nonnegative atMostOne (second - first)
  rewrite [one_pow] at extra
  rewrite [← reconstruct, pow_add]
  have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct extra (Arithmetic.pow_nonneg_direct nonnegative first)
  exact bounded.trans_eq (Fraction.Field.mul_one_direct _)

/-- A rate at least one has an explicit finite linear lower bound for every natural power. -/
public theorem power_linear_lower {rate : Fraction.Rational} (oneLe : 1 ≤ rate) (index : Nat) :
    1 + (index : Fraction.Rational) * (rate - 1) ≤ rate ^ index := by
  have rateNonnegative : 0 ≤ rate := (by decide : (0 : Fraction.Rational) ≤ 1).trans oneLe
  induction index with
  | zero =>
      rewrite [Nat.cast_zero, zero_mul, add_zero, pow_zero]
      exact le_rfl
  | succ index previous =>
      have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct previous rateNonnegative
      have remainder := Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index))
        (Arithmetic.sq_nonneg_direct (rate - 1))
      have first : 1 + ((index + 1 : Nat) : Fraction.Rational) * (rate - 1) ≤
          (1 + (index : Fraction.Rational) * (rate - 1)) * rate := by
        apply Arithmetic.le_of_sub_nonneg_direct
        exact remainder.trans_eq (by rewrite [Purelib.Algebra.NatCast.add]; ring1)
      exact first.trans (scaled.trans_eq (pow_succ rate index).symm)

/-- Every nonnegative rate has an explicit finite reciprocal linear power bound. -/
public theorem power_linear_upper {rate : Fraction.Rational} (nonnegative : 0 ≤ rate)
    (index : Nat) : rate ^ index * (1 + (index : Fraction.Rational) * (1 - rate)) ≤ 1 := by
  induction index with
  | zero =>
      rewrite [Nat.cast_zero, zero_mul, add_zero, pow_zero, one_mul]
      exact le_rfl
  | succ index previous =>
      have remainder := Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (index + 1)))
        (Arithmetic.sq_nonneg_direct (1 - rate))
      have first : rate * (1 + ((index + 1 : Nat) : Fraction.Rational) * (1 - rate)) ≤
          1 + (index : Fraction.Rational) * (1 - rate) := by
        apply Arithmetic.le_of_sub_nonneg_direct
        exact remainder.trans_eq (by rewrite [Purelib.Algebra.NatCast.add]; ring1)
      have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct first
        (Arithmetic.pow_nonneg_direct nonnegative index)
      calc
        _ = rate ^ index * (rate * (1 + ((index + 1 : Nat) : Fraction.Rational) * (1 - rate))) := by
          rewrite [pow_succ]
          ring1
        _ ≤ rate ^ index * (1 + (index : Fraction.Rational) * (1 - rate)) := scaled
        _ ≤ 1 := previous

/-- Compute a finite block length that contracts a rational rate below the original two-thirds rate. -/
@[expose] public def rateBlock (rate : Fraction.Rational) : Nat :=
  Floor.ceilNat (1 / (2 * (1 - rate)))

/-- The computed original ceiling makes one rate block at most two thirds. -/
public theorem rateBlock_sufficient {rate : Fraction.Rational} (nonnegative : 0 ≤ rate) (lessOne : rate < 1) :
    rate ^ rateBlock rate ≤ 2 / 3 := by
  have gapPositive := Arithmetic.sub_pos_direct lessOne
  have denominatorPositive := Arithmetic.mul_pos_direct (by decide : (0 : Fraction.Rational) < 2) gapPositive
  have ratioPositive := Field.div_pos_direct (by decide : (0 : Fraction.Rational) < 1) denominatorPositive
  have ceiling : 1 / (2 * (1 - rate)) ≤ (rateBlock rate : Fraction.Rational) :=
    Floor.le_natCast_ceilNat_of_nonneg ratioPositive.le
  have multiplied := (Field.div_le_iff_pos denominatorPositive).mp ceiling
  have halfScaled := Arithmetic.mul_le_mul_of_nonneg_right_direct multiplied
    (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
  have half : (1 / 2 : Fraction.Rational) ≤ (rateBlock rate : Fraction.Rational) * (1 - rate) := by
    exact (show (1 / 2 : Fraction.Rational) = 1 * (1 / 2) by decide +kernel).trans_le
      (halfScaled.trans_eq (by
        calc
          _ = ((rateBlock rate : Fraction.Rational) * (1 - rate)) * (2 * (1 / 2)) := by ring1
          _ = _ := by
            rewrite [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide +kernel]
            exact Fraction.Field.mul_one_direct _))
  have factor : (3 / 2 : Fraction.Rational) ≤ 1 + (rateBlock rate : Fraction.Rational) * (1 - rate) := by
    have translated := Arithmetic.add_le_add_direct (by decide : (1 : Fraction.Rational) ≤ 1) half
    exact (show (3 / 2 : Fraction.Rational) = 1 + 1 / 2 by decide +kernel).trans_le translated
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct factor
    (Arithmetic.pow_nonneg_direct nonnegative (rateBlock rate))
  have terminal := scaled.trans (power_linear_upper nonnegative (rateBlock rate))
  exact ((Field.le_div_iff_pos (by decide : (0 : Fraction.Rational) < 3 / 2)).mpr terminal).trans_eq
    (by decide +kernel : (1 : Fraction.Rational) / (3 / 2) = 2 / 3)

/-- Compute a sufficient finite depth for any rational rate by the same original bounded contraction search. -/
@[expose] public def rateDepth (rate width epsilon : Fraction.Rational) : Nat :=
  rateBlock rate * geometricDepth width epsilon

/-- The computed generic-rate depth reduces the original nonnegative width below its positive request. -/
public theorem rateDepth_sufficient {rate width epsilon : Fraction.Rational}
    (nonnegative : 0 ≤ rate) (lessOne : rate < 1) (widthNonnegative : 0 ≤ width) (epsilonPositive : 0 < epsilon) :
    rate ^ rateDepth rate width epsilon * width ≤ epsilon := by
  unfold rateDepth
  rewrite [pow_mul]
  have blockNonnegative := Arithmetic.pow_nonneg_direct nonnegative (rateBlock rate)
  have blocks := Arithmetic.pow_le_pow_direct blockNonnegative
    (rateBlock_sufficient nonnegative lessOne) (geometricDepth width epsilon)
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct blocks widthNonnegative).trans
    (geometricDepth_sufficient widthNonnegative epsilonPositive)

/-- Every later finite index satisfies the same original generic-rate request. -/
public theorem rateDepth_tail {rate width epsilon : Fraction.Rational}
    (nonnegative : 0 ≤ rate) (lessOne : rate < 1) (widthNonnegative : 0 ≤ width) (epsilonPositive : 0 < epsilon)
    (index : Nat) (later : rateDepth rate width epsilon ≤ index) : rate ^ index * width ≤ epsilon :=
  (Arithmetic.mul_le_mul_of_nonneg_right_direct (power_antitone nonnegative lessOne.le later) widthNonnegative).trans
    (rateDepth_sufficient nonnegative lessOne widthNonnegative epsilonPositive)

end Purelib.Approximation.Rational.Contraction
