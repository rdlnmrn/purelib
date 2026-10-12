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
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Semiring.Normalization
import Purelib.Tactic.Ring

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
        Fraction.Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            depthNonnegative halfNonnegative)
          halfNonnegative
      have ratioNonnegative : (0 : Fraction.Rational) ≤ 3 / 2 := by decide
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          inductionHypothesis ratioNonnegative
      calc
        (1 : Fraction.Rational) + (Nat.succ depth : Fraction.Rational) * (1 / 2) ≤
            (1 + (depth : Fraction.Rational) * (1 / 2)) * (3 / 2) := by
          apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
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
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        widthNonnegative)
      (Fraction.Order.Field.inv_pos_direct epsilonPositive).le
  have ceiling : 2 * width / epsilon ≤ (depth : Fraction.Rational) := by
    exact Floor.le_natCast_ceilNat_of_nonneg
      ratioNonnegative
  have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := by decide
  have halfScaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
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
      (Fraction.Order.Field.div_le_iff_pos epsilonPositive).mp ratioPower
    simpa only [Fraction.Field.mul_comm] using divided
  have contractionNonnegative :
      0 ≤ (2 / 3 : Fraction.Rational) ^ depth :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth
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
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
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
  exact Purelib.Approximation.Rational.Contraction.geometricDepthSearch_sufficient _
    (geometricDepthBound_sufficient widthNonnegative epsilonPositive)

end Purelib.Approximation.Rational.Contraction
