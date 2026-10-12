module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Bounds.Fraction
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
public import Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Sequence
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Law

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Approximation.Gaussian.Exponential.Horner.Addition
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

/-- Constructive, finite-request exponential addition law on the rational unit disk. Given any two current indices and
any positive rational squared tolerance, this program computes synchronized later indices after which every pair of
displayed samples satisfies that tolerance. -/
@[expose] public def exp_add_equivalent {x y : Data.Gaussian.Basic.Canonical}
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
    (sumUnit : Data.Gaussian.Norm.Basic.normSq (x + y) ≤ 1) :
    Gaussian.Equivalence.Equivalent
      (Sequence.expProductApproximation x y xUnit yUnit)
      (Sequence.approximation (x + y) sumUnit) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let start := max leftStart rightStart
    let index := Search.firstQuarterBelow
      Sequence.expProductErrorScale start smallTarget
    let synchronized := 2 * index + 1
    have indexGe : start ≤ index :=
      Search.firstQuarterBelow_ge
        Sequence.expProductErrorScale start smallTarget
    have synchronizedGeIndex : index ≤ synchronized := by
      dsimp only [synchronized]
      omega
    have masterSmall :
        Geometric.Basic.quarterRadius
          Sequence.expProductErrorScale index <
          smallTarget :=
      Search.firstQuarterBelow_accurate
        Sequence.expProductErrorScale Sequence.expProductErrorScale_nonneg
          start smallTarget smallPositive
    exact
      { leftIndex := synchronized
        rightIndex := synchronized
        left_ge := (Purelib.Data.Nat.Order.le_max_left _ _).trans
          (indexGe.trans synchronizedGeIndex)
        right_ge := (Purelib.Data.Nat.Order.le_max_right _ _).trans
          (indexGe.trans synchronizedGeIndex)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have productTailLe :=
            (Sequence.expProductApproximation x y xUnit yUnit).later_close leftOrder
          have productRadiusLe :
              Geometric.Basic.quarterRadius
                  Sequence.expProductErrorScale synchronized ≤
                Geometric.Basic.quarterRadius
                  Sequence.expProductErrorScale index :=
            quarterRadius_antitone
              Sequence.expProductErrorScale_nonneg
              synchronizedGeIndex
          have productTail :
              Data.Gaussian.Norm.Basic.normSq
                  (Sequence.expProductSample x y leftLater -
                    Sequence.expProductSample x y synchronized) < smallTarget :=
            productTailLe.trans_lt (productRadiusLe.trans_lt masterSmall)
          have directLe := Sequence.expProductSample_addition_error_odd
            xUnit yUnit index
          have directScaleLe :
              Geometric.Basic.quarterRadius 16 index ≤
                Geometric.Basic.quarterRadius
                  Sequence.expProductErrorScale index :=
            Geometric.Basic.quarterRadius_scale_mono (by
              dsimp only [Sequence.expProductErrorScale]
              calc
                (16 : Fraction.Rational) ≤ 400 :=
                  Fraction.Cast.Order.natCast_le_direct (by decide)
                _ = 40 * 10 := by ring1) index
          have direct :
              Data.Gaussian.Norm.Basic.normSq
                  (Sequence.expProductSample x y synchronized -
                    Sample.sample (x + y) synchronized) <
                smallTarget :=
            directLe.trans_lt (directScaleLe.trans_lt masterSmall)
          have sumTailForward :=
            (Sequence.approximation (x + y) sumUnit).later_close
              rightOrder
          have sumRadiusLe :
              Geometric.Basic.quarterRadius 10 synchronized ≤
                Geometric.Basic.quarterRadius
                  Sequence.expProductErrorScale index :=
            (Geometric.Basic.quarterRadius_scale_mono (by
              dsimp only [Sequence.expProductErrorScale]
              calc
                (10 : Fraction.Rational) ≤ 400 :=
                  Fraction.Cast.Order.natCast_le_direct (by decide)
                _ = 40 * 10 := by ring1) synchronized).trans
              productRadiusLe
          have sumTailReverse :
              Data.Gaussian.Norm.Basic.normSq
                  (Sample.sample (x + y) synchronized -
                    Sample.sample (x + y) rightLater) <
                smallTarget := by
            have reverseIdentity :
                Sample.sample (x + y) synchronized -
                    Sample.sample (x + y) rightLater =
                  -(Sample.sample (x + y) rightLater -
                    Sample.sample (x + y) synchronized) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [reverseIdentity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact sumTailForward.trans_lt (sumRadiusLe.trans_lt masterSmall)
          have middle :
              Data.Gaussian.Norm.Basic.normSq
                  (Sequence.expProductSample x y synchronized -
                    Sample.sample (x + y) rightLater) <
                2 * (smallTarget + smallTarget) := by
            exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
              (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  direct sumTailReverse))
          calc
            Data.Gaussian.Norm.Basic.normSq
                (Sequence.expProductSample x y leftLater -
                  Sample.sample (x + y) rightLater) ≤
              2 * (Data.Gaussian.Norm.Basic.normSq
                    (Sequence.expProductSample x y leftLater -
                      Sequence.expProductSample x y synchronized) +
                Data.Gaussian.Norm.Basic.normSq
                    (Sequence.expProductSample x y synchronized -
                      Sample.sample (x + y) rightLater)) :=
                Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ < 2 * (smallTarget + 2 * (smallTarget + smallTarget)) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  productTail middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact Purelib.Data.Rat.Bounds.Fraction.ten_sixteenths_lt positive
      }

/-- The pointwise product side of the local exponential addition law exposed through the ordinary productive CCL
controller. -/
@[expose] public def expProductNamed (x y : Data.Gaussian.Basic.Canonical)
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1) :
    Gaussian.Name.Basic.Named :=
  (Sequence.expProductApproximation x y xUnit yUnit).toNamed

/-- The direct `exp(x+y)` side of the local addition law exposed through the ordinary productive CCL controller. -/
@[expose] public def expSumNamed (x y : Data.Gaussian.Basic.Canonical) (sumUnit :
  Data.Gaussian.Norm.Basic.normSq (x + y) ≤ 1) :
    Gaussian.Name.Basic.Named :=
  (Sequence.approximation (x + y) sumUnit).toNamed

/-- CCL-name form of the constructive local exponential addition law. Both sides emit arbitrary finite ordinary CCL
prefixes, and their canonical finite sampling paths are operationally equivalent at every positive rational squared
tolerance. -/
@[expose] public def exp_add_named_equivalent {x y : Data.Gaussian.Basic.Canonical}
    (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1)
    (sumUnit : Data.Gaussian.Norm.Basic.normSq (x + y) ≤ 1) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.Exponential.Horner.Addition.Law.expProductNamed x y xUnit yUnit)
      (Approximation.Gaussian.Exponential.Horner.Addition.Law.expSumNamed x y sumUnit) :=
  Equivalent.trans
    (Equivalent.toNamed_sampling
      (Sequence.expProductApproximation x y xUnit yUnit))
    (Equivalent.trans
      (Approximation.Gaussian.Exponential.Horner.Addition.Law.exp_add_equivalent xUnit yUnit sumUnit)
      (Equivalent.symm
        (Equivalent.toNamed_sampling
          (Sequence.approximation (x + y) sumUnit))))
end Purelib.Approximation.Gaussian.Exponential.Horner.Addition.Law

end
