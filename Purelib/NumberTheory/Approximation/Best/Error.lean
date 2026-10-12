module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Pair.Basis
public import Purelib.Data.GaussianInt.Pair.LinearCombination

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite approximation algebra for Hurwitz convergents

This module isolates the calculation underlying a second-kind approximation
comparison.  The error of `p/q` is represented without division as `qz-p`.
Adjacent finite continuants have determinant `1` or `-1`, so every displayed
Gaussian-integer competitor has explicit coefficients in that adjacent
continuant basis.  No enumeration of Gaussian rationals is used.
-/

namespace Purelib.NumberTheory.Approximation.Best.Error

/-- Division-free error of the displayed pair `p/q` at `source`: `qz-p`. -/
def error (source : Gaussian.Basic.Canonical) (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : Gaussian.Basic.Canonical :=
  source * GaussianInt.toGaussian pair.denominator - GaussianInt.toGaussian pair.numerator

open Purelib.NumberTheory.Approximation
/-- A competitor-wise second-kind comparison.  Keeping the competitor as an
explicit argument makes each use a finite, checkable statement. -/
def AtLeastAsGoodAs (source : Gaussian.Basic.Canonical)
    (convergent competitor : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (error source convergent) ≤ Data.Gaussian.Norm.Basic.normSq
    (error source competitor)

/-- The competitor error is the same explicit integral combination of the
two adjacent convergent errors.  This is the algebraic reduction used by the
Lakein comparison; the remaining work is the finite Hurwitz-square geometry
that bounds this combination. -/
theorem competitor_error_decomposition
    (source : Gaussian.Basic.Canonical) {current previous competitor : GaussianInt.Pair.Basic.ConvergentPair}
    (unitDeterminant : GaussianInt.Pair.Basis.HasUnitDeterminant current previous) :
    error source competitor =
      GaussianInt.toGaussian (GaussianInt.Pair.Basis.currentCoefficient current previous competitor) *
          error source current +
        GaussianInt.toGaussian (GaussianInt.Pair.Basis.previousCoefficient current previous competitor) *
          error source previous := by
  have numerator := GaussianInt.Pair.Basis.competitor_numerator_decomposition
    (competitor := competitor) unitDeterminant
  have denominator := GaussianInt.Pair.Basis.competitor_denominator_decomposition
    (competitor := competitor) unitDeterminant
  unfold error
  rw [← numerator, ← denominator]
  simp only [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1
end Purelib.NumberTheory.Approximation.Best.Error

end

end

section
@[expose] public section

/-!
# Finite best Gaussian-rational approximations

Chevallier's lattice formulation uses two coordinate sizes: the error
`|qz-p|` and the denominator `|q|`.  This file states the same comparison
without square roots and without a completed complex carrier.  A lattice
vector is represented by its displayed Gaussian-integer pair `(p,q)`, its
first coordinate is the division-free rational error `qz-p`, and its second
coordinate is the displayed denominator `q`.

The main theorem proves directly that the two-tier best-approximation
predicate is equivalent to minimality in the corresponding closed cylinder.
All quantifiers range over supplied finite Gaussian-integer records; no
lattice completion, global enumeration, or choice principle is used.
-/

namespace Purelib.NumberTheory.Approximation.Best.Error

open Purelib.NumberTheory.Approximation in
/-- Squared first-coordinate size of the source-lattice vector represented by
`(p,q)`: the quadrance of `qz-p`. -/
def errorQuadrance (source : Gaussian.Basic.Canonical) (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (error source pair)

/-- Squared second-coordinate size of a displayed source-lattice vector. -/
def denominatorQuadrance (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : Nat :=
  GaussianInt.normNat pair.denominator

section
open Purelib.NumberTheory.Approximation
/-- The two displayed coordinates of the source-lattice vector represented
by `(p,q)`. -/
def sourceVector (source : Gaussian.Basic.Canonical) (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical :=
  (error source pair, GaussianInt.toGaussian pair.denominator)

/-- The coefficient representation of a source-lattice vector is injective:
its second coordinate recovers `q`, and its first then recovers `p`. -/
theorem sourceVector_injective (source : Gaussian.Basic.Canonical)
  :
    Function.Injective (sourceVector source) := by
  intro left right vectorEqual
  have errorEqual : error source left = error source right :=
    congrArg Prod.fst vectorEqual
  have denominatorGaussianEqual :
      GaussianInt.toGaussian left.denominator = GaussianInt.toGaussian right.denominator :=
    congrArg Prod.snd vectorEqual
  have denominatorEqual : left.denominator = right.denominator :=
    GaussianInt.toGaussian_injective
      denominatorGaussianEqual
  have numeratorGaussianEqual :
      GaussianInt.toGaussian left.numerator = GaussianInt.toGaussian right.numerator := by
    calc
      GaussianInt.toGaussian left.numerator =
          source * GaussianInt.toGaussian left.denominator - error source left := by
        unfold error
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im] <;>
          ring1
      _ = source * GaussianInt.toGaussian right.denominator - error source right := by
        rw [denominatorGaussianEqual, errorEqual]
      _ = GaussianInt.toGaussian right.numerator := by
        unfold error
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im] <;>
          ring1
  have numeratorEqual : left.numerator = right.numerator :=
    GaussianInt.toGaussian_injective
      numeratorGaussianEqual
  cases left
  cases right
  cases numeratorEqual
  cases denominatorEqual
  rfl

/-- The zero coefficient pair gives the zero source-lattice vector. -/
@[simp] theorem sourceVector_zeroPair (source :
  Gaussian.Basic.Canonical) :
    sourceVector source GaussianInt.Pair.LinearCombination.zeroPair = (0, 0) := by
  apply Prod.ext
  · change error source GaussianInt.Pair.LinearCombination.zeroPair = 0
    rw [error, GaussianInt.Pair.LinearCombination.zeroPair, GaussianInt.toGaussian_zero,
      Gaussian.Basic.mul_zero,
      Gaussian.Basic.sub_self]
  · rfl

/-- The coefficientwise nonzero test agrees exactly with nonzeroness of the
displayed source-lattice vector. -/
theorem pairNonzero_iff_sourceVector_ne_zero
    (source : Gaussian.Basic.Canonical) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    GaussianInt.Pair.LinearCombination.PairNonzero pair ↔ sourceVector source pair ≠ (0, 0) := by
  constructor
  · intro pairNonzero vectorZero
    apply (GaussianInt.Pair.LinearCombination.pairNonzero_iff_ne_zeroPair pair).mp pairNonzero
    apply sourceVector_injective source
    rw [sourceVector_zeroPair]
    exact vectorZero
  · intro vectorNonzero
    apply (GaussianInt.Pair.LinearCombination.pairNonzero_iff_ne_zeroPair pair).mpr
    intro pairZero
    subst pair
    exact vectorNonzero (sourceVector_zeroPair source)

/-- The coefficient determinant is also the cross difference of the two
division-free errors. -/
theorem toGaussian_coefficientDeterminant
    (source : Gaussian.Basic.Canonical) (left right : GaussianInt.Pair.Basic.ConvergentPair) :
    GaussianInt.toGaussian (GaussianInt.Pair.LinearCombination.coefficientDeterminant left right) =
      GaussianInt.toGaussian left.denominator * error source right -
        GaussianInt.toGaussian right.denominator * error source left := by
  unfold GaussianInt.Pair.LinearCombination.coefficientDeterminant GaussianInt.Pair.Basis.determinant error
  simp only [GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- Scaling both pair coefficients scales its division-free error by the embedded Gaussian integer. -/
theorem error_scalePair
    (source : Gaussian.Basic.Canonical) (coefficient : GaussianInt) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    error source (GaussianInt.Pair.LinearCombination.scalePair coefficient pair) =
      GaussianInt.toGaussian coefficient * error source pair := by
  unfold GaussianInt.Pair.LinearCombination.scalePair error
  simp only [GaussianInt.toGaussian_mul]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- Scaling a pair multiplies its error quadrance by the coefficient norm. -/
theorem errorQuadrance_scalePair
    (source : Gaussian.Basic.Canonical) (coefficient : GaussianInt) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    errorQuadrance source (GaussianInt.Pair.LinearCombination.scalePair coefficient pair) =
      (GaussianInt.normNat coefficient : Fraction.Rational) * errorQuadrance source pair := by
  rw [errorQuadrance, error_scalePair, Gaussian.Norm.Basic.normSq_mul,
    GaussianInt.normSq_toGaussian]
  rfl

/-- Scaling a pair multiplies its denominator quadrance by the coefficient norm. -/
theorem denominatorQuadrance_scalePair
    (coefficient : GaussianInt) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    denominatorQuadrance (GaussianInt.Pair.LinearCombination.scalePair coefficient pair) =
      GaussianInt.normNat coefficient * denominatorQuadrance pair := by
  exact GaussianInt.normNat_mul _ _

/-- Division-free error preserves Gaussian-integer linear combinations of coefficient pairs. -/
theorem error_linearCombination
    (source : Gaussian.Basic.Canonical) (left right : GaussianInt.Pair.Basic.ConvergentPair)
    (leftCoefficient rightCoefficient : GaussianInt) :
    error source
        (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) =
      GaussianInt.toGaussian leftCoefficient * error source left +
        GaussianInt.toGaussian rightCoefficient * error source right := by
  unfold GaussianInt.Pair.LinearCombination.linearCombination error
  simp only [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;>
    ring1

/-- Coordinate identity for the centered unit combination's error. -/
theorem error_linearCombination_negUnit_one
    (source : Gaussian.Basic.Canonical) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) (unit : GaussianInt) :
    error source (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) =
      error source upper - GaussianInt.toGaussian unit * error source lower := by
  rw [error_linearCombination]
  apply Gaussian.Basic.ext <;>
    simp only [GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one,
      Gaussian.Basic.neg_re,
      Gaussian.Basic.neg_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im] <;>
    ring1

end

/-- Coordinate identity for the centered unit combination's denominator. -/
theorem toGaussian_denominator_linearCombination_negUnit_one
    (lower upper : GaussianInt.Pair.Basic.ConvergentPair) (unit : GaussianInt) :
    GaussianInt.toGaussian (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1).denominator =
      GaussianInt.toGaussian upper.denominator -
        GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator := by
  apply Gaussian.Basic.ext <;>
    simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.toGaussian_add,
      GaussianInt.toGaussian_mul,
      GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one,
      Gaussian.Basic.neg_re,
      Gaussian.Basic.neg_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im] <;>
    ring1
end Purelib.NumberTheory.Approximation.Best.Error

end
