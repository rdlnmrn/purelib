module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.NumberTheory.Approximation.Best.Search
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

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

namespace Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

/-- Squared Dirichlet product attached to one consecutive pair.

Multiply the directly read upper denominator quadrance by the lower pair's
error quadrance, retaining the same source and both original pairs. -/
def dirichletWindowQuadrance
    (source : Gaussian.Basic.Canonical) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) : Fraction.Rational :=
  Fraction.Cast.fromInt (Best.Error.denominatorQuadrance upper : Int) * Best.Error.errorQuadrance source lower

/-- The direct product equals the expression using the original natural denominator cast. -/
theorem dirichletWindowQuadrance_eq_cast
    (source : Gaussian.Basic.Canonical) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) :
    dirichletWindowQuadrance source lower upper =
      (Best.Error.denominatorQuadrance upper : Fraction.Rational) * Best.Error.errorQuadrance source lower :=
  congrArg (fun scale => scale * Best.Error.errorQuadrance source lower)
    (Fraction.Cast.natCast_eq_fromInt _).symm

/-- The determinant quadrance of a consecutive pair is strictly less than
four times its squared Dirichlet-window product.  This is a wholly finite
reverse bound: the product cannot collapse toward zero while the displayed
coefficient determinant remains nonzero. -/
theorem
  AreConsecutiveBest.coefficientIndexQuadrance_lt_four_mul_dirichletWindow
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source lower upper) :
    (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) <
      4 * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source lower upper := by
  have denominatorOrdered :
      (Best.Error.denominatorQuadrance lower : Fraction.Rational) <
        (Best.Error.denominatorQuadrance upper : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct consecutive.2.2.1
  have errorOrdered :
      Best.Error.errorQuadrance source upper < Best.Error.errorQuadrance source lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  have upperDenominatorPositive :
      (0 : Fraction.Rational) < (Best.Error.denominatorQuadrance upper : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos consecutive.2.1.1)
  have crossProductStrict :
      (Best.Error.denominatorQuadrance lower : Fraction.Rational) *
          Best.Error.errorQuadrance source upper <
        (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
          Best.Error.errorQuadrance source lower := by
    calc
      (Best.Error.denominatorQuadrance lower : Fraction.Rational) *
            Best.Error.errorQuadrance source upper ≤
          (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source upper :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          denominatorOrdered.le (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source upper))
      _ < (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source lower :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          upperDenominatorPositive errorOrdered
  have sumStrict :
      (Best.Error.denominatorQuadrance lower : Fraction.Rational) *
            Best.Error.errorQuadrance source upper +
          (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source lower <
        (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source lower +
          (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source lower :=
    by
      exact Fraction.Order.Arithmetic.add_lt_add_right_direct
        crossProductStrict
        ((Best.Error.denominatorQuadrance upper : Fraction.Rational) *
          Best.Error.errorQuadrance source lower)
  have scaledStrict :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 2 by decide) sumStrict
  calc
    (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) =
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian
          (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper)) := by
      rw [GaussianInt.normSq_toGaussian]
      rfl
    _ = Data.Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian lower.denominator * Best.Error.error source upper -
          GaussianInt.toGaussian upper.denominator * Best.Error.error source lower) := by
      rw [Best.Error.toGaussian_coefficientDeterminant]
    _ ≤ 2 *
        (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian lower.denominator * Best.Error.error source upper)
          +
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator * Best.Error.error source
            lower)) :=
      Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ = 2 *
        ((Best.Error.denominatorQuadrance lower : Fraction.Rational) *
            Best.Error.errorQuadrance source upper +
          (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) := by
      rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian,
        GaussianInt.normSq_toGaussian]
      rfl
    _ < 2 *
        ((Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source lower +
          (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) := scaledStrict
    _ = 4 * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source lower upper := by
      rewrite [dirichletWindowQuadrance_eq_cast]
      ring1

/-- Every consecutive window has squared Dirichlet product strictly greater
than one quarter, stated without division. -/
theorem
  AreConsecutiveBest.one_lt_four_mul_dirichletWindow
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source lower upper) :
    (1 : Fraction.Rational) < 4 * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source lower upper := by
  have determinantPositive := consecutive.coefficientIndexQuadrance_pos
  have oneLeDeterminant : 1 ≤ GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper := by
    omega
  exact (Fraction.Cast.Order.natCast_le_direct oneLeDeterminant).trans_lt
    (Dirichlet.Window.SourceBound.AreConsecutiveBest.coefficientIndexQuadrance_lt_four_mul_dirichletWindow consecutive)

/-- In the index-two case the same determinant calculation strengthens the
universal lower bound from one quarter to one half, again without division. -/
theorem
  AreConsecutiveBest.two_lt_four_mul_dirichletWindow_of_indexTwo
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    (2 : Fraction.Rational) < 4 * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source lower upper := by
  calc
    (2 : Fraction.Rational) =
        (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := by
      simpa using congrArg (fun value : Nat => (value : Fraction.Rational))
        indexTwo.symm
    _ < 4 * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source lower upper :=
      (Dirichlet.Window.SourceBound.AreConsecutiveBest.coefficientIndexQuadrance_lt_four_mul_dirichletWindow
        consecutive)

/-- Throughout the natural-height window between two consecutive best levels,
the lower pair is an admissible approximation and its scaled error is bounded
by the displayed endpoint product.  This is the finite square-root-free form
of the consecutive-product expression for a Dirichlet constant. -/
theorem
  AreConsecutiveBest.lower_witnesses_dirichletWindow
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source lower upper)
    (request : Nat)
    (aboveLower : Best.Error.denominatorQuadrance lower < request)
    (noHigherThanUpper : request ≤ Best.Error.denominatorQuadrance upper) :
    lower.denominator ≠ 0 ∧
      Best.Error.denominatorQuadrance lower < request ∧
      (request : Fraction.Rational) * Best.Error.errorQuadrance source lower ≤
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source lower upper := by
  refine ⟨consecutive.1.1, aboveLower, ?_⟩
  rewrite [dirichletWindowQuadrance_eq_cast]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Cast.Order.natCast_le_direct noHigherThanUpper)
    (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source lower))

/-- Every finite consecutive window for a displayed rational source has a
source-computed Dirichlet-product bound. -/
theorem
  AreConsecutiveBest.dirichletWindowQuadrance_le_sourceBound
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      (GaussianInt.normNat source.denominator : Fraction.Rational) / 2 := by
  have denominatorBound :
      (Best.Error.denominatorQuadrance upper : Fraction.Rational) ≤
        (GaussianInt.normNat source.denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct
      (Best.Search.IsBest.denominatorQuadrance_le_source consecutive.2.1)
  have sourceDenominatorNonnegative :
      (0 : Fraction.Rational) ≤ (GaussianInt.normNat source.denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper =
        (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
          Best.Error.errorQuadrance source.value lower := dirichletWindowQuadrance_eq_cast _ _ _
    _ ≤ (GaussianInt.normNat source.denominator : Fraction.Rational) * (1 / 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_direct denominatorBound
        consecutive.1.errorQuadrance_le_half
        (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source.value lower))
        sourceDenominatorNonnegative
    _ = (GaussianInt.normNat source.denominator : Fraction.Rational) / 2 := by
      change
        (GaussianInt.normNat source.denominator : Fraction.Rational) *
            (1 * (2 : Fraction.Rational)⁻¹) =
          (GaussianInt.normNat source.denominator : Fraction.Rational) * (2 : Fraction.Rational)⁻¹
      rw [Fraction.Field.one_mul]
end Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

end
