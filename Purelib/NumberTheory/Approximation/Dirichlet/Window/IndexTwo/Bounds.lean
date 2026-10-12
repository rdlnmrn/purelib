module
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Monoid.Int
import Purelib.Algebra.NatCast
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.SignedFraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Data.Rat.SignedFraction.Order
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.RepeatedIndex
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.NormalForm
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
public section

open Purelib.Algebra
attribute [local instance 2000] Group.Negation.subNegZeroMonoid

/-!
# Index-two Dirichlet-window geometry

The centered coefficient coset available when two consecutive best pairs have
determinant quadrance two supplies four explicit unit candidates.  The
opposite-unit alternatives force the real projections of the normalized error
and denominator ratios to have opposite signs, while their imaginary
projections have the same sign.  This file turns those finite alternatives
into the rational gap bound needed for a substantially smaller window
constant.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds

/-- The two complementary products of the normalized error and denominator
quadrances. -/
@[expose] def balancedNormProduct (errorRatio denominatorRatio : Gaussian.Basic.Canonical) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq errorRatio * Data.Gaussian.Norm.Basic.normSq denominatorRatio +
    (1 - Data.Gaussian.Norm.Basic.normSq errorRatio) * (1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio)

/-- The signed-fraction presentation of the centered norm threshold 15/56. -/
private def centeredNormThresholdFraction :
    Data.Rat.SignedFraction :=
  { num := 15, den := 56, den_pos := by decide }

/-- The displayed rational point `15/56`, chosen just below
`2 - sqrt(3)` without introducing that completed value. -/
@[expose] def centeredNormThreshold : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 15, den := 56, den_pos := by decide }

/-- The signed-fraction presentation of the centered determinant-gap threshold 71/56. -/
private def centeredGapThresholdFraction :
    Data.Rat.SignedFraction :=
  { num := 71, den := 56, den_pos := by decide }

/-- The resulting displayed determinant-gap threshold `71/56`. -/
@[expose] def centeredGapThreshold : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 71, den := 56, den_pos := by decide }

/-- The signed-fraction presentation of the centered squared-window bound 112/71. -/
private def centeredWindowBoundFraction :
    Data.Rat.SignedFraction :=
  { num := 112, den := 71, den_pos := by decide }

/-- The index-two window bound `112/71` obtained by dividing the exact
coefficient index two by `71/56`. -/
@[expose] def centeredWindowBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 112, den := 71, den_pos := by decide }

/-- The signed-fraction presentation of the dyadic centered gap 205/128. -/
private def dyadicCenteredGapThresholdFraction :
    Data.Rat.SignedFraction :=
  { num := 13 * 16 - 3, den := 2 ^ 7, den_pos := by decide }

/-- The strengthened index-two gap `205/128`.  Its reciprocal index factor
matches the dyadic index-one window without naming the optimal algebraic
boundary. -/
@[expose] def dyadicCenteredGapThreshold : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 13 * 16 - 3, den := 2 ^ 7, den_pos := by decide }

/-- The signed-fraction presentation of the dyadic centered squared-window bound 256/205. -/
private def dyadicCenteredWindowBoundFraction :
    Data.Rat.SignedFraction :=
  { num := 2 ^ 8, den := 13 * 16 - 3, den_pos := by decide }

/-- The corresponding index-two squared-window bound `256/205`. -/
@[expose] def dyadicCenteredWindowBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 2 ^ 8, den := 13 * 16 - 3, den_pos := by decide }

/-- The signed-fraction presentation of the dyadic excess 77/128 above one. -/
private def dyadicCenteredExcessThresholdFraction :
    Data.Rat.SignedFraction :=
  { num := 9 * 8 + 5, den := 2 ^ 7, den_pos := by decide }

/-- The amount `77/128` by which the strengthened gap exceeds one. -/
@[expose] def dyadicCenteredExcessThreshold : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    { num := 9 * 8 + 5, den := 2 ^ 7, den_pos := by decide }

/-- The dyadic centered gap is one plus its displayed excess threshold. -/
theorem dyadicCenteredGapThreshold_eq_one_add_excess :
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold = 1 +
      Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold := by
  unfold Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold
  rw [show (1 : Fraction.Rational) =
        Data.Rat.SignedFraction.Normalization.ofFraction ⟨1, 1, by decide⟩ from
      Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 1,
    Data.Rat.SignedFraction.Arithmetic.ofFraction_addFraction]
  apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
  change
    ((13 * 16 - 3 : Nat) : Int) *
        (1 * ((2 ^ 7 : Nat) : Int)) =
      (1 * ((2 ^ 7 : Nat) : Int) +
          ((9 * 8 + 5 : Nat) : Int) * 1) *
        ((2 ^ 7 : Nat) : Int)
  decide

/-- The dyadic squared-window bound multiplied by its gap threshold is the coefficient index two. -/
theorem dyadicCenteredWindowBound_mul_gapThreshold :
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredWindowBound *
      Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold = 2 := by
  unfold Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredWindowBound
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold
  rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction]
  calc
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨2, 1, by decide⟩ := by
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change
        (((2 ^ 8 : Nat) : Int) * ((13 * 16 - 3 : Nat) : Int)) * 1 =
          2 * (((13 * 16 - 3 : Nat) : Int) * ((2 ^ 7 : Nat) : Int))
      decide
    _ = 2 := (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 2).symm

/-- The dyadic centered determinant-gap threshold is strictly positive. -/
theorem dyadicCenteredGapThreshold_pos :
    (0 : Fraction.Rational) < Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold := by
  unfold Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold
  change
    Data.Rat.SignedFraction.Order.LessEqFraction
        Data.Rat.SignedFraction.Arithmetic.zeroFraction
        ⟨13 * 16 - 3, 2 ^ 7, by decide⟩ ∧
      ¬Data.Rat.SignedFraction.Order.LessEqFraction
        ⟨13 * 16 - 3, 2 ^ 7, by decide⟩
        Data.Rat.SignedFraction.Arithmetic.zeroFraction
  decide

/-- Multiplying the centered norm threshold by 56 recovers its numerator 15. -/
theorem centeredNormThreshold_mul_denominator :
    Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold * 56 = 15 := by
  unfold Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 15, den := 56, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Multiplying the centered gap threshold by 56 recovers its numerator 71. -/
theorem centeredGapThreshold_mul_denominator :
    Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold * 56 = 71 := by
  unfold Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 71, den := 56, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Multiplying the centered squared-window bound by 71 recovers its numerator 112. -/
theorem centeredWindowBound_mul_denominator :
    Dirichlet.Window.IndexTwo.Bounds.centeredWindowBound * 71 = 112 := by
  unfold Dirichlet.Window.IndexTwo.Bounds.centeredWindowBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 112, den := 71, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Distance quadrance at least two from the unit 1 bounds the complementary norm by minus twice the real coordinate. -/
private theorem error_one_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian (1 : GaussianInt))) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ -2 * value.re := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian (1 : GaussianInt)) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = (-2 * value.re) - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        GaussianInt.one_re,
        GaussianInt.one_im]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- Distance quadrance at least two from the unit -1 bounds the complementary norm by twice the real coordinate. -/
private theorem error_negOne_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian (-1 : GaussianInt))) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ 2 * value.re := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian (-1 : GaussianInt)) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = 2 * value.re - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        GaussianInt.neg_re,
        GaussianInt.neg_im,
        GaussianInt.one_re,
        GaussianInt.one_im,
         ]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- The denominator obstruction at unit 1 bounds the complementary norm by minus twice the real coordinate. -/
private theorem denominator_one_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (1 : GaussianInt) * value)) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ -2 * value.re := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (1 : GaussianInt) * value) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = (-2 * value.re) - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im,
        GaussianInt.one_re,
        GaussianInt.one_im]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- The denominator obstruction at unit -1 bounds the complementary norm by twice the real coordinate. -/
private theorem denominator_negOne_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (-1 : GaussianInt) * value)) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ 2 * value.re := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (-1 : GaussianInt) * value) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = 2 * value.re - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im,
        GaussianInt.neg_re,
        GaussianInt.neg_im,
        GaussianInt.one_re,
        GaussianInt.one_im,
         ]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- Distance quadrance at least two from i bounds the complementary norm by minus twice the imaginary coordinate. -/
private theorem error_imaginary_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
      (value - GaussianInt.toGaussian Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit)) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ -2 * value.im := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq
        (value - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = (-2 * value.im) - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, GaussianInt.Norm.Small.imaginaryUnit]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- Distance quadrance at least two from -i bounds the complementary norm by twice the imaginary coordinate. -/
private theorem error_negImaginary_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
      (value - GaussianInt.toGaussian (-Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit))) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ 2 * value.im := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq
        (value - GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit)) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = 2 * value.im - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, GaussianInt.Norm.Small.imaginaryUnit]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        GaussianInt.neg_re,
        GaussianInt.neg_im,
         ]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- The denominator obstruction at i bounds the complementary norm by twice the imaginary coordinate. -/
private theorem denominator_imaginary_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
      (1 - GaussianInt.toGaussian Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit * value)) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ 2 * value.im := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq
        (1 - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * value) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = 2 * value.im - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, GaussianInt.Norm.Small.imaginaryUnit]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- The denominator obstruction at -i bounds the complementary norm by minus twice the imaginary coordinate. -/
private theorem denominator_negImaginary_projection
    (value : Gaussian.Basic.Canonical)
    (outside : (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
      (1 - GaussianInt.toGaussian (-Purelib.Data.GaussianInt.Norm.Small.imaginaryUnit) * value)) :
    1 - Data.Gaussian.Norm.Basic.normSq value ≤ -2 * value.im := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Data.Gaussian.Norm.Basic.normSq
        (1 - GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) * value) - 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct outside
    _ = (-2 * value.im) - (1 - Data.Gaussian.Norm.Basic.normSq value) := by
      dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, GaussianInt.Norm.Small.imaginaryUnit]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im,
        GaussianInt.neg_re,
        GaussianInt.neg_im,
         ]
      simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1

/-- The four centered-unit alternatives cross in both coordinate directions.
The displayed disjunctions retain which error exterior is paired with which
denominator exterior; no selection from an unbounded set is involved. -/
private theorem centeredUnit_projectionCrosses
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    (((1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ -2 * errorRatio.re ∧
          1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ 2 * denominatorRatio.re) ∨
        (1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ -2 * denominatorRatio.re ∧
          1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ 2 * errorRatio.re)) ∧
      ((1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ -2 * errorRatio.im ∧
          1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ -2 * denominatorRatio.im) ∨
        (1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ 2 * denominatorRatio.im ∧
          1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ 2 * errorRatio.im))) := by
  have realCross := Best.Consecutive.RepeatedIndex.opposite_self_obstructions_cross
    errorRatio denominatorRatio errorInside denominatorInside 1 rfl
      (obstruction 1 rfl) (obstruction (-1) (by decide))
  have imaginaryCross :=
    Best.Consecutive.RepeatedIndex.opposite_self_obstructions_cross
      errorRatio denominatorRatio errorInside denominatorInside
        GaussianInt.Norm.Small.imaginaryUnit (by decide)
        (obstruction GaussianInt.Norm.Small.imaginaryUnit (by decide))
        (obstruction (-GaussianInt.Norm.Small.imaginaryUnit) (by decide))
  constructor
  · rcases realCross with cross | cross
    · exact Or.inl ⟨Dirichlet.Window.IndexTwo.Bounds.error_one_projection errorRatio cross.1,
        Dirichlet.Window.IndexTwo.Bounds.denominator_negOne_projection denominatorRatio cross.2⟩
    · exact Or.inr ⟨Dirichlet.Window.IndexTwo.Bounds.denominator_one_projection denominatorRatio cross.1,
        Dirichlet.Window.IndexTwo.Bounds.error_negOne_projection errorRatio cross.2⟩
  · rcases imaginaryCross with cross | cross
    · exact Or.inl ⟨Dirichlet.Window.IndexTwo.Bounds.error_imaginary_projection errorRatio cross.1,
        Dirichlet.Window.IndexTwo.Bounds.denominator_negImaginary_projection denominatorRatio cross.2⟩
    · exact Or.inr ⟨Dirichlet.Window.IndexTwo.Bounds.denominator_imaginary_projection denominatorRatio cross.1,
        Dirichlet.Window.IndexTwo.Bounds.error_negImaginary_projection errorRatio cross.2⟩

/-- Once the error ratio is in the closed first octant, the four centered
unit alternatives have a forced orientation.  The error ratio lies outside
the circle centred at `-i`, while the denominator ratio lies outside the
circles centred at `1` and `-i`; these are recorded only as rational
projection inequalities. -/
theorem firstOctant_projectionBounds_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ 2 * errorRatio.im ∧
      1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ -2 * denominatorRatio.re ∧
      1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ 2 * denominatorRatio.im := by
  have errorComplementPositive :
      (0 : Fraction.Rational) < 1 - Data.Gaussian.Norm.Basic.normSq errorRatio := by
    exact Fraction.Order.Arithmetic.sub_pos_direct errorInside
  obtain ⟨realCross, imaginaryCross⟩ := Dirichlet.Window.IndexTwo.Bounds.centeredUnit_projectionCrosses
    errorRatio denominatorRatio errorInside denominatorInside obstruction
  have denominatorReal :
      1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ -2 * denominatorRatio.re := by
    rcases realCross with cross | cross
    · have negativeNonpositive :
          -2 * errorRatio.re ≤ (0 : Fraction.Rational) := by
        have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
          realNonnegative
        calc
          -2 * errorRatio.re = 2 * (-errorRatio.re) := by ring1
          _ ≤ 2 * 0 :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              negated (by decide)
          _ = 0 := by ring1
      have complementNonpositive := cross.1.trans negativeNonpositive
      exact ((not_le_of_gt errorComplementPositive)
        complementNonpositive).elim
    · exact cross.1
  have imaginaryBounds :
      1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ 2 * errorRatio.im ∧
        1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ 2 * denominatorRatio.im := by
    rcases imaginaryCross with cross | cross
    · have negativeNonpositive :
          -2 * errorRatio.im ≤ (0 : Fraction.Rational) := by
        have negated := Fraction.Order.Arithmetic.neg_le_neg_direct
          imaginaryNonnegative
        calc
          -2 * errorRatio.im = 2 * (-errorRatio.im) := by ring1
          _ ≤ 2 * 0 :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              negated (by decide)
          _ = 0 := by ring1
      have complementNonpositive := cross.1.trans negativeNonpositive
      exact ((not_le_of_gt errorComplementPositive)
        complementNonpositive).elim
    · exact ⟨cross.2, cross.1⟩
  exact ⟨imaginaryBounds.1, denominatorReal, imaginaryBounds.2⟩

/-- A rational affine minorant for the larger coordinate of a normalized
first-quadrant vector.  The choice `2(X+1)/7` lies just below
`sqrt(X/2)` throughout the centered norm chamber. -/
@[expose] def centeredComponentLower (norm : Fraction.Rational) : Fraction.Rational :=
  2 * (norm + 1) / 7

/-- Algebraic form of the affine centered-component minorant. -/
theorem centeredComponentLower_eq (norm : Fraction.Rational) :
    Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower norm = (2 / 7) * (norm + 1) := by
  unfold Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct]
  calc
    (2 * (norm + 1)) * (7 : Fraction.Rational)⁻¹ =
        2 * ((norm + 1) * (7 : Fraction.Rational)⁻¹) :=
      Fraction.Field.mul_assoc _ _ _
    _ = 2 * ((7 : Fraction.Rational)⁻¹ * (norm + 1)) := by
      rw [Fraction.Field.mul_comm (norm + 1) _]
    _ = (2 * (7 : Fraction.Rational)⁻¹) * (norm + 1) :=
      (Fraction.Field.mul_assoc _ _ _).symm

/-- Division by two agrees with multiplication by the displayed half. -/
theorem div_two_eq_half_mul (value : Fraction.Rational) :
    value / 2 = (1 / 2) * value := by
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct]
  rw [Fraction.Field.one_mul]
  exact Fraction.Field.mul_comm _ _

/-- The centered affine coordinate minorant is nonnegative at every nonnegative norm. -/
private theorem centeredComponentLower_nonnegative
    (normNonnegative : (0 : Fraction.Rational) ≤ norm) :
    0 ≤ Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower norm := by
  unfold Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg normNonnegative (by decide)))
    (by decide)

/-- On `15/56 ≤ X ≤ 1`, the affine minorant has square at most `X/2`.
The proof uses the exact factorization of the difference from the lower
endpoint; it does not select a square root. -/
theorem centeredComponentLower_sq_le_half
    (norm : Fraction.Rational)
    (thresholdLe : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ norm)
    (normLeOne : norm ≤ 1) :
    Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower norm ^ 2 ≤ norm / 2 := by
  let threshold := Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
  have thresholdLeOne : threshold ≤ (1 : Fraction.Rational) := by
    dsimp only [threshold]
    unfold Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
    decide
  have normPlusThresholdPlusTwoLeFour :
      norm + threshold + 2 ≤ (4 : Fraction.Rational) := by
    have first := Fraction.Order.Arithmetic.add_le_add_direct
      normLeOne thresholdLeOne
    have second := Fraction.Order.Arithmetic.add_le_add_right_direct first 2
    calc
      norm + threshold + 2 ≤ (1 : Fraction.Rational) + 1 + 2 := second
      _ = 4 := by ring1
  have scaledLeHalf :
      (2 / 7 : Fraction.Rational) ^ 2 * (norm + threshold + 2) ≤ 1 / 2 := by
    calc
      (2 / 7 : Fraction.Rational) ^ 2 * (norm + threshold + 2) ≤
          (2 / 7) ^ 2 * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          normPlusThresholdPlusTwoLeFour
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ ≤ 1 / 2 := by decide
  have factorNonnegative :
      0 ≤ (1 / 2 : Fraction.Rational) -
        (2 / 7) ^ 2 * (norm + threshold + 2) :=
    Fraction.Order.Arithmetic.sub_nonneg_direct scaledLeHalf
  have endpointNonnegative :
      0 ≤ threshold / 2 - Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower threshold ^ 2 := by
    dsimp only [threshold]
    unfold Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
      Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower
    decide
  have offsetNonnegative : 0 ≤ norm - threshold :=
    Fraction.Order.Arithmetic.sub_nonneg_direct thresholdLe
  have certificateNonnegative :
      0 ≤
        (threshold / 2 - Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower threshold ^ 2) +
          (norm - threshold) *
            (1 / 2 - (2 / 7) ^ 2 * (norm + threshold + 2)) :=
    calc
      (0 : Fraction.Rational) = 0 + 0 := by ring1
      _ ≤
          (threshold / 2 - Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower threshold ^ 2) +
            (norm - threshold) *
              (1 / 2 - (2 / 7) ^ 2 * (norm + threshold + 2)) :=
        Fraction.Order.Arithmetic.add_le_add_direct endpointNonnegative
          (Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
            factorNonnegative)
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤
        (threshold / 2 - Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower threshold ^ 2) +
          (norm - threshold) *
            (1 / 2 - (2 / 7) ^ 2 * (norm + threshold + 2)) :=
      certificateNonnegative
    _ = norm / 2 - Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower norm ^ 2 := by
      rw [Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_eq threshold,
        Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_eq norm]
      rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul threshold,
        Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul norm]
      ring1

/-- The centered affine minorant lies below the larger nonnegative coordinate.

The coordinate squares must sum to the supplied norm, with that norm between 15/56 and one; comparison of squares proves
the bound. -/
private theorem centeredComponentLower_le_largerCoordinate
    (large small norm : Fraction.Rational)
    (largeNonnegative : 0 ≤ large)
    (smallNonnegative : 0 ≤ small)
    (smallLeLarge : small ≤ large)
    (normIdentity : norm = large ^ 2 + small ^ 2)
    (thresholdLe : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ norm)
    (normLeOne : norm ≤ 1) :
    Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower norm ≤ large := by
  have smallSquareLeLargeSquare : small ^ 2 ≤ large ^ 2 := by
    simpa only [pow_two] using
      Fraction.Order.Arithmetic.mul_le_mul_direct smallLeLarge smallLeLarge
        smallNonnegative largeNonnegative
  have halfNormLeLargeSquare : norm / 2 ≤ large ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        (norm / 2) * 2 = norm := by
          exact Fraction.Field.div_mul_cancel_of_ne norm 2
            (by decide)
        _ = large ^ 2 + small ^ 2 := normIdentity
        _ ≤ large ^ 2 + large ^ 2 :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            smallSquareLeLargeSquare
        _ = large ^ 2 * 2 := by ring1
    · decide
  exact Fraction.Order.Arithmetic.le_of_sq_le_sq_direct largeNonnegative
    ((Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_sq_le_half norm thresholdLe normLeOne).trans
      halfNormLeLargeSquare)

/-- A doubled-coordinate projection inequality bounds half the complementary norm by the coordinate. -/
private theorem half_complement_le_of_projection
    (norm coordinate : Fraction.Rational)
    (projection : 1 - norm ≤ 2 * coordinate) :
    (1 - norm) / 2 ≤ coordinate := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      ((1 - norm) / 2) * 2 = 1 - norm := by
        exact Fraction.Field.div_mul_cancel_of_ne (1 - norm) 2
          (by decide)
      _ ≤ 2 * coordinate := projection
      _ = coordinate * 2 := by ring1
  · decide

/-- The rational determinant-gap excess floor for aligned larger coordinates.

It sums the product of norms, twice the product of affine coordinate minorants, and twice the product of complementary
half-norms. -/
private def centeredAlignedExcessFloor
    (firstNorm secondNorm : Fraction.Rational) : Fraction.Rational :=
  firstNorm * secondNorm +
    2 * (Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm *
      Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm) +
    2 * (((1 - firstNorm) / 2) * ((1 - secondNorm) / 2))

/-- Twice the product of two rational halves is half their product. -/
private theorem twice_half_mul_half
    (first second : Fraction.Rational) :
    2 * ((first / 2) * (second / 2)) = (first * second) / 2 := by
  rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul first, Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
    second,
    Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (first * second)]
  have halfCertificate :
      (2 : Fraction.Rational) * (1 / 2) * (1 / 2) = 1 / 2 := by decide
  calc
    2 * ((1 / 2 * first) * (1 / 2 * second)) =
        (2 * (1 / 2) * (1 / 2)) * (first * second) := by ring1
    _ = (1 / 2) * (first * second) := by rw [halfCertificate]

/-- The aligned excess floor has complementary contribution equal to half the product of the complementary norms. -/
private theorem centeredAlignedExcessFloor_eq
    (firstNorm secondNorm : Fraction.Rational) :
    Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor firstNorm secondNorm =
      firstNorm * secondNorm +
        2 * (Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm *
          Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm) +
        ((1 - firstNorm) * (1 - secondNorm)) / 2 := by
  unfold Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor
  rw [Dirichlet.Window.IndexTwo.Bounds.twice_half_mul_half]

/-- The aligned excess floor is at least 77/128 when both norms are at least 15/56.

The endpoint is checked exactly and each increase in a norm contributes a nonnegative factor. -/
private theorem dyadicCenteredExcessThreshold_le_alignedFloor
    (firstNorm secondNorm : Fraction.Rational)
    (firstLower : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ firstNorm)
    (secondLower : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ secondNorm) :
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold ≤
      Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor firstNorm secondNorm := by
  let threshold := Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
  let slope : Fraction.Rational := 2 / 7
  let factor := fun value : Fraction.Rational =>
    value + 2 * slope ^ 2 * (value + 1) - (1 - value) / 2
  have thresholdFactorNonnegative : 0 ≤ factor threshold := by
    dsimp only [factor, slope, threshold]
    unfold Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
    decide
  have factorMonotone : ∀ value : Fraction.Rational, threshold ≤ value →
      factor threshold ≤ factor value := by
    intro value thresholdLe
    have offsetNonnegative : 0 ≤ value - threshold :=
      Fraction.Order.Arithmetic.sub_nonneg_direct thresholdLe
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (value - threshold) *
          (1 + 2 * slope ^ 2 + 1 / 2) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
          (add_nonneg
            (add_nonneg (by decide)
              (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                (Fraction.Order.Arithmetic.sq_nonneg_direct slope)))
            (by decide))
      _ = factor value - factor threshold := by
        dsimp only [factor]
        rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - value),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - threshold)]
        ring1
  have secondFactorNonnegative : 0 ≤ factor secondNorm :=
    thresholdFactorNonnegative.trans (factorMonotone secondNorm secondLower)
  have firstStep :
      Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold secondNorm ≤
        Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor firstNorm secondNorm := by
    have offsetNonnegative : 0 ≤ firstNorm - threshold :=
      Fraction.Order.Arithmetic.sub_nonneg_direct firstLower
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (firstNorm - threshold) * factor secondNorm :=
        Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
          secondFactorNonnegative
      _ = Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor firstNorm secondNorm -
          Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold secondNorm := by
        rw [Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor_eq,
          Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor_eq]
        simp only [Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_eq]
        dsimp only [factor, slope]
        rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
            ((1 - firstNorm) * (1 - secondNorm)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
            ((1 - threshold) * (1 - secondNorm)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - secondNorm)]
        ring1
  have secondStep :
      Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold threshold ≤
        Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold secondNorm := by
    have offsetNonnegative : 0 ≤ secondNorm - threshold :=
      Fraction.Order.Arithmetic.sub_nonneg_direct secondLower
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (secondNorm - threshold) * factor threshold :=
        Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
          thresholdFactorNonnegative
      _ = Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold secondNorm -
          Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold threshold := by
        rw [Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor_eq,
          Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor_eq]
        simp only [Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_eq]
        dsimp only [factor, slope]
        rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
            ((1 - threshold) * (1 - secondNorm)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul ((1 - threshold) * (1 - threshold)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - threshold)]
        ring1
  calc
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold ≤
        Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold threshold := by
      dsimp only [threshold]
      unfold Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold
        Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor
        Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
      decide
    _ ≤ Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor threshold secondNorm := secondStep
    _ ≤ Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor firstNorm secondNorm := firstStep

/-- The crossed excess floor is at least 77/128 when both norms are at least 15/56.

The affine minorants reduce the expression to a constant plus a nonnegative multiple of the norm product. -/
private theorem dyadicCenteredExcessThreshold_le_crossFloor
    (firstNorm secondNorm : Fraction.Rational)
    (firstLower : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ firstNorm)
    (secondLower : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ secondNorm) :
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold ≤
      firstNorm * secondNorm +
        Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm * (1 - secondNorm) +
        (1 - firstNorm) * Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm := by
  let threshold := Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
  let slope : Fraction.Rational := 2 / 7
  have thresholdNonnegative : (0 : Fraction.Rational) ≤ threshold := by
    dsimp only [threshold]
    unfold Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
    decide
  have firstNonnegative : (0 : Fraction.Rational) ≤ firstNorm :=
    thresholdNonnegative.trans firstLower
  have productLower : threshold ^ 2 ≤ firstNorm * secondNorm := by
    simpa only [pow_two] using
      Fraction.Order.Arithmetic.mul_le_mul_direct firstLower secondLower
        thresholdNonnegative firstNonnegative
  have coefficientNonnegative : 0 ≤ (1 : Fraction.Rational) - 2 * slope := by
    dsimp only [slope]
    decide
  have scaledProductLower :
      (1 - 2 * slope) * threshold ^ 2 ≤
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productLower
      coefficientNonnegative
  calc
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold ≤
        2 * slope + (1 - 2 * slope) * threshold ^ 2 := by
      dsimp only [slope, threshold]
      unfold Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold
        Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
      decide
    _ ≤ 2 * slope +
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl scaledProductLower
    _ = firstNorm * secondNorm +
        Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm * (1 - secondNorm) +
        (1 - firstNorm) * Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm := by
      rw [Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_eq,
        Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_eq]
      dsimp only [slope]
      ring1

/-- Coordinate projection bounds force the squared complementary norm to be at most twice the norm.

For a point inside the unit disk, either sign of each doubled coordinate may bound the complementary norm; squaring and
adding removes those sign choices. -/
private theorem complement_sq_le_two_normSq_of_projectionBounds
    (value : Gaussian.Basic.Canonical)
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1)
    (realProjection :
      1 - Data.Gaussian.Norm.Basic.normSq value ≤ -2 * value.re ∨
        1 - Data.Gaussian.Norm.Basic.normSq value ≤ 2 * value.re)
    (imaginaryProjection :
      1 - Data.Gaussian.Norm.Basic.normSq value ≤ -2 * value.im ∨
        1 - Data.Gaussian.Norm.Basic.normSq value ≤ 2 * value.im) :
    (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 ≤ 2 * Data.Gaussian.Norm.Basic.normSq value := by
  let complement := 1 - Data.Gaussian.Norm.Basic.normSq value
  have complementNonnegative : 0 ≤ complement := by
    dsimp only [complement]
    exact Fraction.Order.Arithmetic.sub_nonneg_direct inside.le
  have realSquare : complement ^ 2 ≤ 4 * value.re ^ 2 := by
    rcases realProjection with projection | projection
    · have upperNonnegative : 0 ≤ -2 * value.re :=
        complementNonnegative.trans projection
      have squared := Fraction.Order.Arithmetic.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 =
            (1 - Data.Gaussian.Norm.Basic.normSq value) * (1 - Data.Gaussian.Norm.Basic.normSq value) := by
              ring1
        _ ≤ (-2 * value.re) * (-2 * value.re) := squared
        _ = 4 * value.re ^ 2 := by ring1
    · have upperNonnegative : 0 ≤ 2 * value.re :=
        complementNonnegative.trans projection
      have squared := Fraction.Order.Arithmetic.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 =
            (1 - Data.Gaussian.Norm.Basic.normSq value) * (1 - Data.Gaussian.Norm.Basic.normSq value) := by
              ring1
        _ ≤ (2 * value.re) * (2 * value.re) := squared
        _ = 4 * value.re ^ 2 := by ring1
  have imaginarySquare : complement ^ 2 ≤ 4 * value.im ^ 2 := by
    rcases imaginaryProjection with projection | projection
    · have upperNonnegative : 0 ≤ -2 * value.im :=
        complementNonnegative.trans projection
      have squared := Fraction.Order.Arithmetic.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 =
            (1 - Data.Gaussian.Norm.Basic.normSq value) * (1 - Data.Gaussian.Norm.Basic.normSq value) := by
              ring1
        _ ≤ (-2 * value.im) * (-2 * value.im) := squared
        _ = 4 * value.im ^ 2 := by ring1
    · have upperNonnegative : 0 ≤ 2 * value.im :=
        complementNonnegative.trans projection
      have squared := Fraction.Order.Arithmetic.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 =
            (1 - Data.Gaussian.Norm.Basic.normSq value) * (1 - Data.Gaussian.Norm.Basic.normSq value) := by
              ring1
        _ ≤ (2 * value.im) * (2 * value.im) := squared
        _ = 4 * value.im ^ 2 := by ring1
  have added := Fraction.Order.Arithmetic.add_le_add_direct
    realSquare imaginarySquare
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
  · dsimp only [complement] at added ⊢
    calc
      (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 * 2 =
          (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 + (1 - Data.Gaussian.Norm.Basic.normSq value) ^ 2 :=
            by ring1
      _ ≤ 4 * value.re ^ 2 + 4 * value.im ^ 2 := added
      _ = (2 * Data.Gaussian.Norm.Basic.normSq value) * 2 := by
        dsimp only [Data.Gaussian.Norm.Basic.normSq]
        ring1
  · decide

/-- Four centered-unit obstructions keep both normalized quadrances away
from zero by the same square-root-free quadratic inequality. -/
theorem complement_sq_le_two_norms_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    (1 - Data.Gaussian.Norm.Basic.normSq errorRatio) ^ 2 ≤ 2 * Data.Gaussian.Norm.Basic.normSq errorRatio ∧
      (1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio) ^ 2 ≤
        2 * Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
  obtain ⟨realCross, imaginaryCross⟩ := Dirichlet.Window.IndexTwo.Bounds.centeredUnit_projectionCrosses
    errorRatio denominatorRatio errorInside denominatorInside obstruction
  have errorReal :
      1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ -2 * errorRatio.re ∨
        1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ 2 * errorRatio.re := by
    rcases realCross with cross | cross
    · exact Or.inl cross.1
    · exact Or.inr cross.2
  have errorImaginary :
      1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ -2 * errorRatio.im ∨
        1 - Data.Gaussian.Norm.Basic.normSq errorRatio ≤ 2 * errorRatio.im := by
    rcases imaginaryCross with cross | cross
    · exact Or.inl cross.1
    · exact Or.inr cross.2
  have denominatorReal :
      1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ -2 * denominatorRatio.re ∨
        1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ 2 * denominatorRatio.re := by
    rcases realCross with cross | cross
    · exact Or.inr cross.2
    · exact Or.inl cross.1
  have denominatorImaginary :
      1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ -2 * denominatorRatio.im ∨
        1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ 2 * denominatorRatio.im := by
    rcases imaginaryCross with cross | cross
    · exact Or.inl cross.2
    · exact Or.inr cross.1
  exact ⟨
    Dirichlet.Window.IndexTwo.Bounds.complement_sq_le_two_normSq_of_projectionBounds errorRatio errorInside
      errorReal errorImaginary,
    Dirichlet.Window.IndexTwo.Bounds.complement_sq_le_two_normSq_of_projectionBounds denominatorRatio
      denominatorInside denominatorReal denominatorImaginary⟩

/-- The complementary-square inequality forces a rational value to be at least 15/56.

A smaller value would make its quadratic polynomial positive, contrary to the supplied inequality. -/
private theorem fifteen_fiftySixths_le_of_complement_sq_le_twice
    (value : Fraction.Rational)
    (quadraticBound : (1 - value) ^ 2 ≤ 2 * value) :
    Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ value := by
  by_cases thresholdLe : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ value
  · exact thresholdLe
  · have valueLtThreshold : value < Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct thresholdLe
    have valueLeThreshold : value ≤ Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold :=
      Fraction.Order.Arithmetic.le_of_lt_direct valueLtThreshold
    have sumLe : value + Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤
        Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold + Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
          :=
      Fraction.Order.Arithmetic.add_le_add_direct valueLeThreshold le_rfl
    have sumLtFour : value + Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold < 4 := by
      have rationalGap :
          Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold +
            Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold < 4 := by
        decide
      exact ⟨sumLe.trans rationalGap.1, fun reverse =>
        rationalGap.2 (reverse.trans sumLe)⟩
    have firstFactorPositive :
        0 < Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold - value :=
      Fraction.Order.Arithmetic.sub_pos_direct valueLtThreshold
    have secondFactorPositive :
        0 < 4 - value - Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold := by
      have rewritten :
          4 - value - Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold =
            4 - (value + Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold) := by ring1
      rw [rewritten]
      exact Fraction.Order.Arithmetic.sub_pos_direct sumLtFour
    have productPositive :
        0 < (Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold - value) *
          (4 - value - Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold) :=
      Fraction.Order.Arithmetic.mul_pos_direct firstFactorPositive
        secondFactorPositive
    have thresholdPolynomialPositive :
        0 < Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ^ 2 -
          4 * Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold + 1 := by
      decide
    have valuePolynomialPositive : 0 < value ^ 2 - 4 * value + 1 := by
      calc
        0 = 0 + 0 := by ring1
        _ < (Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ^ 2 -
              4 * Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold + 1) +
            (Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold - value) *
              (4 - value - Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold) :=
          Fraction.Order.Arithmetic.add_lt_add_direct
            thresholdPolynomialPositive productPositive
        _ = value ^ 2 - 4 * value + 1 := by ring1
    have differenceNonnegative :
        0 ≤ 2 * value - (1 - value) ^ 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct quadraticBound
    have valuePolynomialNonpositive : value ^ 2 - 4 * value + 1 ≤ 0 := by
      calc
        value ^ 2 - 4 * value + 1 =
            -(2 * value - (1 - value) ^ 2) := by ring1
        _ ≤ -0 :=
          Fraction.Order.Arithmetic.neg_le_neg_direct differenceNonnegative
        _ = 0 := by ring1
    exact (not_lt_of_ge valuePolynomialNonpositive
      valuePolynomialPositive).elim

/-- A rational point just below the smaller root `2 - sqrt(3)` of the
quadratic obstruction works uniformly for both normalized coordinates. -/
theorem fifteen_fiftySixths_le_norms_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ Data.Gaussian.Norm.Basic.normSq errorRatio ∧
      Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio :=
        by
  obtain ⟨errorQuadratic, denominatorQuadratic⟩ :=
    Dirichlet.Window.IndexTwo.Bounds.complement_sq_le_two_norms_of_centeredUnitObstructions errorRatio
      denominatorRatio errorInside denominatorInside obstruction
  exact ⟨
    Dirichlet.Window.IndexTwo.Bounds.fifteen_fiftySixths_le_of_complement_sq_le_twice
      (Data.Gaussian.Norm.Basic.normSq errorRatio) errorQuadratic,
    Dirichlet.Window.IndexTwo.Bounds.fifteen_fiftySixths_le_of_complement_sq_le_twice
      (Data.Gaussian.Norm.Basic.normSq denominatorRatio) denominatorQuadratic⟩

/-- The balanced norm product is at least 15/56 when both norms lie between that threshold and one.

Splitting the second norm at one half gives a nonnegative factorization of the required difference. -/
private theorem fifteen_fiftySixths_le_balancedNormProduct
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (errorLower : Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ Data.Gaussian.Norm.Basic.normSq
      errorRatio)
    (denominatorLower :
      Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤ Data.Gaussian.Norm.Basic.normSq denominatorRatio) :
    Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold ≤
      Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio := by
  let x := Data.Gaussian.Norm.Basic.normSq errorRatio
  let y := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have xLeOne : x ≤ 1 := errorInside.le
  have yLeOne : y ≤ 1 := denominatorInside.le
  by_cases yLeHalf : y ≤ (1 / 2 : Fraction.Rational)
  · have twiceYLeOne : 2 * y ≤ (1 : Fraction.Rational) := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct yLeHalf
          (show (0 : Fraction.Rational) ≤ 2 by decide)
      calc
        2 * y ≤ 2 * (1 / 2 : Fraction.Rational) := scaled
        _ = 1 := by decide
    have oneMinusXNonnegative : 0 ≤ 1 - x :=
      Fraction.Order.Arithmetic.sub_nonneg_direct xLeOne
    have oneMinusTwiceYNonnegative : 0 ≤ 1 - 2 * y :=
      Fraction.Order.Arithmetic.sub_nonneg_direct twiceYLeOne
    have yLeBalanced : y ≤ Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤ (1 - x) * (1 - 2 * y) :=
          Fraction.Order.Arithmetic.mul_nonneg_direct
            oneMinusXNonnegative oneMinusTwiceYNonnegative
        _ = Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio - y := by
          dsimp only [Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct, x, y]
          ring1
    exact denominatorLower.trans yLeBalanced
  · have halfLtY : (1 / 2 : Fraction.Rational) < y :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct yLeHalf
    have halfLeY : (1 / 2 : Fraction.Rational) ≤ y :=
      Fraction.Order.Arithmetic.le_of_lt_direct halfLtY
    have oneLeTwiceY : (1 : Fraction.Rational) ≤ 2 * y := by
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct halfLeY
          (show (0 : Fraction.Rational) ≤ 2 by decide)
      calc
        (1 : Fraction.Rational) = 2 * (1 / 2 : Fraction.Rational) := by decide
        _ ≤ 2 * y := scaled
    have xMinusThresholdNonnegative :
        0 ≤ x - Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold :=
      Fraction.Order.Arithmetic.sub_nonneg_direct errorLower
    have twiceYMinusOneNonnegative : 0 ≤ 2 * y - 1 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct oneLeTwiceY
    have oneMinusYNonnegative : 0 ≤ 1 - y :=
      Fraction.Order.Arithmetic.sub_nonneg_direct yLeOne
    have rationalFactorNonnegative :
        0 ≤ 1 - 2 * Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold := by
      decide
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (x - Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold) * (2 * y - 1) +
          (1 - y) * (1 - 2 * Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold) :=
        add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            xMinusThresholdNonnegative twiceYMinusOneNonnegative)
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            oneMinusYNonnegative rationalFactorNonnegative)
      _ = Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio -
          Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold := by
        dsimp only [Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct, x, y]
        ring1

/-- Four centered unit obstructions force a lower bound stronger than one:
the determinant gap contains both complementary normalized norm products.
The proof is entirely coordinatewise: opposite real units force a negative
real-coordinate product, and opposite imaginary units force a positive
imaginary-coordinate product. -/
theorem one_add_balancedNormProduct_le_determinantGap_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    1 + Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let errorGap := 1 - Data.Gaussian.Norm.Basic.normSq errorRatio
  let denominatorGap := 1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have errorGapNonnegative : 0 ≤ errorGap := by
    dsimp only [errorGap]
    exact Fraction.Order.Arithmetic.sub_nonneg_direct errorInside.le
  have denominatorGapNonnegative : 0 ≤ denominatorGap := by
    dsimp only [denominatorGap]
    exact Fraction.Order.Arithmetic.sub_nonneg_direct denominatorInside.le
  have realCross := Best.Consecutive.RepeatedIndex.opposite_self_obstructions_cross
    errorRatio denominatorRatio errorInside denominatorInside 1 rfl
      (obstruction 1 rfl) (obstruction (-1) (by decide))
  have imaginaryCross :=
    Best.Consecutive.RepeatedIndex.opposite_self_obstructions_cross
      errorRatio denominatorRatio errorInside denominatorInside
        GaussianInt.Norm.Small.imaginaryUnit (by decide)
        (obstruction GaussianInt.Norm.Small.imaginaryUnit (by decide))
        (obstruction (-GaussianInt.Norm.Small.imaginaryUnit) (by decide))
  have realProductBound :
      4 * errorRatio.re * denominatorRatio.re ≤
        -(errorGap * denominatorGap) := by
    rcases realCross with cross | cross
    · have errorProjection : errorGap ≤ -2 * errorRatio.re := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (1 : GaussianInt)) - 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.1
          _ = (-2 * errorRatio.re) - errorGap := by
            dsimp only [errorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              GaussianInt.one_re,
              GaussianInt.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have denominatorProjection :
          denominatorGap ≤ 2 * denominatorRatio.re := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (1 - GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio) - 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.2
          _ = 2 * denominatorRatio.re - denominatorGap := by
            dsimp only [denominatorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im,
              GaussianInt.neg_re,
              GaussianInt.neg_im,
              GaussianInt.one_re,
              GaussianInt.one_im,
               ]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have productBound := Fraction.Order.Arithmetic.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      have negated := Fraction.Order.Arithmetic.neg_le_neg_direct productBound
      calc
        4 * errorRatio.re * denominatorRatio.re =
            -((-2 * errorRatio.re) * (2 * denominatorRatio.re)) := by ring1
        _ ≤ -(errorGap * denominatorGap) := negated
    · have denominatorProjection :
          denominatorGap ≤ -2 * denominatorRatio.re := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (1 : GaussianInt) * denominatorRatio) - 2
            :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.1
          _ = (-2 * denominatorRatio.re) - denominatorGap := by
            dsimp only [denominatorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im,
              GaussianInt.one_re,
              GaussianInt.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have errorProjection : errorGap ≤ 2 * errorRatio.re := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) - 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.2
          _ = 2 * errorRatio.re - errorGap := by
            dsimp only [errorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              GaussianInt.neg_re,
              GaussianInt.neg_im,
              GaussianInt.one_re,
              GaussianInt.one_im,
               ]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have productBound := Fraction.Order.Arithmetic.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      have negated := Fraction.Order.Arithmetic.neg_le_neg_direct productBound
      calc
        4 * errorRatio.re * denominatorRatio.re =
            -((2 * errorRatio.re) * (-2 * denominatorRatio.re)) := by ring1
        _ ≤ -(errorGap * denominatorGap) := negated
  have imaginaryProductBound :
      errorGap * denominatorGap ≤
        4 * errorRatio.im * denominatorRatio.im := by
    rcases imaginaryCross with cross | cross
    · have errorProjection : errorGap ≤ -2 * errorRatio.im := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (errorRatio -
                GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) - 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.1
          _ = (-2 * errorRatio.im) - errorGap := by
            dsimp only [errorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have denominatorProjection :
          denominatorGap ≤ -2 * denominatorRatio.im := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (1 -
                GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) *
                  denominatorRatio) - 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.2
          _ = (-2 * denominatorRatio.im) - denominatorGap := by
            dsimp only [denominatorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im,
              GaussianInt.neg_re,
              GaussianInt.neg_im,
               ]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have productBound := Fraction.Order.Arithmetic.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      calc
        errorGap * denominatorGap ≤
            (-2 * errorRatio.im) * (-2 * denominatorRatio.im) :=
          productBound
        _ = 4 * errorRatio.im * denominatorRatio.im := by ring1
    · have denominatorProjection :
          denominatorGap ≤ 2 * denominatorRatio.im := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (1 - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
                denominatorRatio) - 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.1
          _ = 2 * denominatorRatio.im - denominatorGap := by
            dsimp only [denominatorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              Gaussian.Basic.mul_re,
              Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re,
              Gaussian.Basic.one_im]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have errorProjection : errorGap ≤ 2 * errorRatio.im := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ Data.Gaussian.Norm.Basic.normSq
              (errorRatio -
                GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit)) - 2 :=
            Fraction.Order.Arithmetic.sub_nonneg_direct cross.2
          _ = 2 * errorRatio.im - errorGap := by
            dsimp only [errorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
              GaussianInt.Norm.Small.imaginaryUnit]
            simp only [Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im,
              GaussianInt.neg_re,
              GaussianInt.neg_im,
               ]
            simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
            ring1
      have productBound := Fraction.Order.Arithmetic.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      calc
        errorGap * denominatorGap ≤
            (2 * errorRatio.im) * (2 * denominatorRatio.im) := productBound
        _ = 4 * errorRatio.im * denominatorRatio.im := by ring1
  have negatedImaginary :=
    Fraction.Order.Arithmetic.neg_le_neg_direct imaginaryProductBound
  have fourRealPartBound :
      4 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im) ≤
        -2 * (errorGap * denominatorGap) := by
    calc
      4 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im) =
          4 * errorRatio.re * denominatorRatio.re +
            -(4 * errorRatio.im * denominatorRatio.im) := by ring1
      _ ≤ -(errorGap * denominatorGap) +
          -(errorGap * denominatorGap) :=
        Fraction.Order.Arithmetic.add_le_add_direct realProductBound
          negatedImaginary
      _ = -2 * (errorGap * denominatorGap) := by ring1
  have twiceRealPartBound :
      2 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im) ≤
        -(errorGap * denominatorGap) := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
    · convert fourRealPartBound using 1 <;> ring1
    · decide
  have gapLeNegatedTwiceRealPart :
      errorGap * denominatorGap ≤
        -(2 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im)) := by
    simpa only [neg_neg] using
      Fraction.Order.Arithmetic.neg_le_neg_direct twiceRealPartBound
  have coreBound :
      Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio ≤
        Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) - 1 := by
    unfold Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct
    dsimp only [errorGap, denominatorGap] at gapLeNegatedTwiceRealPart
    calc
      Data.Gaussian.Norm.Basic.normSq errorRatio * Data.Gaussian.Norm.Basic.normSq denominatorRatio +
          ((1 - Data.Gaussian.Norm.Basic.normSq errorRatio) * (1 - Data.Gaussian.Norm.Basic.normSq
            denominatorRatio)) ≤
          Data.Gaussian.Norm.Basic.normSq errorRatio * Data.Gaussian.Norm.Basic.normSq denominatorRatio -
            2 * (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by
        exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl
          gapLeNegatedTwiceRealPart
      _ = Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) - 1 := by
        dsimp only [Data.Gaussian.Norm.Basic.normSq]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        ring1
  calc
    1 + Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio ≤
        1 + (Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) - 1) :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl coreBound
    _ = Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by ring1

/-- Four centered-unit obstructions give the explicit rational determinant
gap `71/56`.  This uses the balanced-product identity together with the
rational point `15/56 < 2 - sqrt(3)`; no square root is introduced. -/
theorem seventyOne_fiftySixths_le_determinantGap_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  obtain ⟨errorLower, denominatorLower⟩ :=
    Dirichlet.Window.IndexTwo.Bounds.fifteen_fiftySixths_le_norms_of_centeredUnitObstructions errorRatio
      denominatorRatio errorInside denominatorInside obstruction
  have balancedLower := Dirichlet.Window.IndexTwo.Bounds.fifteen_fiftySixths_le_balancedNormProduct
    errorRatio denominatorRatio errorInside denominatorInside errorLower
      denominatorLower
  calc
    Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold = 1 + Dirichlet.Window.IndexTwo.Bounds.centeredNormThreshold
      := by decide
    _ ≤ 1 + Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl balancedLower
    _ ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) :=
      Dirichlet.Window.IndexTwo.Bounds.one_add_balancedNormProduct_le_determinantGap_of_centeredUnitObstructions
        errorRatio denominatorRatio errorInside denominatorInside obstruction

/-- In a displayed first octant, the ordinary coordinate order and the four
centered-unit certificates force the stronger dyadic gap `205/128`.  The
proof replaces the two square roots in the geometric arc argument by the
affine minorant `2(X+1)/7` and two exact rational orientation cases. -/
theorem dyadicCenteredGapThreshold_le_determinantGap_of_firstOctantObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let u := -denominatorRatio.re
  let v := denominatorRatio.im
  let firstNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let secondNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  let firstHalfGap := (1 - firstNorm) / 2
  let secondHalfGap := (1 - secondNorm) / 2
  obtain ⟨firstNormLower, secondNormLower⟩ :=
    Dirichlet.Window.IndexTwo.Bounds.fifteen_fiftySixths_le_norms_of_centeredUnitObstructions errorRatio
      denominatorRatio errorInside denominatorInside obstruction
  obtain ⟨bProjection, uProjectionRaw, vProjection⟩ :=
    Dirichlet.Window.IndexTwo.Bounds.firstOctant_projectionBounds_of_centeredUnitObstructions errorRatio
      denominatorRatio realNonnegative imaginaryNonnegative errorInside
      denominatorInside obstruction
  have firstNormLeOne : firstNorm ≤ (1 : Fraction.Rational) := errorInside.le
  have secondNormLeOne : secondNorm ≤ (1 : Fraction.Rational) :=
    denominatorInside.le
  have firstNormNonnegative : (0 : Fraction.Rational) ≤ firstNorm :=
    Gaussian.Norm.Basic.normSq_nonneg errorRatio
  have secondNormNonnegative : (0 : Fraction.Rational) ≤ secondNorm :=
    Gaussian.Norm.Basic.normSq_nonneg denominatorRatio
  have firstHalfGapNonnegative : (0 : Fraction.Rational) ≤ firstHalfGap := by
    dsimp only [firstHalfGap]
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sub_nonneg_direct firstNormLeOne)
      (by decide)
  have secondHalfGapNonnegative : (0 : Fraction.Rational) ≤ secondHalfGap := by
    dsimp only [secondHalfGap]
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sub_nonneg_direct secondNormLeOne)
      (by decide)
  have bLower : firstHalfGap ≤ b := by
    dsimp only [firstHalfGap, firstNorm, b]
    exact Dirichlet.Window.IndexTwo.Bounds.half_complement_le_of_projection _ _ bProjection
  have uProjection : 1 - secondNorm ≤ 2 * u := by
    dsimp only [secondNorm, u]
    calc
      1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤
          -2 * denominatorRatio.re := uProjectionRaw
      _ = 2 * (-denominatorRatio.re) := by ring1
  have uLower : secondHalfGap ≤ u := by
    dsimp only [secondHalfGap]
    exact Dirichlet.Window.IndexTwo.Bounds.half_complement_le_of_projection secondNorm u uProjection
  have vLower : secondHalfGap ≤ v := by
    dsimp only [secondHalfGap, secondNorm, v]
    exact Dirichlet.Window.IndexTwo.Bounds.half_complement_le_of_projection _ _ vProjection
  have uNonnegative : (0 : Fraction.Rational) ≤ u :=
    secondHalfGapNonnegative.trans uLower
  have vNonnegative : (0 : Fraction.Rational) ≤ v :=
    secondHalfGapNonnegative.trans vLower
  have firstNormIdentity : firstNorm = a ^ 2 + b ^ 2 := by
    dsimp only [firstNorm, a, b, Data.Gaussian.Norm.Basic.normSq]
  have secondNormIdentity : secondNorm = u ^ 2 + v ^ 2 := by
    dsimp only [secondNorm, u, v, Data.Gaussian.Norm.Basic.normSq]
    ring1
  have firstComponentLower : Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm ≤ a :=
    Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_le_largerCoordinate a b firstNorm
      realNonnegative imaginaryNonnegative imaginaryLeReal firstNormIdentity
      firstNormLower firstNormLeOne
  have firstAffineNonnegative :
      (0 : Fraction.Rational) ≤ Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm :=
    Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_nonnegative firstNormNonnegative
  have secondAffineNonnegative :
      (0 : Fraction.Rational) ≤ Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm :=
    Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_nonnegative secondNormNonnegative
  have excessLeCore :
      Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold ≤
        firstNorm * secondNorm + 2 * (a * u + b * v) := by
    by_cases uLeV : u ≤ v
    · have secondComponentLower :
          Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm ≤ v :=
        Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_le_largerCoordinate v u secondNorm
          vNonnegative uNonnegative uLeV (by
            rw [secondNormIdentity]
            ring1)
          secondNormLower secondNormLeOne
      have firstProductLower :
          Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm * secondHalfGap ≤ a * u :=
        Fraction.Order.Arithmetic.mul_le_mul_direct firstComponentLower
          uLower secondHalfGapNonnegative realNonnegative
      have secondProductLower :
          firstHalfGap * Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm ≤ b * v :=
        Fraction.Order.Arithmetic.mul_le_mul_direct bLower
          secondComponentLower secondAffineNonnegative
          imaginaryNonnegative
      have productSumLower :
          Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm * secondHalfGap +
              firstHalfGap * Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm ≤
            a * u + b * v :=
        Fraction.Order.Arithmetic.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Fraction.Rational) ≤ 2 by decide)
      calc
        Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold ≤
            firstNorm * secondNorm +
              Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm * (1 - secondNorm) +
              (1 - firstNorm) * Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm :=
          Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold_le_crossFloor firstNorm secondNorm
            firstNormLower secondNormLower
        _ = firstNorm * secondNorm +
            2 * (Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm * secondHalfGap +
              firstHalfGap * Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm) := by
          have firstDouble : secondHalfGap * 2 = 1 - secondNorm := by
            dsimp only [secondHalfGap]
            exact Fraction.Field.div_mul_cancel_of_ne
              (1 - secondNorm) 2 (by decide)
          have secondDouble : firstHalfGap * 2 = 1 - firstNorm := by
            dsimp only [firstHalfGap]
            exact Fraction.Field.div_mul_cancel_of_ne
              (1 - firstNorm) 2 (by decide)
          rw [← firstDouble, ← secondDouble]
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            twiceProductSumLower
    · have vLeU : v ≤ u := le_of_not_ge uLeV
      have secondComponentLower :
          Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm ≤ u :=
        Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower_le_largerCoordinate u v secondNorm
          uNonnegative vNonnegative vLeU secondNormIdentity
          secondNormLower secondNormLeOne
      have firstProductLower :
          Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm *
              Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm ≤ a * u :=
        Fraction.Order.Arithmetic.mul_le_mul_direct firstComponentLower
          secondComponentLower secondAffineNonnegative realNonnegative
      have secondProductLower : firstHalfGap * secondHalfGap ≤ b * v :=
        Fraction.Order.Arithmetic.mul_le_mul_direct bLower vLower
          secondHalfGapNonnegative imaginaryNonnegative
      have productSumLower :
          Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm *
                Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm +
              firstHalfGap * secondHalfGap ≤
            a * u + b * v :=
        Fraction.Order.Arithmetic.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Fraction.Rational) ≤ 2 by decide)
      calc
        Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold ≤
            Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor firstNorm secondNorm :=
          Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold_le_alignedFloor firstNorm secondNorm
            firstNormLower secondNormLower
        _ = firstNorm * secondNorm +
            2 * (Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower firstNorm *
                Dirichlet.Window.IndexTwo.Bounds.centeredComponentLower secondNorm +
              firstHalfGap * secondHalfGap) := by
          unfold Dirichlet.Window.IndexTwo.Bounds.centeredAlignedExcessFloor
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            twiceProductSumLower
  calc
    Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold =
        1 + Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredExcessThreshold :=
      Dirichlet.Window.IndexTwo.Bounds.dyadicCenteredGapThreshold_eq_one_add_excess
    _ ≤ 1 + (firstNorm * secondNorm + 2 * (a * u + b * v)) :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl excessLeCore
    _ = Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
      dsimp only [firstNorm, secondNorm, a, b, u, v, Data.Gaussian.Norm.Basic.normSq]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im]
      ring1

/-- Four centered unit obstructions force the normalized determinant gap to be at least one.

Both ratios must lie inside the unit disk; their complementary norm products provide a nonnegative contribution beyond
one. -/
theorem one_le_determinantGap_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  have errorComplementNonnegative : 0 ≤ 1 - Data.Gaussian.Norm.Basic.normSq errorRatio :=
    Fraction.Order.Arithmetic.sub_nonneg_direct errorInside.le
  have denominatorComplementNonnegative :
      0 ≤ 1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio :=
    Fraction.Order.Arithmetic.sub_nonneg_direct denominatorInside.le
  have balancedNonnegative :
      0 ≤ Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio := by
    unfold Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct
    exact add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Gaussian.Norm.Basic.normSq_nonneg errorRatio) (Gaussian.Norm.Basic.normSq_nonneg denominatorRatio))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        errorComplementNonnegative denominatorComplementNonnegative)
  calc
    (1 : Fraction.Rational) ≤
        1 + Dirichlet.Window.IndexTwo.Bounds.balancedNormProduct errorRatio denominatorRatio :=
      le_add_of_nonneg_right balancedNonnegative
    _ ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) :=
      Dirichlet.Window.IndexTwo.Bounds.one_add_balancedNormProduct_le_determinantGap_of_centeredUnitObstructions
        errorRatio denominatorRatio errorInside denominatorInside obstruction

/-- The upper-to-lower error ratio of a consecutive best pair lies strictly
inside the unit disk. -/
theorem AreConsecutiveBest.errorRatio_normSq_lt_one
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.Basic.errorRatio source.value lower upper) < 1 := by
  have lowerPositive : 0 < Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) :=
    Gaussian.Norm.Basic.normSq_pos (Dirichlet.Window.Basic.AreConsecutiveBest.lowerError_nonzero
      consecutive)
  unfold Dirichlet.Window.Basic.errorRatio
  rw [Gaussian.Norm.Basic.normSq_mul,
    Gaussian.Field.normSq_inv _
      (Dirichlet.Window.Basic.AreConsecutiveBest.lowerError_nonzero consecutive)]
  change Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value upper) /
      Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) < 1
  apply (Fraction.Order.Field.div_lt_iff_pos lowerPositive).mpr
  rw [Fraction.Field.one_mul]
  exact consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1

/-- The centered coefficient pair available at determinant index two becomes
an exact normalized unit obstruction after cancelling the positive lower-error
and upper-denominator quadrances. -/
theorem AreConsecutiveBest.normalizedCenteredUnitObstruction
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
    (2 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq (Dirichlet.Window.Basic.errorRatio source.value lower upper -
          GaussianInt.toGaussian unit) ∨
      2 ≤ Data.Gaussian.Norm.Basic.normSq
        (1 - GaussianInt.toGaussian unit * Dirichlet.Window.Basic.denominatorRatio lower upper) := by
  let candidate := GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1
  have obstruction :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_selfObstruction consecutive) indexTwo unit unitNorm
  have lowerErrorPositive :
      0 < Best.Error.errorQuadrance source.value lower :=
    Gaussian.Norm.Basic.normSq_pos (Dirichlet.Window.Basic.AreConsecutiveBest.lowerError_nonzero
      consecutive)
  have upperDenominatorPositive :
      (0 : Fraction.Rational) < Best.Error.denominatorQuadrance upper :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos consecutive.2.1.1)
  have errorIdentity :
      Best.Error.error source.value candidate =
        (Dirichlet.Window.Basic.errorRatio source.value lower upper - GaussianInt.toGaussian unit) *
          Best.Error.error source.value lower := by
    dsimp only [candidate]
    rw [Best.Error.error_linearCombination_negUnit_one]
    have ratioCancel :=
      Dirichlet.Window.Basic.AreConsecutiveBest.errorRatio_mul_lowerError
        consecutive
    calc
      Best.Error.error source.value upper -
            GaussianInt.toGaussian unit * Best.Error.error source.value lower =
          Dirichlet.Window.Basic.errorRatio source.value lower upper * Best.Error.error source.value lower -
            GaussianInt.toGaussian unit * Best.Error.error source.value lower := by
        rw [ratioCancel]
      _ =
          (Dirichlet.Window.Basic.errorRatio source.value lower upper - GaussianInt.toGaussian unit) *
            Best.Error.error source.value lower := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
  have denominatorIdentity :
      GaussianInt.toGaussian candidate.denominator =
        (1 - GaussianInt.toGaussian unit * Dirichlet.Window.Basic.denominatorRatio lower upper) *
          GaussianInt.toGaussian upper.denominator := by
    dsimp only [candidate]
    rw [Best.Error.toGaussian_denominator_linearCombination_negUnit_one]
    have ratioCancel :=
      Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_mul_upperDenominator
        consecutive
    calc
      GaussianInt.toGaussian upper.denominator -
            GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator =
          GaussianInt.toGaussian upper.denominator -
            GaussianInt.toGaussian unit *
              (Dirichlet.Window.Basic.denominatorRatio lower upper *
                GaussianInt.toGaussian upper.denominator) := by
        rw [ratioCancel]
      _ =
          (1 - GaussianInt.toGaussian unit * Dirichlet.Window.Basic.denominatorRatio lower upper) *
            GaussianInt.toGaussian upper.denominator := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
  rcases obstruction with errorOutside | denominatorOutside
  · left
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Best.Error.errorQuadrance source.value lower)
    · calc
        (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value lower ≤
            Best.Error.errorQuadrance source.value candidate := errorOutside
        _ = Data.Gaussian.Norm.Basic.normSq
              (Dirichlet.Window.Basic.errorRatio source.value lower upper - GaussianInt.toGaussian unit) *
            Best.Error.errorQuadrance source.value lower := by
          unfold Best.Error.errorQuadrance
          rw [errorIdentity, Gaussian.Norm.Basic.normSq_mul]
    · exact lowerErrorPositive
  · right
    have castOutside :=
      Fraction.Cast.Order.natCast_le_direct denominatorOutside
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (Best.Error.denominatorQuadrance upper : Fraction.Rational))
    · calc
        (2 : Fraction.Rational) * (Best.Error.denominatorQuadrance upper : Fraction.Rational) =
            ((2 * Best.Error.denominatorQuadrance upper : Nat) : Fraction.Rational) := by
          rw [NatCast.mul, Nat.cast_ofNat]
        _ ≤ (Best.Error.denominatorQuadrance candidate : Fraction.Rational) := castOutside
        _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian candidate.denominator) :=
          (GaussianInt.normSq_toGaussian _).symm
        _ = Data.Gaussian.Norm.Basic.normSq
              (1 - GaussianInt.toGaussian unit * Dirichlet.Window.Basic.denominatorRatio lower upper) *
            (Best.Error.denominatorQuadrance upper : Fraction.Rational) := by
          rw [denominatorIdentity, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
          rfl
    · exact upperDenominatorPositive

/-- In the determinant-index-two case, the four centered unit candidates
force the normalized determinant gap to be at least the displayed rational
`71/56`. -/
theorem AreConsecutiveBest.seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact Dirichlet.Window.IndexTwo.Bounds.seventyOne_fiftySixths_le_determinantGap_of_centeredUnitObstructions
    (Dirichlet.Window.Basic.errorRatio source.value lower upper) (Dirichlet.Window.Basic.denominatorRatio lower upper)
    (Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.errorRatio_normSq_lt_one consecutive)
    (Dirichlet.Window.Basic.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.normalizedCenteredUnitObstruction consecutive indexTwo)

/-- Consecutive best pairs of coefficient index two have normalized determinant gap at least one. -/
theorem AreConsecutiveBest.one_le_normalizedDeterminantGap_of_indexTwo
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    (1 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq
        (1 - Dirichlet.Window.Basic.denominatorRatio lower upper *
          Dirichlet.Window.Basic.errorRatio source.value lower upper) := by
  exact (show (1 : Fraction.Rational) ≤ Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold by decide).trans
    (Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
      consecutive indexTwo)

/-- A determinant-index-two consecutive window has squared product at most
the displayed rational `112/71`.  The proof multiplies through by the
positive displayed threshold, so it never constructs a reciprocal. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      Dirichlet.Window.IndexTwo.Bounds.centeredWindowBound := by
  have scaledWindow :=
    Dirichlet.Window.Basic.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold

          (AreConsecutiveBest.seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
          consecutive indexTwo)
  rw [indexTwo, Nat.cast_ofNat] at scaledWindow
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold)
  · calc
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper *
          Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold =
          Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold *
            Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper := by ring1
      _ ≤ 2 := scaledWindow
      _ = Dirichlet.Window.IndexTwo.Bounds.centeredWindowBound * Dirichlet.Window.IndexTwo.Bounds.centeredGapThreshold
        := by
        decide
  · decide

/-- Consecutive best pairs of coefficient index two have squared window product at most two. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexTwo
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤ 2 :=

    (AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
      consecutive indexTwo).trans (by decide)

/-- The universal quadratic index factor 1189/102 is at least two. -/
theorem two_le_quadraticIndexFactor :
    (2 : Fraction.Rational) ≤ Dirichlet.Window.Basic.quadraticIndexFactor := by
  unfold Dirichlet.Window.Basic.quadraticIndexFactor
  decide

/-- Multiplying the quadratic index factor by 102 recovers its numerator 1189. -/
theorem quadraticIndexFactor_mul_denominator :
    Dirichlet.Window.Basic.quadraticIndexFactor * 102 = 1189 := by
  unfold Dirichlet.Window.Basic.quadraticIndexFactor
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 1189, den := 102, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Splitting on the exact determinant index improves the universal squared
window bound from `1189/51` to `1189/102`: index one uses the quadratic gap
factor once, while index two has the independent centered-coset bound `2`. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
      Dirichlet.Window.Basic.quadraticIndexFactor := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two consecutive) with
      indexOne | indexTwo
  · have indexed :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
        consecutive
    calc
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper ≤
          Dirichlet.Window.Basic.quadraticIndexFactor *
            (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) := indexed
      _ = Dirichlet.Window.Basic.quadraticIndexFactor := by rw [indexOne]; ring1
  · exact
      (Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexTwo consecutive
        indexTwo).trans
        Dirichlet.Window.IndexTwo.Bounds.two_le_quadraticIndexFactor

end Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds

end
