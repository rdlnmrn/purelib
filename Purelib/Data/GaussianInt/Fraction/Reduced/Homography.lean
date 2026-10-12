module

public import Purelib.Data.GaussianInt.Fraction.Reduced
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.Ring

/-!
# Unimodular homographies centred at reduced fractions

The original Bézout coefficients complete a reduced numerator-denominator
column to an integral determinant-one matrix. A retained integral
translation moves the affine input before this action. The exact source
displacement and affine denominator identities supply rational placement
and pole-clearance estimates.
-/

public section

namespace Purelib.Data.GaussianInt.Fraction.Reduced

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2

/-- Complete the retained reduced column to a unimodular homography after an integral input translation.

The second column uses the original Bézout coefficients. Neither reduction
nor coefficient selection is repeated by this construction.
-/
@[expose] def homography (fraction : Reduced) (translation : GaussianInt) : Matrix GaussianInt where
  a := fraction.numerator
  b := fraction.numerator * translation - fraction.rightCoefficient
  c := fraction.denominator
  d := fraction.denominator * translation + fraction.leftCoefficient

/-- The original Bézout identity certifies determinant one for every retained translation. -/
theorem homography_determinant (fraction : Reduced) (translation : GaussianInt) :
    (fraction.homography translation).determinant = 1 := by
  calc
    (fraction.homography translation).determinant =
        fraction.leftCoefficient * fraction.numerator + fraction.rightCoefficient * fraction.denominator := by
      unfold homography Matrix.determinant
      apply GaussianInt.ext <;>
        simp only [GaussianInt.add_re, GaussianInt.add_im, GaussianInt.sub_re, GaussianInt.sub_im,
          GaussianInt.mul_re, GaussianInt.mul_im] <;> ring1
    _ = 1 := fraction.bezout.symm

/-- The affine denominator retains the original denominator, translation, tail and Bézout coefficient. -/
theorem homography_denominator (fraction : Reduced) (translation : GaussianInt)
    (tail : Gaussian.Basic.Canonical) :
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail =
      GaussianInt.toGaussian fraction.denominator * (tail + GaussianInt.toGaussian translation) +
        GaussianInt.toGaussian fraction.leftCoefficient := by
  unfold Homography.Basic.denominator Matrix.map homography
  rewrite [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- The exact affine offset before the retained integral translation. -/
@[expose] def homographyOffset (fraction : Reduced) (tail : Gaussian.Basic.Canonical) :
    Gaussian.Basic.Canonical :=
  tail + GaussianInt.toGaussian fraction.leftCoefficient *
    Gaussian.Field.inv (GaussianInt.toGaussian fraction.denominator)

/-- The homographic denominator factors through the original denominator and the translated affine offset. -/
theorem homography_denominator_factor (fraction : Reduced) (translation : GaussianInt)
    (tail : Gaussian.Basic.Canonical) :
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail =
      GaussianInt.toGaussian fraction.denominator *
        (GaussianInt.toGaussian translation + fraction.homographyOffset tail) := by
  have coefficientPaid : GaussianInt.toGaussian fraction.denominator *
      (GaussianInt.toGaussian fraction.leftCoefficient *
        Gaussian.Field.inv (GaussianInt.toGaussian fraction.denominator)) =
      GaussianInt.toGaussian fraction.leftCoefficient := by
    calc
      _ = (GaussianInt.toGaussian fraction.denominator *
            Gaussian.Field.inv (GaussianInt.toGaussian fraction.denominator)) *
          GaussianInt.toGaussian fraction.leftCoefficient := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
      _ = _ := by
        rewrite [Gaussian.Field.mul_inv _ fraction.denominatorGaussianNonzero, Gaussian.Basic.one_mul]
        rfl
  rewrite [fraction.homography_denominator]
  unfold homographyOffset
  calc
    GaussianInt.toGaussian fraction.denominator * (tail + GaussianInt.toGaussian translation) +
        GaussianInt.toGaussian fraction.leftCoefficient =
      GaussianInt.toGaussian fraction.denominator * (tail + GaussianInt.toGaussian translation) +
        GaussianInt.toGaussian fraction.denominator *
          (GaussianInt.toGaussian fraction.leftCoefficient *
            Gaussian.Field.inv (GaussianInt.toGaussian fraction.denominator)) := by
      rewrite [coefficientPaid]
      rfl
    _ = _ := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Paying both actual denominators gives the exact displacement from the original reduced fraction. -/
theorem homographic_difference_mul_denominators (fraction : Reduced) (translation : GaussianInt)
    (tail : Gaussian.Basic.Canonical)
    (poleExcluded : Homography.Basic.denominator
      (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail ≠ 0) :
    (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail -
        fraction.value) *
        (GaussianInt.toGaussian fraction.denominator * Homography.Basic.denominator
          (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail) = -1 := by
  let matrix := Matrix.map GaussianInt.toGaussian (fraction.homography translation)
  let denominator := Homography.Basic.denominator matrix tail
  let output := Homography.Basic.homographic matrix tail
  have outputPaid : output * denominator = Homography.Basic.numerator matrix tail := by
    unfold output Homography.Basic.homographic
    rewrite [Gaussian.Basic.mul_assoc, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ poleExcluded, Gaussian.Basic.mul_one]
    rfl
  have embeddedDeterminant := congrArg GaussianInt.toGaussian (fraction.homography_determinant translation)
  unfold Matrix.determinant at embeddedDeterminant
  rewrite [GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul,
    GaussianInt.toGaussian_one] at embeddedDeterminant
  calc
    (output - fraction.value) * (GaussianInt.toGaussian fraction.denominator * denominator) =
        (output * denominator) * GaussianInt.toGaussian fraction.denominator -
          (fraction.value * GaussianInt.toGaussian fraction.denominator) * denominator := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
    _ = Homography.Basic.numerator matrix tail * GaussianInt.toGaussian fraction.denominator -
        GaussianInt.toGaussian fraction.numerator * denominator := by
      rewrite [outputPaid, fraction.value_mul_denominator]
      rfl
    _ = -(GaussianInt.toGaussian (fraction.homography translation).a *
        GaussianInt.toGaussian (fraction.homography translation).d -
        GaussianInt.toGaussian (fraction.homography translation).b *
          GaussianInt.toGaussian (fraction.homography translation).c) := by
      dsimp only [matrix, Homography.Basic.numerator, denominator, Homography.Basic.denominator,
        Matrix.map, homography]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1
    _ = -1 := by
      rewrite [embeddedDeterminant]
      rfl

/-- The squared displacement has the exact product of the two denominator quadrances as its payment. -/
theorem homographic_distance_mul_denominator_normSq (fraction : Reduced) (translation : GaussianInt)
    (tail : Gaussian.Basic.Canonical)
    (poleExcluded : Homography.Basic.denominator
      (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail ≠ 0) :
    Gaussian.Norm.Basic.normSq
        (Homography.Basic.homographic (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail -
          fraction.value) *
        (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator) *
          Gaussian.Norm.Basic.normSq (Homography.Basic.denominator
            (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail)) = 1 := by
  have paid := congrArg Gaussian.Norm.Basic.normSq
    (fraction.homographic_difference_mul_denominators translation tail poleExcluded)
  rewrite [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul,
    Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_one] at paid
  exact paid

/-- Compute an integral input translation whose affine denominator quadrance exceeds the requested rational bound.

The real coordinate is the natural ceiling of one explicit nonnegative
shift, plus one. The original denominator and tail offset determine the
shift; no search or repeated fraction reduction is used.
-/
def homographyTranslation (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    (denominatorBound : Fraction.Rational) : GaussianInt :=
  let target := 1 + denominatorBound / Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator)
  GaussianInt.ofNat (Rounding.Floor.ceilNat (max 0 (target - (fraction.homographyOffset tail).re)) + 1)

/-- The computed translation puts the real affine coordinate strictly above its requested target. -/
private theorem homographyTranslation_re_gt (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    (denominatorBound : Fraction.Rational) :
    1 + denominatorBound / Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator) <
      (GaussianInt.toGaussian (fraction.homographyTranslation tail denominatorBound) +
        fraction.homographyOffset tail).re := by
  let target := 1 + denominatorBound / Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator)
  let shift := max 0 (target - (fraction.homographyOffset tail).re)
  let integer := Rounding.Floor.ceilNat shift
  have shiftNonnegative : 0 ≤ shift := Fraction.Order.Basic.le_max_left _ _
  have ceilingBound : target - (fraction.homographyOffset tail).re ≤ (integer : Fraction.Rational) :=
    (Fraction.Order.Basic.le_max_right _ _).trans (Rounding.Floor.le_natCast_ceilNat_of_nonneg shiftNonnegative)
  have successorStrict : (integer : Fraction.Rational) < ((integer + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct (Nat.lt_add_one_iff.mpr (Nat.le_refl _))
  unfold homographyTranslation
  rewrite [GaussianInt.toGaussian_ofNat]
  change target < ((integer + 1 : Nat) : Fraction.Rational) + (fraction.homographyOffset tail).re
  calc
    target = (target - (fraction.homographyOffset tail).re) + (fraction.homographyOffset tail).re := by ring1
    _ < ((integer + 1 : Nat) : Fraction.Rational) + (fraction.homographyOffset tail).re :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct (ceilingBound.trans_lt successorStrict) _

/-- The computed finite translation exceeds every supplied nonnegative denominator-quadrance bound. -/
theorem homographyTranslation_denominator_normSq_gt (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    {denominatorBound : Fraction.Rational} (nonnegative : 0 ≤ denominatorBound) :
    denominatorBound < Gaussian.Norm.Basic.normSq (Homography.Basic.denominator
      (Matrix.map GaussianInt.toGaussian (fraction.homography (fraction.homographyTranslation tail denominatorBound)))
        tail) := by
  let translation := fraction.homographyTranslation tail denominatorBound
  let translated := GaussianInt.toGaussian translation + fraction.homographyOffset tail
  let denominatorNorm := Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator)
  have denominatorPositive : 0 < denominatorNorm :=
    Gaussian.Norm.Basic.normSq_pos fraction.denominatorGaussianNonzero
  have quotientNonnegative : 0 ≤ denominatorBound / denominatorNorm :=
    Fraction.Order.Field.div_nonneg_direct nonnegative denominatorPositive.le
  have oneLeTarget : (1 : Fraction.Rational) ≤ 1 + denominatorBound / denominatorNorm :=
    le_add_of_nonneg_right quotientNonnegative
  have coordinateStrict : 1 + denominatorBound / denominatorNorm < translated.re :=
    fraction.homographyTranslation_re_gt tail denominatorBound
  have coordinatePositive : 0 < translated.re :=
    ((by decide : (0 : Fraction.Rational) < 1).trans_le oneLeTarget).trans coordinateStrict
  have coordinateLeSquare : translated.re ≤ translated.re ^ 2 := by
    calc
      translated.re = translated.re * 1 := by ring1
      _ ≤ translated.re * translated.re :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (oneLeTarget.trans coordinateStrict.le) coordinatePositive.le
      _ = translated.re ^ 2 := by ring1
  have squareLeNorm : translated.re ^ 2 ≤ Gaussian.Norm.Basic.normSq translated :=
    le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct translated.im)
  have quotientStrict : denominatorBound / denominatorNorm < translated.re := by
    calc
      denominatorBound / denominatorNorm < 1 + denominatorBound / denominatorNorm := by
        have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
          (by decide : (0 : Fraction.Rational) < 1) (denominatorBound / denominatorNorm)
        simpa only [Fraction.zero_add] using shifted
      _ < translated.re := coordinateStrict
  have factorNorm : Gaussian.Norm.Basic.normSq (Homography.Basic.denominator
      (Matrix.map GaussianInt.toGaussian (fraction.homography translation)) tail) =
      denominatorNorm * Gaussian.Norm.Basic.normSq translated := by
    rewrite [fraction.homography_denominator_factor, Gaussian.Norm.Basic.normSq_mul]
    rfl
  calc
    denominatorBound = denominatorNorm * (denominatorBound / denominatorNorm) := by
      rewrite [Fraction.Field.mul_comm, Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne']
      rfl
    _ < denominatorNorm * translated.re :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct denominatorPositive quotientStrict
    _ ≤ denominatorNorm * Gaussian.Norm.Basic.normSq translated :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (coordinateLeSquare.trans squareLeNorm) denominatorPositive.le
    _ = _ := factorNorm.symm

/-- The computed translation excludes the affine pole for every nonnegative requested denominator bound. -/
theorem homographyTranslation_poleExcluded (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    {denominatorBound : Fraction.Rational} (nonnegative : 0 ≤ denominatorBound) :
    Homography.Basic.denominator
      (Matrix.map GaussianInt.toGaussian (fraction.homography (fraction.homographyTranslation tail denominatorBound)))
        tail ≠ 0 := by
  have positive := nonnegative.trans_lt (fraction.homographyTranslation_denominator_normSq_gt tail nonnegative)
  intro zero
  rewrite [zero, Gaussian.Norm.Basic.normSq_zero] at positive
  exact not_lt_of_ge (Fraction.Order.Basic.le_refl 0) positive

/-- Compute the denominator payment for a spatial distance request and an additional quadrance floor. -/
@[expose] def placementDenominatorBound (fraction : Reduced)
    (distanceSq denominatorFloor : Fraction.Rational) : Fraction.Rational :=
  1 + 1 / (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator) * distanceSq) + denominatorFloor

/-- Construct one retained integral homography paying the spatial request and denominator floor. -/
@[expose] def placementHomography (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    (distanceSq denominatorFloor : Fraction.Rational) : Matrix GaussianInt :=
  fraction.homography
    (fraction.homographyTranslation tail (fraction.placementDenominatorBound distanceSq denominatorFloor))

/-- A positive spatial request and nonnegative floor produce a positive denominator payment. -/
private theorem placementDenominatorBound_pos (fraction : Reduced)
    {distanceSq denominatorFloor : Fraction.Rational}
    (positive : 0 < distanceSq) (floorNonnegative : 0 ≤ denominatorFloor) :
    0 < fraction.placementDenominatorBound distanceSq denominatorFloor := by
  have denominatorPositive := Fraction.Order.Arithmetic.mul_pos_direct
    (Gaussian.Norm.Basic.normSq_pos fraction.denominatorGaussianNonzero) positive
  have reciprocalPositive := Fraction.Order.Field.div_pos_direct
    (by decide : (0 : Fraction.Rational) < 1) denominatorPositive
  exact ((by decide : (0 : Fraction.Rational) < 1).trans_le
    (le_add_of_nonneg_right reciprocalPositive.le)).trans_le
      (le_add_of_nonneg_right floorNonnegative)

/-- The spatial payment lies strictly below the computed placement denominator bound. -/
private theorem placementDenominatorBound_gt_distance (fraction : Reduced)
    (distanceSq : Fraction.Rational) {denominatorFloor : Fraction.Rational}
    (floorNonnegative : 0 ≤ denominatorFloor) :
    1 / (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator) * distanceSq) <
      fraction.placementDenominatorBound distanceSq denominatorFloor := by
  let cost := 1 / (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator) * distanceSq)
  calc
    cost = 0 + cost := (Fraction.zero_add _).symm
    _ < 1 + cost := Fraction.Order.Arithmetic.add_lt_add_right_direct (by decide) _
    _ ≤ 1 + cost + denominatorFloor := le_add_of_nonneg_right floorNonnegative

/-- The constructed placement homography retains determinant one. -/
theorem placementHomography_determinant (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    (distanceSq denominatorFloor : Fraction.Rational) :
    (fraction.placementHomography tail distanceSq denominatorFloor).determinant = 1 :=
  fraction.homography_determinant _

/-- The constructed placement homography excludes its affine pole at the retained tail. -/
theorem placementHomography_poleExcluded (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    {distanceSq denominatorFloor : Fraction.Rational}
    (positive : 0 < distanceSq) (floorNonnegative : 0 ≤ denominatorFloor) :
    Homography.Basic.denominator
      (Matrix.map GaussianInt.toGaussian (fraction.placementHomography tail distanceSq denominatorFloor)) tail ≠ 0 :=
  fraction.homographyTranslation_poleExcluded tail
    (fraction.placementDenominatorBound_pos positive floorNonnegative).le

/-- The actual denominator quadrance of the placement homography strictly exceeds the requested floor. -/
theorem placementHomography_denominator_normSq_gt (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    {distanceSq denominatorFloor : Fraction.Rational}
    (positive : 0 < distanceSq) (floorNonnegative : 0 ≤ denominatorFloor) :
    denominatorFloor < Gaussian.Norm.Basic.normSq (Homography.Basic.denominator
      (Matrix.map GaussianInt.toGaussian (fraction.placementHomography tail distanceSq denominatorFloor)) tail) := by
  have boundPositive := fraction.placementDenominatorBound_pos positive floorNonnegative
  have denominatorStrict := fraction.homographyTranslation_denominator_normSq_gt tail boundPositive.le
  have reciprocalPositive := Fraction.Order.Field.div_pos_direct
    (by decide : (0 : Fraction.Rational) < 1)
    (Fraction.Order.Arithmetic.mul_pos_direct
      (Gaussian.Norm.Basic.normSq_pos fraction.denominatorGaussianNonzero) positive)
  calc
    denominatorFloor = 0 + denominatorFloor := (Fraction.zero_add _).symm
    _ < (1 + 1 / (Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator) * distanceSq)) +
        denominatorFloor :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        ((by decide : (0 : Fraction.Rational) < 1).trans_le
          (le_add_of_nonneg_right reciprocalPositive.le)) _
    _ < _ := denominatorStrict

/-- The constructed placement homography maps its retained tail strictly within the requested squared distance.

The denominator bound pays the exact displacement identity for the same
matrix, tail and reduced fraction. No limiting point is selected.
-/
theorem placementHomography_distance_lt (fraction : Reduced) (tail : Gaussian.Basic.Canonical)
    {distanceSq denominatorFloor : Fraction.Rational}
    (positive : 0 < distanceSq) (floorNonnegative : 0 ≤ denominatorFloor) :
    Gaussian.Norm.Basic.normSq
      (Homography.Basic.homographic
        (Matrix.map GaussianInt.toGaussian (fraction.placementHomography tail distanceSq denominatorFloor)) tail -
          fraction.value) < distanceSq := by
  let denominator := Homography.Basic.denominator
    (Matrix.map GaussianInt.toGaussian (fraction.placementHomography tail distanceSq denominatorFloor)) tail
  let denominatorNorm := Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian fraction.denominator)
  let displacement := Homography.Basic.homographic
    (Matrix.map GaussianInt.toGaussian (fraction.placementHomography tail distanceSq denominatorFloor)) tail -
      fraction.value
  have poleExcluded := fraction.placementHomography_poleExcluded tail positive floorNonnegative
  have denominatorPositive : 0 < denominatorNorm :=
    Gaussian.Norm.Basic.normSq_pos fraction.denominatorGaussianNonzero
  have sourceDenominatorPositive : 0 < Gaussian.Norm.Basic.normSq denominator :=
    Gaussian.Norm.Basic.normSq_pos poleExcluded
  have distanceFactorPositive : 0 < denominatorNorm * distanceSq :=
    Fraction.Order.Arithmetic.mul_pos_direct denominatorPositive positive
  have denominatorStrict : 1 / (denominatorNorm * distanceSq) < Gaussian.Norm.Basic.normSq denominator :=
    (fraction.placementDenominatorBound_gt_distance distanceSq floorNonnegative).trans
      (fraction.homographyTranslation_denominator_normSq_gt tail
        (fraction.placementDenominatorBound_pos positive floorNonnegative).le)
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct denominatorStrict distanceFactorPositive
  have paid := fraction.homographic_distance_mul_denominator_normSq
    (fraction.homographyTranslation tail (fraction.placementDenominatorBound distanceSq denominatorFloor))
      tail poleExcluded
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := denominatorNorm * Gaussian.Norm.Basic.normSq denominator) _
    (Fraction.Order.Arithmetic.mul_pos_direct denominatorPositive sourceDenominatorPositive)
  calc
    Gaussian.Norm.Basic.normSq displacement * (denominatorNorm * Gaussian.Norm.Basic.normSq denominator) = 1 := paid
    _ = (1 / (denominatorNorm * distanceSq)) * (denominatorNorm * distanceSq) :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ distanceFactorPositive.ne').symm
    _ < Gaussian.Norm.Basic.normSq denominator * (denominatorNorm * distanceSq) := scaled
    _ = distanceSq * (denominatorNorm * Gaussian.Norm.Basic.normSq denominator) := by ring1

end Purelib.Data.GaussianInt.Fraction.Reduced
