module

import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Int.Arithmetic
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.NormalForm
import Purelib.NumberTheory.Approximation.Best.Error

import Purelib.Tactic.QuotientFreeOmega
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite exclusion of repeated coefficient index two

This file continues the finite normal form in `BestApproximation`.  It keeps
the remaining argument in normalized Gaussian-rational coordinates and
records every cylinder alternative explicitly.  No completed complex point,
compactness argument, or unbounded search is used.
-/

public section

namespace Purelib.NumberTheory.Approximation.Best.Consecutive.RepeatedIndex

open Purelib.Data
open Purelib.Data.Rat
open Purelib.NumberTheory.Approximation

open Purelib.Algebra

/-- The Gaussian integer `1 + i`, the canonical coefficient of quadrance two. -/
@[expose] def diagonalStep : GaussianInt := ⟨1, 1⟩

/-- The Gaussian integer `2 + 2i`, the canonical coefficient of quadrance eight. -/
@[expose] def doubledDiagonalStep : GaussianInt := ⟨2, 2⟩

/-- The Gaussian integer `2`, the canonical axial coefficient of quadrance four. -/
@[expose] def doubledAxisStep : GaussianInt := ⟨2, 0⟩

set_option genInjectivity false in
/-- The normalized finite data consumed by the three canonical transition
exclusions. -/
structure NormalizedCylinderData (coefficient : GaussianInt) where
  /-- The smaller error divided by the nonzero reference error. -/ errorRatio : Gaussian.Basic.Canonical
  /-- The lower denominator divided by the nonzero middle denominator. -/ denominatorRatio : Gaussian.Basic.Canonical
  /-- The normalized error lies strictly inside the unit disc. -/ errorInside : Data.Gaussian.Norm.Basic.normSq
    errorRatio < 1
  /-- The normalized error quadrance is strictly greater than one quarter. -/ factorFour : (1 : Fraction.Rational) < 4 *
    Data.Gaussian.Norm.Basic.normSq errorRatio
  /-- The normalized lower denominator lies strictly inside the unit disc. -/ denominatorInside :
    Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1
  /-- The displayed coefficient produces a strictly smaller next error quadrance. -/ errorTransition :
    Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian coefficient * errorRatio) <
      Data.Gaussian.Norm.Basic.normSq errorRatio
  /-- The displayed coefficient produces a next denominator outside the unit disc. -/ denominatorTransition :
    1 < Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian coefficient)
  /-- Every Gaussian unit translate escapes the current mixed cylinder.

Its error quadrance or denominator quadrance is at least two in the normalized coordinates. -/ selfObstruction : ∀ unit
  : GaussianInt, GaussianInt.normNat unit = 1 →
    (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
      2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)
  /-- Every Gaussian unit translate escapes the next mixed cylinder.

The two alternatives use twice the normalized current error quadrance or twice the next denominator quadrance,
  respectively. -/ nextObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
    (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq errorRatio ≤
        Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
      2 * Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian coefficient) ≤
        Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)

constructive_injectivity NormalizedCylinderData

/-- Normalize homogeneous error and denominator coordinates by their two
positive reference quadrances.  Every conclusion is obtained by multiplying
back by the displayed nonzero reference, so the construction uses no choice
of a completed quotient. -/
@[expose] def normalizeCylinderData
    (coefficient : GaussianInt)
    (largeError smallError nextError : Gaussian.Basic.Canonical)
    (lowerDenominator middleDenominator upperDenominator : Gaussian.Basic.Canonical)
    (largeErrorNonzero : largeError ≠ 0)
    (middleDenominatorNonzero : middleDenominator ≠ 0)
    (errorOrdered : Data.Gaussian.Norm.Basic.normSq smallError < Data.Gaussian.Norm.Basic.normSq largeError)
    (nextErrorOrdered : Data.Gaussian.Norm.Basic.normSq nextError < Data.Gaussian.Norm.Basic.normSq smallError)
    (factorFour : Data.Gaussian.Norm.Basic.normSq largeError < 4 * Data.Gaussian.Norm.Basic.normSq smallError)
    (denominatorOrdered :
      Data.Gaussian.Norm.Basic.normSq lowerDenominator < Data.Gaussian.Norm.Basic.normSq middleDenominator)
    (nextDenominatorOrdered :
      Data.Gaussian.Norm.Basic.normSq middleDenominator < Data.Gaussian.Norm.Basic.normSq upperDenominator)
    (errorIdentity :
      nextError = largeError + GaussianInt.toGaussian coefficient * smallError)
    (denominatorIdentity :
      upperDenominator =
        lowerDenominator + GaussianInt.toGaussian coefficient * middleDenominator)
    (selfObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian unit * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq middleDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (middleDenominator -
            GaussianInt.toGaussian unit * lowerDenominator))
    (nextObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq smallError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian unit * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (middleDenominator -
            GaussianInt.toGaussian unit * lowerDenominator)) :
    Best.Consecutive.RepeatedIndex.NormalizedCylinderData coefficient := by
  let errorRatio :=
    smallError * Data.Gaussian.Field.inv largeError
  let denominatorRatio :=
    lowerDenominator *
      Data.Gaussian.Field.inv middleDenominator
  have largeNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq largeError := Gaussian.Norm.Basic.normSq_pos
    largeErrorNonzero
  have middleNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq middleDenominator :=
    Gaussian.Norm.Basic.normSq_pos middleDenominatorNonzero
  have largeNormNonzero : Data.Gaussian.Norm.Basic.normSq largeError ≠ 0 := ne_of_gt largeNormPositive
  have middleNormNonzero : Data.Gaussian.Norm.Basic.normSq middleDenominator ≠ 0 :=
    ne_of_gt middleNormPositive
  have errorRatioNorm :
      Data.Gaussian.Norm.Basic.normSq errorRatio =
        Data.Gaussian.Norm.Basic.normSq smallError * (Data.Gaussian.Norm.Basic.normSq largeError)⁻¹ := by
    dsimp only [errorRatio]
    rw [Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Field.normSq_inv largeError
        largeErrorNonzero]
  have denominatorRatioNorm :
      Data.Gaussian.Norm.Basic.normSq denominatorRatio =
        Data.Gaussian.Norm.Basic.normSq lowerDenominator * (Data.Gaussian.Norm.Basic.normSq middleDenominator)⁻¹
          := by
    dsimp only [denominatorRatio]
    rw [Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Field.normSq_inv middleDenominator
        middleDenominatorNonzero]
  have errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1 := by
    rw [errorRatioNorm]
    change Data.Gaussian.Norm.Basic.normSq smallError / Data.Gaussian.Norm.Basic.normSq largeError < 1
    exact (Fraction.Order.Field.div_lt_iff_pos largeNormPositive).mpr
      (by simpa only [Fraction.Field.one_mul] using errorOrdered)
  have normalizedFactorFour :
      (1 : Fraction.Rational) < 4 * Data.Gaussian.Norm.Basic.normSq errorRatio := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq largeError)
    · calc
        (1 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq largeError = Data.Gaussian.Norm.Basic.normSq
          largeError := by ring1
        _ < 4 * Data.Gaussian.Norm.Basic.normSq smallError := factorFour
        _ = (4 * Data.Gaussian.Norm.Basic.normSq errorRatio) * Data.Gaussian.Norm.Basic.normSq largeError := by
          rw [errorRatioNorm]
          symm
          calc
            (4 * (Data.Gaussian.Norm.Basic.normSq smallError * (Data.Gaussian.Norm.Basic.normSq largeError)⁻¹))
              *
                Data.Gaussian.Norm.Basic.normSq largeError =
                4 * (Data.Gaussian.Norm.Basic.normSq smallError *
                  ((Data.Gaussian.Norm.Basic.normSq largeError)⁻¹ * Data.Gaussian.Norm.Basic.normSq largeError))
                    := by
              rw [Fraction.Field.mul_assoc,
                Fraction.Field.mul_assoc]
            _ = 4 * Data.Gaussian.Norm.Basic.normSq smallError := by
              rw [Fraction.Field.inv_mul_cancel _
                largeNormNonzero]
              ring1
    · exact largeNormPositive
  have denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1 := by
    rw [denominatorRatioNorm]
    change Data.Gaussian.Norm.Basic.normSq lowerDenominator / Data.Gaussian.Norm.Basic.normSq middleDenominator
      < 1
    exact (Fraction.Order.Field.div_lt_iff_pos middleNormPositive).mpr
      (by
        simpa only [Fraction.Field.one_mul] using
          denominatorOrdered)
  have errorRatioCancel : errorRatio * largeError = smallError := by
    dsimp only [errorRatio]
    rw [Gaussian.Basic.mul_assoc, Gaussian.Field.inv_mul largeError largeErrorNonzero, Gaussian.Basic.mul_one]
  have denominatorRatioCancel :
      denominatorRatio * middleDenominator = lowerDenominator := by
    dsimp only [denominatorRatio]
    rw [Gaussian.Basic.mul_assoc, Gaussian.Field.inv_mul middleDenominator middleDenominatorNonzero,
      Gaussian.Basic.mul_one]
  have normalizedErrorIdentity :
      nextError * Data.Gaussian.Field.inv largeError =
        1 + GaussianInt.toGaussian coefficient * errorRatio := by
    calc
      nextError * Data.Gaussian.Field.inv largeError =
          (largeError + GaussianInt.toGaussian coefficient * smallError) *
            Data.Gaussian.Field.inv largeError := by
        rw [errorIdentity]
      _ = largeError * Data.Gaussian.Field.inv largeError +
          (GaussianInt.toGaussian coefficient * smallError) *
            Data.Gaussian.Field.inv largeError :=
        Gaussian.Basic.right_distrib _ _ _
      _ = 1 + GaussianInt.toGaussian coefficient * errorRatio := by
        rw [Gaussian.Field.mul_inv largeError
          largeErrorNonzero]
        dsimp only [errorRatio]
        rw [Gaussian.Basic.mul_assoc]
  have normalizedDenominatorIdentity :
      upperDenominator *
          Data.Gaussian.Field.inv middleDenominator =
        denominatorRatio + GaussianInt.toGaussian coefficient := by
    calc
      upperDenominator *
          Data.Gaussian.Field.inv middleDenominator =
          (lowerDenominator +
              GaussianInt.toGaussian coefficient * middleDenominator) *
            Data.Gaussian.Field.inv middleDenominator := by
        rw [denominatorIdentity]
      _ = lowerDenominator *
            Data.Gaussian.Field.inv middleDenominator +
          (GaussianInt.toGaussian coefficient * middleDenominator) *
            Data.Gaussian.Field.inv middleDenominator :=
        Gaussian.Basic.right_distrib _ _ _
      _ = denominatorRatio + GaussianInt.toGaussian coefficient := by
        dsimp only [denominatorRatio]
        rw [Gaussian.Basic.mul_assoc,
          Gaussian.Field.mul_inv middleDenominator
            middleDenominatorNonzero,
          Gaussian.Basic.mul_one]
  have normalizedErrorTransition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian coefficient * errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio := by
    rw [← normalizedErrorIdentity, errorRatioNorm, Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Field.normSq_inv largeError
        largeErrorNonzero]
    exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      nextErrorOrdered
      (Fraction.Order.Field.inv_pos_direct largeNormPositive)
  have normalizedDenominatorTransition :
      1 < Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian coefficient) := by
    rw [← normalizedDenominatorIdentity, Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Field.normSq_inv middleDenominator
        middleDenominatorNonzero]
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq middleDenominator)
    · calc
        (1 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq middleDenominator =
            Data.Gaussian.Norm.Basic.normSq middleDenominator := by ring1
        _ < Data.Gaussian.Norm.Basic.normSq upperDenominator := nextDenominatorOrdered
        _ =
            (Data.Gaussian.Norm.Basic.normSq upperDenominator * (Data.Gaussian.Norm.Basic.normSq
              middleDenominator)⁻¹) *
              Data.Gaussian.Norm.Basic.normSq middleDenominator := by
          symm
          calc
            (Data.Gaussian.Norm.Basic.normSq upperDenominator * (Data.Gaussian.Norm.Basic.normSq
              middleDenominator)⁻¹) *
                Data.Gaussian.Norm.Basic.normSq middleDenominator =
                Data.Gaussian.Norm.Basic.normSq upperDenominator *
                  ((Data.Gaussian.Norm.Basic.normSq middleDenominator)⁻¹ *
                    Data.Gaussian.Norm.Basic.normSq middleDenominator) :=
              Fraction.Field.mul_assoc _ _ _
            _ = Data.Gaussian.Norm.Basic.normSq upperDenominator := by
              rw [Fraction.Field.inv_mul_cancel _
                middleNormNonzero]
              ring1
    · exact middleNormPositive
  refine
    { errorRatio := errorRatio
      denominatorRatio := denominatorRatio
      errorInside := errorInside
      factorFour := normalizedFactorFour
      denominatorInside := denominatorInside
      errorTransition := normalizedErrorTransition
      denominatorTransition := normalizedDenominatorTransition
      selfObstruction := ?_
      nextObstruction := ?_ }
  · intro unit unitNorm
    rcases selfObstruction unit unitNorm with
      errorExterior | denominatorExterior
    · left
      let normalizedDifference := errorRatio - GaussianInt.toGaussian unit
      have scaledDifference :
          normalizedDifference * largeError =
            smallError - GaussianInt.toGaussian unit * largeError := by
        calc
          normalizedDifference * largeError =
              errorRatio * largeError - GaussianInt.toGaussian unit * largeError := by
            dsimp only [normalizedDifference]
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im] <;>
              ring1
          _ = smallError - GaussianInt.toGaussian unit * largeError := by
            rw [errorRatioCancel]
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := Data.Gaussian.Norm.Basic.normSq largeError)
      · calc
          (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq largeError ≤
              Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian unit * largeError) :=
            errorExterior
          _ = Data.Gaussian.Norm.Basic.normSq normalizedDifference * Data.Gaussian.Norm.Basic.normSq largeError
            := by
            rw [← scaledDifference, Gaussian.Norm.Basic.normSq_mul]
      · exact largeNormPositive
    · right
      let normalizedDifference :=
        (1 : Gaussian.Basic.Canonical) - GaussianInt.toGaussian unit * denominatorRatio
      have scaledDifference :
          normalizedDifference * middleDenominator =
            middleDenominator - GaussianInt.toGaussian unit * lowerDenominator := by
        calc
          normalizedDifference * middleDenominator =
              middleDenominator -
                GaussianInt.toGaussian unit *
                  (denominatorRatio * middleDenominator) := by
            dsimp only [normalizedDifference]
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im,
                Gaussian.Basic.one_re,
                Gaussian.Basic.one_im] <;>
              ring1
          _ = middleDenominator - GaussianInt.toGaussian unit * lowerDenominator := by
            rw [denominatorRatioCancel]
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := Data.Gaussian.Norm.Basic.normSq middleDenominator)
      · calc
          (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq middleDenominator ≤
              Data.Gaussian.Norm.Basic.normSq (middleDenominator -
                GaussianInt.toGaussian unit * lowerDenominator) := denominatorExterior
          _ = Data.Gaussian.Norm.Basic.normSq normalizedDifference * Data.Gaussian.Norm.Basic.normSq
            middleDenominator := by
            rw [← scaledDifference, Gaussian.Norm.Basic.normSq_mul]
      · exact middleNormPositive
  · intro unit unitNorm
    rcases nextObstruction unit unitNorm with
      errorExterior | denominatorExterior
    · left
      let normalizedDifference := errorRatio - GaussianInt.toGaussian unit
      have scaledDifference :
          normalizedDifference * largeError =
            smallError - GaussianInt.toGaussian unit * largeError := by
        calc
          normalizedDifference * largeError =
              errorRatio * largeError - GaussianInt.toGaussian unit * largeError := by
            dsimp only [normalizedDifference]
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im] <;>
              ring1
          _ = smallError - GaussianInt.toGaussian unit * largeError := by
            rw [errorRatioCancel]
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := Data.Gaussian.Norm.Basic.normSq largeError)
      · calc
          ((2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq errorRatio) *
            Data.Gaussian.Norm.Basic.normSq largeError =
              2 * Data.Gaussian.Norm.Basic.normSq smallError := by
            rw [errorRatioNorm]
            calc
              (2 * (Data.Gaussian.Norm.Basic.normSq smallError * (Data.Gaussian.Norm.Basic.normSq
                largeError)⁻¹)) *
                  Data.Gaussian.Norm.Basic.normSq largeError =
                  2 * (Data.Gaussian.Norm.Basic.normSq smallError *
                    ((Data.Gaussian.Norm.Basic.normSq largeError)⁻¹ * Data.Gaussian.Norm.Basic.normSq
                      largeError)) := by
                rw [Fraction.Field.mul_assoc,
                  Fraction.Field.mul_assoc]
              _ = 2 * Data.Gaussian.Norm.Basic.normSq smallError := by
                rw [Fraction.Field.inv_mul_cancel _
                  largeNormNonzero]
                ring1
          _ ≤ Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian unit * largeError) :=
            errorExterior
          _ = Data.Gaussian.Norm.Basic.normSq normalizedDifference * Data.Gaussian.Norm.Basic.normSq largeError
            := by
            rw [← scaledDifference, Gaussian.Norm.Basic.normSq_mul]
      · exact largeNormPositive
    · right
      let normalizedDifference :=
        (1 : Gaussian.Basic.Canonical) - GaussianInt.toGaussian unit * denominatorRatio
      have scaledDifference :
          normalizedDifference * middleDenominator =
            middleDenominator - GaussianInt.toGaussian unit * lowerDenominator := by
        calc
          normalizedDifference * middleDenominator =
              middleDenominator -
                GaussianInt.toGaussian unit *
                  (denominatorRatio * middleDenominator) := by
            dsimp only [normalizedDifference]
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im,
                Gaussian.Basic.one_re,
                Gaussian.Basic.one_im] <;>
              ring1
          _ = middleDenominator - GaussianInt.toGaussian unit * lowerDenominator := by
            rw [denominatorRatioCancel]
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := Data.Gaussian.Norm.Basic.normSq middleDenominator)
      · calc
          (2 * Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian coefficient)) *
              Data.Gaussian.Norm.Basic.normSq middleDenominator =
              2 * Data.Gaussian.Norm.Basic.normSq upperDenominator := by
            rw [← normalizedDenominatorIdentity, Gaussian.Norm.Basic.normSq_mul,
              Gaussian.Field.normSq_inv middleDenominator
                middleDenominatorNonzero]
            calc
              (2 * (Data.Gaussian.Norm.Basic.normSq upperDenominator *
                    (Data.Gaussian.Norm.Basic.normSq middleDenominator)⁻¹)) *
                  Data.Gaussian.Norm.Basic.normSq middleDenominator =
                  2 * (Data.Gaussian.Norm.Basic.normSq upperDenominator *
                    ((Data.Gaussian.Norm.Basic.normSq middleDenominator)⁻¹ *
                      Data.Gaussian.Norm.Basic.normSq middleDenominator)) := by
                rw [Fraction.Field.mul_assoc,
                  Fraction.Field.mul_assoc]
              _ = 2 * Data.Gaussian.Norm.Basic.normSq upperDenominator := by
                rw [Fraction.Field.inv_mul_cancel _
                  middleNormNonzero]
                ring1
          _ ≤ Data.Gaussian.Norm.Basic.normSq (middleDenominator -
              GaussianInt.toGaussian unit * lowerDenominator) := denominatorExterior
          _ = Data.Gaussian.Norm.Basic.normSq normalizedDifference * Data.Gaussian.Norm.Basic.normSq
            middleDenominator := by
            rw [← scaledDifference, Gaussian.Norm.Basic.normSq_mul]
      · exact middleNormPositive

/-- A finite Gaussian-unit certificate carries quadrance one. -/
theorem normNat_eq_one_of_isGaussianUnit {unit : GaussianInt}
    (property : GaussianInt.Norm.Small.IsGaussianUnit unit) :
    GaussianInt.normNat unit = 1 := by
  have quadrance :=
    GaussianInt.Norm.Small.normSq_toGaussian_eq_one_of_isGaussianUnit property
  rw [GaussianInt.normSq_toGaussian] at quadrance
  exact Fraction.Cast.Compatibility.natCast_injective_direct quadrance

/-- Transport normalized data through a displayed Gaussian-unit associate.
The error ratio rotates by the associate and the denominator ratio by its
displayed conjugate inverse; all four unit tests are merely permuted. -/
@[expose] def transportNormalizedData
    (coefficient canonical associate : GaussianInt)
    (associateProperty : GaussianInt.Norm.Small.IsGaussianUnit associate)
    (associated : coefficient = canonical * associate)
    (data : Best.Consecutive.RepeatedIndex.NormalizedCylinderData coefficient) :
    Best.Consecutive.RepeatedIndex.NormalizedCylinderData canonical := by
  let inverseAssociate := GaussianInt.Norm.Basic.conjugate associate
  let associateValue := GaussianInt.toGaussian associate
  let inverseAssociateValue := GaussianInt.toGaussian inverseAssociate
  let errorRatio := associateValue * data.errorRatio
  let denominatorRatio := inverseAssociateValue * data.denominatorRatio
  have associateNorm : GaussianInt.normNat associate = 1 :=
    Best.Consecutive.RepeatedIndex.normNat_eq_one_of_isGaussianUnit associateProperty
  have inverseAssociateNorm : GaussianInt.normNat inverseAssociate = 1 := by
    dsimp only [inverseAssociate]
    rw [GaussianInt.Embedding.normNat_conjugate, associateNorm]
  have associateQuadrance : Data.Gaussian.Norm.Basic.normSq associateValue = (1 : Fraction.Rational) := by
    dsimp only [associateValue]
    rw [GaussianInt.normSq_toGaussian, associateNorm]
    rfl
  have inverseAssociateQuadrance :
      Data.Gaussian.Norm.Basic.normSq inverseAssociateValue = (1 : Fraction.Rational) := by
    dsimp only [inverseAssociateValue]
    rw [GaussianInt.normSq_toGaussian, inverseAssociateNorm]
    rfl
  have associateInverseInteger : associate * inverseAssociate = 1 := by
    dsimp only [inverseAssociate]
    exact GaussianInt.Norm.Small.self_mul_conjugate_of_isGaussianUnit
      associateProperty
  have associateInverse :
      associateValue * inverseAssociateValue = (1 : Gaussian.Basic.Canonical) := by
    dsimp only [associateValue, inverseAssociateValue]
    rw [← GaussianInt.toGaussian_mul, associateInverseInteger, GaussianInt.toGaussian_one]
  have errorRatioNorm : Data.Gaussian.Norm.Basic.normSq errorRatio = Data.Gaussian.Norm.Basic.normSq
    data.errorRatio := by
    dsimp only [errorRatio]
    rw [Gaussian.Norm.Basic.normSq_mul, associateQuadrance]
    ring1
  have denominatorRatioNorm :
      Data.Gaussian.Norm.Basic.normSq denominatorRatio = Data.Gaussian.Norm.Basic.normSq data.denominatorRatio
        := by
    dsimp only [denominatorRatio]
    rw [Gaussian.Norm.Basic.normSq_mul, inverseAssociateQuadrance]
    ring1
  have coefficientValue :
      GaussianInt.toGaussian coefficient = GaussianInt.toGaussian canonical * associateValue := by
    dsimp only [associateValue]
    rw [associated, GaussianInt.toGaussian_mul]
  have errorTransitionIdentity :
      1 + GaussianInt.toGaussian canonical * errorRatio =
        1 + GaussianInt.toGaussian coefficient * data.errorRatio := by
    dsimp only [errorRatio]
    rw [coefficientValue,
      Gaussian.Basic.mul_assoc]
  have denominatorTransitionIdentity :
      associateValue *
          (denominatorRatio + GaussianInt.toGaussian canonical) =
        data.denominatorRatio + GaussianInt.toGaussian coefficient := by
    calc
      associateValue *
          (denominatorRatio + GaussianInt.toGaussian canonical) =
          associateValue * denominatorRatio +
            associateValue * GaussianInt.toGaussian canonical :=
        Gaussian.Basic.left_distrib _ _ _
      _ = (associateValue * inverseAssociateValue) *
            data.denominatorRatio +
          GaussianInt.toGaussian canonical * associateValue := by
        dsimp only [denominatorRatio]
        rw [Gaussian.Basic.mul_assoc,
          Gaussian.Basic.mul_comm associateValue
            (GaussianInt.toGaussian canonical)]
      _ = data.denominatorRatio + GaussianInt.toGaussian coefficient := by
        rw [associateInverse, Gaussian.Basic.one_mul,
          ← coefficientValue]
  have denominatorTransitionNorm :
      Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian canonical) =
        Data.Gaussian.Norm.Basic.normSq (data.denominatorRatio + GaussianInt.toGaussian coefficient) := by
    have normIdentity := congrArg Data.Gaussian.Norm.Basic.normSq denominatorTransitionIdentity
    rw [Gaussian.Norm.Basic.normSq_mul, associateQuadrance] at normIdentity
    simpa only [Fraction.Field.one_mul] using normIdentity
  refine
    { errorRatio := errorRatio
      denominatorRatio := denominatorRatio
      errorInside := by rw [errorRatioNorm]; exact data.errorInside
      factorFour := by rw [errorRatioNorm]; exact data.factorFour
      denominatorInside := by
        rw [denominatorRatioNorm]
        exact data.denominatorInside
      errorTransition := by
        rw [errorTransitionIdentity, errorRatioNorm]
        exact data.errorTransition
      denominatorTransition := by
        rw [denominatorTransitionNorm]
        exact data.denominatorTransition
      selfObstruction := ?_
      nextObstruction := ?_ }
  · intro unit unitNorm
    let sourceUnit := inverseAssociate * unit
    have sourceUnitNorm : GaussianInt.normNat sourceUnit = 1 := by
      dsimp only [sourceUnit]
      rw [GaussianInt.Embedding.normNat_mul, inverseAssociateNorm, unitNorm]
    have sourceUnitValue :
        GaussianInt.toGaussian sourceUnit = inverseAssociateValue * GaussianInt.toGaussian unit := by
      dsimp only [sourceUnit, inverseAssociateValue]
      rw [GaussianInt.toGaussian_mul]
    have rotatedSourceUnit :
        associateValue * GaussianInt.toGaussian sourceUnit = GaussianInt.toGaussian unit := by
      calc
        associateValue * GaussianInt.toGaussian sourceUnit =
            associateValue *
              (inverseAssociateValue * GaussianInt.toGaussian unit) := by
          rw [sourceUnitValue]
        _ = (associateValue * inverseAssociateValue) * GaussianInt.toGaussian unit :=
          (Gaussian.Basic.mul_assoc _ _ _).symm
        _ = GaussianInt.toGaussian unit := by
          rw [associateInverse, Gaussian.Basic.one_mul]
    rcases data.selfObstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
    · left
      have differenceIdentity :
          errorRatio - GaussianInt.toGaussian unit =
            associateValue *
              (data.errorRatio - GaussianInt.toGaussian sourceUnit) := by
        calc
          errorRatio - GaussianInt.toGaussian unit =
              associateValue * data.errorRatio -
                associateValue * GaussianInt.toGaussian sourceUnit := by
            dsimp only [errorRatio]
            rw [rotatedSourceUnit]
          _ = associateValue *
              (data.errorRatio - GaussianInt.toGaussian sourceUnit) := by
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im] <;>
              ring1
      rw [differenceIdentity, Gaussian.Norm.Basic.normSq_mul, associateQuadrance]
      simpa only [Fraction.Field.one_mul] using errorExterior
    · right
      have differenceIdentity :
          (1 : Gaussian.Basic.Canonical) - GaussianInt.toGaussian unit * denominatorRatio =
            1 - GaussianInt.toGaussian sourceUnit * data.denominatorRatio := by
        dsimp only [denominatorRatio]
        rw [sourceUnitValue]
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
      rw [differenceIdentity]
      exact denominatorExterior
  · intro unit unitNorm
    let sourceUnit := inverseAssociate * unit
    have sourceUnitNorm : GaussianInt.normNat sourceUnit = 1 := by
      dsimp only [sourceUnit]
      rw [GaussianInt.Embedding.normNat_mul, inverseAssociateNorm, unitNorm]
    have sourceUnitValue :
        GaussianInt.toGaussian sourceUnit = inverseAssociateValue * GaussianInt.toGaussian unit := by
      dsimp only [sourceUnit, inverseAssociateValue]
      rw [GaussianInt.toGaussian_mul]
    have rotatedSourceUnit :
        associateValue * GaussianInt.toGaussian sourceUnit = GaussianInt.toGaussian unit := by
      calc
        associateValue * GaussianInt.toGaussian sourceUnit =
            associateValue *
              (inverseAssociateValue * GaussianInt.toGaussian unit) := by
          rw [sourceUnitValue]
        _ = (associateValue * inverseAssociateValue) * GaussianInt.toGaussian unit :=
          (Gaussian.Basic.mul_assoc _ _ _).symm
        _ = GaussianInt.toGaussian unit := by
          rw [associateInverse, Gaussian.Basic.one_mul]
    rcases data.nextObstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
    · left
      have differenceIdentity :
          errorRatio - GaussianInt.toGaussian unit =
            associateValue *
              (data.errorRatio - GaussianInt.toGaussian sourceUnit) := by
        calc
          errorRatio - GaussianInt.toGaussian unit =
              associateValue * data.errorRatio -
                associateValue * GaussianInt.toGaussian sourceUnit := by
            dsimp only [errorRatio]
            rw [rotatedSourceUnit]
          _ = associateValue *
              (data.errorRatio - GaussianInt.toGaussian sourceUnit) := by
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im] <;>
              ring1
      rw [errorRatioNorm, differenceIdentity, Gaussian.Norm.Basic.normSq_mul,
        associateQuadrance]
      simpa only [Fraction.Field.one_mul] using errorExterior
    · right
      have differenceIdentity :
          (1 : Gaussian.Basic.Canonical) - GaussianInt.toGaussian unit * denominatorRatio =
            1 - GaussianInt.toGaussian sourceUnit * data.denominatorRatio := by
        dsimp only [denominatorRatio]
        rw [sourceUnitValue]
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
      rw [denominatorTransitionNorm, differenceIdentity]
      exact denominatorExterior

/-- Every quadrance-two coefficient is a displayed unit associate of the
canonical diagonal coefficient `1+i`. -/
theorem exists_unit_associate_of_normNat_eq_two
    (coefficient : GaussianInt) (coefficientNorm : GaussianInt.normNat coefficient = 2) :
    ∃ associate, GaussianInt.Norm.Small.IsGaussianUnit associate ∧
      coefficient = Best.Consecutive.RepeatedIndex.diagonalStep * associate := by
  have coefficientDiagonal :=
    GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two coefficientNorm
  have canonicalDiagonal :
      GaussianInt.Norm.Small.IsDiagonal Best.Consecutive.RepeatedIndex.diagonalStep := Or.inl rfl
  exact GaussianInt.Norm.Small.exists_unit_right_factor_of_diagonals
    coefficientDiagonal canonicalDiagonal

/-- Every quadrance-four coefficient is a displayed unit associate of the
canonical axial coefficient `2`. -/
theorem exists_unit_associate_of_normNat_eq_four
    (coefficient : GaussianInt) (coefficientNorm : GaussianInt.normNat coefficient = 4) :
    ∃ associate, GaussianInt.Norm.Small.IsGaussianUnit associate ∧
      coefficient = Best.Consecutive.RepeatedIndex.doubledAxisStep * associate := by
  rcases GaussianInt.Norm.Small.axisDouble_cases_of_normNat_eq_four
      coefficientNorm with
    coefficientCase | coefficientCase | coefficientCase | coefficientCase
  · exact ⟨1, Or.inl rfl, coefficientCase⟩
  · exact ⟨-1, Or.inr (Or.inl rfl), by
      rw [coefficientCase]
      decide⟩
  · exact ⟨GaussianInt.Norm.Small.imaginaryUnit,
      Or.inr (Or.inr (Or.inl rfl)), by
        rw [coefficientCase]
        decide⟩
  · exact ⟨-GaussianInt.Norm.Small.imaginaryUnit,
      Or.inr (Or.inr (Or.inr rfl)), by
        rw [coefficientCase]
        decide⟩

/-- The four Gaussian integers of quadrance eight are precisely the doubled
diagonals.  This is a bounded coordinate case split. -/
theorem doubledDiagonal_cases_of_normNat_eq_eight
    {coefficient : GaussianInt} (coefficientNorm : GaussianInt.normNat coefficient = 8) :
    coefficient = ⟨2, 2⟩ ∨ coefficient = ⟨2, -2⟩ ∨
      coefficient = ⟨-2, 2⟩ ∨ coefficient = ⟨-2, -2⟩ :=
  GaussianInt.Norm.Small.doubledDiagonal_cases_of_normNat_eq_eight
    coefficientNorm

/-- Every quadrance-eight coefficient is a displayed unit associate of the
canonical doubled diagonal coefficient `2+2i`. -/
theorem exists_unit_associate_of_normNat_eq_eight
    (coefficient : GaussianInt) (coefficientNorm : GaussianInt.normNat coefficient = 8) :
    ∃ associate, GaussianInt.Norm.Small.IsGaussianUnit associate ∧
      coefficient = Best.Consecutive.RepeatedIndex.doubledDiagonalStep * associate := by
  rcases Best.Consecutive.RepeatedIndex.doubledDiagonal_cases_of_normNat_eq_eight coefficientNorm with
    coefficientCase | coefficientCase | coefficientCase | coefficientCase
  · exact ⟨1, Or.inl rfl, coefficientCase⟩
  · exact ⟨-GaussianInt.Norm.Small.imaginaryUnit,
      Or.inr (Or.inr (Or.inr rfl)), by
        rw [coefficientCase]
        decide⟩
  · exact ⟨GaussianInt.Norm.Small.imaginaryUnit,
      Or.inr (Or.inr (Or.inl rfl)), by
        rw [coefficientCase]
        decide⟩
  · exact ⟨-1, Or.inr (Or.inl rfl), by
      rw [coefficientCase]
      decide⟩

/-- The parallelogram identity in the exact Gaussian-rational coordinate
model. -/
theorem normSq_sub_add_parallelogram (left right : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (left - right) + Data.Gaussian.Norm.Basic.normSq (left + right) =
      2 * (Data.Gaussian.Norm.Basic.normSq left + Data.Gaussian.Norm.Basic.normSq right) := by
  dsimp only [Data.Gaussian.Norm.Basic.normSq]
  simp only [Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im,
    Gaussian.Basic.add_re,
    Gaussian.Basic.add_im]
  ring1

/-- A coordinate of a Gaussian rational in the open unit disc is strictly
larger than minus one. -/
theorem neg_one_lt_coordinate_of_square_lt_one {value : Fraction.Rational}
    (small : value ^ 2 < 1) : -1 < value := by
  have lower : (-1 : Fraction.Rational) ≤ value :=
    Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct
      (show (0 : Fraction.Rational) ≤ 1 by decide) small.le
  refine ⟨lower, ?_⟩
  intro reverse
  have equal : value = -1 := le_antisymm reverse lower
  rw [equal] at small
  exact (not_lt_of_ge (show (1 : Fraction.Rational) ≤ 1 by decide) small)

/-- A rational coordinate whose square is below one is strictly below one. -/
theorem coordinate_lt_one_of_square_lt_one {value : Fraction.Rational}
    (small : value ^ 2 < 1) : value < 1 := by
  have upper : value ≤ (1 : Fraction.Rational) :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
      (show (0 : Fraction.Rational) ≤ 1 by decide) small.le
  refine ⟨upper, ?_⟩
  intro reverse
  have equal : value = 1 := le_antisymm upper reverse
  rw [equal] at small
  exact (not_lt_of_ge (show (1 : Fraction.Rational) ≤ 1 by decide) small)

/-- The real coordinate square is below one inside the open Gaussian unit disc. -/
theorem real_square_lt_one_of_normSq_lt_one {value : Gaussian.Basic.Canonical}
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1) : value.re ^ 2 < 1 :=
  (le_add_of_nonneg_right
    (Fraction.Order.Arithmetic.sq_nonneg_direct value.im)).trans_lt inside

/-- The imaginary coordinate square is below one inside the open Gaussian unit disc. -/
theorem imaginary_square_lt_one_of_normSq_lt_one {value : Gaussian.Basic.Canonical}
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1) : value.im ^ 2 < 1 := by
  have reordered : value.im ^ 2 + value.re ^ 2 < 1 := by
    calc
      value.im ^ 2 + value.re ^ 2 = Data.Gaussian.Norm.Basic.normSq value := by
        dsimp only [Data.Gaussian.Norm.Basic.normSq]
        ring1
      _ < 1 := inside
  exact (le_add_of_nonneg_right
    (Fraction.Order.Arithmetic.sq_nonneg_direct value.re)).trans_lt reordered

/-- The real coordinate is above minus one inside the open Gaussian unit disc. -/
theorem neg_one_lt_real_of_normSq_lt_one {value : Gaussian.Basic.Canonical}
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1) : -1 < value.re :=
  Best.Consecutive.RepeatedIndex.neg_one_lt_coordinate_of_square_lt_one
    (Best.Consecutive.RepeatedIndex.real_square_lt_one_of_normSq_lt_one inside)

/-- The imaginary coordinate is above minus one inside the open Gaussian unit disc. -/
theorem neg_one_lt_imaginary_of_normSq_lt_one {value : Gaussian.Basic.Canonical}
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1) : -1 < value.im :=
  Best.Consecutive.RepeatedIndex.neg_one_lt_coordinate_of_square_lt_one
    (Best.Consecutive.RepeatedIndex.imaginary_square_lt_one_of_normSq_lt_one inside)

/-- The real coordinate is below one inside the open Gaussian unit disc. -/
theorem real_lt_one_of_normSq_lt_one {value : Gaussian.Basic.Canonical}
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1) : value.re < 1 :=
  Best.Consecutive.RepeatedIndex.coordinate_lt_one_of_square_lt_one
    (Best.Consecutive.RepeatedIndex.real_square_lt_one_of_normSq_lt_one inside)

/-- The imaginary coordinate is below one inside the open Gaussian unit disc. -/
theorem imaginary_lt_one_of_normSq_lt_one {value : Gaussian.Basic.Canonical}
    (inside : Data.Gaussian.Norm.Basic.normSq value < 1) : value.im < 1 :=
  Best.Consecutive.RepeatedIndex.coordinate_lt_one_of_square_lt_one
    (Best.Consecutive.RepeatedIndex.imaginary_square_lt_one_of_normSq_lt_one inside)

/-- The self-cylinder alternatives for opposite units must cross: one unit
escapes through the error coordinate and the opposite unit through the
denominator coordinate. -/
theorem opposite_self_obstructions_cross
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1)
    (unitObstruction :
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio))
    (oppositeObstruction :
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-unit)) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (-unit) * denominatorRatio)) :
    ((2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∧
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (-unit) * denominatorRatio)) ∨
      ((2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit *
        denominatorRatio) ∧
        2 ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-unit))) := by
  have unitQuadrance : Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit) = (1 : Fraction.Rational) := by
    rw [GaussianInt.normSq_toGaussian, unitNorm]
    rfl
  have negatedUnitIdentity : GaussianInt.toGaussian (-unit) = -GaussianInt.toGaussian unit :=
    GaussianInt.toGaussian_neg unit
  have errorParallelogram :
      Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) +
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-unit)) =
        2 * (1 + Data.Gaussian.Norm.Basic.normSq errorRatio) := by
    rw [negatedUnitIdentity]
    have plusIdentity :
        errorRatio - -GaussianInt.toGaussian unit = errorRatio + GaussianInt.toGaussian unit := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im] <;>
        ring1
    rw [plusIdentity, Best.Consecutive.RepeatedIndex.normSq_sub_add_parallelogram, unitQuadrance]
    ring1
  have errorNotBoth :
      ¬ ((2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∧
        2 ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-unit))) := by
    intro both
    exact Best.Consecutive.NormalForm.not_both_opposite_exterior errorInside
      both.1 both.2 errorParallelogram
  have multipliedRatioQuadrance :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit * denominatorRatio) =
        Data.Gaussian.Norm.Basic.normSq denominatorRatio := by
    rw [Gaussian.Norm.Basic.normSq_mul, unitQuadrance]
    ring1
  have denominatorParallelogram :
      Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio) +
          Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (-unit) * denominatorRatio) =
        2 * (1 + Data.Gaussian.Norm.Basic.normSq denominatorRatio) := by
    rw [negatedUnitIdentity]
    have plusIdentity :
        (1 : Gaussian.Basic.Canonical) - -GaussianInt.toGaussian unit * denominatorRatio =
          1 + GaussianInt.toGaussian unit * denominatorRatio := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im] <;>
        ring1
    rw [plusIdentity, Best.Consecutive.RepeatedIndex.normSq_sub_add_parallelogram,
      multipliedRatioQuadrance, Gaussian.Norm.Basic.normSq_one]
  have denominatorNotBoth :
      ¬ ((2 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio) ∧
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian (-unit) * denominatorRatio)) := by
    intro both
    exact Best.Consecutive.NormalForm.not_both_opposite_exterior
      denominatorInside both.1 both.2 denominatorParallelogram
  rcases unitObstruction with unitError | unitDenominator
  · rcases oppositeObstruction with oppositeError | oppositeDenominator
    · exact (errorNotBoth ⟨unitError, oppositeError⟩).elim
    · exact Or.inl ⟨unitError, oppositeDenominator⟩
  · rcases oppositeObstruction with oppositeError | oppositeDenominator
    · exact Or.inr ⟨unitDenominator, oppositeError⟩
    · exact (denominatorNotBoth
        ⟨unitDenominator, oppositeDenominator⟩).elim

/-- For the `1+i` transition, the `-1` error translate cannot reach the
self-cylinder boundary. -/
theorem diagonalStep_negativeOne_error_impossible
    (errorRatio : Gaussian.Basic.Canonical) (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (transition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.diagonalStep *
        errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio) :
    ¬ (2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq errorRatio
  have transitionExpanded :
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := Fraction.Order.Arithmetic.sub_neg_direct transition
    calc
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) =
          Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.diagonalStep *
            errorRatio) -
            Data.Gaussian.Norm.Basic.normSq errorRatio := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.diagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Fraction.Rational) ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      (2 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) := exterior
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have twiceGapNegative :
      2 - 2 * errorRatio.im < (0 : Fraction.Rational) := by
    calc
      2 - 2 * errorRatio.im ≤
          (1 + quadrance + 2 * errorRatio.re) -
            2 * errorRatio.im := by
        convert Fraction.Order.Arithmetic.add_le_add_right_direct
          exteriorExpanded (-2 * errorRatio.im) using 1 <;> ring1
      _ = 1 + quadrance +
          2 * (errorRatio.re - errorRatio.im) := by ring1
      _ < 0 := transitionExpanded
  have twiceOrdered : (2 : Fraction.Rational) < 2 * errorRatio.im := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      twiceGapNegative (2 * errorRatio.im)
    convert shifted using 1
    all_goals ring1
  have imaginaryGreaterThanOne : (1 : Fraction.Rational) < errorRatio.im := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  exact (not_lt_of_ge (Best.Consecutive.RepeatedIndex.imaginary_lt_one_of_normSq_lt_one errorInside).le)
    imaginaryGreaterThanOne

/-- For the `1+i` transition, the `i` error translate cannot reach the
self-cylinder boundary. -/
theorem diagonalStep_positiveImaginary_error_impossible
    (errorRatio : Gaussian.Basic.Canonical) (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (transition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.diagonalStep *
        errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio) :
    ¬ (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
      (errorRatio - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq errorRatio
  have transitionExpanded :
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := Fraction.Order.Arithmetic.sub_neg_direct transition
    calc
      1 + quadrance + 2 * (errorRatio.re - errorRatio.im) =
          Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.diagonalStep *
            errorRatio) -
            Data.Gaussian.Norm.Basic.normSq errorRatio := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.diagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Fraction.Rational) ≤ 1 + quadrance - 2 * errorRatio.im := by
    calc
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
          (errorRatio -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) := exterior
      _ = 1 + quadrance - 2 * errorRatio.im := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
          GaussianInt.Norm.Small.imaginaryUnit]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have twiceSumNegative :
      2 + 2 * errorRatio.re < (0 : Fraction.Rational) := by
    calc
      2 + 2 * errorRatio.re ≤
          (1 + quadrance - 2 * errorRatio.im) +
            2 * errorRatio.re := by
        exact Fraction.Order.Arithmetic.add_le_add_right_direct
          exteriorExpanded (2 * errorRatio.re)
      _ = 1 + quadrance +
          2 * (errorRatio.re - errorRatio.im) := by ring1
      _ < 0 := transitionExpanded
  have twiceOrdered :
      (2 : Fraction.Rational) < 2 * (-errorRatio.re) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      twiceSumNegative (-2 * errorRatio.re)
    convert shifted using 1
    all_goals ring1
  have negativeRealGreaterThanOne :
      (1 : Fraction.Rational) < -errorRatio.re := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  have realLessThanNegativeOne : errorRatio.re < (-1 : Fraction.Rational) := by
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
      negativeRealGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (Best.Consecutive.RepeatedIndex.neg_one_lt_real_of_normSq_lt_one errorInside).le)
      realLessThanNegativeOne

/-- For the `1+i` denominator transition, the `-1` centered translate is
too small to reach twice the next denominator quadrance. -/
theorem diagonalStep_negativeOne_nextDenominator_impossible
    (denominatorRatio : Gaussian.Basic.Canonical)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (nextOutside :
      1 < Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
        Best.Consecutive.RepeatedIndex.diagonalStep)) :
    ¬ (2 : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
          Best.Consecutive.RepeatedIndex.diagonalStep) ≤
      Data.Gaussian.Norm.Basic.normSq (1 -
        GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have nextExpanded :
      0 < quadrance + 1 +
        2 * denominatorRatio.re + 2 * denominatorRatio.im := by
    have shifted := Fraction.Order.Arithmetic.sub_pos_direct nextOutside
    calc
      0 < Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
        Best.Consecutive.RepeatedIndex.diagonalStep) - 1 := shifted
      _ = quadrance + 1 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.diagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have exteriorExpanded :
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.re := by
    calc
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) =
          2 * Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
            Best.Consecutive.RepeatedIndex.diagonalStep) := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.diagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (1 -
          GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have exteriorPolynomial :
      quadrance + 3 + 2 * denominatorRatio.re +
          4 * denominatorRatio.im ≤ 0 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.re) -
            2 * (quadrance + 2 +
              2 * denominatorRatio.re + 2 * denominatorRatio.im) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 3 + 2 * denominatorRatio.re +
          4 * denominatorRatio.im) := by ring1
  have twiceSumNegative :
      2 + 2 * denominatorRatio.im < (0 : Fraction.Rational) := by
    have polynomialLtNext :
        quadrance + 3 + 2 * denominatorRatio.re +
            4 * denominatorRatio.im <
          quadrance + 1 + 2 * denominatorRatio.re +
            2 * denominatorRatio.im :=
      lt_of_le_of_lt exteriorPolynomial nextExpanded
    have negativeDifference :=
      Fraction.Order.Arithmetic.sub_neg_direct polynomialLtNext
    convert negativeDifference using 1
    ring1
  have twiceOrdered :
      (2 : Fraction.Rational) < 2 * (-denominatorRatio.im) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      twiceSumNegative (-2 * denominatorRatio.im)
    convert shifted using 1 <;> ring1
  have negativeImaginaryGreaterThanOne :
      (1 : Fraction.Rational) < -denominatorRatio.im := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  have imaginaryLessThanNegativeOne :
      denominatorRatio.im < (-1 : Fraction.Rational) := by
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
      negativeImaginaryGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (Best.Consecutive.RepeatedIndex.neg_one_lt_imaginary_of_normSq_lt_one denominatorInside).le)
      imaginaryLessThanNegativeOne

/-- The adjacent `i` centered translate is likewise too small for the next
denominator cylinder of a `1+i` transition. -/
theorem diagonalStep_positiveImaginary_nextDenominator_impossible
    (denominatorRatio : Gaussian.Basic.Canonical)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (nextOutside :
      1 < Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
        Best.Consecutive.RepeatedIndex.diagonalStep)) :
    ¬ (2 : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
          Best.Consecutive.RepeatedIndex.diagonalStep) ≤
      Data.Gaussian.Norm.Basic.normSq (1 -
        GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
          denominatorRatio) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have nextExpanded :
      0 < quadrance + 1 +
        2 * denominatorRatio.re + 2 * denominatorRatio.im := by
    have shifted := Fraction.Order.Arithmetic.sub_pos_direct nextOutside
    calc
      0 < Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
        Best.Consecutive.RepeatedIndex.diagonalStep) - 1 := shifted
      _ = quadrance + 1 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.diagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have exteriorExpanded :
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.im := by
    calc
      2 * (quadrance + 2 +
          2 * denominatorRatio.re + 2 * denominatorRatio.im) =
          2 * Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
            Best.Consecutive.RepeatedIndex.diagonalStep) := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.diagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (1 -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
            denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.im := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
          GaussianInt.Norm.Small.imaginaryUnit]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have exteriorPolynomial :
      quadrance + 3 + 4 * denominatorRatio.re +
          2 * denominatorRatio.im ≤ 0 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.im) -
            2 * (quadrance + 2 +
              2 * denominatorRatio.re + 2 * denominatorRatio.im) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 3 + 4 * denominatorRatio.re +
          2 * denominatorRatio.im) := by ring1
  have twiceSumNegative :
      2 + 2 * denominatorRatio.re < (0 : Fraction.Rational) := by
    have polynomialLtNext :
        quadrance + 3 + 4 * denominatorRatio.re +
            2 * denominatorRatio.im <
          quadrance + 1 + 2 * denominatorRatio.re +
            2 * denominatorRatio.im :=
      lt_of_le_of_lt exteriorPolynomial nextExpanded
    have negativeDifference :=
      Fraction.Order.Arithmetic.sub_neg_direct polynomialLtNext
    convert negativeDifference using 1
    ring1
  have twiceOrdered :
      (2 : Fraction.Rational) < 2 * (-denominatorRatio.re) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      twiceSumNegative (-2 * denominatorRatio.re)
    convert shifted using 1 <;> ring1
  have negativeRealGreaterThanOne :
      (1 : Fraction.Rational) < -denominatorRatio.re := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 2)
    · convert twiceOrdered using 1 <;> ring1
    · decide
  have realLessThanNegativeOne :
      denominatorRatio.re < (-1 : Fraction.Rational) := by
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
      negativeRealGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (Best.Consecutive.RepeatedIndex.neg_one_lt_real_of_normSq_lt_one denominatorInside).le)
      realLessThanNegativeOne

/-- The doubled diagonal transition still excludes the `-1` error exterior;
the factor-four error bound supplies the extra margin. -/
theorem doubledDiagonalStep_negativeOne_error_impossible
    (errorRatio : Gaussian.Basic.Canonical) (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (factorFour : (1 : Fraction.Rational) < 4 * Data.Gaussian.Norm.Basic.normSq errorRatio)
    (transition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledDiagonalStep
        * errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio) :
    ¬ (2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq errorRatio
  have transitionExpanded :
      1 + 7 * quadrance +
          4 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := Fraction.Order.Arithmetic.sub_neg_direct transition
    calc
      1 + 7 * quadrance + 4 * (errorRatio.re - errorRatio.im) =
          Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian
            Best.Consecutive.RepeatedIndex.doubledDiagonalStep * errorRatio) -
            Data.Gaussian.Norm.Basic.normSq errorRatio := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.doubledDiagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Fraction.Rational) ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      (2 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) := exterior
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have realBase : 1 - quadrance ≤ 2 * errorRatio.re := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * errorRatio.re) - 2 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = 2 * errorRatio.re - (1 - quadrance) := by ring1
  have realScaled : 2 - 2 * quadrance ≤ 4 * errorRatio.re := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      realBase (show (0 : Fraction.Rational) ≤ 2 by decide)
    convert scaled using 1
    all_goals ring1
  have lowerTransitionNegative :
      3 + 5 * quadrance - 4 * errorRatio.im < (0 : Fraction.Rational) := by
    calc
      3 + 5 * quadrance - 4 * errorRatio.im ≤
          1 + 7 * quadrance +
            4 * (errorRatio.re - errorRatio.im) := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ 4 * errorRatio.re - (2 - 2 * quadrance) :=
            Fraction.Order.Arithmetic.sub_nonneg_direct realScaled
          _ =
              (1 + 7 * quadrance +
                  4 * (errorRatio.re - errorRatio.im)) -
                (3 + 5 * quadrance - 4 * errorRatio.im) := by ring1
      _ < 0 := transitionExpanded
  have quadrancePositive : 0 < quadrance := by
    have fourPositive : (0 : Fraction.Rational) < 4 * quadrance :=
      (show (0 : Fraction.Rational) < 1 by decide).trans factorFour
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourPositive using 1 <;> ring1
    · decide
  have fourQuadranceLtFive :
      4 * quadrance < 5 * quadrance := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      quadrancePositive (4 * quadrance)
    convert shifted using 1 <;> ring1
  have oneLtFiveQuadrance : (1 : Fraction.Rational) < 5 * quadrance :=
    factorFour.trans fourQuadranceLtFive
  have fourLtThreePlusFive :
      (4 : Fraction.Rational) < 3 + 5 * quadrance := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      oneLtFiveQuadrance 3
    convert shifted using 1 <;> ring1
  have fourGapNegative :
      4 - 4 * errorRatio.im < (0 : Fraction.Rational) := by
    calc
      4 - 4 * errorRatio.im <
          3 + 5 * quadrance - 4 * errorRatio.im := by
        convert Fraction.Order.Arithmetic.add_lt_add_right_direct
          fourLtThreePlusFive (-4 * errorRatio.im) using 1 <;> ring1
      _ < 0 := lowerTransitionNegative
  have fourOrdered : (4 : Fraction.Rational) < 4 * errorRatio.im := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      fourGapNegative (4 * errorRatio.im)
    convert shifted using 1 <;> ring1
  have imaginaryGreaterThanOne : (1 : Fraction.Rational) < errorRatio.im := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourOrdered using 1 <;> ring1
    · decide
  exact (not_lt_of_ge (Best.Consecutive.RepeatedIndex.imaginary_lt_one_of_normSq_lt_one errorInside).le)
    imaginaryGreaterThanOne

/-- The adjacent `i` error exterior is excluded symmetrically for the
doubled diagonal transition. -/
theorem doubledDiagonalStep_positiveImaginary_error_impossible
    (errorRatio : Gaussian.Basic.Canonical) (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (factorFour : (1 : Fraction.Rational) < 4 * Data.Gaussian.Norm.Basic.normSq errorRatio)
    (transition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledDiagonalStep
        * errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio) :
    ¬ (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
      (errorRatio - GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq errorRatio
  have transitionExpanded :
      1 + 7 * quadrance +
          4 * (errorRatio.re - errorRatio.im) < 0 := by
    have difference := Fraction.Order.Arithmetic.sub_neg_direct transition
    calc
      1 + 7 * quadrance + 4 * (errorRatio.re - errorRatio.im) =
          Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian
            Best.Consecutive.RepeatedIndex.doubledDiagonalStep * errorRatio) -
            Data.Gaussian.Norm.Basic.normSq errorRatio := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.doubledDiagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Fraction.Rational) ≤ 1 + quadrance - 2 * errorRatio.im := by
    calc
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
          (errorRatio -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) := exterior
      _ = 1 + quadrance - 2 * errorRatio.im := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
          GaussianInt.Norm.Small.imaginaryUnit]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have imaginaryBase :
      1 - quadrance ≤ -2 * errorRatio.im := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * errorRatio.im) - 2 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = -2 * errorRatio.im - (1 - quadrance) := by ring1
  have imaginaryScaled :
      2 - 2 * quadrance ≤ -4 * errorRatio.im := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      imaginaryBase (show (0 : Fraction.Rational) ≤ 2 by decide)
    convert scaled using 1 <;> ring1
  have lowerTransitionNegative :
      3 + 5 * quadrance + 4 * errorRatio.re < (0 : Fraction.Rational) := by
    calc
      3 + 5 * quadrance + 4 * errorRatio.re ≤
          1 + 7 * quadrance +
            4 * (errorRatio.re - errorRatio.im) := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ -4 * errorRatio.im - (2 - 2 * quadrance) :=
            Fraction.Order.Arithmetic.sub_nonneg_direct imaginaryScaled
          _ =
              (1 + 7 * quadrance +
                  4 * (errorRatio.re - errorRatio.im)) -
                (3 + 5 * quadrance + 4 * errorRatio.re) := by ring1
      _ < 0 := transitionExpanded
  have quadrancePositive : 0 < quadrance := by
    have fourPositive : (0 : Fraction.Rational) < 4 * quadrance :=
      (show (0 : Fraction.Rational) < 1 by decide).trans factorFour
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourPositive using 1 <;> ring1
    · decide
  have fourQuadranceLtFive :
      4 * quadrance < 5 * quadrance := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      quadrancePositive (4 * quadrance)
    convert shifted using 1 <;> ring1
  have oneLtFiveQuadrance : (1 : Fraction.Rational) < 5 * quadrance :=
    factorFour.trans fourQuadranceLtFive
  have fourLtThreePlusFive :
      (4 : Fraction.Rational) < 3 + 5 * quadrance := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      oneLtFiveQuadrance 3
    convert shifted using 1 <;> ring1
  have fourSumNegative :
      4 + 4 * errorRatio.re < (0 : Fraction.Rational) := by
    calc
      4 + 4 * errorRatio.re <
          3 + 5 * quadrance + 4 * errorRatio.re := by
        exact Fraction.Order.Arithmetic.add_lt_add_right_direct
          fourLtThreePlusFive (4 * errorRatio.re)
      _ < 0 := lowerTransitionNegative
  have fourOrdered : (4 : Fraction.Rational) < 4 * (-errorRatio.re) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      fourSumNegative (-4 * errorRatio.re)
    convert shifted using 1 <;> ring1
  have negativeRealGreaterThanOne :
      (1 : Fraction.Rational) < -errorRatio.re := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourOrdered using 1 <;> ring1
    · decide
  have realLessThanNegativeOne : errorRatio.re < (-1 : Fraction.Rational) := by
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct
      negativeRealGreaterThanOne
    simpa only [neg_neg] using negated
  exact (not_lt_of_ge
    (Best.Consecutive.RepeatedIndex.neg_one_lt_real_of_normSq_lt_one errorInside).le)
      realLessThanNegativeOne

/-- The `-1` next-denominator exterior is impossible for the doubled
diagonal coefficient already from the open-unit-disc bound. -/
theorem doubledDiagonalStep_negativeOne_nextDenominator_impossible
    (denominatorRatio : Gaussian.Basic.Canonical)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1) :
    ¬ (2 : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
          Best.Consecutive.RepeatedIndex.doubledDiagonalStep) ≤
      Data.Gaussian.Norm.Basic.normSq (1 -
        GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have exteriorExpanded :
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.re := by
    calc
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) =
          2 * Data.Gaussian.Norm.Basic.normSq
            (denominatorRatio + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledDiagonalStep) := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.doubledDiagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (1 -
          GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have exteriorPolynomial :
      quadrance + 15 + 6 * denominatorRatio.re +
          8 * denominatorRatio.im ≤ 0 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.re) -
            2 * (quadrance + 8 +
              4 * denominatorRatio.re + 4 * denominatorRatio.im) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 15 + 6 * denominatorRatio.re +
          8 * denominatorRatio.im) := by ring1
  have realShiftPositive :
      0 < denominatorRatio.re + (1 : Fraction.Rational) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      (Best.Consecutive.RepeatedIndex.neg_one_lt_real_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have imaginaryShiftPositive :
      0 < denominatorRatio.im + (1 : Fraction.Rational) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      (Best.Consecutive.RepeatedIndex.neg_one_lt_imaginary_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have sixRealPositive :
      0 < 6 * (denominatorRatio.re + 1) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide) realShiftPositive
  have eightImaginaryPositive :
      0 < 8 * (denominatorRatio.im + 1) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide) imaginaryShiftPositive
  have basePositive : 0 < quadrance + 1 := by
    calc
      (0 : Fraction.Rational) < 1 := by decide
      _ ≤ quadrance + 1 := by
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          (Gaussian.Norm.Basic.normSq_nonneg denominatorRatio) 1
        convert shifted using 1
        all_goals ring1
  have withRealPositive :
      0 < quadrance + 1 + 6 * (denominatorRatio.re + 1) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      sixRealPositive (quadrance + 1)
    have increased :
        quadrance + 1 <
          6 * (denominatorRatio.re + 1) + (quadrance + 1) := by
      convert shifted using 1
      all_goals ring1
    have increased' :
        quadrance + 1 <
          quadrance + 1 + 6 * (denominatorRatio.re + 1) := by
      convert increased using 1
      all_goals ring1
    exact basePositive.trans increased'
  have polynomialPositive :
      0 < quadrance + 15 + 6 * denominatorRatio.re +
          8 * denominatorRatio.im := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      eightImaginaryPositive
        (quadrance + 1 + 6 * (denominatorRatio.re + 1))
    exact withRealPositive.trans (by
      calc
        quadrance + 1 + 6 * (denominatorRatio.re + 1) <
            8 * (denominatorRatio.im + 1) +
              (quadrance + 1 + 6 * (denominatorRatio.re + 1)) := by
          convert shifted using 1
          all_goals ring1
        _ = quadrance + 15 + 6 * denominatorRatio.re +
            8 * denominatorRatio.im := by ring1)
  exact (not_lt_of_ge exteriorPolynomial) polynomialPositive

/-- The adjacent `i` next-denominator exterior is impossible by the same
finite coordinate estimate. -/
theorem doubledDiagonalStep_positiveImaginary_nextDenominator_impossible
    (denominatorRatio : Gaussian.Basic.Canonical)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1) :
    ¬ (2 : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
          Best.Consecutive.RepeatedIndex.doubledDiagonalStep) ≤
      Data.Gaussian.Norm.Basic.normSq (1 -
        GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
          denominatorRatio) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have exteriorExpanded :
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) ≤
        1 + quadrance + 2 * denominatorRatio.im := by
    calc
      2 * (quadrance + 8 +
          4 * denominatorRatio.re + 4 * denominatorRatio.im) =
          2 * Data.Gaussian.Norm.Basic.normSq
            (denominatorRatio + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledDiagonalStep) := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.doubledDiagonalStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (1 -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
            denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.im := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
          GaussianInt.Norm.Small.imaginaryUnit]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have exteriorPolynomial :
      quadrance + 15 + 8 * denominatorRatio.re +
          6 * denominatorRatio.im ≤ 0 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤
          (1 + quadrance + 2 * denominatorRatio.im) -
            2 * (quadrance + 8 +
              4 * denominatorRatio.re + 4 * denominatorRatio.im) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 15 + 8 * denominatorRatio.re +
          6 * denominatorRatio.im) := by ring1
  have realShiftPositive :
      0 < denominatorRatio.re + (1 : Fraction.Rational) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      (Best.Consecutive.RepeatedIndex.neg_one_lt_real_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have imaginaryShiftPositive :
      0 < denominatorRatio.im + (1 : Fraction.Rational) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      (Best.Consecutive.RepeatedIndex.neg_one_lt_imaginary_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have eightRealPositive :
      0 < 8 * (denominatorRatio.re + 1) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide) realShiftPositive
  have sixImaginaryPositive :
      0 < 6 * (denominatorRatio.im + 1) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide) imaginaryShiftPositive
  have basePositive : 0 < quadrance + 1 := by
    calc
      (0 : Fraction.Rational) < 1 := by decide
      _ ≤ quadrance + 1 := by
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          (Gaussian.Norm.Basic.normSq_nonneg denominatorRatio) 1
        convert shifted using 1
        all_goals ring1
  have withRealPositive :
      0 < quadrance + 1 + 8 * (denominatorRatio.re + 1) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      eightRealPositive (quadrance + 1)
    have increased :
        quadrance + 1 <
          8 * (denominatorRatio.re + 1) + (quadrance + 1) := by
      convert shifted using 1
      all_goals ring1
    have increased' :
        quadrance + 1 <
          quadrance + 1 + 8 * (denominatorRatio.re + 1) := by
      convert increased using 1
      all_goals ring1
    exact basePositive.trans increased'
  have polynomialPositive :
      0 < quadrance + 15 + 8 * denominatorRatio.re +
          6 * denominatorRatio.im := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      sixImaginaryPositive
        (quadrance + 1 + 8 * (denominatorRatio.re + 1))
    exact withRealPositive.trans (by
      calc
        quadrance + 1 + 8 * (denominatorRatio.re + 1) <
            6 * (denominatorRatio.im + 1) +
              (quadrance + 1 + 8 * (denominatorRatio.re + 1)) := by
          convert shifted using 1
          all_goals ring1
        _ = quadrance + 15 + 8 * denominatorRatio.re +
            6 * denominatorRatio.im := by ring1)
  exact (not_lt_of_ge exteriorPolynomial) polynomialPositive

/-- An axial `2` transition excludes the opposite `-1` error exterior. -/
theorem doubledAxisStep_negativeOne_error_impossible
    (errorRatio : Gaussian.Basic.Canonical)
    (transition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledAxisStep *
        errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio) :
    ¬ (2 : Fraction.Rational) ≤
      Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq errorRatio
  have transitionExpanded :
      1 + 3 * quadrance + 4 * errorRatio.re < 0 := by
    have difference := Fraction.Order.Arithmetic.sub_neg_direct transition
    calc
      1 + 3 * quadrance + 4 * errorRatio.re =
          Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledAxisStep
            * errorRatio) -
            Data.Gaussian.Norm.Basic.normSq errorRatio := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.doubledAxisStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ < 0 := difference
  have exteriorExpanded :
      (2 : Fraction.Rational) ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      (2 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) := exterior
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have realBase : 1 - quadrance ≤ 2 * errorRatio.re := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * errorRatio.re) - 2 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = 2 * errorRatio.re - (1 - quadrance) := by ring1
  have realScaled : 2 - 2 * quadrance ≤ 4 * errorRatio.re := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      realBase (show (0 : Fraction.Rational) ≤ 2 by decide)
    convert scaled using 1 <;> ring1
  have positiveLower : 0 < 3 + quadrance := by
    calc
      (0 : Fraction.Rational) < 3 := by decide
      _ ≤ 3 + quadrance := by
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          (Gaussian.Norm.Basic.normSq_nonneg errorRatio) 3
        convert shifted using 1 <;> ring1
  have lowerNegative : 3 + quadrance < (0 : Fraction.Rational) := by
    calc
      3 + quadrance ≤ 1 + 3 * quadrance + 4 * errorRatio.re := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        calc
          0 ≤ 4 * errorRatio.re - (2 - 2 * quadrance) :=
            Fraction.Order.Arithmetic.sub_nonneg_direct realScaled
          _ = (1 + 3 * quadrance + 4 * errorRatio.re) -
              (3 + quadrance) := by ring1
      _ < 0 := transitionExpanded
  exact (not_lt_of_ge positiveLower.le) lowerNegative

/-- For the axial coefficient, the `-1` next-denominator exterior is already
incompatible with the open unit disc. -/
theorem doubledAxisStep_negativeOne_nextDenominator_impossible
    (denominatorRatio : Gaussian.Basic.Canonical)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1) :
    ¬ (2 : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
          Best.Consecutive.RepeatedIndex.doubledAxisStep) ≤
      Data.Gaussian.Norm.Basic.normSq (1 -
        GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio) := by
  intro exterior
  let quadrance := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  have exteriorExpanded :
      2 * (quadrance + 4 + 4 * denominatorRatio.re) ≤
        1 + quadrance + 2 * denominatorRatio.re := by
    calc
      2 * (quadrance + 4 + 4 * denominatorRatio.re) =
          2 * Data.Gaussian.Norm.Basic.normSq
            (denominatorRatio + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledAxisStep) := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.doubledAxisStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (1 -
          GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio) := exterior
      _ = 1 + quadrance + 2 * denominatorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have exteriorPolynomial :
      quadrance + 7 + 6 * denominatorRatio.re ≤ 0 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * denominatorRatio.re) -
          2 * (quadrance + 4 + 4 * denominatorRatio.re) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct exteriorExpanded
      _ = 0 - (quadrance + 7 + 6 * denominatorRatio.re) := by ring1
  have realShiftPositive :
      0 < denominatorRatio.re + (1 : Fraction.Rational) := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      (Best.Consecutive.RepeatedIndex.neg_one_lt_real_of_normSq_lt_one denominatorInside) 1
    convert shifted using 1
    all_goals ring1
  have sixRealPositive :
      0 < 6 * (denominatorRatio.re + 1) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide) realShiftPositive
  have basePositive : 0 < quadrance + 1 := by
    calc
      (0 : Fraction.Rational) < 1 := by decide
      _ ≤ quadrance + 1 := by
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          (Gaussian.Norm.Basic.normSq_nonneg denominatorRatio) 1
        convert shifted using 1
        all_goals ring1
  have polynomialPositive :
      0 < quadrance + 7 + 6 * denominatorRatio.re := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      sixRealPositive (quadrance + 1)
    have increased : quadrance + 1 <
        6 * (denominatorRatio.re + 1) + (quadrance + 1) := by
      convert shifted using 1
      all_goals ring1
    exact basePositive.trans (by
      calc
        quadrance + 1 <
            6 * (denominatorRatio.re + 1) + (quadrance + 1) := increased
        _ = quadrance + 7 + 6 * denominatorRatio.re := by ring1)
  exact (not_lt_of_ge exteriorPolynomial) polynomialPositive

/-- Once the two transition-specific error exteriors and the two
transition-specific denominator exteriors have been excluded, the four
remaining cylinder branches are exactly the irrational diagonal boundary
pattern. -/
theorem diagonal_obstruction_core_impossible
    (errorRatio denominatorRatio nextDenominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (selfObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq errorRatio ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 * Data.Gaussian.Norm.Basic.normSq nextDenominatorRatio ≤
          Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio))
    (negativeOneErrorImpossible :
      ¬ (2 : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)))
    (positiveImaginaryErrorImpossible :
      ¬ (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq
        (errorRatio -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit))
    (negativeOneNextDenominatorImpossible :
      ¬ (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq nextDenominatorRatio ≤
        Data.Gaussian.Norm.Basic.normSq (1 -
          GaussianInt.toGaussian (-1 : GaussianInt) * denominatorRatio))
    (positiveImaginaryNextDenominatorImpossible :
      ¬ (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq nextDenominatorRatio ≤
        Data.Gaussian.Norm.Basic.normSq (1 -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
            denominatorRatio)) :
    False := by
  have realCross := Best.Consecutive.RepeatedIndex.opposite_self_obstructions_cross errorRatio
    denominatorRatio errorInside denominatorInside 1 rfl
    (selfObstruction 1 rfl) (selfObstruction (-1) (by decide))
  obtain ⟨positiveOneError, negativeOneDenominator⟩ :=
    realCross.resolve_right (fun alternative =>
      negativeOneErrorImpossible alternative.2)
  have imaginaryCross := Best.Consecutive.RepeatedIndex.opposite_self_obstructions_cross errorRatio
    denominatorRatio errorInside denominatorInside
    GaussianInt.Norm.Small.imaginaryUnit (by decide)
    (selfObstruction GaussianInt.Norm.Small.imaginaryUnit (by decide))
    (selfObstruction (-GaussianInt.Norm.Small.imaginaryUnit) (by decide))
  obtain ⟨positiveImaginaryDenominator, negativeImaginaryError⟩ :=
    imaginaryCross.resolve_left (fun alternative =>
      positiveImaginaryErrorImpossible alternative.1)
  have negativeOneNext := nextObstruction (-1) (by decide)
  have negativeOneNextError := negativeOneNext.resolve_right
    negativeOneNextDenominatorImpossible
  have positiveImaginaryNext :=
    nextObstruction GaussianInt.Norm.Small.imaginaryUnit (by decide)
  have positiveImaginaryNextError := positiveImaginaryNext.resolve_right
    positiveImaginaryNextDenominatorImpossible
  have positiveOneIdentity :
      errorRatio - GaussianInt.toGaussian (1 : GaussianInt) = errorRatio - 1 := by
    rw [GaussianInt.toGaussian_one]
  have negativeOneIdentity :
      errorRatio - GaussianInt.toGaussian (-1 : GaussianInt) = errorRatio + 1 := by
    apply Gaussian.Basic.ext <;>
      simp only [GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one,
        Gaussian.Basic.neg_re,
        Gaussian.Basic.neg_im,
        Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im] <;>
      ring1
  have negativeImaginaryIdentity :
      errorRatio -
          GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) =
        errorRatio +
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit := by
    apply Gaussian.Basic.ext <;>
      simp only [GaussianInt.toGaussian_neg,
        Gaussian.Basic.neg_re,
        Gaussian.Basic.neg_im,
        Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.add_re,
        Gaussian.Basic.add_im] <;>
      ring1
  rw [positiveOneIdentity] at positiveOneError
  rw [negativeOneIdentity] at negativeOneNextError
  rw [negativeImaginaryIdentity] at negativeImaginaryError
  exact Best.Consecutive.NormalForm.centered_diagonal_error_pattern_impossible
    1 errorRatio (by decide) positiveOneError negativeOneNextError
      positiveImaginaryNextError negativeImaginaryError

/-- Complete finite normalized exclusion for the canonical `1+i`
coefficient. -/
theorem diagonalStep_obstructions_impossible
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (errorTransition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.diagonalStep *
        errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio)
    (denominatorTransition :
      1 < Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
        Best.Consecutive.RepeatedIndex.diagonalStep))
    (selfObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq errorRatio ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 * Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
          Best.Consecutive.RepeatedIndex.diagonalStep) ≤
          Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    False := by
  exact Best.Consecutive.RepeatedIndex.diagonal_obstruction_core_impossible errorRatio denominatorRatio
    (denominatorRatio + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.diagonalStep) errorInside
    denominatorInside selfObstruction nextObstruction
    (Best.Consecutive.RepeatedIndex.diagonalStep_negativeOne_error_impossible errorRatio errorInside
      errorTransition)
    (Best.Consecutive.RepeatedIndex.diagonalStep_positiveImaginary_error_impossible errorRatio errorInside
      errorTransition)
    (Best.Consecutive.RepeatedIndex.diagonalStep_negativeOne_nextDenominator_impossible denominatorRatio
      denominatorInside denominatorTransition)
    (Best.Consecutive.RepeatedIndex.diagonalStep_positiveImaginary_nextDenominator_impossible
      denominatorRatio denominatorInside denominatorTransition)

/-- Complete finite normalized exclusion for the canonical `2+2i`
coefficient. -/
theorem doubledDiagonalStep_obstructions_impossible
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (factorFour : (1 : Fraction.Rational) < 4 * Data.Gaussian.Norm.Basic.normSq errorRatio)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (errorTransition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledDiagonalStep
        * errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio)
    (selfObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq errorRatio ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 * Data.Gaussian.Norm.Basic.normSq
            (denominatorRatio + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledDiagonalStep) ≤
          Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    False := by
  exact Best.Consecutive.RepeatedIndex.diagonal_obstruction_core_impossible errorRatio denominatorRatio
    (denominatorRatio + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledDiagonalStep) errorInside
    denominatorInside selfObstruction nextObstruction
    (Best.Consecutive.RepeatedIndex.doubledDiagonalStep_negativeOne_error_impossible errorRatio errorInside
      factorFour errorTransition)
    (Best.Consecutive.RepeatedIndex.doubledDiagonalStep_positiveImaginary_error_impossible errorRatio
      errorInside factorFour errorTransition)
    (Best.Consecutive.RepeatedIndex.doubledDiagonalStep_negativeOne_nextDenominator_impossible
      denominatorRatio denominatorInside)
    (Best.Consecutive.RepeatedIndex.doubledDiagonalStep_positiveImaginary_nextDenominator_impossible
      denominatorRatio denominatorInside)

/-- Complete finite normalized exclusion for the canonical axial coefficient
`2`.  The two real unit translates pin an exact boundary equality; the
factor-four estimate then makes the axial transition inequality impossible. -/
theorem doubledAxisStep_obstructions_impossible
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (factorFour : (1 : Fraction.Rational) < 4 * Data.Gaussian.Norm.Basic.normSq errorRatio)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (errorTransition :
      Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledAxisStep *
        errorRatio) <
        Data.Gaussian.Norm.Basic.normSq errorRatio)
    (selfObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio))
    (nextObstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq errorRatio ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 * Data.Gaussian.Norm.Basic.normSq (denominatorRatio + GaussianInt.toGaussian
          Best.Consecutive.RepeatedIndex.doubledAxisStep) ≤
          Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    False := by
  have realCross := Best.Consecutive.RepeatedIndex.opposite_self_obstructions_cross errorRatio
    denominatorRatio errorInside denominatorInside 1 rfl
    (selfObstruction 1 rfl) (selfObstruction (-1) (by decide))
  obtain ⟨positiveOneError, _⟩ := realCross.resolve_right
    (fun alternative =>
      Best.Consecutive.RepeatedIndex.doubledAxisStep_negativeOne_error_impossible errorRatio
        errorTransition alternative.2)
  have negativeOneNext := nextObstruction (-1) (by decide)
  have negativeOneNextError := negativeOneNext.resolve_right
    (Best.Consecutive.RepeatedIndex.doubledAxisStep_negativeOne_nextDenominator_impossible
      denominatorRatio denominatorInside)
  let quadrance := Data.Gaussian.Norm.Basic.normSq errorRatio
  have positiveOneExpanded :
      (2 : Fraction.Rational) ≤ 1 + quadrance - 2 * errorRatio.re := by
    calc
      (2 : Fraction.Rational) ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (1 : GaussianInt)) :=
        positiveOneError
      _ = 1 + quadrance - 2 * errorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have negativeOneExpanded :
      2 * quadrance ≤ 1 + quadrance + 2 * errorRatio.re := by
    calc
      2 * quadrance ≤
          Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian (-1 : GaussianInt)) :=
        negativeOneNextError
      _ = 1 + quadrance + 2 * errorRatio.re := by
        dsimp only [quadrance, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian]
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  have realUpper : 2 * errorRatio.re ≤ quadrance - 1 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * errorRatio.re) - 2 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct positiveOneExpanded
      _ = (quadrance - 1) - 2 * errorRatio.re := by ring1
  have realLower : quadrance - 1 ≤ 2 * errorRatio.re := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * errorRatio.re) - 2 * quadrance :=
        Fraction.Order.Arithmetic.sub_nonneg_direct negativeOneExpanded
      _ = 2 * errorRatio.re - (quadrance - 1) := by ring1
  have realIdentity : 2 * errorRatio.re = quadrance - 1 :=
    le_antisymm realUpper realLower
  have realScaledIdentity :
      4 * errorRatio.re = 2 * (quadrance - 1) := by
    have scaled := congrArg (fun value : Fraction.Rational => 2 * value)
      realIdentity
    convert scaled using 1
    all_goals ring1
  have transitionExpanded :
      1 + 3 * quadrance + 4 * errorRatio.re < 0 := by
    have difference := Fraction.Order.Arithmetic.sub_neg_direct
      errorTransition
    calc
      1 + 3 * quadrance + 4 * errorRatio.re =
          Data.Gaussian.Norm.Basic.normSq (1 + GaussianInt.toGaussian Best.Consecutive.RepeatedIndex.doubledAxisStep
            * errorRatio) -
            Data.Gaussian.Norm.Basic.normSq errorRatio := by
        dsimp only [quadrance, Best.Consecutive.RepeatedIndex.doubledAxisStep, Data.Gaussian.Norm.Basic.normSq,
          GaussianInt.toGaussian]
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
      _ < 0 := difference
  have fiveQuadranceLtOne : 5 * quadrance < (1 : Fraction.Rational) := by
    apply Fraction.Order.Arithmetic.lt_of_sub_neg_direct
    calc
      5 * quadrance - 1 =
          1 + 3 * quadrance + 4 * errorRatio.re := by
        rw [realScaledIdentity]
        ring1
      _ < 0 := transitionExpanded
  have quadrancePositive : 0 < quadrance := by
    have fourPositive : (0 : Fraction.Rational) < 4 * quadrance :=
      (show (0 : Fraction.Rational) < 1 by decide).trans factorFour
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 4)
    · convert fourPositive using 1 <;> ring1
    · decide
  have fourQuadranceLtFive :
      4 * quadrance < 5 * quadrance := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      quadrancePositive (4 * quadrance)
    convert shifted using 1 <;> ring1
  exact (not_lt_of_ge fiveQuadranceLtOne.le)
    (factorFour.trans fourQuadranceLtFive)

/-- Normalized cylinder data with a quadrance-two transition coefficient is
impossible, after rotating its displayed coefficient to `1+i`. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_eq_two
    {coefficient : GaussianInt} (data : Best.Consecutive.RepeatedIndex.NormalizedCylinderData coefficient)
    (coefficientNorm : GaussianInt.normNat coefficient = 2) : False := by
  obtain ⟨associate, associateProperty, associated⟩ :=
    Best.Consecutive.RepeatedIndex.exists_unit_associate_of_normNat_eq_two coefficient coefficientNorm
  let canonicalData := Best.Consecutive.RepeatedIndex.transportNormalizedData coefficient
    Best.Consecutive.RepeatedIndex.diagonalStep
    associate associateProperty associated data
  exact Best.Consecutive.RepeatedIndex.diagonalStep_obstructions_impossible canonicalData.errorRatio
    canonicalData.denominatorRatio canonicalData.errorInside
    canonicalData.denominatorInside canonicalData.errorTransition
    canonicalData.denominatorTransition canonicalData.selfObstruction
    canonicalData.nextObstruction

/-- Normalized cylinder data with a quadrance-four transition coefficient is
impossible, after rotating its displayed coefficient to `2`. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_eq_four
    {coefficient : GaussianInt} (data : Best.Consecutive.RepeatedIndex.NormalizedCylinderData coefficient)
    (coefficientNorm : GaussianInt.normNat coefficient = 4) : False := by
  obtain ⟨associate, associateProperty, associated⟩ :=
    Best.Consecutive.RepeatedIndex.exists_unit_associate_of_normNat_eq_four coefficient coefficientNorm
  let canonicalData := Best.Consecutive.RepeatedIndex.transportNormalizedData coefficient
    Best.Consecutive.RepeatedIndex.doubledAxisStep
    associate associateProperty associated data
  exact Best.Consecutive.RepeatedIndex.doubledAxisStep_obstructions_impossible canonicalData.errorRatio
    canonicalData.denominatorRatio canonicalData.errorInside
    canonicalData.factorFour canonicalData.denominatorInside
    canonicalData.errorTransition canonicalData.selfObstruction
    canonicalData.nextObstruction

/-- Normalized cylinder data with a quadrance-eight transition coefficient is
impossible, after rotating its displayed coefficient to `2+2i`. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_eq_eight
    {coefficient : GaussianInt} (data : Best.Consecutive.RepeatedIndex.NormalizedCylinderData coefficient)
    (coefficientNorm : GaussianInt.normNat coefficient = 8) : False := by
  obtain ⟨associate, associateProperty, associated⟩ :=
    Best.Consecutive.RepeatedIndex.exists_unit_associate_of_normNat_eq_eight coefficient coefficientNorm
  let canonicalData := Best.Consecutive.RepeatedIndex.transportNormalizedData coefficient
    Best.Consecutive.RepeatedIndex.doubledDiagonalStep associate associateProperty associated data
  exact Best.Consecutive.RepeatedIndex.doubledDiagonalStep_obstructions_impossible canonicalData.errorRatio
    canonicalData.denominatorRatio canonicalData.errorInside
    canonicalData.factorFour canonicalData.denominatorInside
    canonicalData.errorTransition canonicalData.selfObstruction
    canonicalData.nextObstruction

/-- The three coefficient quadrances left by the bounded repeated-index
normal form are all impossible. -/
theorem NormalizedCylinderData.impossible_of_coefficientNorm_cases
    {coefficient : GaussianInt} (data : Best.Consecutive.RepeatedIndex.NormalizedCylinderData coefficient)
    (coefficientNorm : GaussianInt.normNat coefficient = 2 ∨
      GaussianInt.normNat coefficient = 4 ∨ GaussianInt.normNat coefficient = 8) : False := by
  rcases coefficientNorm with normTwo | normFour | normEight
  · exact data.impossible_of_coefficientNorm_eq_two normTwo
  · exact data.impossible_of_coefficientNorm_eq_four normFour
  · exact data.impossible_of_coefficientNorm_eq_eight normEight

/-- Two consecutive best-approximation transitions cannot both have
coefficient-index quadrance two.  The proof constructs the normalized
cylinder record directly from the finite normal form and invokes the
three-case normalized exclusion above. -/
theorem repeatedIndexTwo_impossible
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper = 2) :
    False := by
  obtain ⟨lowerUnit, step, lowerUnitNorm, stepCases, transitionIdentity⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.repeatedIndexTwo_enumeratedNormalForm first) second leftIndexTwo
      rightIndexTwo
  let determinantValue :=
    GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle
  let coefficient := determinantValue * step
  let largeError :=
    GaussianInt.toGaussian lowerUnit * Best.Error.error source.value lower
  let smallError := Best.Error.error source.value middle
  let nextError := Best.Error.error source.value upper
  let lowerDenominator :=
    GaussianInt.toGaussian lowerUnit * GaussianInt.toGaussian lower.denominator
  let middleDenominator := GaussianInt.toGaussian middle.denominator
  let upperDenominator := GaussianInt.toGaussian upper.denominator
  have determinantNorm : GaussianInt.normNat determinantValue = 2 := by
    simpa only [determinantValue,
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance] using leftIndexTwo
  have coefficientNormCases :
      GaussianInt.normNat coefficient = 2 ∨ GaussianInt.normNat coefficient = 4 ∨
        GaussianInt.normNat coefficient = 8 := by
    dsimp only [ coefficient]
    rw [GaussianInt.Embedding.normNat_mul, determinantNorm]
    rcases stepCases with stepOne | stepTwo | stepFour
    · exact Or.inl (by rw [stepOne])
    · exact Or.inr (Or.inl (by rw [stepTwo]))
    · exact Or.inr (Or.inr (by rw [stepFour]))
  have largeErrorNorm :
      Data.Gaussian.Norm.Basic.normSq largeError =
        Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) := by
    dsimp only [ largeError]
    rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, lowerUnitNorm]
    ring1
  have lowerDenominatorNorm :
      Data.Gaussian.Norm.Basic.normSq lowerDenominator = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian
        lower.denominator) := by
    dsimp only [ lowerDenominator]
    rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, lowerUnitNorm]
    ring1
  have rawErrorOrdered :
      Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value middle) <
        Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) :=
    first.2.1.2.1 lower first.1.1 first.2.2.1
  have largeErrorNonzero : largeError ≠ 0 := by
    intro largeErrorZero
    have lowerNormZero := congrArg Data.Gaussian.Norm.Basic.normSq largeErrorZero
    rw [largeErrorNorm, Gaussian.Norm.Basic.normSq_zero] at lowerNormZero
    have impossible := rawErrorOrdered
    rw [lowerNormZero] at impossible
    exact (not_lt_of_ge
      (Gaussian.Norm.Basic.normSq_nonneg
        (Best.Error.error source.value middle))) impossible
  have middleDenominatorNonzero : middleDenominator ≠ 0 := by
    intro middleZero
    apply first.2.1.1
    apply GaussianInt.toGaussian_eq_zero.mp
    exact middleZero
  have errorOrdered : Data.Gaussian.Norm.Basic.normSq smallError < Data.Gaussian.Norm.Basic.normSq largeError :=
    by
    rw [largeErrorNorm]
    exact rawErrorOrdered
  have nextErrorOrdered : Data.Gaussian.Norm.Basic.normSq nextError < Data.Gaussian.Norm.Basic.normSq smallError
    := by
    dsimp only [ nextError, smallError]
    exact second.2.1.2.1 middle second.1.1 second.2.2.1
  have factorFour : Data.Gaussian.Norm.Basic.normSq largeError < 4 * Data.Gaussian.Norm.Basic.normSq smallError
    := by
    rw [largeErrorNorm]
    dsimp only [ smallError]
    exact (Best.Consecutive.NormalForm.AreConsecutiveBest.errorQuadrance_lower_lt_four_mul_upper_of_index_two first)
      leftIndexTwo
  have denominatorOrdered :
      Data.Gaussian.Norm.Basic.normSq lowerDenominator < Data.Gaussian.Norm.Basic.normSq middleDenominator := by
    rw [lowerDenominatorNorm]
    dsimp only [ middleDenominator]
    rw [GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]
    exact Fraction.Cast.Order.natCast_lt_direct first.2.2.1
  have nextDenominatorOrdered :
      Data.Gaussian.Norm.Basic.normSq middleDenominator < Data.Gaussian.Norm.Basic.normSq upperDenominator := by
    dsimp only [ middleDenominator, upperDenominator]
    rw [GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]
    exact Fraction.Cast.Order.natCast_lt_direct second.2.2.1
  have errorIdentity :
      nextError = largeError + GaussianInt.toGaussian coefficient * smallError := by
    dsimp only [ nextError, largeError, coefficient, determinantValue,
      smallError]
    rw [transitionIdentity,
      Best.Error.error_linearCombination]
  have denominatorIdentity :
      upperDenominator =
        lowerDenominator + GaussianInt.toGaussian coefficient * middleDenominator := by
    dsimp only [ upperDenominator, lowerDenominator, coefficient,
      determinantValue, middleDenominator]
    rw [transitionIdentity]
    simp only [-eq_self, -iff_self, GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.toGaussian_add,
      GaussianInt.toGaussian_mul]
    rfl
  have selfObstruction (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian unit * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq middleDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (middleDenominator -
            GaussianInt.toGaussian unit * lowerDenominator) := by
    let sourceUnit := unit * lowerUnit
    have sourceUnitNorm : GaussianInt.normNat sourceUnit = 1 := by
      dsimp only [ sourceUnit]
      rw [GaussianInt.Embedding.normNat_mul, unitNorm, lowerUnitNorm]
    have obstruction := (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_selfCoordinateObstruction first)
      leftIndexTwo sourceUnit sourceUnitNorm
    rw [largeErrorNorm]
    simpa only [largeError, smallError, lowerDenominator,
      middleDenominator, sourceUnit, GaussianInt.toGaussian_mul,
      Gaussian.Basic.mul_assoc] using obstruction
  have nextObstruction (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq smallError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian unit * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (middleDenominator -
            GaussianInt.toGaussian unit * lowerDenominator) := by
    let sourceUnit := unit * lowerUnit
    have sourceUnitNorm : GaussianInt.normNat sourceUnit = 1 := by
      dsimp only [ sourceUnit]
      rw [GaussianInt.Embedding.normNat_mul, unitNorm, lowerUnitNorm]
    have obstruction := (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_nextCoordinateObstruction first)
      second
      leftIndexTwo sourceUnit sourceUnitNorm
    simpa only [largeError, smallError, lowerDenominator,
      middleDenominator, upperDenominator, sourceUnit, GaussianInt.toGaussian_mul,
      Gaussian.Basic.mul_assoc] using obstruction
  let data := Best.Consecutive.RepeatedIndex.normalizeCylinderData coefficient largeError smallError nextError
    lowerDenominator middleDenominator upperDenominator largeErrorNonzero
    middleDenominatorNonzero errorOrdered nextErrorOrdered factorFour
    denominatorOrdered nextDenominatorOrdered errorIdentity denominatorIdentity
    selfObstruction nextObstruction
  exact data.impossible_of_coefficientNorm_cases coefficientNormCases

/-- After an index-two consecutive transition, the next consecutive
transition has index one. -/
theorem nextCoefficientIndexQuadrance_eq_one_of_eq_two
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest
      source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo :
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper = 1 := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two second) with
    rightIndexOne | rightIndexTwo
  · exact rightIndexOne
  · exact False.elim
      (Best.Consecutive.RepeatedIndex.repeatedIndexTwo_impossible first second leftIndexTwo rightIndexTwo)

end Purelib.NumberTheory.Approximation.Best.Consecutive.RepeatedIndex
