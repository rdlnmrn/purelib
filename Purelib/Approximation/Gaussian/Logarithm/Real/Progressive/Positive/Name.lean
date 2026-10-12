module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Domain
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Name
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.DyadicScaling
import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
public import Purelib.Approximation.Gaussian.Name.PositiveReal.Dyadic
import Purelib.Approximation.Gaussian.Name.PositiveReal.Preparation
import Purelib.Data.Gaussian.Dyadic
import Purelib.Data.Rat.Dyadic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Dyadic.Normalization
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name (PositiveReal)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.PositiveReal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.Name

/-- The retained positive-real lower bound makes the explicitly refined and dyadically scaled input lie in the real
logarithm chart.

Every possible scaled reading is real with coordinate between one half and two. -/
theorem automaticLocalChart {input :
  Named} (positive : PositiveReal input) :
    Domain.Chart
      (DyadicScaling.scaledInput
        (Preparation.refinedInput positive) (Dyadic.centerNormalization positive).direction
          (Dyadic.centerNormalization positive).exponent) where
  possible_real_chart := by
    intro value possible
    rcases possible with ⟨scaleValue, sourceValue,
      scalePossible, sourcePossible, rfl⟩
    change scaleValue =
      Dyadic.dyadicFactor
        (Dyadic.centerNormalization positive).direction
        (Dyadic.centerNormalization positive).exponent at scalePossible
    subst scaleValue
    let normalization := Dyadic.centerNormalization positive
    let scalar := Dyadic.Basic.factor
      normalization.direction normalization.exponent
    have sourceData := Preparation.refined_possible_real_lower positive sourcePossible
    have deviation := Preparation.candidate_deviation positive sourcePossible
    have scalarPositive : 0 < scalar :=
      Dyadic.Basic.factor_pos _ _
    have scaledDeviationLower :
        -(scalar * Preparation.refinementSlack positive) ≤
          scalar * sourceValue.re - scalar * (Preparation.refinedCenter positive).re := by
      have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        deviation.1 scalarPositive.le
      calc
        -(scalar * Preparation.refinementSlack positive) =
            scalar * (-Preparation.refinementSlack positive) := by ring1
        _ ≤ scalar * (sourceValue.re - (Preparation.refinedCenter positive).re) := scaled
        _ = scalar * sourceValue.re - scalar * (Preparation.refinedCenter positive).re := by
          ring1
    have scaledDeviationUpper :
        scalar * sourceValue.re - scalar * (Preparation.refinedCenter positive).re ≤
          scalar * Preparation.refinementSlack positive := by
      have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        deviation.2 scalarPositive.le
      calc
        scalar * sourceValue.re - scalar * (Preparation.refinedCenter positive).re =
            scalar * (sourceValue.re - (Preparation.refinedCenter positive).re) := by
          ring1
        _ ≤ scalar * Preparation.refinementSlack positive := scaled
    have centerIdentity :
        scalar * (Preparation.refinedCenter positive).re =
          Dyadic.Basic.normalized
            (Preparation.refinedCenter positive).re normalization.direction
              normalization.exponent :=
      (Dyadic.Basic.normalized_eq_factor_mul _ _ _).symm
    have lower : 1 / 2 ≤ scalar * sourceValue.re := by
      calc
        (1 / 2 : Fraction.Rational) = 3 / 4 - 1 / 4 := by decide
        _ ≤ Dyadic.Basic.normalized
              (Preparation.refinedCenter positive).re normalization.direction
                normalization.exponent -
            scalar * Preparation.refinementSlack positive :=
          Fraction.Order.Arithmetic.sub_le_sub_direct normalization.lower (Dyadic.scaledSlack_le_quarter positive)
        _ = scalar * (Preparation.refinedCenter positive).re -
            scalar * Preparation.refinementSlack positive := by rw [centerIdentity]
        _ ≤ scalar * sourceValue.re := by
          apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
            (c := -(scalar * (Preparation.refinedCenter positive).re))
          calc
            (scalar * (Preparation.refinedCenter positive).re -
                scalar * Preparation.refinementSlack positive) +
                -(scalar * (Preparation.refinedCenter positive).re) =
                -(scalar * Preparation.refinementSlack positive) := by ring1
            _ ≤ scalar * sourceValue.re -
                scalar * (Preparation.refinedCenter positive).re := scaledDeviationLower
            _ = scalar * sourceValue.re +
                -(scalar * (Preparation.refinedCenter positive).re) := by ring1
    have upper : scalar * sourceValue.re ≤ 2 := by
      calc
        scalar * sourceValue.re ≤
            scalar * (Preparation.refinedCenter positive).re +
              scalar * Preparation.refinementSlack positive := by
          apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
            (c := -(scalar * (Preparation.refinedCenter positive).re))
          calc
            scalar * sourceValue.re +
                -(scalar * (Preparation.refinedCenter positive).re) =
                scalar * sourceValue.re -
                  scalar * (Preparation.refinedCenter positive).re := by ring1
            _ ≤ scalar * Preparation.refinementSlack positive := scaledDeviationUpper
            _ = (scalar * (Preparation.refinedCenter positive).re +
                scalar * Preparation.refinementSlack positive) +
                -(scalar * (Preparation.refinedCenter positive).re) := by ring1
        _ = Dyadic.Basic.normalized
              (Preparation.refinedCenter positive).re normalization.direction
                normalization.exponent +
            scalar * Preparation.refinementSlack positive := by rw [centerIdentity]
        _ ≤ 3 / 2 + 1 / 4 :=
          add_le_add normalization.upper (Dyadic.scaledSlack_le_quarter positive)
        _ ≤ 2 := by decide
    exact
      ⟨Dyadic.dyadicFactor_mul_im_of_real
          normalization.direction normalization.exponent sourceData.1,
        by
          rw [Dyadic.dyadicFactor_mul_re]
          exact lower,
        by
          rw [Dyadic.dyadicFactor_mul_re]
          exact upper⟩

/-- Construct the dyadic logarithm chart from the retained refined input and its computed center normalization. -/
def automaticChart {input :
  Named} (positive : PositiveReal input) :
    Domain.DyadicChart (Preparation.refinedInput positive) :=
  { direction := (Dyadic.centerNormalization positive).direction
    exponent := (Dyadic.centerNormalization positive).exponent
    localChart := automaticLocalChart positive }

/-- Total positive-real logarithm entry point from a finite lower-bound certificate. -/
def named (input :
  Named) (positive : PositiveReal input) : Named :=
  Dyadic.Name.named
    (Preparation.refinedInput positive) (automaticChart
      positive)
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.Name

end
