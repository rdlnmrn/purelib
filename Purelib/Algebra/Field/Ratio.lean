module

import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11: triangle proportions

The denominator-free theorem records exactly the three cross-products supplied
by the Spread law.  The printed quotient chain is then recovered only from its
visible nonzero denominators.  This separation keeps the result meaningful in
finite fields even when a displayed quotient would be undefined geometrically.
-/

namespace Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Equal cross products give equal ratios with nonzero denominators.

Each denominator carries its own nonzero certificate, which justifies clearing and cancelling the two divisions. -/
theorem Field.Ratio.ratio_eq_of_cross_product
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

/-- Equal ratios with nonzero denominators give equal cross products.

The two nonzero certificates justify multiplying out both divisions. -/
theorem Field.Ratio.cross_product_of_ratio_eq
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (equalRatios :
      leftNumerator / leftDenominator =
        rightNumerator / rightDenominator) :
    leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := by
  calc
    leftNumerator * rightDenominator =
        ((leftNumerator / leftDenominator) * leftDenominator) *
          rightDenominator := by
      rw [ExplicitField.div_mul_cancel leftNumerator leftNonzero]
    _ = (leftNumerator / leftDenominator) *
        (leftDenominator * rightDenominator) := by ring1
    _ = (rightNumerator / rightDenominator) *
        (leftDenominator * rightDenominator) := by rw [equalRatios]
    _ = ((rightNumerator / rightDenominator) * rightDenominator) *
        leftDenominator := by ring1
    _ = rightNumerator * leftDenominator := by
      rw [ExplicitField.div_mul_cancel rightNumerator rightNonzero]
end Purelib.Algebra

end

end

section
/-!
# Divine Proportions, Chapter 1 finite calculation

The introductory `4,5,7` triangle is recorded entirely through its three
quadrances.  Its Archimedes value is the common numerator in the three spread
ratios, so Exercise 1.1 reduces to two exact finite fraction calculations.
Exercise 1.2 asks the reader to inspect other books; it makes no mathematical
claim to encode in Lean.
-/

@[expose] public section

namespace Purelib.Algebra.Field.Ratio

section ChapterOneExamples

variable {K : Type*} [ExplicitField K]

/-- Equal cross products give equal ratios with nonzero denominators.

Each denominator carries its own nonzero certificate, which justifies cancelling the two divisions. -/
private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]
end ChapterOneExamples
end Purelib.Algebra.Field.Ratio

end

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7 worked examples

This module records the exact rational calculation of Example 7.2 and the
fully executable finite-field calculation of Example 7.3.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSeven

namespace ChapterSevenExamples

/-- Equal cross products give equal ratios with nonzero denominators.

Each denominator carries its own nonzero certificate, which justifies clearing and cancelling the two divisions. -/
private theorem ratio_eq_of_cross_product
    {K : Type*} [ExplicitField K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

end ChapterSevenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSeven

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7 field-fragment examples

The book's two complex examples need only one explicitly supplied element
`i` satisfying `i²=-1`.  Keeping that finite field fragment abstract makes the
same proofs usable in admissible finite fields and in the constructive
Gaussian rationals; no completed complex carrier is introduced.
-/

namespace formalisations.DivineProportions.Chapters.Examples

namespace ChapterSevenFieldFragments

variable {K : Type*} [ExplicitField K]

/-- Equal cross products give equal ratios with nonzero denominators.

Each denominator carries its own nonzero certificate, which justifies clearing and cancelling the two divisions. -/
private theorem ratio_eq_of_cross_product
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) * rightDenominator⁻¹ := by
          ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

end ChapterSevenFieldFragments

end formalisations.DivineProportions.Chapters.Examples

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6 worked examples

The numerical examples use the project's executable constructive rational
field.  Every equality below reduces to finite integer arithmetic; no decimal
or completed-real interpretation is involved.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSix

namespace ChapterSixExamples

/-- Equal cross products give equal ratios with nonzero denominators.

Each denominator carries its own nonzero certificate, which justifies clearing and cancelling the two divisions. -/
private theorem ratio_eq_of_cross_product
    {K : Type*} [ExplicitField K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

end ChapterSixExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSix

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 rational examples

The two examples below retain the source's literal rational coordinates.  All
side matches and spread matches are explicit finite permutation witnesses.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTen

namespace ChapterTenExamples

/-- Equal cross products give equal ratios with nonzero denominators.

Each denominator carries its own nonzero certificate, which justifies clearing and cancelling the two divisions. -/
private theorem ratio_eq_of_cross_product
    {K : Type*} [ExplicitField K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel :
      rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
      rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
      rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

end ChapterTenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterTen

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
public section
namespace Purelib.Algebra.Field.Ratio

variable {K : Type*} [ExplicitField K]

/-- Equal quantities with retained scalar factorizations determine the ratio of their residual factors.

The left coefficient is nonzero; the left residual equals the ratio of the right and left coefficients times the right
residual. -/
public theorem scale_eq_of_equal_products
    (leftRatio rightRatio leftSpread rightSpread leftQuadrance
      rightQuadrance : K)
    (leftRatioNonzero : leftRatio ≠ 0)
    (leftFactor : leftSpread = leftRatio * leftQuadrance)
    (rightFactor : rightSpread = rightRatio * rightQuadrance)
    (spreadsEqual : leftSpread = rightSpread) :
    leftQuadrance = (rightRatio / leftRatio) * rightQuadrance := by
  apply ExplicitField.eq_of_mul_eq_mul_left leftRatioNonzero
  calc
    leftRatio * leftQuadrance = leftSpread := leftFactor.symm
    _ = rightSpread := spreadsEqual
    _ = rightRatio * rightQuadrance := rightFactor
    _ = ((rightRatio / leftRatio) * leftRatio) * rightQuadrance := by
      rw [ExplicitField.div_mul_cancel rightRatio leftRatioNonzero]
    _ = leftRatio *
        ((rightRatio / leftRatio) * rightQuadrance) := by ring1

end Purelib.Algebra.Field.Ratio
end

end
