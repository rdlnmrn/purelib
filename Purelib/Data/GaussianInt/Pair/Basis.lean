module
public import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.GaussianInt.Pair

open Purelib.Data.GaussianInt.Pair.Basic

@[expose] public section

/-!
# Finite approximation algebra for Hurwitz convergents

This module isolates the calculation underlying a second-kind approximation
comparison.  The error of `p/q` is represented without division as `qz-p`.
Adjacent finite continuants have determinant `1` or `-1`, so every displayed
Gaussian-integer competitor has explicit coefficients in that adjacent
continuant basis.  No enumeration of Gaussian rationals is used.
-/

namespace Purelib.Data.GaussianInt.Pair.Basis

/-- Compute the cross determinant of two retained integral numerator/denominator pairs. -/
def determinant (left right : ConvergentPair) : GaussianInt :=
  left.numerator * right.denominator -
    right.numerator * left.denominator

/-- Require the displayed pair determinant to be exactly one or negative one. -/
def HasUnitDeterminant (left right : ConvergentPair) : Prop :=
  determinant left right = 1 ∨ determinant left right = -1

/-- A displayed determinant equal to one or negative one has square one. -/
theorem determinant_mul_self_eq_one {left right : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant left right) :
    determinant left right * determinant left right = 1 := by
  rcases unitDeterminant with positive | negative
  · rw [positive]
    exact GaussianInt.one_mul 1
  · rw [negative]
    ring1

/-- Compute the current-pair coefficient from the two retained cross determinants.

When the current/previous determinant is one or negative one, this explicit value
reconstructs the competitor together with previousCoefficient. -/
def currentCoefficient (current previous competitor : ConvergentPair) :
    GaussianInt :=
  determinant current previous * determinant competitor previous

/-- Compute the previous-pair coefficient from the retained basis and competitor
determinants.

The product uses the same current/previous determinant as currentCoefficient; the
reconstruction laws require that determinant to equal one or negative one. -/
def previousCoefficient (current previous competitor : ConvergentPair) :
    GaussianInt :=
  determinant current previous * determinant current competitor

/-- The explicit determinant coefficients reconstruct a competitor's numerator in a
signed-unit pair basis. -/
theorem competitor_numerator_decomposition
    {current previous competitor : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant current previous) :
    currentCoefficient current previous competitor * current.numerator +
        previousCoefficient current previous competitor * previous.numerator =
      competitor.numerator := by
  have square := determinant_mul_self_eq_one unitDeterminant
  have algebraic :
      currentCoefficient current previous competitor * current.numerator +
          previousCoefficient current previous competitor *
            previous.numerator =
        (determinant current previous * determinant current previous) *
          competitor.numerator := by
    apply GaussianInt.ext <;>
      simp only [currentCoefficient, previousCoefficient, determinant,
        GaussianInt.add_re,
        GaussianInt.add_im,
        GaussianInt.sub_re,
        GaussianInt.sub_im,
        GaussianInt.mul_re,
        GaussianInt.mul_im] <;>
      ring1
  rw [algebraic, square]
  exact GaussianInt.one_mul _

/-- The explicit determinant coefficients reconstruct a competitor's denominator in a
signed-unit pair basis. -/
theorem competitor_denominator_decomposition
    {current previous competitor : ConvergentPair}
    (unitDeterminant : HasUnitDeterminant current previous) :
    currentCoefficient current previous competitor * current.denominator +
        previousCoefficient current previous competitor * previous.denominator =
      competitor.denominator := by
  have square := determinant_mul_self_eq_one unitDeterminant
  have algebraic :
      currentCoefficient current previous competitor * current.denominator +
          previousCoefficient current previous competitor *
            previous.denominator =
        (determinant current previous * determinant current previous) *
          competitor.denominator := by
    apply GaussianInt.ext <;>
      simp only [currentCoefficient, previousCoefficient, determinant,
        GaussianInt.add_re,
        GaussianInt.add_im,
        GaussianInt.sub_re,
        GaussianInt.sub_im,
        GaussianInt.mul_re,
        GaussianInt.mul_im] <;>
      ring1
  rw [algebraic, square]
  exact GaussianInt.one_mul _

/-- Represent an integral Gaussian value by that numerator and denominator one. -/
def integralPair (value : GaussianInt) : ConvergentPair := ⟨value, 1⟩
end Purelib.Data.GaussianInt.Pair.Basis

end
