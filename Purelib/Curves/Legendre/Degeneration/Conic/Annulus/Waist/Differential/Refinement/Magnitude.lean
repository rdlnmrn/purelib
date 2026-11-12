module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Program
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Width-controlled magnitudes of actual waist integral samples

The retained cofactor reading has the original uniform positive quadrance
floor. Its coefficient bound and the existing finite refinement comparison
bound control every actual integral sample by the original squared chart
width. This supplies quantitative small-span bounds, including branch-safe
value spans, without replacing the original process or differential owner.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Piece

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Polynomial.Gaussian

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {accuracy : Fraction.Rational}

/-- The original cached coefficient is bounded using its own square residual and uniform cofactor floor. -/
private theorem coefficient_normSq_le (initial : Piece data simple quarter regular bound accuracy) :
    normSq initial.cell.reading.center ≤ 16 * data.numeratorBound := by
  let root := initial.cell.reading.centerRoot
  have floor : (1 / 16 : Fraction.Rational) ≤ normSq root :=
    UnitRoot.root_normSq_lower site
      (point_inside site parameter (direction quarter initial.span.lower) regular bound)
      initial.cell.reading.centerResidual
  have positive : 0 < normSq root := (by decide +kernel : (0 : Fraction.Rational) < 1 / 16).trans_le floor
  have nonzero : root ≠ 0 := by
    intro zero
    have normZero := (congrArg normSq zero).trans Norm.Basic.normSq_zero
    exact positive.ne' normZero
  have inverseBound := Fraction.Order.Field.inv_le_inv_of_pos_direct
    (by decide +kernel : (0 : Fraction.Rational) < 1 / 16) floor
  rewrite [show ((1 / 16 : Fraction.Rational)⁻¹) = 16 by decide +kernel] at inverseBound
  rewrite [initial.cell.reading.center_eq]
  unfold Bounds.Data.coefficient
  rewrite [Field.normSq_div _ _ nonzero]
  calc
    _ ≤ normSq (data.numerator quarter regular bound initial.span.lower) * 16 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct inverseBound (Norm.Basic.normSq_nonneg _)
    _ ≤ data.numeratorBound * 16 := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (data.numerator_normSq_le quarter regular bound initial.span.lower) (by decide +kernel)
    _ = _ := by ring1

/-- The original single-cell integral has a bound proportional to its exact squared chart width. -/
theorem model_normSq_le (initial : Piece data simple quarter regular bound accuracy) :
    normSq initial.model.integralSample ≤ initial.span.width ^ 2 * (16 * data.numeratorBound) := by
  have sample := Cell.Basic.CellModel.integralSample_constant initial.model initial.cell.reading.center rfl
  rewrite [sample, Norm.Basic.normSq_mul, initial.displacement_sq]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct (coefficient_normSq_le initial)
    (Arithmetic.sq_nonneg_direct _)

/-- The retained program's common magnitude bound scales with the original squared chart width and allowance. -/
theorem centerBound_le (initial : Piece data simple quarter regular bound accuracy) :
    initial.program.centerBound ≤
      initial.span.width ^ 2 * (32 * data.numeratorBound + 32 * initial.cell.allowance) := by
  have firstSample : normSq (initial.program.model 0).integralSample ≤
      initial.span.width ^ 2 * (16 * data.numeratorBound) := by
    change normSq (Path.Basic.PathModel.mk [initial.model]).integralSample ≤ _
    rewrite [Path.Basic.PathModel.singleton_integralSample]
    exact initial.model_normSq_le
  change 2 * (normSq (initial.program.model 0).integralSample + initial.program.errorScale) ≤ _
  rewrite [initial.errorScale_eq]
  apply (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct firstSample (Fraction.Order.Basic.le_refl _))
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)).trans_eq
  ring1

/-- Every actual refined sample obeys the original width-controlled magnitude bound, at every finite depth. -/
theorem sample_normSq_le (initial : Piece data simple quarter regular bound accuracy) (depth : Nat) :
    normSq (initial.program.model depth).integralSample ≤
      initial.span.width ^ 2 * (32 * data.numeratorBound + 32 * initial.cell.allowance) := by
  have sampled := initial.program.sample_bounded depth
  rewrite [← Norm.Basic.normSq_eq_canonical] at sampled
  exact sampled.trans initial.centerBound_le

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement.Piece
