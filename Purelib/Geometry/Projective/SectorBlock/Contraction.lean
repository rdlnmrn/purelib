module
import Purelib.Geometry.Projective.Line.Hermitian

import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.BalancedRatio
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Affine
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Matrix
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Matrix
public import Purelib.Geometry.Projective.SectorBlock.Basic
public import Purelib.Geometry.Projective.SectorBlock.Tail
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Chordal.Matrix

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.Geometry.Projective.SectorBlock

open Purelib.LinearAlgebra.Coordinates2.Matrix

public section

namespace Purelib.Geometry.Projective.SectorBlock
namespace Tail.CompatibleTail

/-- Exact output weight of a compatible affine tail. -/
theorem act_weight {sector : Data.ComplexContinuedFraction.Encoding.Sector} {tail value scale :
  Data.Gaussian.Basic.Canonical}
    (compatible : Tail.CompatibleTail sector tail value) :
    Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine tail)) =
      2 * Data.Gaussian.Norm.Basic.normSq tail * (1 + Data.Gaussian.Norm.Basic.normSq scale *
        Data.Gaussian.Norm.Basic.normSq value) := by
  have firstCoordinate :
      scale * Data.Gaussian.Basic.Canonical.gamma * sector.rep * tail + scale =
        scale * (Data.Gaussian.Basic.Canonical.gamma * tail * value) := by
    rw [compatible.equation]
    apply Data.Gaussian.Basic.ext <;>
      simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;>
        ring1
  simp only [Proj.weight, Line.Matrix.act, Proj.affine, SectorBlock.Basic.block,
    Data.Gaussian.Basic.mul_one,
    Data.Gaussian.Basic.add_zero]
  rw [firstCoordinate, Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul,
    Data.Gaussian.Norm.Basic.normSq_mul, Constants.normSq_gamma]
  ring1

/-- One compatible output weight strictly dominates the factor needed for the relative chordal estimate. -/
theorem factor_weight_lt {sector : Data.ComplexContinuedFraction.Encoding.Sector} {tail value scale :
  Data.Gaussian.Basic.Canonical}
    (scaleNonzero : scale ≠ 0)
    (compatible : Tail.CompatibleTail sector tail value) :
    (1 + Data.Gaussian.Norm.Basic.normSq scale) * (1 + Data.Gaussian.Norm.Basic.normSq tail) <
      Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector)
        (Proj.affine tail)) := by
  have tailGreater := compatible.tail_norm_gt_one
  have tailPositive := (by decide : (0 : Fraction.Rational) < 1).trans tailGreater
  have scaleNormNonnegative := Data.Gaussian.Norm.Basic.normSq_nonneg scale
  have scaleNormPositive := Data.Gaussian.Norm.Basic.normSq_pos scaleNonzero
  have valueNormLower := compatible.band.1
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical value] at valueNormLower
  have onePlusTailLt :
      1 + Data.Gaussian.Norm.Basic.normSq tail < 2 * Data.Gaussian.Norm.Basic.normSq tail := by
    calc
      1 + Data.Gaussian.Norm.Basic.normSq tail < Data.Gaussian.Norm.Basic.normSq tail +
        Data.Gaussian.Norm.Basic.normSq tail :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct tailGreater
          (Data.Gaussian.Norm.Basic.normSq tail)
      _ = 2 * Data.Gaussian.Norm.Basic.normSq tail := by ring1
  have scalePartLe :
      1 + Data.Gaussian.Norm.Basic.normSq scale ≤ 1 + Data.Gaussian.Norm.Basic.normSq scale *
        Data.Gaussian.Norm.Basic.normSq value := by
    apply add_le_add le_rfl
    calc
      Data.Gaussian.Norm.Basic.normSq scale = Data.Gaussian.Norm.Basic.normSq scale * 1 := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq value :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          valueNormLower scaleNormNonnegative
  calc
    (1 + Data.Gaussian.Norm.Basic.normSq scale) * (1 + Data.Gaussian.Norm.Basic.normSq tail) <
        (1 + Data.Gaussian.Norm.Basic.normSq scale) * (2 * Data.Gaussian.Norm.Basic.normSq tail) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by exact add_pos_of_pos_of_nonneg (by decide) scaleNormNonnegative)
        onePlusTailLt
    _ ≤ (1 + Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq value) * (2 *
      Data.Gaussian.Norm.Basic.normSq tail) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scalePartLe
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          tailPositive.le)
    _ = Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector)
        (Proj.affine tail)) := by
      rw [compatible.act_weight]
      ring1

end Tail.CompatibleTail

namespace Contraction

/-- The completed sector-block determinant is minus the scale times the canonical Gaussian factor. -/
theorem block_det (scale : Data.Gaussian.Basic.Canonical) (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    Matrix2.determinant (SectorBlock.Basic.block scale sector) =
      -(scale * Data.Gaussian.Basic.Canonical.gamma) := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Matrix2.determinant, SectorBlock.Basic.block, Basic.sub_re, Basic.sub_im,
      Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im, Basic.zero_re, Basic.zero_im,
        Data.Gaussian.Basic.Canonical.gamma] <;>
    ring1

/-- A completed compatible block contracts affine two-tail squared chordal quadrance by `q(N(λ))`. -/
theorem affine_contraction {sector : Data.ComplexContinuedFraction.Encoding.Sector}
    {leftTail rightTail leftValue rightValue scale : Data.Gaussian.Basic.Canonical}
    (scaleNonzero : scale ≠ 0)
    (leftCompatible : Tail.CompatibleTail sector leftTail leftValue)
    (rightCompatible : Tail.CompatibleTail sector rightTail rightValue) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine leftTail))
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine rightTail)) ≤
      BalancedRatio.factor scale *
        Chordal.Basic.chordalSq (Proj.affine leftTail) (Proj.affine rightTail) := by
  let length := Data.Gaussian.Norm.Basic.normSq scale
  let leftNorm := Data.Gaussian.Norm.Basic.normSq leftTail
  let rightNorm := Data.Gaussian.Norm.Basic.normSq rightTail
  let numerator := 2 * length * Data.Gaussian.Norm.Basic.normSq (leftTail - rightTail)
  let outputDenominator :=
    Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector)
      (Proj.affine leftTail)) *
    Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector)
      (Proj.affine rightTail))
  let comparisonDenominator :=
    (1 + length) ^ 2 * ((1 + leftNorm) * (1 + rightNorm))
  have leftWeightLower := leftCompatible.factor_weight_lt scaleNonzero
  have rightWeightLower := rightCompatible.factor_weight_lt scaleNonzero
  have leftFactorPositive :
      0 < (1 + length) * (1 + leftNorm) :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg scale))
      (add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg leftTail))
  have rightFactorPositive :
      0 < (1 + length) * (1 + rightNorm) :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg scale))
      (add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg rightTail))
  have leftWeightPositive := leftFactorPositive.trans leftWeightLower
  have denominatorOrder : comparisonDenominator ≤ outputDenominator := by
    have strictProduct :
        ((1 + length) * (1 + leftNorm)) *
            ((1 + length) * (1 + rightNorm)) < outputDenominator := by
      calc
        ((1 + length) * (1 + leftNorm)) *
            ((1 + length) * (1 + rightNorm)) <
            Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector)
              (Proj.affine leftTail)) *
              ((1 + length) * (1 + rightNorm)) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
            leftWeightLower rightFactorPositive
        _ < outputDenominator :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            leftWeightPositive rightWeightLower
    exact (by
      calc
        comparisonDenominator =
            ((1 + length) * (1 + leftNorm)) *
              ((1 + length) * (1 + rightNorm)) := by
          dsimp only [comparisonDenominator]
          ring1
        _ ≤ outputDenominator := strictProduct.le)
  have comparisonPositive : 0 < comparisonDenominator := by
    dsimp only [comparisonDenominator]
    exact Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct
        (add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg scale)) 2)
      (Fraction.Order.Arithmetic.mul_pos_direct
        (add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg leftTail))
        (add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg rightTail)))
  have numeratorNonnegative : 0 ≤ numerator := by
    dsimp only [numerator, length]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg scale))
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
  rw [Mat2.chordalSq_act_affine,
    Contraction.block_det, Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul,
      Constants.normSq_gamma,
    Affine.chordalSq_affine, BalancedRatio.factor]
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical scale]
  rw [show Data.Gaussian.Norm.Basic.normSq scale * 2 = 2 * Data.Gaussian.Norm.Basic.normSq scale by
    ring1]
  change numerator / outputDenominator ≤
    (2 * length / (1 + length) ^ 2) *
      (Data.Gaussian.Norm.Basic.normSq (leftTail - rightTail) /
        ((1 + leftNorm) * (1 + rightNorm)))
  calc
    numerator / outputDenominator ≤ numerator / comparisonDenominator :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative comparisonPositive denominatorOrder
    _ = (2 * length / (1 + length) ^ 2) *
        (Data.Gaussian.Norm.Basic.normSq (leftTail - rightTail) /
          ((1 + leftNorm) * (1 + rightNorm))) :=
      (Fraction.Field.div_mul_div_direct
        (2 * length) ((1 + length) ^ 2)
        (Data.Gaussian.Norm.Basic.normSq (leftTail - rightTail))
        ((1 + leftNorm) * (1 + rightNorm))).symm

/-- Uniform half-contraction corollary. -/
theorem affine_contraction_half {sector : Data.ComplexContinuedFraction.Encoding.Sector}
    {leftTail rightTail leftValue rightValue scale : Data.Gaussian.Basic.Canonical}
    (scaleNonzero : scale ≠ 0)
    (leftCompatible : Tail.CompatibleTail sector leftTail leftValue)
    (rightCompatible : Tail.CompatibleTail sector rightTail rightValue) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine leftTail))
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine rightTail)) ≤
      (1 / 2 : Fraction.Rational) *
        Chordal.Basic.chordalSq (Proj.affine leftTail) (Proj.affine rightTail) := by
  calc
    Chordal.Basic.chordalSq
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine leftTail))
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine rightTail)) ≤
        BalancedRatio.factor scale * Chordal.Basic.chordalSq (Proj.affine leftTail)
          (Proj.affine rightTail) :=
      Contraction.affine_contraction scaleNonzero leftCompatible rightCompatible
    _ ≤ (1 / 2 : Fraction.Rational) *
        Chordal.Basic.chordalSq (Proj.affine leftTail) (Proj.affine rightTail) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (BalancedRatio.factor_le_half scale)
        (Chordal.Basic.chordalSq_nonneg _ _)

/-- Exact weight of the image of the formal projective tail `ω`. -/
theorem act_omega_weight (scale : Data.Gaussian.Basic.Canonical) (sector :
  Data.ComplexContinuedFraction.Encoding.Sector) :
    Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) =
      2 * (1 + Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq sector.rep) :=
        by
  simp only [Proj.weight, Line.Matrix.act, Proj.omega, SectorBlock.Basic.block,
    Data.Gaussian.Basic.mul_one,
    Data.Gaussian.Basic.mul_zero,
    Data.Gaussian.Basic.add_zero, Data.Gaussian.Norm.Basic.normSq_mul, Constants.normSq_gamma]
  ring1

/-- The terminal image weight is at least one plus the scale quadrance. -/
theorem scale_factor_le_omega_weight (scale : Data.Gaussian.Basic.Canonical) (sector :
  Data.ComplexContinuedFraction.Encoding.Sector) :
    1 + Data.Gaussian.Norm.Basic.normSq scale ≤
      Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) := by
  have scaleNonnegative := Data.Gaussian.Norm.Basic.normSq_nonneg scale
  have representativeNormLower := Sector.Basic.rep_norm_lower sector
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical sector.rep] at representativeNormLower
  have productOrder : Data.Gaussian.Norm.Basic.normSq scale ≤ Data.Gaussian.Norm.Basic.normSq scale *
    Data.Gaussian.Norm.Basic.normSq sector.rep := by
    calc
      Data.Gaussian.Norm.Basic.normSq scale = Data.Gaussian.Norm.Basic.normSq scale * 1 := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq sector.rep :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          representativeNormLower scaleNonnegative
  have sumNonnegative :
      0 ≤ 1 + Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq sector.rep :=
    add_nonneg (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct scaleNonnegative
        (Data.Gaussian.Norm.Basic.normSq_nonneg sector.rep))
  calc
    1 + Data.Gaussian.Norm.Basic.normSq scale ≤ 1 + Data.Gaussian.Norm.Basic.normSq scale *
      Data.Gaussian.Norm.Basic.normSq sector.rep :=
      add_le_add le_rfl productOrder
    _ ≤ 2 * (1 + Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq sector.rep)
      := by
      calc
        1 + Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq sector.rep =
            1 * (1 + Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq
              sector.rep) := by ring1
        _ ≤ 2 * (1 + Data.Gaussian.Norm.Basic.normSq scale * Data.Gaussian.Norm.Basic.normSq
          sector.rep) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) sumNonnegative
    _ = Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) :=
      (Contraction.act_omega_weight scale sector).symm

/-- Completed-block contraction between one compatible affine tail and the formal terminal tail `ω`.

The retained completed-sector matrix acts on both original tails. Its exact determinant and weight equations bound their
squared chordal quadrance by the original balanced scale factor. -/
theorem affine_omega_contraction {sector : Data.ComplexContinuedFraction.Encoding.Sector} {tail value scale :
  Data.Gaussian.Basic.Canonical}
    (scaleNonzero : scale ≠ 0)
    (compatible : Tail.CompatibleTail sector tail value) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine tail))
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) ≤
      BalancedRatio.factor scale * Chordal.Basic.chordalSq (Proj.affine tail) Proj.omega := by
  let length := Data.Gaussian.Norm.Basic.normSq scale
  let tailNorm := Data.Gaussian.Norm.Basic.normSq tail
  let numerator := 2 * length
  let outputDenominator :=
    Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) *
    Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine tail))
  let comparisonDenominator := (1 + length) ^ 2 * (1 + tailNorm)
  have truncationDenominator :
      (Data.Gaussian.Norm.Basic.normSq (SectorBlock.Basic.block scale sector).a +
        Data.Gaussian.Norm.Basic.normSq (SectorBlock.Basic.block scale sector).c) *
          (Data.Gaussian.Norm.Basic.normSq ((SectorBlock.Basic.block scale sector).a * tail +
            (SectorBlock.Basic.block scale sector).b) +
            Data.Gaussian.Norm.Basic.normSq ((SectorBlock.Basic.block scale sector).c * tail +
              (SectorBlock.Basic.block scale sector).d)) =
        outputDenominator := by
    dsimp only [outputDenominator, Proj.weight, Line.Matrix.act,
      Proj.omega, Proj.affine]
    rewrite [Data.Gaussian.Basic.mul_one, Data.Gaussian.Basic.mul_one,
      Data.Gaussian.Basic.mul_one, Data.Gaussian.Basic.mul_one,
      Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.mul_zero,
      Data.Gaussian.Basic.add_zero, Data.Gaussian.Basic.add_zero]
    rfl
  have affineLower := compatible.factor_weight_lt scaleNonzero
  have omegaLower := Contraction.scale_factor_le_omega_weight scale sector
  have scaleFactorPositive : 0 < 1 + length :=
    add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg scale)
  have tailFactorPositive : 0 < 1 + tailNorm :=
    add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg tail)
  have omegaWeightPositive :
      0 < Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) :=
    scaleFactorPositive.trans_le omegaLower
  have denominatorOrder : comparisonDenominator ≤ outputDenominator := by
    calc
      comparisonDenominator =
          (1 + length) * ((1 + length) * (1 + tailNorm)) := by
        dsimp only [comparisonDenominator]
        ring1
      _ ≤ Proj.weight (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) *
          ((1 + length) * (1 + tailNorm)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct omegaLower
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            scaleFactorPositive.le tailFactorPositive.le)
      _ ≤ outputDenominator :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          affineLower.le omegaWeightPositive.le
  have comparisonPositive : 0 < comparisonDenominator := by
    dsimp only [comparisonDenominator]
    exact Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct scaleFactorPositive 2)
      tailFactorPositive
  have numeratorNonnegative : 0 ≤ numerator := by
    dsimp only [numerator, length]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Data.Gaussian.Norm.Basic.normSq_nonneg scale)
  rw [Mat2.chordalSq_truncation,
    Contraction.block_det, Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul,
      Constants.normSq_gamma,
    Affine.chordalSq_omega, BalancedRatio.factor]
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical scale]
  rw [show Data.Gaussian.Norm.Basic.normSq scale * 2 = 2 * Data.Gaussian.Norm.Basic.normSq scale by
    ring1]
  rw [truncationDenominator]
  change numerator / outputDenominator ≤
    (2 * length / (1 + length) ^ 2) * (1 / (1 + tailNorm))
  calc
    numerator / outputDenominator ≤ numerator / comparisonDenominator :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative comparisonPositive denominatorOrder
    _ = ((2 * length) * 1) /
        ((1 + length) ^ 2 * (1 + tailNorm)) := by
      dsimp only [numerator, comparisonDenominator]
      rw [Fraction.Field.mul_one_direct]
    _ = (2 * length / (1 + length) ^ 2) * (1 / (1 + tailNorm)) :=
      (Fraction.Field.div_mul_div_direct
        (2 * length) ((1 + length) ^ 2) 1 (1 + tailNorm)).symm
end Contraction

namespace Tail

/-- Full completed-block contraction, including affine/terminal pairs. -/
theorem contraction {sector : Data.ComplexContinuedFraction.Encoding.Sector} (scale : Data.Gaussian.Basic.Canonical)
  (scaleNonzero : scale ≠ 0)
    (left right : Tail sector) :
    Chordal.Basic.chordalSq (Line.Matrix.act (SectorBlock.Basic.block scale sector) left.point)
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) right.point) ≤
      BalancedRatio.factor scale * Chordal.Basic.chordalSq left.point right.point := by
  cases left with
  | omega =>
      cases right with
      | omega =>
          change Chordal.Basic.chordalSq
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.omega :
                GaussianLine))
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) ≤
            BalancedRatio.factor scale * Chordal.Basic.chordalSq (Proj.omega :
              GaussianLine) Proj.omega
          have outputZero : Chordal.Basic.chordalSq
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.omega :
                GaussianLine))
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega) = 0 :=
            Chordal.Basic.chordalSq_eq_zero_of_equivalent rfl
          have inputZero : Chordal.Basic.chordalSq (Proj.omega : GaussianLine) Proj.omega =
            0 :=
            Chordal.Basic.chordalSq_eq_zero_of_equivalent rfl
          rw [outputZero, inputZero]
          rw [Fraction.Field.mul_zero_direct]
      | affine tail value compatible =>
          change Chordal.Basic.chordalSq
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.omega :
                GaussianLine))
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine tail)) ≤
            BalancedRatio.factor scale * Chordal.Basic.chordalSq (Proj.omega :
              GaussianLine)
              (Proj.affine tail)
          rw [Chordal.Basic.chordalSq_comm
            (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.omega :
              GaussianLine))
            (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine tail)),
            Chordal.Basic.chordalSq_comm (Proj.omega : GaussianLine) (Proj.affine tail)]
          exact Contraction.affine_omega_contraction scaleNonzero compatible
  | affine leftTail leftValue leftCompatible =>
      cases right with
      | omega =>
          change Chordal.Basic.chordalSq
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine leftTail))
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.omega :
                GaussianLine)) ≤
            BalancedRatio.factor scale * Chordal.Basic.chordalSq (Proj.affine leftTail)
              (Proj.omega : GaussianLine)
          exact Contraction.affine_omega_contraction scaleNonzero leftCompatible
      | affine rightTail rightValue rightCompatible =>
          change Chordal.Basic.chordalSq
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine leftTail))
              (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine rightTail)) ≤
            BalancedRatio.factor scale * Chordal.Basic.chordalSq (Proj.affine leftTail)
              (Proj.affine rightTail)
          exact Contraction.affine_contraction scaleNonzero leftCompatible rightCompatible

end Tail
end Purelib.Geometry.Projective.SectorBlock

end
