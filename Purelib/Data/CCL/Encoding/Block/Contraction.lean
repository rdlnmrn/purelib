module

import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.BalancedRatio
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Chordal.Scale
public import Purelib.Geometry.Projective.Homography.Scale
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
public import Purelib.Geometry.Projective.SectorBlock.Basic
import Purelib.Geometry.Projective.SectorBlock.Contraction
import Purelib.Geometry.Projective.SectorBlock.Tail
public import Purelib.Geometry.Projective.SectorBlock.Tail.Projective
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic

/-!
# Choice-free completed-block chordal contraction

This file proves the affine two-tail part of the companion paper's completed
CCL block contraction.  The proof is entirely cross-multiplied over explicit
fractions; no square root, limit, supremum, or inherited ordered-field
division theorem is used.
-/

@[expose] public section

namespace Purelib.Data.CCL.Encoding.Block.Contraction

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The regular decoder matrix is the sector block with the retained gamma-power scale. -/
theorem regularBlock_eq_block (exponent : Nat) (sector :
  ComplexContinuedFraction.Encoding.Sector) :
    Block.Matrix.regularBlock exponent sector =
      SectorBlock.Basic.block (Power.natPow Basic.Canonical.gamma exponent) sector := by
  apply Matrix2.ext
  · rw [Block.Matrix.regularBlock, SectorBlock.Basic.block, Power.natPow_succ]
  · rfl
  · rfl
  · rfl

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- A regular block reduces chordal squared distance between compatible sector tails by at least a factor of one half.
-/
theorem regularBlock_contraction_half {sector : ComplexContinuedFraction.Encoding.Sector}
  (exponent : Nat)
    (left right : Geometry.Projective.SectorBlock.Tail sector) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (Block.Matrix.regularBlock exponent sector)
          left.point)
        (Line.Matrix.act (Block.Matrix.regularBlock exponent sector)
          right.point) ≤
      (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point := by
  rw [Block.Contraction.regularBlock_eq_block]
  calc
    Chordal.Basic.chordalSq (Line.Matrix.act (SectorBlock.Basic.block (Power.natPow Basic.Canonical.gamma exponent)
      sector) left.point)
        (Line.Matrix.act (SectorBlock.Basic.block (Power.natPow Basic.Canonical.gamma exponent) sector) right.point) ≤
        BalancedRatio.factor (Power.natPow Basic.Canonical.gamma exponent) * Chordal.Basic.chordalSq left.point
          right.point :=
      Geometry.Projective.SectorBlock.Tail.contraction (Power.natPow Basic.Canonical.gamma exponent)
        (Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent) left right
    _ ≤ (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (BalancedRatio.factor_le_half _) (Chordal.Basic.chordalSq_nonneg _ _)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The initial-low decoder matrix is the retained gamma power times the sector block with reciprocal scale. -/
theorem lowBlock_eq_scaledBlock (exponent : Nat) (sector :
  ComplexContinuedFraction.Encoding.Sector) :
    Block.Matrix.lowBlock exponent sector =
      Homography.Scale.scaleMatrix (Power.natPow Basic.Canonical.gamma exponent)
        (SectorBlock.Basic.block (Power.natPow Basic.Canonical.gamma exponent)⁻¹ sector) := by
  let power := Power.natPow Basic.Canonical.gamma exponent
  have powerNonzero : power ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
  have cancel : power * power⁻¹ = 1 :=
    Basic.Canonical.mul_inv_cancel power powerNonzero
  apply Matrix2.ext
  · change Basic.Canonical.gamma * sector.rep = power * (power⁻¹ * Basic.Canonical.gamma * sector.rep)
    calc
      Basic.Canonical.gamma * sector.rep = 1 * (Basic.Canonical.gamma * sector.rep) :=
        (Basic.one_mul _).symm
      _ = (power * power⁻¹) * (Basic.Canonical.gamma * sector.rep) := by rw [cancel]
      _ = power * (power⁻¹ * Basic.Canonical.gamma * sector.rep) := by
        rw [Basic.mul_assoc,
          Basic.mul_assoc]
  · change (1 : Basic.Canonical) = power * power⁻¹
    exact cancel.symm
  · change Power.natPow Basic.Canonical.gamma (exponent + 1) = power * Basic.Canonical.gamma
    rfl
  · change (0 : Basic.Canonical) = power * 0
    exact (Basic.mul_zero power).symm

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- An initial-low block reduces chordal squared distance between compatible sector tails by at least a factor of one
half. -/
theorem lowBlock_contraction_half {sector : ComplexContinuedFraction.Encoding.Sector}
  (exponent : Nat)
    (left right : Geometry.Projective.SectorBlock.Tail sector) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (Block.Matrix.lowBlock exponent sector)
          left.point)
        (Line.Matrix.act (Block.Matrix.lowBlock exponent sector)
          right.point) ≤
      (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point := by
  let power := Power.natPow Basic.Canonical.gamma exponent
  have powerNonzero : power ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
  have inverseNonzero : power⁻¹ ≠ 0 := Field.inv_ne_zero_direct powerNonzero
  rw [Block.Contraction.lowBlock_eq_scaledBlock]
  rw [Chordal.Scale.chordalSq_act_scaleMatrix power powerNonzero]
  calc
    Chordal.Basic.chordalSq (Line.Matrix.act (SectorBlock.Basic.block power⁻¹ sector) left.point)
        (Line.Matrix.act (SectorBlock.Basic.block power⁻¹ sector) right.point) ≤
        BalancedRatio.factor power⁻¹ * Chordal.Basic.chordalSq left.point right.point :=
      Geometry.Projective.SectorBlock.Tail.contraction power⁻¹ inverseNonzero left right
    _ ≤ (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (BalancedRatio.factor_le_half _) (Chordal.Basic.chordalSq_nonneg _ _)

end Purelib.Data.CCL.Encoding.Block.Contraction

end

/-!
# Finite completed-block cylinders

A cylinder is represented by a finite list of completed raw CCL blocks and a
finite realization trace.  No collection of all compatible points is formed.
The main theorem compares any two supplied realization traces and obtains the
explicit `2⁻ⁿ` squared-chordal bound.
-/

@[expose] public section

namespace Purelib.Data.CCL.Encoding.Block
section Block

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The retained block matrix halves chordal squared distance between tails for its exact sector. -/
theorem contraction_half (block : Block)
    (left right : Geometry.Projective.SectorBlock.Tail block.sector) :
    Chordal.Basic.chordalSq (Line.Matrix.act block.matrix left.point)
        (Line.Matrix.act block.matrix right.point) ≤
      (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point := by
  cases block with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          exact Block.Contraction.regularBlock_contraction_half exponent left right
      | initialLow =>
          exact Block.Contraction.lowBlock_contraction_half exponent left right
end Block

section Block

section
open Purelib.Data.CCL.Encoding
open Purelib.Geometry.Projective
/-- Acting by the retained block matrix preserves a nonzero coordinate of a valid projective sector tail. -/
theorem act_projectiveTail_valid (block : Block)
    (tail : Geometry.Projective.SectorBlock.Tail.ProjectiveTail block.sector) :
    Line.Gaussian.Proj.HasNonzeroCoordinate
      (Line.Matrix.act block.matrix tail.point) :=
  Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
    block.matrix_det_ne_zero tail.valid

/-- The block image of the retained model tail has a nonzero projective coordinate. -/
theorem act_model_valid (block : Block) (tail :
  Geometry.Projective.SectorBlock.Tail.ProjectiveTail block.sector) :
    Line.Gaussian.Proj.HasNonzeroCoordinate
      (Line.Matrix.act block.matrix tail.model.point) :=
  Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
    block.matrix_det_ne_zero tail.model_valid

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The retained block halves chordal squared distance between compatible projective tail representatives.

Each representative keeps its own valid model and equivalence witness. The estimate transports through those exact
witnesses and the original block matrix. -/
theorem projective_contraction_half (block : Block)
    (left right : Geometry.Projective.SectorBlock.Tail.ProjectiveTail block.sector) :
    Chordal.Basic.chordalSq (Line.Matrix.act block.matrix left.point)
        (Line.Matrix.act block.matrix right.point) ≤
      (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point := by
  have leftActEquivalent :
      (Line.Matrix.act block.matrix left.point).Equivalent
        (Line.Matrix.act block.matrix left.model.point) :=
    Line.Matrix.act_respects_equivalent block.matrix left.equivalent
  have rightActEquivalent :
      (Line.Matrix.act block.matrix right.point).Equivalent
        (Line.Matrix.act block.matrix right.model.point) :=
    Line.Matrix.act_respects_equivalent block.matrix right.equivalent
  have inputEquality : Chordal.Basic.chordalSq left.model.point right.model.point =
      Chordal.Basic.chordalSq left.point right.point := by
    calc
      Chordal.Basic.chordalSq left.model.point right.model.point =
          Chordal.Basic.chordalSq left.point right.model.point :=
        (Chordal.Equivalence.chordalSq_eq_of_equivalent_left
          left.valid left.model_valid left.equivalent
          right.model.point).symm
      _ = Chordal.Basic.chordalSq left.point right.point :=
        (Chordal.Equivalence.chordalSq_eq_of_equivalent_right
          right.valid right.model_valid right.equivalent left.point).symm
  calc
    Chordal.Basic.chordalSq (Line.Matrix.act block.matrix left.point)
        (Line.Matrix.act block.matrix right.point) =
        Chordal.Basic.chordalSq (Line.Matrix.act block.matrix left.model.point)
          (Line.Matrix.act block.matrix right.point) :=
      Chordal.Equivalence.chordalSq_eq_of_equivalent_left
        (block.act_projectiveTail_valid left) (block.act_model_valid left)
        leftActEquivalent (Line.Matrix.act block.matrix right.point)
    _ = Chordal.Basic.chordalSq (Line.Matrix.act block.matrix left.model.point)
        (Line.Matrix.act block.matrix right.model.point) :=
      Chordal.Equivalence.chordalSq_eq_of_equivalent_right
        (block.act_projectiveTail_valid right) (block.act_model_valid right)
        rightActEquivalent (Line.Matrix.act block.matrix left.model.point)
    _ ≤ (1 / 2 : Fraction.Rational) *
        Chordal.Basic.chordalSq left.model.point right.model.point :=
      block.contraction_half left.model right.model
    _ = (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point := by
      rw [inputEquality]

end Block

end Purelib.Data.CCL.Encoding.Block

end
