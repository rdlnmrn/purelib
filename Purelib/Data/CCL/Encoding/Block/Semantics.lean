module
public import Purelib.Data.CCL.Encoding.Block.Matrix
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
public import Purelib.Geometry.Projective.SectorBlock.Tail

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.Ring

section
/-!
# Finite completed-block cylinders

A cylinder is represented by a finite list of completed raw CCL blocks and a
finite realization trace.  No collection of all compatible points is formed.
The main theorem compares any two supplied realization traces and obtains the
explicit `2⁻ⁿ` squared-chordal bound.
-/

@[expose] public section

namespace Purelib.Data.CCL.Encoding.Block.Semantics

namespace Tail

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
/-- A regular decoder block sends a compatible retained sector tail to the exact gamma-scaled affine target. -/
theorem regularBlock_act_equivalent {sector :
  Data.ComplexContinuedFraction.Encoding.Sector}
  (exponent : Nat)
    (tail : Geometry.Projective.SectorBlock.Tail sector) (value target : Basic.Canonical)
    (models : tail.ModelsValue value)
    (targetIdentity : Power.natPow Basic.Canonical.gamma exponent * value = target) :
    (Line.Matrix.act (Block.Matrix.regularBlock exponent sector)
      tail.point).Equivalent (Line.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [targetIdentity.symm, models]
      dsimp only [Line.Proj.Equivalent,
        Geometry.Projective.SectorBlock.Tail.point, Line.Matrix.act,
        Block.Matrix.regularBlock, Line.Proj.omega,
        Line.Proj.affine]
      rw [Power.natPow_succ]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im,
          Basic.one_re, Basic.one_im] <;>
        ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      rw [targetIdentity.symm]
      dsimp only [Line.Proj.Equivalent,
        Geometry.Projective.SectorBlock.Tail.point, Line.Matrix.act,
        Block.Matrix.regularBlock, Line.Proj.affine]
      simp only [Basic.mul_one,
        Basic.add_zero]
      rw [Power.natPow_succ]
      calc
        Power.natPow Basic.Canonical.gamma exponent * Basic.Canonical.gamma * sector.rep * tail +
            Power.natPow Basic.Canonical.gamma exponent =
            Power.natPow Basic.Canonical.gamma exponent *
              (Basic.Canonical.gamma * tail * sector.rep + 1) := by
          apply Basic.ext <;>
            simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;>
            ring1
        _ = Power.natPow Basic.Canonical.gamma exponent * (Basic.Canonical.gamma * tail * value) := by
          rw [compatible.equation]
        _ = (Power.natPow Basic.Canonical.gamma exponent * value) * (Basic.Canonical.gamma * tail) := by
          apply Basic.ext <;>
            simp only [Basic.mul_re, Basic.mul_im] <;>
            ring1

/-- An initial-low decoder block sends a compatible tail to the target whose gamma-scaled value it models. -/
theorem lowBlock_act_equivalent {sector :
  Data.ComplexContinuedFraction.Encoding.Sector}
  (exponent : Nat)
    (tail : Geometry.Projective.SectorBlock.Tail sector) (value target : Basic.Canonical)
    (models : tail.ModelsValue value)
    (sourceIdentity : value = Power.natPow Basic.Canonical.gamma exponent * target) :
    (Line.Matrix.act (Block.Matrix.lowBlock exponent sector)
      tail.point).Equivalent (Line.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [models] at sourceIdentity
      dsimp only [Line.Proj.Equivalent,
        Geometry.Projective.SectorBlock.Tail.point, Line.Matrix.act,
        Block.Matrix.lowBlock, Line.Proj.omega,
        Line.Proj.affine]
      rw [sourceIdentity, Power.natPow_succ]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im,
          Basic.one_re, Basic.one_im] <;>
        ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      dsimp only [Line.Proj.Equivalent,
        Geometry.Projective.SectorBlock.Tail.point, Line.Matrix.act,
        Block.Matrix.lowBlock, Line.Proj.affine]
      simp only [Basic.mul_one,
        Basic.add_zero]
      rw [Power.natPow_succ]
      calc
        Basic.Canonical.gamma * sector.rep * tail + 1 =
            Basic.Canonical.gamma * tail * sector.rep + 1 := by
          apply Basic.ext <;>
            simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;>
            ring1
        _ = Basic.Canonical.gamma * tail * value := compatible.equation.symm
        _ = target * (Power.natPow Basic.Canonical.gamma exponent * Basic.Canonical.gamma * tail) := by
          rw [sourceIdentity]
          apply Basic.ext <;>
            simp only [Basic.mul_re, Basic.mul_im] <;>
            ring1

end Tail

end Purelib.Data.CCL.Encoding.Block.Semantics

end

end

section
@[expose] public section

/-!
# Constructive one-bit raw-parser semantics

This module reduces semantic possibility of one more raw CCL bit to an
explicit predicate at the current affine tail.  The only nontrivial case is
the third sector bit: completing that bit subtracts the selected sector
representative and changes to a reciprocal coordinate.  All decisions and
inverse calculations below are finite and rational.
-/

namespace Purelib.Data.CCL.Encoding.Block.Semantics

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
/-- The regular block homography inverts a retained nonzero gamma-scaled residual decomposition. -/
private theorem regularBlock_homographic_inverse
    (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value residual : Basic.Canonical)
    (residualNonzero : residual ≠ 0)
    (decomposition :
      value = Power.natPow Basic.Canonical.gamma exponent * (sector.rep + residual)) :
    Homography.Basic.homographic (Block.Matrix.regularBlock exponent sector)
        ((Basic.Canonical.gamma * residual)⁻¹) = value := by
  let power := Power.natPow Basic.Canonical.gamma exponent
  let tail := (Basic.Canonical.gamma * residual)⁻¹
  have inverseDenominator : (Basic.Canonical.gamma * tail)⁻¹ = residual := by
    simpa only [tail] using Constants.inverse_gamma_inverse_mul residual residualNonzero
  have gammaResidualNonzero : Basic.Canonical.gamma * residual ≠ 0 :=
    Field.mul_ne_zero_direct Constants.Inverse.gamma_ne residualNonzero
  have tailNonzero : tail ≠ 0 := Field.inv_ne_zero_direct gammaResidualNonzero
  have denominatorNonzero : Basic.Canonical.gamma * tail ≠ 0 :=
    Field.mul_ne_zero_direct Constants.Inverse.gamma_ne tailNonzero
  unfold Homography.Basic.homographic Homography.Basic.numerator Homography.Basic.denominator
  simp only [Block.Matrix.regularBlock,
    Basic.add_zero]
  change (Power.natPow Basic.Canonical.gamma (exponent + 1) * sector.rep * tail + power) *
      (Basic.Canonical.gamma * tail)⁻¹ = value
  rw [inverseDenominator, decomposition, Power.natPow_succ]
  have cancellation : Basic.Canonical.gamma * tail * residual = 1 := by
    calc
      Basic.Canonical.gamma * tail * residual =
          (Basic.Canonical.gamma * residual) * (Basic.Canonical.gamma * residual)⁻¹ := by
        apply Basic.ext <;>
          simp only [tail, Basic.mul_re, Basic.mul_im] <;>
          ring1
      _ = 1 :=
        Basic.Canonical.mul_inv_cancel
          _ gammaResidualNonzero
  calc
    (power * Basic.Canonical.gamma * sector.rep * tail + power) * residual =
        power * (sector.rep * (Basic.Canonical.gamma * tail * residual) + residual) := by
      apply Basic.ext <;>
        simp only [Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im] <;>
        ring1
    _ = power * (sector.rep + residual) := by
      rw [cancellation, Basic.mul_one]

/-- The initial-low block homography inverts the retained nonzero residual of the gamma-scaled source. -/
private theorem lowBlock_homographic_inverse
    (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value residual : Basic.Canonical)
    (residualNonzero : residual ≠ 0)
    (decomposition :
      Power.natPow Basic.Canonical.gamma exponent * value = sector.rep + residual) :
    Homography.Basic.homographic (Block.Matrix.lowBlock exponent sector)
        ((Basic.Canonical.gamma * residual)⁻¹) = value := by
  let power := Power.natPow Basic.Canonical.gamma exponent
  let tail := (Basic.Canonical.gamma * residual)⁻¹
  have powerNonzero : power ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne exponent
  have inverseGammaTail : (Basic.Canonical.gamma * tail)⁻¹ = residual := by
    simpa only [tail] using Constants.inverse_gamma_inverse_mul residual residualNonzero
  have gammaResidualNonzero : Basic.Canonical.gamma * residual ≠ 0 :=
    Field.mul_ne_zero_direct Constants.Inverse.gamma_ne residualNonzero
  have tailNonzero : tail ≠ 0 := Field.inv_ne_zero_direct gammaResidualNonzero
  have gammaTailNonzero : Basic.Canonical.gamma * tail ≠ 0 :=
    Field.mul_ne_zero_direct Constants.Inverse.gamma_ne tailNonzero
  have fullDenominatorNonzero :
      Power.natPow Basic.Canonical.gamma (exponent + 1) * tail ≠ 0 :=
    Field.mul_ne_zero_direct
      (Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne (exponent + 1)) tailNonzero
  have residualCancellation : residual * (Basic.Canonical.gamma * tail) = 1 := by
    calc
      residual * (Basic.Canonical.gamma * tail) =
          (Basic.Canonical.gamma * tail)⁻¹ * (Basic.Canonical.gamma * tail) := by rw [inverseGammaTail]
      _ = 1 :=
        Basic.Canonical.inv_mul_cancel _ gammaTailNonzero
  have inverseDenominator :
      (Power.natPow Basic.Canonical.gamma (exponent + 1) * tail)⁻¹ =
        residual * power⁻¹ := by
    apply Field.mul_right_cancel_of_ne
      fullDenominatorNonzero
    calc
      (Power.natPow Basic.Canonical.gamma (exponent + 1) * tail)⁻¹ *
          (Power.natPow Basic.Canonical.gamma (exponent + 1) * tail) = 1 :=
        Basic.Canonical.inv_mul_cancel
          _ fullDenominatorNonzero
      _ = (residual * power⁻¹) *
          (Power.natPow Basic.Canonical.gamma (exponent + 1) * tail) := by
        rw [Power.natPow_succ]
        have powerCancellation : power⁻¹ * power = 1 := by
          exact Basic.Canonical.inv_mul_cancel
            power powerNonzero
        calc
          1 = (power⁻¹ * power) * (residual * (Basic.Canonical.gamma * tail)) := by
            rw [powerCancellation, residualCancellation,
              Basic.one_mul]
          _ = (residual * power⁻¹) * (power * Basic.Canonical.gamma * tail) := by
            apply Basic.ext <;>
              simp only [Basic.mul_re, Basic.mul_im] <;>
              ring1
  unfold Homography.Basic.homographic Homography.Basic.numerator Homography.Basic.denominator
  simp only [Block.Matrix.lowBlock,
    Basic.add_zero]
  change (Basic.Canonical.gamma * sector.rep * tail + 1) *
      (Power.natPow Basic.Canonical.gamma (exponent + 1) * tail)⁻¹ = value
  rw [inverseDenominator]
  have gammaTailResidual : Basic.Canonical.gamma * tail * residual = 1 := by
    calc
      Basic.Canonical.gamma * tail * residual = (Basic.Canonical.gamma * tail) * (Basic.Canonical.gamma * tail)⁻¹ := by
        rw [inverseGammaTail]
      _ = 1 :=
        Basic.Canonical.mul_inv_cancel _ gammaTailNonzero
  have powerCancellation : power⁻¹ * power = 1 := by
    exact Basic.Canonical.inv_mul_cancel power powerNonzero
  apply Field.mul_right_cancel_of_ne powerNonzero
  calc
    ((Basic.Canonical.gamma * sector.rep * tail + 1) * (residual * power⁻¹)) *
          power =
        sector.rep * (Basic.Canonical.gamma * tail * residual) *
            (power⁻¹ * power) + residual * (power⁻¹ * power) := by
      apply Basic.ext <;>
        simp only [Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im] <;>
        ring1
    _ = sector.rep + residual := by
      rw [gammaTailResidual, powerCancellation,
        Basic.mul_one,
        Basic.mul_one]
      exact congrArg (fun item => sector.rep + item)
        (Basic.mul_one residual)
    _ = power * value := decomposition.symm
    _ = value * power := Basic.mul_comm _ _

/-- The block homography reconstructs the original Gaussian from the reciprocal gamma-scaled normalized residual.

The residual is nonzero and uses the exact parser kind, normalization exponent and sector representative. The formula
preserves the distinct regular and initial-low normalization branches. -/
theorem block_homographic_inverse
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Basic.Canonical)
    (residualNonzero :
      Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep ≠ 0) :
    Homography.Basic.homographic (Block.Matrix.blockMatrix kind exponent sector)
        ((Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))⁻¹) =
      value := by
  cases kind with
  | initialHigh =>
      let residual := value * (Power.natPow Basic.Canonical.gamma exponent)⁻¹ - sector.rep
      apply regularBlock_homographic_inverse exponent sector value residual
        residualNonzero
      have powerNonzero :=
        Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne exponent
      have cancellation : (Power.natPow Basic.Canonical.gamma exponent)⁻¹ *
          Power.natPow Basic.Canonical.gamma exponent = 1 := by
        exact Basic.Canonical.inv_mul_cancel
          (Power.natPow Basic.Canonical.gamma exponent) powerNonzero
      calc
        value = value * ((Power.natPow Basic.Canonical.gamma exponent)⁻¹ *
            Power.natPow Basic.Canonical.gamma exponent) := by
          rw [cancellation, Basic.mul_one]
        _ = Power.natPow Basic.Canonical.gamma exponent * (sector.rep + residual) := by
          apply Basic.ext <;>
            simp only [residual, Basic.sub_re, Basic.sub_im,
              Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im] <;>
            ring1
  | initialLow =>
      let residual := Power.natPow Basic.Canonical.gamma exponent * value - sector.rep
      apply lowBlock_homographic_inverse exponent sector value residual
        residualNonzero
      apply Basic.ext <;>
        simp only [residual, Basic.sub_re, Basic.sub_im,
          Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im] <;>
        ring1
  | loop =>
      let residual := value * (Power.natPow Basic.Canonical.gamma exponent)⁻¹ - sector.rep
      apply regularBlock_homographic_inverse exponent sector value residual
        residualNonzero
      have powerNonzero :=
        Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne exponent
      have cancellation : (Power.natPow Basic.Canonical.gamma exponent)⁻¹ *
          Power.natPow Basic.Canonical.gamma exponent = 1 := by
        exact Basic.Canonical.inv_mul_cancel
          (Power.natPow Basic.Canonical.gamma exponent) powerNonzero
      calc
        value = value * ((Power.natPow Basic.Canonical.gamma exponent)⁻¹ *
            Power.natPow Basic.Canonical.gamma exponent) := by
          rw [cancellation, Basic.mul_one]
        _ = Power.natPow Basic.Canonical.gamma exponent * (sector.rep + residual) := by
          apply Basic.ext <;>
            simp only [residual, Basic.sub_re, Basic.sub_im,
              Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im] <;>
            ring1

/-- The homographic denominator at the retained inverse residual is nonzero for every parser block kind. -/
theorem block_inverse_denominator_ne
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Basic.Canonical)
    (residualNonzero :
      Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep ≠ 0) :
    Homography.Basic.denominator (Block.Matrix.blockMatrix kind exponent sector)
      ((Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))⁻¹) ≠
        0 := by
  let tail :=
    (Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))⁻¹
  have tailNonzero : tail ≠ 0 :=
    Field.inv_ne_zero_direct (Field.mul_ne_zero_direct Constants.Inverse.gamma_ne residualNonzero)
  cases kind with
  | initialHigh =>
      change Basic.Canonical.gamma * tail + 0 ≠ 0
      rw [Basic.add_zero]
      exact Field.mul_ne_zero_direct Constants.Inverse.gamma_ne tailNonzero
  | initialLow =>
      change Power.natPow Basic.Canonical.gamma (exponent + 1) * tail + 0 ≠ 0
      rw [Basic.add_zero]
      exact Field.mul_ne_zero_direct
        (Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne (exponent + 1)) tailNonzero
  | loop =>
      change Basic.Canonical.gamma * tail + 0 ≠ 0
      rw [Basic.add_zero]
      exact Field.mul_ne_zero_direct Constants.Inverse.gamma_ne tailNonzero

/-- A tail with nonzero retained block homography denominator is itself nonzero.

Both retained block kinds have a denominator that vanishes at a zero tail, so the supplied nonzero denominator excludes
that input. -/
theorem tail_ne_of_block_denominator
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (tail : Basic.Canonical)
    (denominatorNonzero :
      Homography.Basic.denominator (Block.Matrix.blockMatrix kind exponent sector) tail ≠ 0) :
    tail ≠ 0 := by
  intro tailZero
  subst tail
  apply denominatorNonzero
  cases kind <;>
    (simp only [Homography.Basic.denominator, Block.Matrix.blockMatrix, Block.Matrix.regularBlock,
      Block.Matrix.lowBlock, Basic.mul_zero, Basic.add_zero, -eq_self, -iff_self]
     rfl)

/-- Normalizing the block homography value recovers the sector representative plus the reciprocal gamma-scaled tail. -/
theorem normalizedValue_block_homographic
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (tail : Basic.Canonical)
    (denominatorNonzero :
      Homography.Basic.denominator (Block.Matrix.blockMatrix kind exponent sector) tail ≠ 0) :
    Parser.Semantics.Basic.normalizedValue kind exponent
        (Homography.Basic.homographic (Block.Matrix.blockMatrix kind exponent sector) tail) =
      sector.rep + (Basic.Canonical.gamma * tail)⁻¹ := by
  have tailNonzero := tail_ne_of_block_denominator kind exponent sector tail
    denominatorNonzero
  have gammaTailNonzero : Basic.Canonical.gamma * tail ≠ 0 :=
    Field.mul_ne_zero_direct Constants.Inverse.gamma_ne tailNonzero
  let power := Power.natPow Basic.Canonical.gamma exponent
  have powerNonzero : power ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne exponent
  have powerCancellation : power * power⁻¹ = 1 := by
    exact Basic.Canonical.mul_inv_cancel power powerNonzero
  have denominatorCancellation :
      Basic.Canonical.gamma * tail * (Basic.Canonical.gamma * tail)⁻¹ = 1 := by
    exact Basic.Canonical.mul_inv_cancel _ gammaTailNonzero
  cases kind with
  | initialHigh | loop =>
      simp only [Parser.Semantics.Basic.normalizedValue, Block.Matrix.blockMatrix,
        Block.Matrix.regularBlock, Homography.Basic.homographic, Homography.Basic.numerator,
        Homography.Basic.denominator, Basic.add_zero, Power.natPow_succ]
      change ((power * Basic.Canonical.gamma * sector.rep * tail + power) *
          (Basic.Canonical.gamma * tail)⁻¹) * power⁻¹ =
        sector.rep + (Basic.Canonical.gamma * tail)⁻¹
      calc
        ((power * Basic.Canonical.gamma * sector.rep * tail + power) *
            (Basic.Canonical.gamma * tail)⁻¹) * power⁻¹ =
          sector.rep * (Basic.Canonical.gamma * tail * (Basic.Canonical.gamma * tail)⁻¹) *
              (power * power⁻¹) +
            (Basic.Canonical.gamma * tail)⁻¹ * (power * power⁻¹) := by
          apply Basic.ext <;>
            simp only [Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im] <;>
            ring1
        _ = sector.rep + (Basic.Canonical.gamma * tail)⁻¹ := by
          rw [denominatorCancellation, powerCancellation,
            Basic.mul_one sector.rep,
            Basic.mul_one (Basic.Canonical.gamma * tail)⁻¹]
          exact congrArg (fun item => item + (Basic.Canonical.gamma * tail)⁻¹)
            (Basic.mul_one sector.rep)
  | initialLow =>
      have fullDenominatorNonzero : power * (Basic.Canonical.gamma * tail) ≠ 0 :=
        Field.mul_ne_zero_direct powerNonzero gammaTailNonzero
      have inverseDenominator :
          (power * (Basic.Canonical.gamma * tail))⁻¹ =
            (Basic.Canonical.gamma * tail)⁻¹ * power⁻¹ := by
        apply Field.mul_right_cancel_of_ne
          fullDenominatorNonzero
        calc
          (power * (Basic.Canonical.gamma * tail))⁻¹ *
                (power * (Basic.Canonical.gamma * tail)) = 1 := by
            exact Basic.Canonical.inv_mul_cancel
              _ fullDenominatorNonzero
          _ = ((Basic.Canonical.gamma * tail)⁻¹ * power⁻¹) *
                (power * (Basic.Canonical.gamma * tail)) := by
            have inversePowerCancellation : power⁻¹ * power = 1 := by
              exact Basic.Canonical.inv_mul_cancel
                power powerNonzero
            have inverseTailCancellation :
                (Basic.Canonical.gamma * tail)⁻¹ * (Basic.Canonical.gamma * tail) = 1 := by
              exact Basic.Canonical.inv_mul_cancel
                _ gammaTailNonzero
            calc
              1 = (Basic.Canonical.gamma * tail)⁻¹ * (Basic.Canonical.gamma * tail) :=
                inverseTailCancellation.symm
              _ = ((Basic.Canonical.gamma * tail)⁻¹ * 1) * (Basic.Canonical.gamma * tail) := by
                rw [Basic.mul_one]
              _ = ((Basic.Canonical.gamma * tail)⁻¹ * (power⁻¹ * power)) *
                    (Basic.Canonical.gamma * tail) := by rw [inversePowerCancellation]
              _ = ((Basic.Canonical.gamma * tail)⁻¹ * power⁻¹) *
                    (power * (Basic.Canonical.gamma * tail)) := by
                apply Basic.ext <;>
                  simp only [Basic.mul_re, Basic.mul_im] <;>
                  ring1
      simp only [Parser.Semantics.Basic.normalizedValue, Block.Matrix.blockMatrix,
        Block.Matrix.lowBlock, Homography.Basic.homographic, Homography.Basic.numerator, Homography.Basic.denominator,
        Basic.add_zero]
      rw [show Power.natPow Basic.Canonical.gamma (exponent + 1) * tail =
          power * (Basic.Canonical.gamma * tail) by
        rw [Power.natPow_succ]
        apply Basic.ext <;>
          simp only [Basic.mul_re, Basic.mul_im] <;>
          ring1,
        inverseDenominator]
      change power * ((Basic.Canonical.gamma * sector.rep * tail + 1) *
          ((Basic.Canonical.gamma * tail)⁻¹ * power⁻¹)) =
        sector.rep + (Basic.Canonical.gamma * tail)⁻¹
      calc
        power * ((Basic.Canonical.gamma * sector.rep * tail + 1) *
            ((Basic.Canonical.gamma * tail)⁻¹ * power⁻¹)) =
          sector.rep * (Basic.Canonical.gamma * tail * (Basic.Canonical.gamma * tail)⁻¹) *
              (power * power⁻¹) +
            (Basic.Canonical.gamma * tail)⁻¹ * (power * power⁻¹) := by
          apply Basic.ext <;>
            simp only [Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im] <;>
            ring1
        _ = sector.rep + (Basic.Canonical.gamma * tail)⁻¹ := by
          rw [denominatorCancellation, powerCancellation,
            Basic.mul_one sector.rep,
            Basic.mul_one (Basic.Canonical.gamma * tail)⁻¹]
          exact congrArg (fun item => item + (Basic.Canonical.gamma * tail)⁻¹)
            (Basic.mul_one sector.rep)
end

end Purelib.Data.CCL.Encoding.Block.Semantics

end
