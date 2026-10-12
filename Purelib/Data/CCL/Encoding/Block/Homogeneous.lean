module
public import Purelib.Data.CCL.Encoding.Block.Matrix
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.Group.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Exact semantics of redundant progressive CCL blocks

The arithmetic controller is allowed to select an overlapping safe sector
outside the canonical half-open annulus table.  This file proves that doing
so does not alter the represented point.  Local safety alone gives both the
exact inverse chart and the strict lower norm needed by the following loop.

The zero-residual case is kept projective.  It maps exactly to the completed
block's `omega` tail and can therefore emit the productive unary padding of
`TerminalPadding` without deciding equality.
-/

namespace Purelib.Data.CCL.Encoding.Block.Homogeneous

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The block matrix sends the exact homogeneous normalized residual back to the original affine value.

The homogeneous tail is one over gamma times the normalized residual. The identity holds for every parser block kind,
including a zero residual, without selecting an affine inverse. -/
theorem blockHomogeneous_exact
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
      Basic.Canonical) :
    Line.Proj.Equivalent
      (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
        ⟨1, Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep)⟩)
      (Line.Proj.affine value) := by
  cases kind with
  | initialHigh | loop =>
      let power := Power.natPow Basic.Canonical.gamma exponent
      have powerNonzero : power ≠ 0 :=
        Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
      have cancellation : power * power⁻¹ = 1 :=
        Basic.Canonical.mul_inv_cancel power powerNonzero
      simp only [Block.Matrix.blockMatrix, Block.Matrix.regularBlock,
        Line.Matrix.act, Line.Proj.Equivalent, Line.Proj.affine,
        Parser.Semantics.Basic.normalizedValue, Power.natPow_succ,
        Basic.mul_one,
        Basic.zero_mul,
        Basic.add_zero]
      change power * Basic.Canonical.gamma * sector.rep +
          power * (Basic.Canonical.gamma * (value * power⁻¹ - sector.rep)) = value * Basic.Canonical.gamma
      calc
        power * Basic.Canonical.gamma * sector.rep +
            power * (Basic.Canonical.gamma * (value * power⁻¹ - sector.rep)) =
            (power * power⁻¹) * (value * Basic.Canonical.gamma) := by
          apply Basic.ext <;>
            simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;>
            ring1
        _ = value * Basic.Canonical.gamma := by
          rw [cancellation, Basic.one_mul]
  | initialLow =>
      let power := Power.natPow Basic.Canonical.gamma exponent
      simp only [Block.Matrix.blockMatrix, Block.Matrix.lowBlock,
        Line.Matrix.act, Line.Proj.Equivalent, Line.Proj.affine,
        Parser.Semantics.Basic.normalizedValue, Power.natPow_succ,
        Basic.mul_one,
        Basic.one_mul,
        Basic.zero_mul,
        Basic.add_zero]
      change Basic.Canonical.gamma * sector.rep + Basic.Canonical.gamma * (power * value - sector.rep) =
        value * (power * Basic.Canonical.gamma)
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;>
        ring1

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.Algebra in
/-- A zero normalized sector residual makes the block matrix send infinity to the original affine value. -/
theorem terminalBlock_exact
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
      Basic.Canonical)
    (residualZero :
      Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep = 0) :
    Line.Proj.Equivalent
      (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) Line.Proj.omega)
      (Line.Proj.affine value) := by
  have normalizedEqual :
      Parser.Semantics.Basic.normalizedValue kind exponent value = sector.rep :=
    Group.eq_of_sub_eq_zero residualZero
  have gammaNonzero : Basic.Canonical.gamma ≠ 0 := by decide
  cases kind with
  | initialHigh | loop =>
      let power := Power.natPow Basic.Canonical.gamma exponent
      have powerNonzero : power ≠ 0 :=
        Power.natPow_ne_zero_direct Basic.Canonical.gamma gammaNonzero exponent
      have scaled : value * power⁻¹ = sector.rep := by
        simpa only [Parser.Semantics.Basic.normalizedValue, power] using normalizedEqual
      have valueIdentity : value = power * sector.rep := by
        have cancellation : power⁻¹ * power = 1 := by
          exact Basic.Canonical.inv_mul_cancel
            power powerNonzero
        calc
          value = value * (power⁻¹ * power) := by
            rw [cancellation,
              Basic.mul_one]
          _ = (value * power⁻¹) * power :=
            (Basic.mul_assoc _ _ _).symm
          _ = sector.rep * power := by rw [scaled]
          _ = power * sector.rep :=
            Basic.mul_comm _ _
      simp only [Block.Matrix.blockMatrix, Block.Matrix.regularBlock,
        Line.Matrix.act, Line.Proj.omega, Line.Proj.affine,
        Line.Proj.Equivalent,
        Basic.mul_one,
        Basic.mul_zero,
        Basic.add_zero]
      rw [Power.natPow_succ, valueIdentity]
      apply Basic.ext <;>
        simp only [Basic.mul_re, Basic.mul_im] <;> ring1
  | initialLow =>
      let power := Power.natPow Basic.Canonical.gamma exponent
      have scaled : power * value = sector.rep := by
        simpa only [Parser.Semantics.Basic.normalizedValue, power] using normalizedEqual
      simp only [Block.Matrix.blockMatrix, Block.Matrix.lowBlock,
        Line.Matrix.act, Line.Proj.omega, Line.Proj.affine,
        Line.Proj.Equivalent,
        Basic.mul_one,
        Basic.mul_zero,
        Basic.add_zero]
      rw [Power.natPow_succ, ← scaled]
      apply Basic.ext <;>
        simp only [Basic.mul_re, Basic.mul_im] <;> ring1
end Purelib.Data.CCL.Encoding.Block.Homogeneous

end
