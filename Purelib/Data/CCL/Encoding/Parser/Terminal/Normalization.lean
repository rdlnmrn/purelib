module
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
public import Purelib.Data.CCL.Encoding.Block.Semantics
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite candidates for a local CCL terminal

A represented value can stop immediately before the third sector bit only
when its normalized tail is exactly one of the two sector representatives
compatible with the already-read two-bit fragment.  This module makes those
two candidates explicit.  It is the bounded replacement for repeatedly
excluding arbitrary rational terminal samples.
-/

namespace Purelib.Data.CCL.Encoding.Parser.Terminal

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
/-- Undo the retained block normalization at its exact sector representative.

Initial-low uses reciprocal gamma-power scaling; initial-high and loop use gamma-power scaling. The result is the unique
Gaussian whose normalized value is that retained representative. -/
def terminalBefore
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
      Basic.Canonical :=
  match kind with
  | .initialLow => (Power.natPow Basic.Canonical.gamma exponent)⁻¹ * sector.rep
  | .initialHigh | .loop => Power.natPow Basic.Canonical.gamma exponent * sector.rep

/-- Normalizing the retained terminal candidate recovers its exact sector representative. -/
theorem normalizedValue_terminalBefore
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    Parser.Semantics.Basic.normalizedValue kind exponent (terminalBefore kind exponent sector) =
      sector.rep := by
  have powerNonzero : Power.natPow Basic.Canonical.gamma exponent ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
  have cancellation : Power.natPow Basic.Canonical.gamma exponent *
      (Power.natPow Basic.Canonical.gamma exponent)⁻¹ = 1 := by
    exact Basic.Canonical.mul_inv_cancel _ powerNonzero
  cases kind with
  | initialLow =>
      simp only [Parser.Semantics.Basic.normalizedValue, terminalBefore]
      calc
        Power.natPow Basic.Canonical.gamma exponent *
            ((Power.natPow Basic.Canonical.gamma exponent)⁻¹ * sector.rep) =
          (Power.natPow Basic.Canonical.gamma exponent * (Power.natPow Basic.Canonical.gamma exponent)⁻¹) *
            sector.rep :=
          (Basic.mul_assoc _ _ _).symm
        _ = 1 * sector.rep := by rw [cancellation]
        _ = sector.rep := Basic.one_mul _
  | initialHigh | loop =>
      simp only [Parser.Semantics.Basic.normalizedValue, terminalBefore]
      calc
        (Power.natPow Basic.Canonical.gamma exponent * sector.rep) *
            (Power.natPow Basic.Canonical.gamma exponent)⁻¹ =
          sector.rep *
            (Power.natPow Basic.Canonical.gamma exponent * (Power.natPow Basic.Canonical.gamma exponent)⁻¹) := by
          apply Basic.ext <;>
            simp only [Basic.mul_re, Basic.mul_im] <;> ring1
        _ = sector.rep * 1 := by rw [cancellation]
        _ = sector.rep := Basic.mul_one _

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- The exact normalization map for any retained block kind and exponent is injective. -/
theorem normalizedValue_injective
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) :
    Function.Injective (Parser.Semantics.Basic.normalizedValue kind exponent) := by
  intro left right equal
  have powerNonzero : Power.natPow Basic.Canonical.gamma exponent ≠ 0 :=
    Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
  cases kind with
  | initialLow =>
      apply Field.mul_right_cancel_of_ne powerNonzero
      calc
        left * Power.natPow Basic.Canonical.gamma exponent =
            Power.natPow Basic.Canonical.gamma exponent * left :=
          Basic.mul_comm _ _
        _ = Power.natPow Basic.Canonical.gamma exponent * right := equal
        _ = right * Power.natPow Basic.Canonical.gamma exponent :=
          Basic.mul_comm _ _
  | initialHigh | loop =>
      have inverseNonzero : (Power.natPow Basic.Canonical.gamma exponent)⁻¹ ≠ 0 :=
        Field.inv_ne_zero_direct powerNonzero
      exact Field.mul_right_cancel_of_ne
        inverseNonzero equal

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- A Gaussian normalizing to the retained sector representative equals its exact terminal candidate. -/
theorem eq_terminalBefore_of_normalized_eq
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    {before : Basic.Canonical}
    (equal : Parser.Semantics.Basic.normalizedValue kind exponent before = sector.rep) :
    before = terminalBefore kind exponent sector := by
  apply normalizedValue_injective kind exponent
  rw [normalizedValue_terminalBefore]
  exact equal
end Purelib.Data.CCL.Encoding.Parser.Terminal

end

section
public section
namespace Purelib.Data.CCL.Encoding.Parser.Terminal

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective

/-- The exact completed parser block sends infinity to its same retained terminal affine tail. -/
theorem block_terminal (kind : Syntax.BlockKind) (exponent : Nat) (sector : Sector) :
    (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector) Line.Proj.omega).Equivalent
      (Line.Proj.affine (terminalBefore kind exponent sector)) := by
  let tail : SectorBlock.Tail sector := .omega
  have models : tail.ModelsValue sector.rep := rfl
  cases kind with
  | initialHigh | loop =>
      exact Block.Semantics.Tail.regularBlock_act_equivalent exponent tail sector.rep _ models rfl
  | initialLow =>
      have identity : sector.rep = Power.natPow Basic.Canonical.gamma exponent *
          terminalBefore .initialLow exponent sector := by
        have nonzero := Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
        change sector.rep = _ * (_⁻¹ * sector.rep)
        rewrite [← Basic.mul_assoc, Basic.Canonical.mul_inv_cancel _ nonzero, Basic.one_mul]
        rfl
      exact Block.Semantics.Tail.lowBlock_act_equivalent exponent tail sector.rep _ models identity

end Purelib.Data.CCL.Encoding.Parser.Terminal
end
end
