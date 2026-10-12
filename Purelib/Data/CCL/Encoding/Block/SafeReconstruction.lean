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
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
public import Purelib.Geometry.Projective.SectorBlock.Safe.Tail
import Purelib.Geometry.Rational.Sector.Eight.Inversion
import Purelib.Geometry.Rational.Sector.Eight.Safe
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Encoding.Block.Semantics
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Completed-block contraction for redundant CCL choices

The canonical contraction theorem stores annulus and disjoint-sector proofs.
For arithmetic output those hypotheses are unnecessarily strong.  A block is
sound and has the same contraction factor whenever its displayed value has
norm at least one and its chosen representative has residual quadrance below
one half.

This parallel structure deliberately leaves the canonical theorem and parser
unchanged.  `ofCanonical` embeds every old compatible block into this wider
arithmetic layer.
-/

namespace Purelib.Geometry.Projective.SectorBlock.Safe.Tail
section Tail

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
/-- A regular block maps a retained safe tail to the affine target obtained by its exact gamma-power scaling. -/
theorem regularBlock_act_equivalent {sector :
  Data.ComplexContinuedFraction.Encoding.Sector} (exponent : Nat)
    (tail : Tail sector) (value target : Basic.Canonical)
    (models : tail.ModelsValue value)
    (targetIdentity : Power.natPow Basic.Canonical.gamma exponent * value = target) :
    (Line.Matrix.act (Block.Matrix.regularBlock exponent sector)
      tail.point).Equivalent (Line.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [targetIdentity.symm, models]
      dsimp only [Line.Proj.Equivalent, point, Line.Matrix.act,
        Block.Matrix.regularBlock, Line.Proj.omega,
        Line.Proj.affine]
      rw [Power.natPow_succ]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im,
          Basic.one_re, Basic.one_im] <;> ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      rw [targetIdentity.symm]
      dsimp only [Line.Proj.Equivalent, point, Line.Matrix.act,
        Block.Matrix.regularBlock, Line.Proj.affine]
      simp only [Basic.mul_one,
        Basic.add_zero]
      rw [Power.natPow_succ]
      calc
        Power.natPow Basic.Canonical.gamma exponent * Basic.Canonical.gamma * sector.rep * tail +
            Power.natPow Basic.Canonical.gamma exponent =
            Power.natPow Basic.Canonical.gamma exponent * (Basic.Canonical.gamma * tail * sector.rep + 1) := by
          apply Basic.ext <;>
            simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;>
            ring1
        _ = Power.natPow Basic.Canonical.gamma exponent * (Basic.Canonical.gamma * tail * value) := by
          rw [compatible.equation]
        _ = (Power.natPow Basic.Canonical.gamma exponent * value) * (Basic.Canonical.gamma * tail) := by
          apply Basic.ext <;>
            simp only [Basic.mul_re, Basic.mul_im] <;> ring1

/-- An initial-low block maps a retained safe tail to the affine target whose gamma-power scaling is the modeled value.
-/
theorem lowBlock_act_equivalent {sector :
  Data.ComplexContinuedFraction.Encoding.Sector} (exponent : Nat)
    (tail : Tail sector) (value target : Basic.Canonical)
    (models : tail.ModelsValue value)
    (sourceIdentity : value = Power.natPow Basic.Canonical.gamma exponent * target) :
    (Line.Matrix.act (Block.Matrix.lowBlock exponent sector)
      tail.point).Equivalent (Line.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [models] at sourceIdentity
      dsimp only [Line.Proj.Equivalent, point, Line.Matrix.act,
        Block.Matrix.lowBlock, Line.Proj.omega, Line.Proj.affine]
      rw [sourceIdentity, Power.natPow_succ]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im,
          Basic.one_re, Basic.one_im] <;> ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      dsimp only [Line.Proj.Equivalent, point, Line.Matrix.act,
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
            simp only [Basic.mul_re, Basic.mul_im] <;> ring1
end Tail

end Purelib.Geometry.Projective.SectorBlock.Safe.Tail

end

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

namespace Purelib.Data.CCL.Encoding.Block.SafeReconstruction

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.Geometry.Rational
/-- A safe nonzero normalized residual gives exact inverse-block reconstruction and a tail squared norm above one. -/
theorem safeBlock_sufficient
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
      Basic.Canonical)
    (safe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent value))
    (residualNonzero :
      Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep ≠ 0) :
    Homography.Basic.homographic (Block.Matrix.blockMatrix kind exponent sector)
        ((Basic.Canonical.gamma *
          (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))⁻¹) = value ∧
      1 < Data.Gaussian.Norm.Basic.normSq
        ((Basic.Canonical.gamma *
          (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))⁻¹) :=
  ⟨Block.Semantics.block_homographic_inverse
      kind exponent sector value residualNonzero,
    Sector.Eight.Inversion.postInversion_norm_gt_one
      safe residualNonzero⟩

/-- Construct the safe sector tail of the exact normalized value using its retained norm and safety witnesses.

The output keeps the supplied sector and the original normalized value. The existing safe-tail constructor handles
terminal and nonterminal residuals without replacing the witnesses. -/
def safeBlockTail
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
      Basic.Canonical)
    (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent value))
    (safe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent value)) :
    Geometry.Projective.SectorBlock.Safe.Tail sector :=
  Geometry.Projective.SectorBlock.Safe.Tail.ofSafe sector
    (Parser.Semantics.Basic.normalizedValue kind exponent value) normLower safe

/-- The constructed safe tail models the exact original normalized value. -/
theorem safeBlockTail_models
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
      Basic.Canonical)
    (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent value))
    (safe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent value)) :
    (safeBlockTail kind exponent sector value normLower safe).ModelsValue
      (Parser.Semantics.Basic.normalizedValue kind exponent value) :=
  Geometry.Projective.SectorBlock.Safe.Tail.ofSafe_models sector
    (Parser.Semantics.Basic.normalizedValue kind exponent value) normLower safe

/-- The retained block matrix sends the constructed safe tail to a projectively equivalent original affine value. -/
theorem safeBlockTail_exact
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
      Basic.Canonical)
    (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent value))
    (safe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent value)) :
    Line.Proj.Equivalent
      (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
        (safeBlockTail kind exponent sector value normLower safe).point)
      (Line.Proj.affine value) := by
  let tail := safeBlockTail kind exponent sector value normLower safe
  have models : tail.ModelsValue (Parser.Semantics.Basic.normalizedValue kind exponent value) :=
    safeBlockTail_models kind exponent sector value normLower safe
  cases kind with
  | initialLow =>
      exact
        Geometry.Projective.SectorBlock.Safe.Tail.lowBlock_act_equivalent
          exponent tail (Parser.Semantics.Basic.normalizedValue .initialLow exponent value) value
          models rfl
  | initialHigh | loop =>
      have gammaNonzero : Basic.Canonical.gamma ≠ 0 := by decide
      let power := Power.natPow Basic.Canonical.gamma exponent
      have powerNonzero : power ≠ 0 :=
        Power.natPow_ne_zero_direct Basic.Canonical.gamma gammaNonzero exponent
      have cancellation : power⁻¹ * power = 1 := by
        exact Basic.Canonical.inv_mul_cancel
          power powerNonzero
      have targetIdentity :
          power * Parser.Semantics.Basic.normalizedValue .initialHigh exponent value = value := by
        simp only [Parser.Semantics.Basic.normalizedValue, power]
        calc
          power * (value * power⁻¹) = value * (power⁻¹ * power) := by
            apply Basic.ext <;>
              simp only [Basic.mul_re, Basic.mul_im] <;> ring1
          _ = value := by
            rw [cancellation, Basic.mul_one]
      simpa only [Block.Matrix.blockMatrix] using
        Geometry.Projective.SectorBlock.Safe.Tail.regularBlock_act_equivalent
          exponent tail (Parser.Semantics.Basic.normalizedValue .initialHigh exponent value) value
          models targetIdentity

/-- The retained safe homogeneous residual reconstructs the original affine value through the exact block matrix. -/
theorem safeBlockHomogeneous_exact
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value :
      Basic.Canonical)
    (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue kind exponent value))
    (safe : Geometry.Rational.Sector.Eight.Safe sector
      (Parser.Semantics.Basic.normalizedValue kind exponent value)) :
    Line.Proj.Equivalent
      (Line.Matrix.act (Block.Matrix.blockMatrix kind exponent sector)
        ⟨1, Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep)⟩)
      (Line.Proj.affine value) := by
  let tail := safeBlockTail kind exponent sector value normLower safe
  have tailToHomogeneous : tail.point.Equivalent
      ⟨1, Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep)⟩ :=
    Geometry.Projective.SectorBlock.Safe.Tail.ofSafe_point_equivalent_homogeneous
      sector (Parser.Semantics.Basic.normalizedValue kind exponent value) normLower safe
  have homogeneousToTail := Line.Matrix.act_respects_equivalent
    (Block.Matrix.blockMatrix kind exponent sector) tailToHomogeneous.symm
  have exact := safeBlockTail_exact kind exponent sector value normLower safe
  exact Line.Gaussian.Proj.equivalent_trans
    homogeneousToTail exact
    (Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      (Block.Matrix.blockMatrix_det_ne kind exponent sector)
      tail.point_valid)
    (Line.Gaussian.Proj.affine_hasNonzeroCoordinate value)
end

end Purelib.Data.CCL.Encoding.Block.SafeReconstruction

end
