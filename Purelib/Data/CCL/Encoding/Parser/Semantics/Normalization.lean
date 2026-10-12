module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Descent
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

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

namespace Purelib.Data.CCL.Encoding.Parser.Semantics.Normalization

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained block's radial bracket places its exact normalized Gaussian in the closed unit-to-two squared-norm
band. -/
theorem normalizedValue_band_of_radialBracket
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (value : Basic.Canonical)
    (radial : Parser.Semantics.Basic.radialBracket kind exponent value) :
    Data.ComplexContinuedFraction.Encoding.Sector.Band (Parser.Semantics.Basic.normalizedValue kind exponent value) :=
      by
  have powerPositive : (0 : Fraction.Rational) < (2 : Fraction.Rational) ^ exponent :=
    Fraction.Order.Arithmetic.pow_pos_direct (by decide) exponent
  cases kind with
  | initialHigh =>
      rcases radial with ⟨lower, upper⟩
      simp only [← Norm.Basic.normSq_eq_canonical] at lower upper
      have powerNonzero : Power.natPow Basic.Canonical.gamma exponent ≠ 0 :=
        Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
      have normIdentity :
          Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue .initialHigh exponent value) =
            Data.Gaussian.Norm.Basic.normSq value / (2 : Fraction.Rational) ^ exponent := by
        rw [Parser.Semantics.Basic.normalizedValue, Norm.Basic.normSq_mul, Field.inv_eq,
          Field.normSq_inv _ powerNonzero,
          Power.normSq_natPow, Constants.normSq_gamma]
        rfl
      rw [Data.ComplexContinuedFraction.Encoding.Sector.Band, ← Norm.Basic.normSq_eq_canonical, normIdentity]
      constructor
      · apply (Fraction.Order.Field.le_div_iff_pos powerPositive).2
        simpa only [Fraction.Field.one_mul] using lower
      · apply (Fraction.Order.Field.div_le_iff_pos powerPositive).2
        simpa only [pow_succ, mul_comm] using upper.le
  | initialLow =>
      rcases radial with ⟨lower, upper⟩
      simp only [← Norm.Basic.normSq_eq_canonical] at lower upper
      rw [Data.ComplexContinuedFraction.Encoding.Sector.Band, ← Norm.Basic.normSq_eq_canonical,
        Parser.Semantics.Basic.normalizedValue,
        Norm.Basic.normSq_mul, Power.normSq_natPow,
        Constants.normSq_gamma]
      exact ⟨lower, upper.le⟩
  | loop =>
      rcases radial with ⟨lower, upper⟩
      simp only [← Norm.Basic.normSq_eq_canonical] at lower upper
      have powerNonzero : Power.natPow Basic.Canonical.gamma exponent ≠ 0 :=
        Power.natPow_ne_zero_direct Basic.Canonical.gamma (by decide) exponent
      have normIdentity :
          Data.Gaussian.Norm.Basic.normSq (Parser.Semantics.Basic.normalizedValue .loop exponent value) =
            Data.Gaussian.Norm.Basic.normSq value / (2 : Fraction.Rational) ^ exponent := by
        rw [Parser.Semantics.Basic.normalizedValue, Norm.Basic.normSq_mul, Field.inv_eq,
          Field.normSq_inv _ powerNonzero,
          Power.normSq_natPow, Constants.normSq_gamma]
        rfl
      rw [Data.ComplexContinuedFraction.Encoding.Sector.Band, ← Norm.Basic.normSq_eq_canonical, normIdentity]
      constructor
      · apply (Fraction.Order.Field.le_div_iff_pos powerPositive).2
        simpa only [Fraction.Field.one_mul] using lower.le
      · apply (Fraction.Order.Field.div_le_iff_pos powerPositive).2
        simpa only [pow_succ, mul_comm] using upper

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
/-- A completed block condition places its exact normalized value in the closed sector norm band. -/
theorem normalizedValue_band_of_fullBlock
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Basic.Canonical)
    (full : Parser.Semantics.Basic.fullBlockHolds kind exponent sector value) :
    Data.ComplexContinuedFraction.Encoding.Sector.Band (Parser.Semantics.Basic.normalizedValue kind exponent value) :=
  normalizedValue_band_of_radialBracket kind exponent value full.1

/-- A completed block with nonzero selected residual has an inverse gamma-scaled residual satisfying the initial loop
condition. -/
theorem inverse_selected_loop_active
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (value : Basic.Canonical)
    (full : Parser.Semantics.Basic.fullBlockHolds kind exponent sector value)
    (residual : Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep ≠ 0) :
    Parser.Semantics.Basic.activeHolds (.loopUnary 0)
      ((Basic.Canonical.gamma * (Parser.Semantics.Basic.normalizedValue kind exponent value - sector.rep))⁻¹) := by
  rw [Parser.Semantics.Basic.activeHolds, pow_zero]
  rw [← Norm.Basic.normSq_eq_canonical]
  exact Block.Descent.postInversion_norm_gt_one
    (normalizedValue_band_of_fullBlock kind exponent sector value full)
    sector full.2 residual
end Purelib.Data.CCL.Encoding.Parser.Semantics.Normalization

end
