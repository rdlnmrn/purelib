module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.CCL.Encoding.Encoder.Cylinder
public import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.SignedFraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Normalization
public import Purelib.Examples.Data.GaussianInt.Fraction.WorkedExamples
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Basic

open Purelib

open Purelib.Data

section
@[expose] public section

/-!
# Exact executable CCL examples

The three CCL expansions printed in the manuscript are evaluated by the
active constructive encoder.  Kernel `decide` checks only the displayed
finite Gaussian-integer inputs and finite output lists; no native-code axiom
or completed stream is involved.
-/

namespace Purelib.Examples.Data.CCL.Encoding.WorkedExamples

open Purelib.Examples
open Purelib.Data.Rat

open Purelib.Data.CCL.Encoding.Encoder
open Purelib.Examples.Data.GaussianInt.Fraction.WorkedExamples
open Purelib.Data.ComplexContinuedFraction.Encoding
/-- A finite CCL bit word. -/
abbrev Word := List Bool

/-- The normalized rational represented by the supplied integer numerator and positive denominator. -/
def displayedRational (numerator denominator : Int)
    (denominatorPositive : 0 < denominator) : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction
    ⟨numerator, denominator, denominatorPositive⟩

/-- The initial annulus value −355/452 − (355/452)i in the encoding of 355/113. -/
def longInitialValue : Gaussian.Basic.Canonical :=
  ⟨displayedRational (-355) 452 (by decide),
    displayedRational (-355) 452 (by decide)⟩

/-- The first residual annulus value −113/97 in the encoding of 355/113. -/
def longStepZeroValue : Gaussian.Basic.Canonical :=
  ⟨displayedRational (-113) 97 (by decide), 0⟩

/-- The second residual annulus value 97/128 − (97/128)i in the encoding of 355/113. -/
def longStepOneValue : Gaussian.Basic.Canonical :=
  ⟨displayedRational 97 128 (by decide),
    displayedRational (-97) 128 (by decide)⟩

/-- The third residual annulus value (32/31)i in the encoding of 355/113. -/
def longStepTwoValue : Gaussian.Basic.Canonical :=
  ⟨0, displayedRational 32 31 (by decide)⟩

/-- The fourth residual annulus value −31/32 − (31/32)i in the encoding of 355/113. -/
def longStepThreeValue : Gaussian.Basic.Canonical :=
  ⟨displayedRational (-31) 32 (by decide),
    displayedRational (-31) 32 (by decide)⟩

/-- The terminal annulus value 1 − i in the encoding of 355/113. -/
def longStepFourValue : Gaussian.Basic.Canonical :=
  ⟨1, -1⟩

/-- The constructive encoder produces the displayed three blocks for (3 + 4i)/5. -/
theorem threePlusFourIOverFive_blocks :
    (Blocks.encodeBlocks
      threePlusFourIOverFive
      threePlusFourIOverFive_num_ne).blocks =
      [⟨.initialLow, 0, .northEast⟩,
        ⟨.regular, 1, .northEast⟩,
        ⟨.regular, 0, .northWest⟩] := by
  have lowBranch : threePlusFourIOverFive.numerator.normNat <
      2 * threePlusFourIOverFive.denominator.normNat := by
        decide
  let initial := Blocks.initialLowBlockStep
    threePlusFourIOverFive
      threePlusFourIOverFive_num_ne lowBranch
  rw [Blocks.encodeBlocks_blocks_of_low_step _ _ lowBranch]
  change initial.block ::
      (Annulus.Blocks.encodeAnnulusBlocks
        initial.annulus).continuation = _
  have residual₀ : Annulus.Blocks.annulusResidual
      initial.annulus ≠ 0 := by decide +revert
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    initial.annulus residual₀]
  let step₀ := Annulus.Blocks.annulusStep initial.annulus residual₀
  change initial.block :: step₀.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₀.next).continuation = _
  have residual₁ : Annulus.Blocks.annulusResidual step₀.next ≠ 0 := by
    decide +revert
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    step₀.next residual₁]
  let step₁ := Annulus.Blocks.annulusStep step₀.next residual₁
  change initial.block :: step₀.block :: step₁.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₁.next).continuation = _
  have terminal : Annulus.Blocks.annulusResidual step₁.next = 0 := by
    decide +revert
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_residual_eq
    step₁.next terminal]
  decide +revert

/-- The constructive encoder produces the displayed fourteen-bit word for (3 + 4i)/5. -/
theorem threePlusFourIOverFive_raw :
    Integral.encode
      threePlusFourIOverFive
      threePlusFourIOverFive_num_ne =
      [false, false, false, false, true, true, false, false, false, true,
        false, false, true, true] := by
  rw [Cylinder.encode_eq_rawWord,
    threePlusFourIOverFive_blocks]
  decide

/-- The constructive encoder produces the displayed four blocks for 13/5. -/
theorem thirteenOverFive_blocks :
    (Blocks.encodeBlocks thirteenOverFive
      thirteenOverFive_num_ne).blocks =
      [⟨.regular, 2, .south⟩,
        ⟨.regular, 2, .southEast⟩,
        ⟨.regular, 3, .northEast⟩,
        ⟨.regular, 1, .northEast⟩] := by
  have highBranch : 2 * thirteenOverFive.denominator.normNat ≤
      thirteenOverFive.numerator.normNat := by decide
  let initial := Blocks.initialHighBlockStep
    thirteenOverFive
      thirteenOverFive_num_ne highBranch
  rw [Blocks.encodeBlocks_blocks_of_high_step _ _ highBranch]
  change initial.block ::
      (Annulus.Blocks.encodeAnnulusBlocks
        initial.annulus).continuation = _
  have residual₀ : Annulus.Blocks.annulusResidual
      initial.annulus ≠ 0 := by decide +revert
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    initial.annulus residual₀]
  let step₀ := Annulus.Blocks.annulusStep initial.annulus residual₀
  change initial.block :: step₀.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₀.next).continuation = _
  have residual₁ : Annulus.Blocks.annulusResidual step₀.next ≠ 0 := by
    decide +revert
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    step₀.next residual₁]
  let step₁ := Annulus.Blocks.annulusStep step₀.next residual₁
  change initial.block :: step₀.block :: step₁.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₁.next).continuation = _
  have residual₂ : Annulus.Blocks.annulusResidual step₁.next ≠ 0 := by
    decide +revert
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    step₁.next residual₂]
  let step₂ := Annulus.Blocks.annulusStep step₁.next residual₂
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₂.next).continuation = _
  have terminal : Annulus.Blocks.annulusResidual step₂.next = 0 := by
    decide +revert
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_residual_eq
    step₂.next terminal]
  decide +revert

/-- The constructive encoder produces the displayed twenty-four-bit word for 13/5. -/
theorem thirteenOverFive_raw :
    Integral.encode thirteenOverFive
      thirteenOverFive_num_ne =
      [true, true, false, true, true, false, true, true, false, true, true,
        true, true, true, true, false, false, false, true, true, false, false,
        false, true] := by
  rw [Cylinder.encode_eq_rawWord, thirteenOverFive_blocks]
  decide

/-- The constructive encoder produces the displayed six blocks for 355/113.

Each retained annulus step is checked through its exact Gaussian-integer numerator, denominator, sector and terminating
residual. -/
theorem threeFiftyFiveOverOneThirteen_blocks :
    (Blocks.encodeBlocks
      threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne).blocks =
      [⟨.regular, 3, .southWest⟩,
        ⟨.regular, 2, .west⟩,
        ⟨.regular, 4, .southEast⟩,
        ⟨.regular, 2, .north⟩,
        ⟨.regular, 8, .southWest⟩,
        ⟨.regular, 7, .southEast⟩] := by
  have highBranch : 2 * threeFiftyFiveOverOneThirteen.denominator.normNat ≤
      threeFiftyFiveOverOneThirteen.numerator.normNat := by decide
  let initial := Blocks.initialHighBlockStep
    threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne
      highBranch
  rw [Blocks.encodeBlocks_blocks_of_high_step _ _ highBranch]
  change initial.block ::
      (Annulus.Blocks.encodeAnnulusBlocks
        initial.annulus).continuation = _
  have initialExponent : initial.block.exponent = 3 :=
    Blocks.initialHighBlockStep_exponent_eq_of_bounds
      threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne highBranch 3
      (by decide) (by decide)
  have initialNum : initial.annulus.frac.numerator = ⟨355, 0⟩ :=
    Blocks.initialHighBlockStep_num_eq
      threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne highBranch
  have initialDen : initial.annulus.frac.denominator = ⟨-226, 226⟩ := by
    rw [Blocks.initialHighBlockStep_den_eq,
      initialExponent]
    decide
  have initialValue : initial.annulus.frac.value = longInitialValue := by
    apply GaussianInt.Fraction.value_eq_of_mul_den
    rw [initialNum, initialDen]
    apply Gaussian.Basic.ext <;>
      simp only [longInitialValue, displayedRational,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        GaussianInt.toGaussian,
        SignedFraction.Arithmetic.intCast_eq_fraction, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
      decide
  have initialSector : Sector.select
      initial.annulus.frac.value = .southWest := by
    rw [initialValue]
    apply Sector.select_eq_of_holds
    decide
  have initialResidual : Annulus.Blocks.annulusResidual
      initial.annulus = ⟨-97, 0⟩ := by
    unfold Annulus.Blocks.annulusResidual
    rw [initialNum, initialDen, initialSector]
    decide
  have residual₀ : Annulus.Blocks.annulusResidual
      initial.annulus ≠ 0 := by
    rw [initialResidual]
    decide
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    initial.annulus residual₀]
  let step₀ := Annulus.Blocks.annulusStep initial.annulus residual₀
  change initial.block :: step₀.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₀.next).continuation = _
  have step₀Exponent : step₀.block.exponent = 2 :=
    Blocks.annulusStep_exponent_eq_of_bounds
      initial.annulus residual₀ 2
      (by rw [initialDen, initialResidual]; decide)
      (by rw [initialDen, initialResidual]; decide)
  have step₀Num : step₀.next.frac.numerator = ⟨-226, 226⟩ :=
    (Blocks.annulusStep_next_num_eq
      initial.annulus residual₀).trans initialDen
  have step₀Den : step₀.next.frac.denominator = ⟨194, -194⟩ := by
    rw [Blocks.annulusStep_next_den_eq,
      step₀Exponent, initialResidual]
    decide
  have step₀Value : step₀.next.frac.value = longStepZeroValue := by
    apply GaussianInt.Fraction.value_eq_of_mul_den
    rw [step₀Num, step₀Den]
    apply Gaussian.Basic.ext <;>
      simp only [longStepZeroValue, displayedRational,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        GaussianInt.toGaussian,
        SignedFraction.Arithmetic.intCast_eq_fraction, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
      decide
  have step₀Sector : Sector.select
      step₀.next.frac.value = .west := by
    rw [step₀Value]
    apply Sector.select_eq_of_holds
    decide
  have step₀Residual : Annulus.Blocks.annulusResidual
      step₀.next = ⟨-32, 32⟩ := by
    unfold Annulus.Blocks.annulusResidual
    rw [step₀Num, step₀Den, step₀Sector]
    decide
  have residual₁ : Annulus.Blocks.annulusResidual step₀.next ≠ 0 := by
    rw [step₀Residual]
    decide
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    step₀.next residual₁]
  let step₁ := Annulus.Blocks.annulusStep step₀.next residual₁
  change initial.block :: step₀.block :: step₁.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₁.next).continuation = _
  have step₁Exponent : step₁.block.exponent = 4 :=
    Blocks.annulusStep_exponent_eq_of_bounds
      step₀.next residual₁ 4
      (by rw [step₀Den, step₀Residual]; decide)
      (by rw [step₀Den, step₀Residual]; decide)
  have step₁Num : step₁.next.frac.numerator = ⟨194, -194⟩ :=
    (Blocks.annulusStep_next_num_eq
      step₀.next residual₁).trans step₀Den
  have step₁Den : step₁.next.frac.denominator = ⟨256, 0⟩ := by
    rw [Blocks.annulusStep_next_den_eq,
      step₁Exponent, step₀Residual]
    decide
  have step₁Value : step₁.next.frac.value = longStepOneValue := by
    apply GaussianInt.Fraction.value_eq_of_mul_den
    rw [step₁Num, step₁Den]
    apply Gaussian.Basic.ext <;>
      simp only [longStepOneValue, displayedRational,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        GaussianInt.toGaussian,
        SignedFraction.Arithmetic.intCast_eq_fraction, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
      decide
  have step₁Sector : Sector.select
      step₁.next.frac.value = .southEast := by
    rw [step₁Value]
    apply Sector.select_eq_of_holds
    decide
  have step₁Residual : Annulus.Blocks.annulusResidual
      step₁.next = ⟨-62, 62⟩ := by
    unfold Annulus.Blocks.annulusResidual
    rw [step₁Num, step₁Den, step₁Sector]
    decide
  have residual₂ : Annulus.Blocks.annulusResidual step₁.next ≠ 0 := by
    rw [step₁Residual]
    decide
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    step₁.next residual₂]
  let step₂ := Annulus.Blocks.annulusStep step₁.next residual₂
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₂.next).continuation = _
  have step₂Exponent : step₂.block.exponent = 2 :=
    Blocks.annulusStep_exponent_eq_of_bounds
      step₁.next residual₂ 2
      (by rw [step₁Den, step₁Residual]; decide)
      (by rw [step₁Den, step₁Residual]; decide)
  have step₂Num : step₂.next.frac.numerator = ⟨256, 0⟩ :=
    (Blocks.annulusStep_next_num_eq
      step₁.next residual₂).trans step₁Den
  have step₂Den : step₂.next.frac.denominator = ⟨0, -248⟩ := by
    rw [Blocks.annulusStep_next_den_eq,
      step₂Exponent, step₁Residual]
    decide
  have step₂Value : step₂.next.frac.value = longStepTwoValue := by
    apply GaussianInt.Fraction.value_eq_of_mul_den
    rw [step₂Num, step₂Den]
    apply Gaussian.Basic.ext <;>
      simp only [longStepTwoValue, displayedRational,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        GaussianInt.toGaussian,
        SignedFraction.Arithmetic.intCast_eq_fraction, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
      decide
  have step₂Sector : Sector.select
      step₂.next.frac.value = .north := by
    rw [step₂Value]
    apply Sector.select_eq_of_holds
    decide
  have step₂Residual : Annulus.Blocks.annulusResidual
      step₂.next = ⟨8, 0⟩ := by
    unfold Annulus.Blocks.annulusResidual
    rw [step₂Num, step₂Den, step₂Sector]
    decide
  have residual₃ : Annulus.Blocks.annulusResidual step₂.next ≠ 0 := by
    rw [step₂Residual]
    decide
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    step₂.next residual₃]
  let step₃ := Annulus.Blocks.annulusStep step₂.next residual₃
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      step₃.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₃.next).continuation = _
  have step₃Exponent : step₃.block.exponent = 8 :=
    Blocks.annulusStep_exponent_eq_of_bounds
      step₂.next residual₃ 8
      (by rw [step₂Den, step₂Residual]; decide)
      (by rw [step₂Den, step₂Residual]; decide)
  have step₃Num : step₃.next.frac.numerator = ⟨0, -248⟩ :=
    (Blocks.annulusStep_next_num_eq
      step₂.next residual₃).trans step₂Den
  have step₃Den : step₃.next.frac.denominator = ⟨128, 128⟩ := by
    rw [Blocks.annulusStep_next_den_eq,
      step₃Exponent, step₂Residual]
    decide
  have step₃Value : step₃.next.frac.value = longStepThreeValue := by
    apply GaussianInt.Fraction.value_eq_of_mul_den
    rw [step₃Num, step₃Den]
    apply Gaussian.Basic.ext <;>
      simp only [longStepThreeValue,
        displayedRational,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        GaussianInt.toGaussian,
        SignedFraction.Arithmetic.intCast_eq_fraction, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
      decide
  have step₃Sector : Sector.select
      step₃.next.frac.value = .southWest := by
    rw [step₃Value]
    apply Sector.select_eq_of_holds
    decide
  have step₃Residual : Annulus.Blocks.annulusResidual
      step₃.next = ⟨0, 8⟩ := by
    unfold Annulus.Blocks.annulusResidual
    rw [step₃Num, step₃Den, step₃Sector]
    decide
  have residual₄ : Annulus.Blocks.annulusResidual step₃.next ≠ 0 := by
    rw [step₃Residual]
    decide
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne_step
    step₃.next residual₄]
  let step₄ := Annulus.Blocks.annulusStep step₃.next residual₄
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      step₃.block :: step₄.block ::
      (Annulus.Blocks.encodeAnnulusBlocks step₄.next).continuation = _
  have step₄Exponent : step₄.block.exponent = 7 :=
    Blocks.annulusStep_exponent_eq_of_bounds
      step₃.next residual₄ 7
      (by rw [step₃Den, step₃Residual]; decide)
      (by rw [step₃Den, step₃Residual]; decide)
  have step₄Num : step₄.next.frac.numerator = ⟨128, 128⟩ :=
    (Blocks.annulusStep_next_num_eq
      step₃.next residual₄).trans step₃Den
  have step₄Den : step₄.next.frac.denominator = ⟨0, 128⟩ := by
    rw [Blocks.annulusStep_next_den_eq,
      step₄Exponent, step₃Residual]
    decide
  have step₄Value : step₄.next.frac.value = longStepFourValue := by
    apply GaussianInt.Fraction.value_eq_of_mul_den
    rw [step₄Num, step₄Den]
    apply Gaussian.Basic.ext <;>
      simp only [longStepFourValue,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        GaussianInt.toGaussian,
        SignedFraction.Arithmetic.intCast_eq_fraction, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
      decide
  have step₄Sector : Sector.select
      step₄.next.frac.value = .southEast := by
    rw [step₄Value]
    apply Sector.select_eq_of_holds
    decide
  have step₄Residual : Annulus.Blocks.annulusResidual
      step₄.next = 0 := by
    unfold Annulus.Blocks.annulusResidual
    rw [step₄Num, step₄Den, step₄Sector]
    decide
  have terminal : Annulus.Blocks.annulusResidual step₄.next = 0 := by
    exact step₄Residual
  rw [Annulus.Blocks.encodeAnnulusBlocks_continuation_of_residual_eq
    step₄.next terminal]
  rw [Blocks.initialHighBlockStep_block_eq,
    Blocks.annulusStep_block_eq initial.annulus residual₀,
    Blocks.annulusStep_block_eq step₀.next residual₁,
    Blocks.annulusStep_block_eq step₁.next residual₂,
    Blocks.annulusStep_block_eq step₂.next residual₃,
    Blocks.annulusStep_block_eq step₃.next residual₄,
    initialExponent, step₀Exponent, step₁Exponent, step₂Exponent,
    step₃Exponent, step₄Exponent]
  rw [initialSector, step₀Sector, step₁Sector, step₂Sector,
    step₃Sector, step₄Sector]

/-- The constructive encoder produces the displayed finite raw word for 355/113. -/
theorem threeFiftyFiveOverOneThirteen_raw :
    Integral.encode threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne =
      [true, true, true, false, true, false, true, true, true, false, true,
        false, false, true, true, true, true, false, true, true, true, true,
        true, false, false, true, false, true, true, true, true, true, true,
        true, true, false, true, false, true, true, true, true, true, true,
        true, true, false, true, true, true] := by
  rw [Cylinder.encode_eq_rawWord,
    threeFiftyFiveOverOneThirteen_blocks]
  decide

end Purelib.Examples.Data.CCL.Encoding.WorkedExamples

end
