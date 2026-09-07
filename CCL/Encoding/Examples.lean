import CCL.Encoding.Encoder

/-!
# Exact executable CCL examples

The three CCL expansions printed in the manuscript are evaluated by the
active constructive encoder.  Kernel `decide` checks only the displayed
finite Gaussian-integer inputs and finite output lists; no native-code axiom
or completed stream is involved.
-/

namespace CCL.Examples

abbrev GaussianInt := CCL.Integral.GaussianInt
abbrev Frac := CCL.Integral.Frac
abbrev Block := CCL.Cylinder.Block
abbrev Word := List Bool
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

/-- A displayed rational coordinate with no quotient normalization or
division computation hidden in its syntax. -/
def displayedRational (numerator denominator : Int)
    (denominatorPositive : 0 < denominator) : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction
    ⟨numerator, denominator, denominatorPositive⟩

def longInitialValue : Gaussian :=
  ⟨displayedRational (-355) 452 (by decide),
    displayedRational (-355) 452 (by decide)⟩

def longStepZeroValue : Gaussian :=
  ⟨displayedRational (-113) 97 (by decide), 0⟩

def longStepOneValue : Gaussian :=
  ⟨displayedRational 97 128 (by decide),
    displayedRational (-97) 128 (by decide)⟩

def longStepTwoValue : Gaussian :=
  ⟨0, displayedRational 32 31 (by decide)⟩

def longStepThreeValue : Gaussian :=
  ⟨displayedRational (-31) 32 (by decide),
    displayedRational (-31) 32 (by decide)⟩

def longStepFourValue : Gaussian :=
  ⟨1, -1⟩

def threePlusFourIOverFive : Frac :=
  ⟨⟨3, 4⟩, ⟨5, 0⟩, by decide⟩

def thirteenOverFive : Frac :=
  ⟨⟨13, 0⟩, ⟨5, 0⟩, by decide⟩

def threeFiftyFiveOverOneThirteen : Frac :=
  ⟨⟨355, 0⟩, ⟨113, 0⟩, by decide⟩

theorem threePlusFourIOverFive_num_ne :
    threePlusFourIOverFive.num ≠ 0 := by decide

theorem thirteenOverFive_num_ne : thirteenOverFive.num ≠ 0 := by decide

theorem threeFiftyFiveOverOneThirteen_num_ne :
    threeFiftyFiveOverOneThirteen.num ≠ 0 := by decide

theorem threePlusFourIOverFive_blocks :
    (CCL.Encoder.encodeBlocks threePlusFourIOverFive
      threePlusFourIOverFive_num_ne).blocks =
      [⟨.initialLow, 0, .northEast⟩,
        ⟨.regular, 1, .northEast⟩,
        ⟨.regular, 0, .northWest⟩] := by
  have lowBranch : threePlusFourIOverFive.num.normNat <
      2 * threePlusFourIOverFive.den.normNat := by decide
  let initial := CCL.Encoder.initialLowBlockStep
    threePlusFourIOverFive threePlusFourIOverFive_num_ne lowBranch
  rw [CCL.Encoder.encodeBlocks_blocks_of_low_step _ _ lowBranch]
  change initial.block ::
      (CCL.Encoder.encodeAnnulusBlocks
        initial.annulus).continuation = _
  have residual₀ : CCL.Encoder.annulusResidual
      initial.annulus ≠ 0 := by decide +revert
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    initial.annulus residual₀]
  let step₀ := CCL.Encoder.annulusStep initial.annulus residual₀
  change initial.block :: step₀.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₀.next).continuation = _
  have residual₁ : CCL.Encoder.annulusResidual step₀.next ≠ 0 := by
    decide +revert
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    step₀.next residual₁]
  let step₁ := CCL.Encoder.annulusStep step₀.next residual₁
  change initial.block :: step₀.block :: step₁.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₁.next).continuation = _
  have terminal : CCL.Encoder.annulusResidual step₁.next = 0 := by
    decide +revert
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_residual_eq
    step₁.next terminal]
  decide +revert

theorem threePlusFourIOverFive_raw :
    CCL.Encoder.encode threePlusFourIOverFive
      threePlusFourIOverFive_num_ne =
      [false, false, false, false, true, true, false, false, false, true,
        false, false, true, true] := by
  rw [CCL.Encoder.encode_eq_rawWord,
    threePlusFourIOverFive_blocks]
  decide

theorem thirteenOverFive_blocks :
    (CCL.Encoder.encodeBlocks thirteenOverFive
      thirteenOverFive_num_ne).blocks =
      [⟨.regular, 2, .south⟩,
        ⟨.regular, 2, .southEast⟩,
        ⟨.regular, 3, .northEast⟩,
        ⟨.regular, 1, .northEast⟩] := by
  have highBranch : 2 * thirteenOverFive.den.normNat ≤
      thirteenOverFive.num.normNat := by decide
  let initial := CCL.Encoder.initialHighBlockStep
    thirteenOverFive thirteenOverFive_num_ne highBranch
  rw [CCL.Encoder.encodeBlocks_blocks_of_high_step _ _ highBranch]
  change initial.block ::
      (CCL.Encoder.encodeAnnulusBlocks
        initial.annulus).continuation = _
  have residual₀ : CCL.Encoder.annulusResidual
      initial.annulus ≠ 0 := by decide +revert
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    initial.annulus residual₀]
  let step₀ := CCL.Encoder.annulusStep initial.annulus residual₀
  change initial.block :: step₀.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₀.next).continuation = _
  have residual₁ : CCL.Encoder.annulusResidual step₀.next ≠ 0 := by
    decide +revert
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    step₀.next residual₁]
  let step₁ := CCL.Encoder.annulusStep step₀.next residual₁
  change initial.block :: step₀.block :: step₁.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₁.next).continuation = _
  have residual₂ : CCL.Encoder.annulusResidual step₁.next ≠ 0 := by
    decide +revert
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    step₁.next residual₂]
  let step₂ := CCL.Encoder.annulusStep step₁.next residual₂
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₂.next).continuation = _
  have terminal : CCL.Encoder.annulusResidual step₂.next = 0 := by
    decide +revert
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_residual_eq
    step₂.next terminal]
  decide +revert

theorem thirteenOverFive_raw :
    CCL.Encoder.encode thirteenOverFive thirteenOverFive_num_ne =
      [true, true, false, true, true, false, true, true, false, true, true,
        true, true, true, true, false, false, false, true, true, false, false,
        false, true] := by
  rw [CCL.Encoder.encode_eq_rawWord, thirteenOverFive_blocks]
  decide

theorem threeFiftyFiveOverOneThirteen_blocks :
    (CCL.Encoder.encodeBlocks threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne).blocks =
      [⟨.regular, 3, .southWest⟩,
        ⟨.regular, 2, .west⟩,
        ⟨.regular, 4, .southEast⟩,
        ⟨.regular, 2, .north⟩,
        ⟨.regular, 8, .southWest⟩,
        ⟨.regular, 7, .southEast⟩] := by
  have highBranch : 2 * threeFiftyFiveOverOneThirteen.den.normNat ≤
      threeFiftyFiveOverOneThirteen.num.normNat := by decide
  let initial := CCL.Encoder.initialHighBlockStep
    threeFiftyFiveOverOneThirteen threeFiftyFiveOverOneThirteen_num_ne
      highBranch
  rw [CCL.Encoder.encodeBlocks_blocks_of_high_step _ _ highBranch]
  change initial.block ::
      (CCL.Encoder.encodeAnnulusBlocks
        initial.annulus).continuation = _
  have initialExponent : initial.block.exponent = 3 :=
    CCL.Encoder.initialHighBlockStep_exponent_eq_of_bounds
      threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne highBranch 3
      (by decide) (by decide)
  have initialNum : initial.annulus.frac.num = ⟨355, 0⟩ :=
    CCL.Encoder.initialHighBlockStep_num_eq
      threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne highBranch
  have initialDen : initial.annulus.frac.den = ⟨-226, 226⟩ := by
    rw [CCL.Encoder.initialHighBlockStep_den_eq,
      initialExponent]
    decide
  have initialValue : initial.annulus.frac.value = longInitialValue := by
    apply CCL.Encoder.Frac.value_eq_of_mul_den
    rw [initialNum, initialDen]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [longInitialValue, displayedRational,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        CCL.Integral.GaussianInt.toGaussian,
        RFAP.ConstructiveFraction.intCast_eq_fraction] <;>
      decide
  have initialSector : CCL.Sectors.Sector.select
      initial.annulus.frac.value = .southWest := by
    rw [initialValue]
    apply CCL.Sectors.Sector.select_eq_of_holds
    decide
  have initialResidual : CCL.Encoder.annulusResidual
      initial.annulus = ⟨-97, 0⟩ := by
    unfold CCL.Encoder.annulusResidual
    rw [initialNum, initialDen, initialSector]
    decide
  have residual₀ : CCL.Encoder.annulusResidual
      initial.annulus ≠ 0 := by
    rw [initialResidual]
    decide
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    initial.annulus residual₀]
  let step₀ := CCL.Encoder.annulusStep initial.annulus residual₀
  change initial.block :: step₀.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₀.next).continuation = _
  have step₀Exponent : step₀.block.exponent = 2 :=
    CCL.Encoder.annulusStep_exponent_eq_of_bounds
      initial.annulus residual₀ 2
      (by rw [initialDen, initialResidual]; decide)
      (by rw [initialDen, initialResidual]; decide)
  have step₀Num : step₀.next.frac.num = ⟨-226, 226⟩ :=
    (CCL.Encoder.annulusStep_next_num_eq
      initial.annulus residual₀).trans initialDen
  have step₀Den : step₀.next.frac.den = ⟨194, -194⟩ := by
    rw [CCL.Encoder.annulusStep_next_den_eq,
      step₀Exponent, initialResidual]
    decide
  have step₀Value : step₀.next.frac.value = longStepZeroValue := by
    apply CCL.Encoder.Frac.value_eq_of_mul_den
    rw [step₀Num, step₀Den]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [longStepZeroValue, displayedRational,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        CCL.Integral.GaussianInt.toGaussian,
        RFAP.ConstructiveFraction.intCast_eq_fraction] <;>
      decide
  have step₀Sector : CCL.Sectors.Sector.select
      step₀.next.frac.value = .west := by
    rw [step₀Value]
    apply CCL.Sectors.Sector.select_eq_of_holds
    decide
  have step₀Residual : CCL.Encoder.annulusResidual
      step₀.next = ⟨-32, 32⟩ := by
    unfold CCL.Encoder.annulusResidual
    rw [step₀Num, step₀Den, step₀Sector]
    decide
  have residual₁ : CCL.Encoder.annulusResidual step₀.next ≠ 0 := by
    rw [step₀Residual]
    decide
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    step₀.next residual₁]
  let step₁ := CCL.Encoder.annulusStep step₀.next residual₁
  change initial.block :: step₀.block :: step₁.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₁.next).continuation = _
  have step₁Exponent : step₁.block.exponent = 4 :=
    CCL.Encoder.annulusStep_exponent_eq_of_bounds
      step₀.next residual₁ 4
      (by rw [step₀Den, step₀Residual]; decide)
      (by rw [step₀Den, step₀Residual]; decide)
  have step₁Num : step₁.next.frac.num = ⟨194, -194⟩ :=
    (CCL.Encoder.annulusStep_next_num_eq
      step₀.next residual₁).trans step₀Den
  have step₁Den : step₁.next.frac.den = ⟨256, 0⟩ := by
    rw [CCL.Encoder.annulusStep_next_den_eq,
      step₁Exponent, step₀Residual]
    decide
  have step₁Value : step₁.next.frac.value = longStepOneValue := by
    apply CCL.Encoder.Frac.value_eq_of_mul_den
    rw [step₁Num, step₁Den]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [longStepOneValue, displayedRational,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        CCL.Integral.GaussianInt.toGaussian,
        RFAP.ConstructiveFraction.intCast_eq_fraction] <;>
      decide
  have step₁Sector : CCL.Sectors.Sector.select
      step₁.next.frac.value = .southEast := by
    rw [step₁Value]
    apply CCL.Sectors.Sector.select_eq_of_holds
    decide
  have step₁Residual : CCL.Encoder.annulusResidual
      step₁.next = ⟨-62, 62⟩ := by
    unfold CCL.Encoder.annulusResidual
    rw [step₁Num, step₁Den, step₁Sector]
    decide
  have residual₂ : CCL.Encoder.annulusResidual step₁.next ≠ 0 := by
    rw [step₁Residual]
    decide
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    step₁.next residual₂]
  let step₂ := CCL.Encoder.annulusStep step₁.next residual₂
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₂.next).continuation = _
  have step₂Exponent : step₂.block.exponent = 2 :=
    CCL.Encoder.annulusStep_exponent_eq_of_bounds
      step₁.next residual₂ 2
      (by rw [step₁Den, step₁Residual]; decide)
      (by rw [step₁Den, step₁Residual]; decide)
  have step₂Num : step₂.next.frac.num = ⟨256, 0⟩ :=
    (CCL.Encoder.annulusStep_next_num_eq
      step₁.next residual₂).trans step₁Den
  have step₂Den : step₂.next.frac.den = ⟨0, -248⟩ := by
    rw [CCL.Encoder.annulusStep_next_den_eq,
      step₂Exponent, step₁Residual]
    decide
  have step₂Value : step₂.next.frac.value = longStepTwoValue := by
    apply CCL.Encoder.Frac.value_eq_of_mul_den
    rw [step₂Num, step₂Den]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [longStepTwoValue, displayedRational,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        CCL.Integral.GaussianInt.toGaussian,
        RFAP.ConstructiveFraction.intCast_eq_fraction] <;>
      decide
  have step₂Sector : CCL.Sectors.Sector.select
      step₂.next.frac.value = .north := by
    rw [step₂Value]
    apply CCL.Sectors.Sector.select_eq_of_holds
    decide
  have step₂Residual : CCL.Encoder.annulusResidual
      step₂.next = ⟨8, 0⟩ := by
    unfold CCL.Encoder.annulusResidual
    rw [step₂Num, step₂Den, step₂Sector]
    decide
  have residual₃ : CCL.Encoder.annulusResidual step₂.next ≠ 0 := by
    rw [step₂Residual]
    decide
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    step₂.next residual₃]
  let step₃ := CCL.Encoder.annulusStep step₂.next residual₃
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      step₃.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₃.next).continuation = _
  have step₃Exponent : step₃.block.exponent = 8 :=
    CCL.Encoder.annulusStep_exponent_eq_of_bounds
      step₂.next residual₃ 8
      (by rw [step₂Den, step₂Residual]; decide)
      (by rw [step₂Den, step₂Residual]; decide)
  have step₃Num : step₃.next.frac.num = ⟨0, -248⟩ :=
    (CCL.Encoder.annulusStep_next_num_eq
      step₂.next residual₃).trans step₂Den
  have step₃Den : step₃.next.frac.den = ⟨128, 128⟩ := by
    rw [CCL.Encoder.annulusStep_next_den_eq,
      step₃Exponent, step₂Residual]
    decide
  have step₃Value : step₃.next.frac.value = longStepThreeValue := by
    apply CCL.Encoder.Frac.value_eq_of_mul_den
    rw [step₃Num, step₃Den]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [longStepThreeValue, displayedRational,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        CCL.Integral.GaussianInt.toGaussian,
        RFAP.ConstructiveFraction.intCast_eq_fraction] <;>
      decide
  have step₃Sector : CCL.Sectors.Sector.select
      step₃.next.frac.value = .southWest := by
    rw [step₃Value]
    apply CCL.Sectors.Sector.select_eq_of_holds
    decide
  have step₃Residual : CCL.Encoder.annulusResidual
      step₃.next = ⟨0, 8⟩ := by
    unfold CCL.Encoder.annulusResidual
    rw [step₃Num, step₃Den, step₃Sector]
    decide
  have residual₄ : CCL.Encoder.annulusResidual step₃.next ≠ 0 := by
    rw [step₃Residual]
    decide
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_ne_step
    step₃.next residual₄]
  let step₄ := CCL.Encoder.annulusStep step₃.next residual₄
  change initial.block :: step₀.block :: step₁.block :: step₂.block ::
      step₃.block :: step₄.block ::
      (CCL.Encoder.encodeAnnulusBlocks step₄.next).continuation = _
  have step₄Exponent : step₄.block.exponent = 7 :=
    CCL.Encoder.annulusStep_exponent_eq_of_bounds
      step₃.next residual₄ 7
      (by rw [step₃Den, step₃Residual]; decide)
      (by rw [step₃Den, step₃Residual]; decide)
  have step₄Num : step₄.next.frac.num = ⟨128, 128⟩ :=
    (CCL.Encoder.annulusStep_next_num_eq
      step₃.next residual₄).trans step₃Den
  have step₄Den : step₄.next.frac.den = ⟨0, 128⟩ := by
    rw [CCL.Encoder.annulusStep_next_den_eq,
      step₄Exponent, step₃Residual]
    decide
  have step₄Value : step₄.next.frac.value = longStepFourValue := by
    apply CCL.Encoder.Frac.value_eq_of_mul_den
    rw [step₄Num, step₄Den]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [longStepFourValue,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        CCL.Integral.GaussianInt.toGaussian,
        RFAP.ConstructiveFraction.intCast_eq_fraction] <;>
      decide
  have step₄Sector : CCL.Sectors.Sector.select
      step₄.next.frac.value = .southEast := by
    rw [step₄Value]
    apply CCL.Sectors.Sector.select_eq_of_holds
    decide
  have step₄Residual : CCL.Encoder.annulusResidual
      step₄.next = 0 := by
    unfold CCL.Encoder.annulusResidual
    rw [step₄Num, step₄Den, step₄Sector]
    decide
  have terminal : CCL.Encoder.annulusResidual step₄.next = 0 := by
    exact step₄Residual
  rw [CCL.Encoder.encodeAnnulusBlocks_continuation_of_residual_eq
    step₄.next terminal]
  rw [CCL.Encoder.initialHighBlockStep_block_eq,
    CCL.Encoder.annulusStep_block_eq initial.annulus residual₀,
    CCL.Encoder.annulusStep_block_eq step₀.next residual₁,
    CCL.Encoder.annulusStep_block_eq step₁.next residual₂,
    CCL.Encoder.annulusStep_block_eq step₂.next residual₃,
    CCL.Encoder.annulusStep_block_eq step₃.next residual₄,
    initialExponent, step₀Exponent, step₁Exponent, step₂Exponent,
    step₃Exponent, step₄Exponent]
  rw [initialSector, step₀Sector, step₁Sector, step₂Sector,
    step₃Sector, step₄Sector]

theorem threeFiftyFiveOverOneThirteen_raw :
    CCL.Encoder.encode threeFiftyFiveOverOneThirteen
      threeFiftyFiveOverOneThirteen_num_ne =
      [true, true, true, false, true, false, true, true, true, false, true,
        false, false, true, true, true, true, false, true, true, true, true,
        true, false, false, true, false, true, true, true, true, true, true,
        true, true, false, true, false, true, true, true, true, true, true,
        true, true, false, true, true, true] := by
  rw [CCL.Encoder.encode_eq_rawWord,
    threeFiftyFiveOverOneThirteen_blocks]
  decide

end CCL.Examples
