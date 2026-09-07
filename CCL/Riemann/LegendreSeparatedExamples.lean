import CCL.Riemann.LegendreSeparatedWords
import CCL.Riemann.LegendreSignedGapExamples

/-! # Unsigned word preparation, including the negative acquisition path -/

namespace CCL.Riemann.LegendreSeparatedExamples

open CCL.Riemann.LegendreSeparatedPreparation
open CCL.Riemann.LegendreSeparatedWords (Word)
open CCL.Riemann.LegendreSignedAcquisitionExamples (input report)
open CCL.Riemann.LegendrePositivityAcquisition (initial)

def negativeSeparation : Separation (input (-1)) :=
  Separation.ofGap (initial (input (-1))) 1 (by decide)
    (CCL.Riemann.LegendreSignedGapExamples.negative_gap _)

def negativeWord (word : Word) := CCL.Riemann.LegendreSeparatedWords.acquire negativeSeparation word

theorem negative_acquisition_prepares (word : Word) :
    ∃ prepared, CCL.Riemann.LegendreSeparatedWords.acquireSigned (report (-1)) word = .inl prepared :=
  ⟨_, rfl⟩

theorem positive_acquisition_prepares (word : Word) :
    ∃ prepared, CCL.Riemann.LegendreSeparatedWords.acquireSigned (report 1) word = .inl prepared :=
  ⟨_, rfl⟩

theorem zero_still_near (word : Word) :
    ∃ near, CCL.Riemann.LegendreSeparatedWords.acquireSigned (report 0) word = .inr near := ⟨_, rfl⟩

def negative_outputs_agree (word : Word) : CCL.OperationalEquivalence.NamedEquivalent
    (negativeWord word).single.output.name (negativeWord word).output.name :=
  (negativeWord word).equivalent_single

def negative_reversal (word : Word) : CCL.OperationalEquivalence.NamedEquivalent
    (CCL.Riemann.LegendreFractionalWords.foldAction (negativeWord word).output
      (CCL.Riemann.LegendreFractionalWords.periodBraidMatrices word.inverse)
      (negativeWord word).prepareReversal.reverse).name (input (-1)).name :=
  (negativeWord word).reversal

def negative_braid_invariance (first second : Word)
    (relation : CCL.Knot.ArtinRelations.Equivalent first second) :
    CCL.OperationalEquivalence.NamedEquivalent
      (negativeWord first).output.name (negativeWord second).output.name :=
  (negativeWord first).respects_braid (negativeWord second) relation

def original_positive_compatible {tau : CCL.ProgressiveCoherence.CoherentNamed}
    (positive : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau) (word : Word) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.LegendreSeparatedWords.acquire (Separation.ofPositive positive) word).output.name
      (CCL.Riemann.LegendreAutomaticTransport.guaranteed positive word).output.name :=
  (CCL.Riemann.LegendreSeparatedWords.acquire (Separation.ofPositive positive) word).respects_ready
    (CCL.Riemann.LegendreAutomaticTransport.guaranteed positive word)

def absoluteNegative : Separation (input (-1)) :=
  Separation.ofAbsolute (input (-1)).name.state 1 (by decide) (by
    intro value possible
    change value = (⟨0, -1⟩ : RFAP.ConstructiveGaussian.Gaussian) at possible
    subst value
    decide)

theorem constant_row_bound :
    CCL.Riemann.LegendreAutomaticPreparation.rowLower (-2) 0 absoluteNegative.gap = 4 := by decide

theorem negative_coefficient_bound :
    CCL.Riemann.LegendreAutomaticPreparation.rowLower 0 (-3) absoluteNegative.gap = 9 := by decide

theorem zero_not_separated (certificate : Separation (input 0)) : False := by
  have lower := certificate.squared_lower (value := 0) rfl
  change certificate.gap ^ 2 ≤ (0 : CCL.Riemann.LegendreAutomaticPreparation.Q) ^ 2 at lower
  rw [show (0 : CCL.Riemann.LegendreAutomaticPreparation.Q) ^ 2 = 0 by decide] at lower
  exact (not_lt_of_ge lower) (RFAP.ConstructiveFraction.pow_pos_direct certificate.positive 2)

end CCL.Riemann.LegendreSeparatedExamples
