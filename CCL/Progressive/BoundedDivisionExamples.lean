import CCL.Progressive.BoundedDivision
import CCL.Progressive.PartialDivisionExamples

/-!
# Finite small-or-prepared regression clients

These examples exercise actual decision outcomes, including a nonzero small
input. They do not identify smallness with zero or evaluate generated period
coefficient banks.
-/

namespace CCL.ProgressiveBoundedDivisionExamples

open CCL.ProgressiveBoundedDivision

def zeroInput : CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed.exact 0
def oneInput : CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed.exact 1
def tinyValue : Gaussian := ⟨1 / 10, 0⟩
def tinyInput : CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed.exact tinyValue

theorem tiny_nonzero : tinyValue ≠ 0 := by decide

/-- Exact zero has a mathematical smallness result at every positive
threshold, rather than an exhausted numerical search. -/
theorem zero_small (threshold : Q) (positive : 0 < threshold) :
    ∃ certificate,
      (acquire (CCL.ProgressivePartialDivision.State.initial zeroInput)
        threshold positive).outcome = .inr certificate := by
  apply classify_small
  change (2 : Q) * (0 + RFAP.ConstructiveGaussian.Gaussian.normSq 0) < threshold
  simpa only [RFAP.ConstructiveGaussian.Gaussian.normSq_zero, _root_.add_zero,
    MulZeroClass.mul_zero] using positive

theorem one_prepared :
    ∃ evidence,
      (acquire (CCL.ProgressivePartialDivision.State.initial oneInput)
        1 (by decide)).outcome = .inl evidence := by
  apply classify_apart
  decide

/-- Nonzero inputs can legitimately be classified as small. -/
theorem tiny_small :
    ∃ certificate,
      (acquire (CCL.ProgressivePartialDivision.State.initial tinyInput)
        1 (by decide)).outcome = .inr certificate := by
  apply classify_small
  decide

abbrev delayed := CCL.ProgressivePartialDivisionExamples.delayedOne

theorem delayed_prepared :
    ∃ evidence,
      (acquire (CCL.ProgressivePartialDivision.State.initial delayed)
        1 (by decide)).outcome = .inl evidence := by
  apply classify_apart
  decide

theorem delayed_source_refined :
    (acquire (CCL.ProgressivePartialDivision.State.initial delayed)
      1 (by decide)).inspection.retained.source = true := rfl

theorem delayed_index_unchanged :
    (acquire (CCL.ProgressivePartialDivision.State.initial delayed)
      1 (by decide)).inspection.retained.nextIndex = 0 := rfl

/-- The requested-target route produces the ordinary certified quotient. -/
theorem delayed_division_ready (numerator : CoherentNamed) :
    ∃ result,
      (acquire (CCL.ProgressivePartialDivision.State.initial delayed)
        1 (by decide)).divide numerator = .inl result := by
  obtain ⟨evidence, equal⟩ := delayed_prepared
  unfold Report.divide
  rw [equal]
  exact ⟨_, rfl⟩

/-- The small output is actually passed through to the division caller. -/
theorem tiny_division_small (numerator : CoherentNamed) :
    ∃ certificate,
      (acquire (CCL.ProgressivePartialDivision.State.initial tinyInput)
        1 (by decide)).divide numerator = .inr certificate := by
  obtain ⟨certificate, equal⟩ := tiny_small
  unfold Report.divide
  rw [equal]
  exact ⟨_, rfl⟩

/-- The report exposes a bound for every point of its inspected ball, not
merely the narrower set of possible process readings. -/
theorem tiny_whole_ball {value : Gaussian}
    (inside : (acquire (CCL.ProgressivePartialDivision.State.initial tinyInput)
      1 (by decide)).inspection.ball.Contains value) :
    RFAP.ConstructiveGaussian.Gaussian.normSq value < 1 := by
  obtain ⟨certificate, selected⟩ := tiny_small
  exact Report.small_bound _ selected inside

/-- Compatibility uses the output actually returned by manual evidence
resumption, including when its retained source differs from the preflight. -/
theorem manual_route_compatible {numerator denominator : CoherentNamed}
    {first : CCL.ProgressivePartialDivision.State denominator}
    (result : Quotient numerator denominator first)
    (other : CCL.ProgressivePartialDivision.State denominator)
    (evidence : PossibleApart (CCL.ProgressiveCharts.based denominator.name.process other.source)) :
    ∃ output valid,
      CCL.ProgressivePartialDivision.resume numerator denominator other
        .candidateApartness evidence = .ready output valid ∧
      Nonempty (CCL.OperationalEquivalence.NamedEquivalent result.output.name output.name) := by
  obtain ⟨output, valid, equal⟩ := CCL.ProgressivePartialDivision.resume_is_ready
    numerator denominator other .candidateApartness evidence
  exact ⟨output, valid, equal, ⟨result.respects valid⟩⟩

theorem automatic_route_compatible {numerator denominator : CoherentNamed}
    {first : CCL.ProgressivePartialDivision.State denominator}
    (result : Quotient numerator denominator first)
    (other : CCL.ProgressivePartialDivision.State denominator)
    (separated : 2 * (denominator.name.process.ball other.source).radiusSq <
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (denominator.name.process.ball other.source).center) :
    ∃ output valid,
      CCL.ProgressivePartialDivision.step numerator denominator other = .ready output valid ∧
      Nonempty (CCL.OperationalEquivalence.NamedEquivalent result.output.name output.name) := by
  obtain ⟨output, valid, equal⟩ := CCL.ProgressivePartialDivision.step_is_ready_of_separated
    numerator denominator other separated
  exact ⟨output, valid, equal, ⟨result.respects valid⟩⟩

end CCL.ProgressiveBoundedDivisionExamples
