import CCL.Riemann.LegendreSignedAcquisition
import CCL.Riemann.LegendrePositivityAcquisitionExamples

/-!
# Signed acquisition regression clients

The centre-threshold equalities and a tiny positive input intentionally use
the near-boundary branch. Delayed positive discovery prepares arbitrary
finite words in both evaluator interfaces without supplied preparations.
-/

namespace CCL.Riemann.LegendreSignedAcquisitionExamples

open CCL.Riemann.LegendreSignedAcquisition

def input (height : Q) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact ⟨0, height⟩

def report (height : Q) :=
  acquire (input height) (CCL.Riemann.LegendrePositivityAcquisition.initial (input height))
    1 (by decide)

theorem positive_case : (report 1).2.tag = 1 := by decide
theorem negative_case : (report (-1)).2.tag = 2 := by decide
theorem zero_case : (report 0).2.tag = 0 := by decide
theorem upper_threshold_case : (report (1 / 2)).2.tag = 0 := by decide
theorem lower_threshold_case : (report (-(1 / 2))).2.tag = 0 := by decide
theorem tiny_positive_case : (report (1 / 10)).2.tag = 0 := by decide

abbrev delayed := CCL.Riemann.LegendrePositivityAcquisitionExamples.delayed

def delayedReport := acquire delayed (CCL.Riemann.LegendrePositivityAcquisition.initial delayed)
  1 (by decide)

theorem delayed_positive : delayedReport.2.tag = 1 := by decide

theorem delayed_refined : delayedReport.retained.retained.source = true := rfl

theorem delayed_index_unchanged : delayedReport.retained.retained.nextIndex = 0 := rfl

theorem delayed_transport_ready (word : Word) :
    ∃ result, delayedReport.transport word = .ready result := ⟨_, rfl⟩

theorem delayed_fold_ready (word : Word) :
    ∃ result, delayedReport.fold word = .ready result := ⟨_, rfl⟩

theorem negative_transport_evidence (word : Word) :
    ∃ certificate, (report (-1)).transport word = .negative certificate := ⟨_, rfl⟩

theorem zero_transport_near (word : Word) :
    ∃ certificate, (report 0).transport word = .near certificate := ⟨_, rfl⟩

end CCL.Riemann.LegendreSignedAcquisitionExamples
