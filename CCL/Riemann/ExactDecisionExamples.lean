import CCL.Riemann.SquareRootDecisionLaws
import CCL.Riemann.SquareRootSidecarExamples

namespace CCL.Riemann.ExactDecisionExamples

open CCL.ProgressiveExactProvenance

theorem cancellation_complete :
    IsZero CCL.ProgressiveExactProvenanceExamples.cancellation ↔
      ¬ IsPrepared CCL.ProgressiveExactProvenanceExamples.cancellation :=
  CCL.Riemann.SquareRootSidecarExamples.cancellationSidecar.zero_iff_unpreparable

theorem cancellation_cross_provenance :
    CCL.Riemann.SquareRootSidecarExamples.cancellationSidecar.decide.isPrepared =
      CCL.ProgressiveExactProvenanceExamples.cancellationSidecar.decide.isPrepared :=
  CCL.Riemann.SquareRootSidecarExamples.cancellationSidecar.decide_respects_rational
    CCL.ProgressiveExactProvenanceExamples.cancellationSidecar
    (CCL.OperationalEquivalence.NamedEquivalent.refl _)

def alternateOne : CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed.add
  (CCL.ProgressiveCoherence.CoherentNamed.exact 1) (CCL.ProgressiveCoherence.CoherentNamed.exact 0)

def alternateSidecar : RationalSidecar alternateOne :=
  (RationalSidecar.exact 1).add (RationalSidecar.exact 0)

def alternate_equivalent : NamedEquivalent alternateOne.name
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name :=
  CCL.OperationalFieldLaws.coherentAdd_zero_right _

theorem alternate_verdict :
    alternateSidecar.decide.isPrepared = (RationalSidecar.exact 1).decide.isPrepared :=
  alternateSidecar.decide_respects (RationalSidecar.exact 1) alternate_equivalent

def exactOnePrepared : Prepared (CCL.ProgressiveCoherence.CoherentNamed.exact 1) :=
  ⟨CCL.ProgressiveCoherence.CoherentNamed.exact 1, exactApart 1 (by decide),
    CCL.OperationalEquivalence.NamedEquivalent.refl _⟩

def alternatePrepared : Prepared alternateOne := exactOnePrepared.transport
  (CCL.OperationalEquivalence.NamedEquivalent.symm alternate_equivalent)

def alternate_quotient (numerator : CoherentNamed) : NamedEquivalent
    (alternatePrepared.quotient numerator).name (exactOnePrepared.quotient numerator).name :=
  alternatePrepared.quotient_respects_equivalent exactOnePrepared alternate_equivalent
    (CCL.OperationalEquivalence.NamedEquivalent.refl _)

theorem root_two_complete (sheet : Fin 2) :
    IsPrepared (CCL.Riemann.SquareRootSidecarExamples.rootTwo sheet).1 ↔
      ¬ IsZero (CCL.Riemann.SquareRootSidecarExamples.rootTwo sheet).1 :=
  (CCL.Riemann.SquareRootSidecarExamples.rootTwo sheet).2.prepared_iff_nonzero

end CCL.Riemann.ExactDecisionExamples
