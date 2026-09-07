import CCL.Riemann.SquareRootSidecar
import CCL.Progressive.ExactProvenanceExamples

/-!
# Algebraic provenance regressions

Cover the repeated-zero root, both independently isolated sheets of `Z² - 2`,
retained winding ownership, approximate nonzero candidates on an operationally
zero channel, coefficient-derived observation bounds, and compatibility with
ordinary/manual division. Tests use the proved isolation interface without
kernel-recomputing a large root-isolation trace.
-/

namespace CCL.Riemann.SquareRootSidecarExamples

open CCL.Riemann.SquareRootProvenance
open CCL.ProgressiveExactProvenance (Gaussian CoherentNamed)

def two : Gaussian := ⟨2, 0⟩

theorem two_nonzero : two ≠ 0 := by decide

def rootTwo (sheet : Fin 2) := isolated two sheet

theorem rootTwo_parameter (sheet : Fin 2) : (rootTwo sheet).2.parameter = two :=
  isolated_parameter two sheet

theorem rootTwo_prepared (sheet : Fin 2) :
    ∃ preparation, (rootTwo sheet).2.decide = .prepared preparation := by
  have nonzero : (rootTwo sheet).2.parameter ≠ 0 := by
    rw [rootTwo_parameter]
    exact two_nonzero
  exact ⟨_, decide_prepared (rootTwo sheet).2.square nonzero⟩

theorem rootTwo_retains_owner (sheet : Fin 2) :
    ∃ owner, (rootTwo sheet).2.owner = some owner := by
  unfold rootTwo isolated
  rw [dif_pos two_nonzero]
  exact ⟨_, rfl⟩

theorem rootTwo_not_small (sheet : Fin 2)
    (observation : Observation (rootTwo sheet).1 (rootTwo sheet).2.parameter) :
    ¬ RFAP.ConstructiveGaussian.Gaussian.normSq observation.value <
      separationGap (rootTwo sheet).2.parameter := by
  intro small
  have zero := observation.parameter_zero_of_small small
  rw [rootTwo_parameter] at zero
  exact two_nonzero zero

theorem zero_excluded :
    zeroSidecar.decide = .excluded (zero_of_square zeroSidecar.square) :=
  decide_excluded zeroSidecar.square

theorem zero_has_no_simple_owner : zeroSidecar.owner = none := rfl

theorem isolated_zero (sheet : Fin 2) :
    (isolated 0 sheet).1 = CCL.ProgressiveCoherence.CoherentNamed.exact 0 := by
  unfold isolated
  rw [dif_neg (not_not_intro rfl)]

theorem zero_observation_small :
    RFAP.ConstructiveGaussian.Gaussian.normSq zeroSidecar.observe.value <
      separationGap zeroSidecar.parameter :=
  zeroSidecar.observe.small_of_parameter_zero rfl

def cancellationSidecar :
    Sidecar CCL.ProgressiveExactProvenanceExamples.cancellation :=
  zeroSidecar.transport
    CCL.ProgressiveExactProvenanceExamples.cancellationSidecar.equivalent

/-- A genuine nonzero finite candidate does not invalidate a proved zero
identity. No pointwise candidate zero law is smuggled into the sidecar. -/
theorem cancellation_has_nonzero_candidate :
    CCL.ProgressiveExactProvenanceExamples.cancellation.name.process.Possible
      CCL.ProgressiveExactProvenanceExamples.cancellation.name.state (1 : Gaussian) :=
  CCL.ProgressiveExactProvenanceExamples.cancellation_has_nonzero_candidate

theorem cancellation_square_excluded :
    ∃ identity, cancellationSidecar.decide = .excluded identity :=
  ⟨_, decide_excluded cancellationSidecar.square⟩

def cancellation_observation_zero : CCL.ProgressiveExactProvenance.ZeroIdentity
    CCL.ProgressiveExactProvenanceExamples.cancellation :=
  cancellationSidecar.observe.zero_of_small cancellationSidecar.square
    (cancellationSidecar.observe.small_of_parameter_zero rfl)

theorem cancellation_square_all_budgets (numerator : CoherentNamed)
    (state : CCL.ProgressivePartialDivision.State
      CCL.ProgressiveExactProvenanceExamples.cancellation) (fuel : Nat) :
    ∃ final reachable, CCL.ProgressivePartialDivision.attempt numerator
      CCL.ProgressiveExactProvenanceExamples.cancellation state fuel = .exhausted final reachable :=
  cancellation_observation_zero.attempt_exhausts numerator state fuel

def preparation_agrees_with_ready {channel numerator : CoherentNamed}
    (sidecar : Sidecar channel) (nonzero : sidecar.parameter ≠ 0)
    {state : CCL.ProgressivePartialDivision.State channel} {output : CoherentNamed}
    (ready : CCL.ProgressivePartialDivision.Ready numerator channel state output) :
    CCL.OperationalEquivalence.NamedEquivalent
      ((prepared_of_square sidecar.square nonzero).quotient numerator).name output.name :=
  (prepared_of_square sidecar.square nonzero).quotient_respects_ready ready

theorem forgetting_preserves_prefix (sheet : Fin 2) :
    (WithSidecar.forget ⟨(rootTwo sheet).1, some (rootTwo sheet).2⟩).channel.name.machine.emitted =
      (rootTwo sheet).1.name.machine.emitted := rfl

end CCL.Riemann.SquareRootSidecarExamples
