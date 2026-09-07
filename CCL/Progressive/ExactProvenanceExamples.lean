import CCL.Progressive.ExactProvenanceLaws

/-!
# Exact provenance regression clients

The cancellation example has a nonzero possible finite reading at its
initial state. Its symbolic identity to zero nonetheless rules out every
division preparation, demonstrating why candidate equality and operational
identity must not be conflated.
-/

namespace CCL.ProgressiveExactProvenanceExamples

open CCL.ProgressiveExactProvenance

def switchingSample : Nat → Gaussian
  | 0 => 0
  | _ + 1 => 1

def switchingRadius : Nat → Q
  | 0 => 1
  | _ + 1 => 0

def switchingApproximation : CCL.ProgressiveApproximation.Approximation where
  sample := switchingSample
  radiusSq := switchingRadius
  radiusSq_nonneg := by
    intro index
    cases index <;> dsimp only [switchingRadius] <;> decide
  later_close := by
    intro earlier later order
    cases earlier with
    | zero => cases later <;> dsimp only [switchingSample, switchingRadius] <;> decide
    | succ earlier =>
        cases later with
        | zero => exact (Nat.not_succ_le_zero earlier order).elim
        | succ later =>
            dsimp only [switchingSample, switchingRadius]
            decide
  refineIndex current _ _ := current + 1
  refineIndex_ge current _ _ := Nat.le_succ current
  refineIndex_accurate _ _ positive := positive
  centerBound := 1
  centerBound_nonneg := by decide
  sample_bounded := by
    intro index
    cases index <;> dsimp only [switchingSample] <;> decide

def switchingInput : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation switchingApproximation

def cancellation : CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed.add switchingInput
  (CCL.ProgressiveCoherence.CoherentNamed.neg switchingInput)

def cancellationSidecar : RationalSidecar cancellation := RationalSidecar.addNeg switchingInput

theorem cancellation_has_nonzero_candidate :
    cancellation.name.process.Possible cancellation.name.state (1 : Gaussian) := by
  exact ⟨1, 0, ⟨1, by decide, rfl⟩, ⟨0, ⟨0, le_rfl, rfl⟩, by decide⟩, by decide⟩

theorem cancellation_not_zero_candidates :
    ¬ CCL.ProgressiveDivisionObstructions.ZeroCandidates cancellation
      (CCL.ProgressivePartialDivision.State.initial cancellation) := by
  intro zero
  exact (by decide : (1 : Gaussian) ≠ 0) (zero cancellation_has_nonzero_candidate)

theorem cancellation_excluded :
    ∃ identity, cancellationSidecar.decide = .excluded identity := ⟨_, rfl⟩

theorem cancellation_all_budgets (numerator : CoherentNamed)
    (state : State cancellation) (fuel : Nat) :
    ∃ final reachable, CCL.ProgressivePartialDivision.attempt numerator cancellation state fuel =
      .exhausted final reachable :=
  addNeg_excludes_every_budget switchingInput numerator state fuel

theorem rational_nonzero_prepared :
    ∃ prepared, (RationalSidecar.exact (1 : Gaussian)).decide = .prepared prepared := ⟨_, rfl⟩

theorem rational_sum_excluded :
    ∃ identity, ((RationalSidecar.exact (1 : Gaussian)).add
      (RationalSidecar.exact (-1))).decide = .excluded identity := ⟨_, rfl⟩

theorem rational_product_prepared :
    ∃ prepared, ((RationalSidecar.exact (1 : Gaussian)).mul
      (RationalSidecar.exact (-1))).decide = .prepared prepared := ⟨_, rfl⟩

def withSidecar : WithRationalSidecar := ⟨cancellation, some cancellationSidecar⟩

theorem forgetting_preserves_prefix :
    withSidecar.forget.channel.name.machine.emitted = withSidecar.channel.name.machine.emitted := rfl

end CCL.ProgressiveExactProvenanceExamples
