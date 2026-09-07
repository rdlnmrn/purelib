import CCL.Progressive.DivisionObstructions

/-!
# Zero obstruction with permanently positive enclosure radii

Every finite candidate is exactly zero, but no displayed ball has radius
zero. The symbolic invariant, not a zero-width numerical observation,
certifies that every finite division attempt remains unready.
-/

namespace CCL.ProgressiveDivisionObstructionsExamples

open CCL.ProgressivePartialDivision
open CCL.ProgressiveDivisionObstructions

abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Q := RFAP.ConstructiveFraction.Rational

def radius (index : Nat) : Q := CCL.FiniteGeometric.quarterRadius 1 index

theorem radius_positive (index : Nat) : 0 < radius index :=
  CCL.FiniteGeometric.quarterRadius_pos (by decide) index

def paddedZeroProcess : Process where
  State := Nat
  ball index :=
    { center := 0
      radiusSq := radius index
      radiusSq_nonneg := (radius_positive index).le }
  Possible _ value := value = 0
  witness _ := ⟨0, rfl⟩
  possible_inside := by
    intro index value equal
    subst value
    change RFAP.ConstructiveGaussian.Gaussian.normSq (0 - 0) ≤ radius index
    simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_self,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero] using (radius_positive index).le
  refine index target _ := CCL.FiniteGeometric.firstQuarterBelow 1 index target
  refine_persists := by intro index target positive value possible; exact possible
  accurate index target positive :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide) index target positive
  centerBound := 0
  centerBound_nonneg := le_rfl
  center_bounded := by
    intro index
    change RFAP.ConstructiveGaussian.Gaussian.normSq (0 : Gaussian) ≤ (0 : Q)
    decide

def paddedZeroCoherent : CCL.ProgressiveCoherence.Coherent paddedZeroProcess where
  allowance := radius
  allowance_nonneg index := (radius_positive index).le
  ball_radius_le _ := le_rfl
  possible_close := by
    intro left right leftValue rightValue leftZero rightZero
    subst leftValue
    subst rightValue
    change RFAP.ConstructiveGaussian.Gaussian.normSq (0 - 0) ≤
      4 * (radius left + radius right)
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (radius_positive left).le (radius_positive right).le)
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro index target positive request requestPositive small
    exact (CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide) index
      request requestPositive).trans small

def paddedZero : CoherentNamed where
  name := { process := paddedZeroProcess, state := (0 : Nat) }
  coherent := paddedZeroCoherent

theorem zero_candidates (state : State paddedZero) : ZeroCandidates paddedZero state :=
  fun possible => possible

theorem balls_never_exact (state : State paddedZero) :
    0 < (paddedZero.name.process.ball state.source).radiusSq := radius_positive state.source

theorem all_budgets_exhaust (numerator : CoherentNamed) (state : State paddedZero) (fuel : Nat) :
    ∃ final reachable, attempt numerator paddedZero state fuel = .exhausted final reachable :=
  ZeroCandidates.attempt_exhausts numerator state (zero_candidates state) fuel

theorem requested_preserves_zero (state : State paddedZero) (target : Q) (positive : 0 < target) :
    ZeroCandidates paddedZero
      (CCL.ProgressiveBoundedDivision.request state target positive).retained :=
  ZeroCandidates.requested (zero_candidates state) _

end CCL.ProgressiveDivisionObstructionsExamples
