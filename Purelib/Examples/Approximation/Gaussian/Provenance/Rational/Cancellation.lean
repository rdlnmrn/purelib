module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Division.Obstruction.Symbolic
public import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
public import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Sequence

public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Name.Basic
import Mathlib.Data.Nat.Basic

@[expose] public section

/-!
# Exact provenance regression clients

The cancellation example has a nonzero possible finite reading at its
initial state. Its symbolic identity to zero nonetheless rules out every
division preparation, demonstrating why candidate equality and operational
identity must not be conflated.
-/

namespace Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Examples
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Division

/-- The Gaussian sample zero at index zero and one thereafter. -/
def switchingSample : Nat →
  Basic.Canonical
  | 0 => 0
  | _ + 1 => 1

/-- Squared radius one initially and zero at every positive index. -/
def switchingRadius : Nat →
  Fraction.Rational
  | 0 => 1
  | _ + 1 => 0

/-- Certified approximation that becomes exactly one after its first sample.

Retains the original natural-number index, one-step refinement, geometric closeness proof and unit center bound. -/
def switchingApproximation :
  Sequence.ApproximationData where
  sample := switchingSample
  radiusSq := switchingRadius
  radiusSq_nonneg := by
    intro index
    cases index <;> dsimp only [switchingRadius] <;> decide
  later_close := by
    intro earlier later order
    cases earlier with
    | zero =>
      cases later <;> dsimp only [switchingSample,
        switchingRadius] <;> decide
    | succ earlier =>
        cases later with
        | zero => exact (Nat.not_succ_le_zero earlier order).elim
        | succ later =>
            dsimp only [switchingSample,
              switchingRadius]
            decide
  refineIndex current _ _ := current + 1
  refineIndex_ge current _ _ := Nat.le_succ current
  refineIndex_accurate _ _ positive := positive
  centerBound := 1
  centerBound_nonneg := by decide
  sample_bounded := by
    intro index
    cases index <;> dsimp only [switchingSample] <;> decide

/-- The coherent name induced by the switching approximation. -/
def switchingInput :
  CoherentNamed :=
  CoherentNamed.ofApproximation switchingApproximation

/-- The original switching name added to its own negation. -/
def cancellation :
  CoherentNamed := CoherentNamed.add
  switchingInput
  (CoherentNamed.neg switchingInput)

/-- Exact rational provenance certifying cancellation of the switching input.

Retains the original arithmetic channel while recording its exact additive-inverse identity. -/
def cancellationSidecar :
  RationalSidecar cancellation :=
  RationalSidecar.addNeg
  switchingInput

/-- The initial cancellation process admits one as a possible value.

The two retained arithmetic operands may use different finite sample witnesses even though their exact provenance
cancels. -/
theorem
  cancellation_has_nonzero_candidate :
    cancellation.name.process.Possible
      cancellation.name.state (1 : Basic.Canonical) := by
  exact ⟨1, 0, ⟨1, by decide, rfl⟩, ⟨0, ⟨0, le_rfl, rfl⟩, by decide⟩, by decide⟩

/-- Initial possible values do not certify all candidates as zero. -/
theorem cancellation_not_zero_candidates
  :
    ¬ Zero.ZeroCandidates cancellation
      (Refinement.State.initial
          cancellation) := by
  intro zero
  exact (by decide : (1 : Basic.Canonical) ≠ 0) (zero
    cancellation_has_nonzero_candidate)

/-- The retained rational provenance excludes cancellation as a denominator. -/
theorem cancellation_excluded :
    ∃ identity, cancellationSidecar.decide = .excluded identity
      := ⟨_, rfl⟩

/-- Every finite numerical division attempt against cancellation exhausts.

Retains the actual final state and reachability witness at any supplied denominator state, using the original symbolic
obstruction. -/
theorem cancellation_all_budgets
  (numerator : CoherentNamed)
    (state : Refinement.State
        cancellation) (fuel : Nat) :
    ∃ final reachable, Partial.Run.attempt numerator
      cancellation state fuel =
      .exhausted final reachable :=
  Obstruction.Symbolic.addNeg_excludes_every_budget
    switchingInput numerator state fuel

/-- Exact rational provenance prepares the Gaussian value one. -/
theorem rational_nonzero_prepared :
    ∃ prepared, (RationalSidecar.exact (1 : Basic.Canonical)).decide = .prepared prepared :=
      ⟨_, rfl⟩

/-- Adding exact provenance for one and negative one excludes the sum. -/
theorem rational_sum_excluded :
    ∃ identity, ((RationalSidecar.exact (1 : Basic.Canonical)).add
      (RationalSidecar.exact (-1))).decide = .excluded identity := ⟨_, rfl⟩

/-- Multiplying exact provenance for one and negative one prepares the product. -/
theorem rational_product_prepared :
    ∃ prepared, ((RationalSidecar.exact (1 : Basic.Canonical)).mul
      (RationalSidecar.exact (-1))).decide = .prepared prepared := ⟨_, rfl⟩

/-- The original cancellation name paired with its retained rational provenance. -/
def withSidecar :
  Provenance.Rational.Basic.WithRationalSidecar :=
  ⟨cancellation, some
  cancellationSidecar⟩

end Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation

end
