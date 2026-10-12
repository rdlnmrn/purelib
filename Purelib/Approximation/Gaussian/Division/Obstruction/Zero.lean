module
import Purelib.Approximation.Gaussian.Division.Partial.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Division.Partial.Ready
public import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Division.Partial.Step
public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (State)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

section
@[expose] public section

/-!
# Exact provenance and operational zero obstructions

Exact identities concern finite observation protocols, not equality of every
approximate candidate. One explicit comparison at an apartness lower bound
refutes an identity to zero. Rational provenance then gives exact division
decisions while leaving the original numerical channel unchanged.
-/

namespace Purelib.Approximation.Gaussian.Division.Obstruction.Zero
namespace ZeroIdentity

/-- The contradiction uses one finite request at the supplied positive apartness bound, not a completed value or an
equality decision on readings. -/
theorem incompatible_apart {channel :
  Coherent.CoherentNamed} (zero : Zero.ZeroIdentity channel)
    (apart : Named.Apart channel.name) : False := by
  let comparison := zero.compare 0 0 apart.certificate.lowerSq apart.certificate.positive
  have close := comparison.close (Nat.le_refl comparison.leftIndex)
    (Nat.le_refl comparison.rightIndex)
  change Data.Gaussian.Norm.Basic.normSq ((Sampling.approximation channel.name).sample
    comparison.leftIndex - 0) < apart.certificate.lowerSq at close
  rw [Data.Gaussian.Basic.sub_zero] at close
  exact (not_lt_of_ge (Apart.Sampling.sampled_lower channel apart
    comparison.leftIndex)) close

/-- An operational zero identity contradicts any equivalent prepared apart denominator presentation. -/
theorem incompatible_prepared {channel :
  Coherent.CoherentNamed} (zero : Zero.ZeroIdentity channel)
    (prepared : Approximation.Gaussian.Division.Prepared channel) : False :=
  incompatible_apart
    (NamedEquivalent.trans
      (NamedEquivalent.symm prepared.equivalent) zero)
    prepared.apart

/-- This operational obstruction applies even at independently rebased states; the existing based/apartified equivalence
is the required bridge. -/
theorem no_evidence {channel :
  Coherent.CoherentNamed} (zero : Zero.ZeroIdentity channel)
    (state : State channel)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based channel.name.process state.source)) : False :=
  incompatible_prepared zero
    { denominator := Preparation.preparedDenominator state evidence
      apart := Preparation.preparedApart state evidence
      equivalent := Equivalence.preparedDenominatorEquivalent state evidence }

/-- An operational zero denominator admits no ready quotient at any retained refinement state. -/
theorem no_ready {numerator channel :
  Coherent.CoherentNamed} (zero : Zero.ZeroIdentity channel)
    {state : State channel} {output : Coherent.CoherentNamed}
    (ready : Approximation.Gaussian.Division.Partial.Ready numerator channel state output) : False :=
  no_evidence zero state ready.evidence

/-- An operational zero identity prevents every retained source from passing the sufficient center-separation test. -/
theorem not_separated {channel :
  Coherent.CoherentNamed} (zero : Zero.ZeroIdentity channel)
    (state : State channel) :
    ¬ 2 * (channel.name.process.ball state.source).radiusSq <
      Data.Gaussian.Norm.Basic.normSq (channel.name.process.ball state.source).center :=
  fun separated => no_evidence zero state
    (Preparation.evidenceOfSeparation state separated)

/-- Every finite division run with an operationally zero denominator exhausts while retaining a final state and its
reachability certificate. -/
theorem attempt_exhausts {channel :
  Coherent.CoherentNamed} (zero : Zero.ZeroIdentity channel)
    (numerator : Coherent.CoherentNamed) (state : State channel) (fuel :
        Nat) :
    ∃ final reachable, Run.attempt numerator channel state fuel =
      .exhausted final reachable := by
  induction fuel generalizing state with
  | zero => exact ⟨state, .refl state, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨final, path, exhausted⟩ := inductionHypothesis state.advance
      exact ⟨final, .tail (.refined state) path,
        Run.attempt_succ_eq_exhausted_of_step_progressed
          numerator channel state state.advance final fuel (.refined state) path
          (Step.step_eq_progressed_of_not_separated
            numerator channel state (not_separated zero
              state)) exhausted⟩

end ZeroIdentity
end Purelib.Approximation.Gaussian.Division.Obstruction.Zero

end
