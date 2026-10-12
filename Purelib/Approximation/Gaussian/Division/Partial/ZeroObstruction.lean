module
import Purelib.Approximation.Gaussian.Division.Partial.Ready
public import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Division.Partial.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero

section
@[expose] public section

/-!
# Persistent exact-zero obstructions to division

This is extra finite input evidence, not an automatic interpretation of an
unsuccessful numerical test. The invariant is scoped to the retained source
and candidates with provenance back to it. A later numerical ball need not
have radius zero for the obstruction to remain valid.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial.ZeroObstruction

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical
namespace ZeroCandidates

/-- Exact-zero candidate evidence excludes a ready quotient at every finitely reachable refinement state. -/
theorem no_ready {numerator
  denominator : Coherent.CoherentNamed} {first last : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (zero : Zero.ZeroCandidates denominator first) (path : State.Reachable first last)
    {output : Coherent.CoherentNamed} (ready : Approximation.Gaussian.Division.Partial.Ready numerator denominator last
        output) : False :=
  ZeroCandidates.incompatible (ZeroCandidates.reachable zero path) ready.evidence

/-- Every finite automatic run exhausts with a genuine reachability witness. It never returns a quotient from this
exact-zero refinement branch. -/
theorem attempt_exhausts
  {denominator : Coherent.CoherentNamed} (numerator : Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) (zero : Zero.ZeroCandidates denominator
        state) (fuel : Nat) :
    ∃ final reachable,
      Run.attempt numerator denominator state fuel = .exhausted final reachable := by
  induction fuel generalizing state with
  | zero => exact ⟨state, .refl state, rfl⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨final, path, exhausted⟩ := inductionHypothesis state.advance zero.advance
      exact ⟨final, .tail (.refined state) path,
        Run.attempt_succ_eq_exhausted_of_step_progressed numerator denominator state state.advance
          final fuel (.refined state) path
          (Step.step_eq_progressed_of_not_separated numerator denominator state zero.not_separated)
          exhausted⟩
end ZeroCandidates

end Purelib.Approximation.Gaussian.Division.Partial.ZeroObstruction

end
