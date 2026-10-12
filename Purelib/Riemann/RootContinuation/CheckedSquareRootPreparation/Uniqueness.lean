module

public import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.RootIsolation.Newton.Search.Execution.Uniqueness

/-! A fixed initial proposal cursor determines its complete retained warm-up.
Together with the original finite search, this determines the full runtime
failure report without reacquiring any proposal or accepted candidate. -/

public section

namespace Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation

namespace ProposalExecution

/-- The initial proposal budget bounds the retained warm-up steps. -/
theorem length_le {polynomial : GaussianPolynomial} {box : Box} {radius : Coordinate}
    {remaining : Nat} {center seed : Gaussian} {steps : List ProposalStep}
    (execution : ProposalExecution polynomial box radius remaining center steps seed) :
    steps.length ≤ remaining := by
  induction execution with
  | done => exact Nat.le_refl 0
  | stationary => exact Nat.succ_le_succ (Nat.zero_le _)
  | updated _ _ _ _ _ induction => exact Nat.succ_le_succ induction

/-- The same initial proposal cursor determines both its numerical history and final seed. -/
theorem unique {polynomial : GaussianPolynomial} {box : Box} {radius : Coordinate}
    {remaining : Nat} {center firstSeed lastSeed : Gaussian} {firstSteps lastSteps : List ProposalStep}
    (first : ProposalExecution polynomial box radius remaining center firstSteps firstSeed)
    (last : ProposalExecution polynomial box radius remaining center lastSteps lastSeed) :
    firstSteps = lastSteps ∧ firstSeed = lastSeed := by
  induction first generalizing lastSteps lastSeed with
  | done => cases last; exact ⟨rfl, rfl⟩
  | @stationary remaining center derivative derivativeEq zero =>
    cases last with
    | @stationary _ _ derivativeRight derivativeRightEq _ =>
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      cases derivativeSame
      exact ⟨rfl, rfl⟩
    | @updated _ _ derivativeRight _ _ _ _ derivativeRightEq nonzero _ _ _ =>
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.trans zero))
  | @updated remaining center derivative newton rounded steps seed derivativeEq nonzero newtonEq roundedEq
      tail induction =>
    cases last with
    | @stationary _ _ derivativeRight derivativeRightEq zero =>
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.symm.trans zero))
    | @updated _ _ derivativeRight newtonRight roundedRight stepsRight seedRight derivativeRightEq _ newtonRightEq
        roundedRightEq tailRight =>
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      cases derivativeSame
      have newtonSame := newtonRightEq.trans newtonEq.symm
      cases newtonSame
      have roundedSame := roundedRightEq.trans roundedEq.symm
      cases roundedSame
      obtain ⟨stepsSame, seedSame⟩ := induction tailRight
      cases stepsSame
      exact ⟨rfl, seedSame⟩

end ProposalExecution

/-- Two certified initial proposal traces at the same cursor retain exactly the same seed and steps. -/
theorem ProposalTrace.unique {polynomial : GaussianPolynomial} {box : Box} {radius : Coordinate}
    {remaining : Nat} {center : Gaussian} (first last : ProposalTrace polynomial box radius remaining center) :
    first = last := by
  cases first with
  | mk firstSeed firstSteps firstExecution firstSeedEq =>
    cases last with
    | mk lastSeed lastSteps lastExecution lastSeedEq =>
      obtain ⟨stepsSame, seedSame⟩ := firstExecution.unique lastExecution
      cases stepsSame
      cases seedSame
      rfl

/-- The original finite request determines its retained warm-up, search history and first failure uniquely. -/
theorem Failure.unique {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (diameter : Coordinate) (first last : Failure segment parameter owner diameter) : first = last := by
  cases first with
  | mk firstWarmup firstSteps firstExecution firstReason =>
    cases last with
    | mk lastWarmup lastSteps lastExecution lastReason =>
      have warmupSame := ProposalTrace.unique firstWarmup lastWarmup
      cases warmupSame
      have stepsSame := firstExecution.steps_unique lastExecution
      cases stepsSame
      have reasonSame := FailureReason.unique segment parameter owner diameter firstReason lastReason
      cases reasonSame
      rfl

end Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
