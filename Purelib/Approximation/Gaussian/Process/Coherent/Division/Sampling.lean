module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Division
public import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Approximation.Rational.Request.Common
import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Process.Coherence.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Request.Basic

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Core operational congruence for finite sampled quotients

Division is only continuous after a positive denominator lower bound has been
displayed.  This core file packages that constructive fact for the canonical
finite samplers of coherent CCL names.  It does not select completed values:
every quotient below is a quotient of two Gaussian rationals computed at one
finite index.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherent.Division.Sampling

/-! ## The actual stateful division process -/

/-- A sufficiently small positive quotient refinement request makes both retained operand coherence allowances smaller
than the displayed target.

The outer request bound uses the original process center bounds and the denominator's uniform apartness certificate. -/
private theorem
  quotient_refine_component_allowance_lt
    {numeratorProcess denominatorProcess : Process}
    (numeratorCoherent : Coherent numeratorProcess)
    (denominatorCoherent : Coherent denominatorProcess)
    (apart : Apart denominatorProcess)
    (state : numeratorProcess.State × denominatorProcess.State)
    (request : Fraction.Rational) (requestPositive : 0 < request)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (requestSmall : request <
      Coherent.divisionOuterTarget
        numeratorProcess denominatorProcess apart.lowerSq
        (Coherent.commonRequest
          (numeratorCoherent.accuracyRequest target)
          (denominatorCoherent.accuracyRequest target))) :
    let refined := (numeratorProcess.div denominatorProcess apart).refine
      state request requestPositive
    numeratorCoherent.allowance refined.1 < target ∧
      denominatorCoherent.allowance refined.2 < target := by
  let numeratorRequest := numeratorCoherent.accuracyRequest target
  let denominatorRequest := denominatorCoherent.accuracyRequest target
  have numeratorRequestPositive : 0 < numeratorRequest :=
    numeratorCoherent.accuracyRequest_pos targetPositive
  have denominatorRequestPositive : 0 < denominatorRequest :=
    denominatorCoherent.accuracyRequest_pos targetPositive
  let sharedRequest := Coherent.commonRequest
    numeratorRequest denominatorRequest
  let numeratorName := Name.centerOnly
    (numeratorProcess.ball state.1).center numeratorProcess.centerBound
      numeratorProcess.centerBound_nonneg
        (numeratorProcess.center_bounded state.1)
  let denominatorName := Name.centerOnly
    (denominatorProcess.ball state.2).center denominatorProcess.centerBound
      denominatorProcess.centerBound_nonneg
        (denominatorProcess.center_bounded state.2)
  let inputRequest := Name.divisionInputTarget
    numeratorName denominatorName apart.lowerSq request
  have inputPositive : 0 < inputRequest :=
    Name.divisionInputTarget_pos
      numeratorName denominatorName apart.lowerSq apart.positive
        requestPositive
  have inputLtShared : inputRequest < sharedRequest :=
    Coherent.processDivisionInputTarget_lt
      numeratorName denominatorName rfl rfl apart.positive requestSmall
  have inputLtNumerator : inputRequest < numeratorRequest :=
    inputLtShared.trans
      (Coherent.commonRequest_lt_left
        numeratorRequestPositive denominatorRequestPositive)
  have inputLtDenominator : inputRequest < denominatorRequest :=
    inputLtShared.trans
      (Coherent.commonRequest_lt_right
        numeratorRequestPositive denominatorRequestPositive)
  change
    numeratorCoherent.allowance
        (numeratorProcess.refine state.1 inputRequest inputPositive) < target ∧
      denominatorCoherent.allowance
        (denominatorProcess.refine state.2 inputRequest inputPositive) < target
  exact
    ⟨numeratorCoherent.refine_accurate state.1 target targetPositive
        inputRequest inputPositive inputLtNumerator,
      denominatorCoherent.refine_accurate state.2 target targetPositive
        inputRequest inputPositive inputLtDenominator⟩

/-- At a canonical quotient sample index whose request satisfies the retained outer bound, both operand coherence
allowances lie below the positive target. -/
public theorem
  quotient_stateAt_component_allowance_lt
    {numeratorProcess denominatorProcess : Process}
    (numeratorCoherent : Coherent numeratorProcess)
    (denominatorCoherent : Coherent denominatorProcess)
    (apart : Apart denominatorProcess)
    (start : numeratorProcess.State × denominatorProcess.State)
    (index : Nat) (target : Fraction.Rational) (targetPositive : 0 < target)
    (requestSmall : Sampling.refinementTarget index <
      Coherent.divisionOuterTarget
        numeratorProcess denominatorProcess apart.lowerSq
        (Coherent.commonRequest
          (numeratorCoherent.accuracyRequest target)
          (denominatorCoherent.accuracyRequest target))) :
    let state := Sampling.stateAt
      (numeratorProcess.div denominatorProcess apart) start index
    numeratorCoherent.allowance state.1 < target ∧
      denominatorCoherent.allowance state.2 < target := by
  cases index with
  | zero =>
      exact quotient_refine_component_allowance_lt
        numeratorCoherent
        denominatorCoherent apart start _ _ target targetPositive requestSmall
  | succ index =>
      exact quotient_refine_component_allowance_lt
        numeratorCoherent
        denominatorCoherent apart
          (Sampling.stateAt
            (numeratorProcess.div denominatorProcess apart) start index)
          _ _ target targetPositive requestSmall

end Purelib.Approximation.Gaussian.Process.Coherent.Division.Sampling

end
