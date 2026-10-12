module
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Normalization.Basic
public import Purelib.Approximation.Rational.Request.Common
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Approximation.Rational.Request

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Normalization.Basic
namespace LoopDomain

/-- One request target which is simultaneously below the normalization and uniform redundant-output thresholds. -/
def decisionTarget {process :
  Approximation.Gaussian.Process} (domain : Gaussian.Process.Normalization.Basic.LoopDomain process) :
    Fraction.Rational :=
  Common.commonTarget domain.normalizationTarget
    Budget.uniformRadiusSq

/-- The common normalization and redundant-output request is strictly positive. -/
theorem decisionTarget_pos {process :
  Approximation.Gaussian.Process}
    (domain : Gaussian.Process.Normalization.Basic.LoopDomain process) : 0 < domain.decisionTarget :=
  Common.commonTarget_pos domain.normalizationTarget_pos
    Budget.uniformRadiusSq_pos

/-- Refine the original process state once at the common loop-decision target. -/
def refinedState {process :
  Approximation.Gaussian.Process} (domain : Gaussian.Process.Normalization.Basic.LoopDomain process)
    (state : process.State) : process.State :=
  process.refine state domain.decisionTarget domain.decisionTarget_pos

/-- The loop-decision refinement meets the uniform redundant-output squared-radius threshold. -/
theorem refined_accurate {process :
  Approximation.Gaussian.Process} (domain : Gaussian.Process.Normalization.Basic.LoopDomain process)
    (state : process.State) :
    (process.ball (domain.refinedState state)).radiusSq <
      Budget.uniformRadiusSq :=
  (process.accurate state _ _).trans
    (Common.commonTarget_lt_right domain.normalizationTarget_pos
      Budget.uniformRadiusSq_pos)

/-- The loop-decision refinement has centre squared norm at least one. -/
theorem refined_center_normalized {process
  : Approximation.Gaussian.Process}
    (domain : Gaussian.Process.Normalization.Basic.LoopDomain process) (state : process.State) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq (process.ball (domain.refinedState state)).center := by
  apply domain.center_normalized_of_fine
  exact (process.accurate state _ _).trans
    (Common.commonTarget_lt_left domain.normalizationTarget_pos
      Budget.uniformRadiusSq_pos)

/-- Total loop decision from the semantically natural strict lower norm, without assuming normalized rational centres at
every prior state. -/
def decide {process :
  Approximation.Gaussian.Process} (domain : Gaussian.Process.Normalization.Basic.LoopDomain process)
    (state : process.State) :
    Approximation.Gaussian.Enclosure.Sector.Decision
      (process.ball (domain.refinedState state)) :=
  Decision.decide _
    (domain.refined_center_normalized state) (domain.refined_accurate state)

end LoopDomain
end Purelib.Approximation.Gaussian.Process.Normalization.Basic

end
