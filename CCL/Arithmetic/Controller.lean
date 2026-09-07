import CCL.Progressive.Enclosures
import CCL.Arithmetic.RedundantOutput
import CCL.Arithmetic.ResidualDecision

/-!
# Finite arithmetic output decisions

This module joins progressive finite enclosures to the two overlapping CCL
decisions.  A normalized loop process can always refine once to the uniform
`1/480` squared-error threshold and then emit either a sound unary digit or a
sound redundant sector.  A residual process can always refine once to the
requested padding threshold and then return either a sound small-residual
certificate or positive apartness for affine inversion.

Both constructions are ordinary finite function calls.  In particular, the
residual construction does not ask whether the represented result is exactly
zero.  Repeating it at successively smaller finite padding targets is the
constructive non-return route for an opaque exact rational result.
-/

namespace CCL.ArithmeticController

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev Process := CCL.ProgressiveEnclosures.Process

open RFAP.ConstructiveGaussian.Gaussian

/-- A progressive process already in a loop chart.  The centre lower bound is
finite state data, normally obtained from radial scaling or the strict margin
of the preceding safe inversion. -/
structure LoopProcess where
  process : Process
  center_normalized : ∀ (state : process.State),
    1 ≤ normSq (process.ball state).center

namespace LoopProcess

/-- The one finite refinement used for a redundant output decision. -/
def refinedState (loop : LoopProcess) (state : loop.process.State) :
    loop.process.State :=
  loop.process.refine state
    CCL.RedundantOutput.uniformRadiusSq
    CCL.RedundantOutput.uniformRadiusSq_pos

theorem refined_persists (loop : LoopProcess) (state : loop.process.State)
    {value : Gaussian}
    (possible : loop.process.Possible (loop.refinedState state) value) :
    loop.process.Possible state value :=
  loop.process.refine_persists state _ _ possible

theorem refined_accurate (loop : LoopProcess) (state : loop.process.State) :
    (loop.process.ball (loop.refinedState state)).radiusSq <
      CCL.RedundantOutput.uniformRadiusSq :=
  loop.process.accurate state _ _

/-- Total bounded unary-or-sector decision at one normalized loop state. -/
def decide (loop : LoopProcess) (state : loop.process.State) :
    CCL.RedundantOutput.Decision
      (loop.process.ball (loop.refinedState state)) :=
  CCL.RedundantOutput.decide _
    (loop.center_normalized (loop.refinedState state))
    (loop.refined_accurate state)

/-- The unary outcome is sound for every finite possibility at the refined
state. -/
theorem unary_sound (loop : LoopProcess) (state : loop.process.State)
    (certificate : CCL.RedundantOutput.UnaryBall
      (loop.process.ball (loop.refinedState state)))
    {value : Gaussian}
    (possible : loop.process.Possible (loop.refinedState state) value) :
    2 < normSq value :=
  CCL.RedundantOutput.normSq_gt_two_of_contains certificate
    (loop.process.possible_inside possible)

/-- The sector outcome is sound for every finite possibility at the refined
state. -/
theorem sector_sound (loop : LoopProcess) (state : loop.process.State)
    (sector : CCL.Sectors.Sector)
    (certificate : CCL.RedundantOutput.SafeBall sector
      (loop.process.ball (loop.refinedState state)))
    {value : Gaussian}
    (possible : loop.process.Possible (loop.refinedState state) value) :
    CCL.RedundantSectors.Safe sector value :=
  CCL.RedundantOutput.safe_of_contains certificate
    (loop.process.possible_inside possible)

end LoopProcess

/-! ## Residual padding or inversion -/

/-- The finite state requested to decide whether `count` unary padding bits
are safe or whether positive residual apartness is already visible. -/
def residualState (process : Process) (state : process.State) (count : Nat) :
    process.State :=
  let target := CCL.ResidualDecision.paddingTarget count
  process.refine state (target / 6)
    (RFAP.ConstructiveFraction.div_pos_direct
      (CCL.ResidualDecision.paddingTarget_pos count) (by decide))

theorem residual_accurate (process : Process) (state : process.State)
    (count : Nat) :
    (process.ball (residualState process state count)).radiusSq <
      CCL.ResidualDecision.paddingTarget count / 6 :=
  process.accurate state _ _

/-- Total finite small-or-apart decision for the requested padding length. -/
def decideResidual (process : Process) (state : process.State) (count : Nat) :
    CCL.ResidualDecision.Decision
      (process.ball (residualState process state count))
      (CCL.ResidualDecision.paddingTarget count) :=
  CCL.ResidualDecision.decide _ _
    (CCL.ResidualDecision.paddingTarget_pos count)
    (residual_accurate process state count)

theorem residual_persists (process : Process) (state : process.State)
    (count : Nat) {value : Gaussian}
    (possible : process.Possible (residualState process state count) value) :
    process.Possible state value :=
  process.refine_persists state _ _ possible

/-- A small outcome justifies the requested finite residual bound for every
remaining possibility. -/
theorem residual_small_sound (process : Process) (state : process.State)
    (count : Nat)
    (certificate : CCL.ResidualDecision.SmallBall
      (process.ball (residualState process state count))
      (CCL.ResidualDecision.paddingTarget count))
    {value : Gaussian}
    (possible : process.Possible (residualState process state count) value) :
    normSq value < CCL.ResidualDecision.paddingTarget count :=
  CCL.ResidualDecision.normSq_lt_of_contains certificate
    (process.possible_inside possible)

/-- The alternative outcome supplies exactly the positive finite sidecar
needed by affine inversion. -/
theorem residual_apart_sound (process : Process) (state : process.State)
    (count : Nat)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (process.ball (residualState process state count)))
    {value : Gaussian}
    (possible : process.Possible (residualState process state count) value) :
    certificate.lowerSq ≤ normSq value :=
  certificate.lower (process.possible_inside possible)

/-- The small branch directly yields the projective loop-tail witness for
each finite possibility, including exact zero without an equality oracle in
the controller. -/
def loopTailOfResidualSmall (process : Process) (state : process.State)
    (count : Nat)
    (certificate : CCL.ResidualDecision.SmallBall
      (process.ball (residualState process state count))
      (CCL.ResidualDecision.paddingTarget count))
    (value : Gaussian)
    (possible : process.Possible (residualState process state count) value) :
    CCL.TerminalPadding.LoopTail count :=
  CCL.ResidualDecision.loopTailOfSmall certificate value
    (process.possible_inside possible)

end CCL.ArithmeticController
