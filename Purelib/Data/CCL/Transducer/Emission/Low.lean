module
public import Purelib.Data.CCL.Transducer.Emission.Preparation
import Purelib.Approximation.Gaussian.Process.Observation.Operations
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
public import Purelib.Data.CCL.Transducer.Emission.Low.Preparation
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

public section

namespace Purelib.Data.CCL.Transducer.Emission.Low

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Process.Based
open Purelib.Data.CCL.Transducer
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- The original low-state unary or selected-sector decision over its same cached ball. -/
inductive Selection (ball : Ball) where
  /-- The original strict small-center branch. -/ | low (small : Norm.Basic.normSq ball.center < 1)
  /-- The exact original selected sector and its whole-ball safety certificate. -/ | sector
      (sector : Sector) (certificate : Sector.Safe.SafeBall sector ball)

namespace Selection

/-- Select the original low-state branch once using the retained refined ball and its certified norm band. -/
@[expose] def decide (ball : Ball) (upper : Norm.Basic.normSq ball.center < 13 / 6)
    (small : ball.radiusSq < Sector.Budget.uniformRadiusSq) : Selection ball :=
  if normalized : 1 ≤ Norm.Basic.normSq ball.center then
    .sector (Sector.select ball.center) (Sector.Safe.safeBall_of_extendedBand ⟨normalized, upper.le⟩ small)
  else .low (lt_of_not_ge normalized)

/-- Construct the original low-state emission from its exact retained branch and source observation.

The selected sector keeps the original residual process and dependent base.
The unary branch keeps the original gamma-upscaled state and successor count.
Both branches consume the cached ball without another source observation.
-/
@[expose] def emission (current : Mode.Basic.LowState) (base : current.process.State)
    (observation : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Initial.Budget.initialRadiusSq) :
    Selection observation.ball → Emission
  | .low small =>
      { bits := [true]
        nonempty := by decide
        next := .low (Preparation.nextLowState current.process base accurate
          (observation.ballEq ▸ small) (current.count + 1)) }
  | .sector chosen certificate =>
      { bits := false :: chosen.code
        nonempty := by intro empty; cases empty
        next := .residual (Mode.Basic.ResidualState.ofObservation current.process base chosen observation certificate) }

/-- Reuse the original refined observation for the exact next low or residual mode. -/
@[expose] def observation (current : Mode.Basic.LowState) (base : current.process.State)
    (observed : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Initial.Budget.initialRadiusSq) :
    (selected : Selection observed.ball) → Mode.Observation (selected.emission current base observed accurate).next
  | .low _ =>
      Process.Observation.mul (Process.Observation.exact (Power.natPow Basic.Canonical.gamma 1))
        (Process.Observation.based base (BasedState.initial current.process base) observed)
  | .sector chosen _ =>
      Process.Observation.translate
        (Process.Observation.based base (BasedState.initial current.process base) observed) chosen.rep

/-- Retain the same supplied source through the selected original low-state chart. -/
@[expose] def route {source : Process} (current : Mode.Basic.LowState)
    (earlier : Process.Route source current.process) (base : current.process.State)
    (observed : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Initial.Budget.initialRadiusSq) :
    (selected : Selection observed.ball) →
      Process.Route source (selected.emission current base observed accurate).next.process
  | .low _ => .upscale earlier base 1
  | .sector chosen _ => .residual earlier base chosen

end Selection

/-- Construct the original low emission from its retained initial-radius refinement.

The same cached state and observation determine the original norm decision,
next chart and bounds. Construction makes no further source calls; the earlier
refinement receipt retains its own payment.
-/
@[expose] def fromRefinement {source : Process} (current : Mode.Basic.LowState)
    (route : Process.Route source current.process)
    (receipt : Process.Route.Refinement route current.state Initial.Budget.initialRadiusSq
      Initial.Budget.initialRadiusSq_pos) : Emission.Prepared source :=
  have accurate : (current.process.ball receipt.state).radiusSq < Initial.Budget.initialRadiusSq :=
    receipt.stateEq.symm ▸ current.process.accurate current.state
      Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  have upper : Norm.Basic.normSq (current.process.ball receipt.state).center < 13 / 6 :=
    receipt.stateEq.symm ▸ Preparation.low_center_lt_extended_upper current
  have fine := receipt.observation.ballEq.symm ▸ accurate
  have cachedUpper := receipt.observation.ballEq.symm ▸ upper
  let selected := Selection.decide receipt.observation.ball cachedUpper
    (fine.trans Initial.Budget.initialRadiusSq_lt_uniform)
  let emission := selected.emission current receipt.state receipt.observation accurate
  ⟨emission, selected.route current route receipt.state receipt.observation accurate,
    selected.observation current receipt.state receipt.observation accurate, 0⟩

/-- Prepare the original low emission and include its actual source-refinement payment. -/
@[expose] def prepare {source : Process} (current : Mode.Basic.LowState)
    (route : Process.Route source current.process) : Emission.Prepared source :=
  let receipt := route.refine current.state Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos
  let prepared := fromRefinement current route receipt
  { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls }

/-- A retained refinement preserves the complete original low preparation and separates its earlier payment. -/
theorem prepare_eq_fromRefinement {source : Process} (current : Mode.Basic.LowState)
    (route : Process.Route source current.process)
    (receipt : Process.Route.Refinement route current.state Initial.Budget.initialRadiusSq
      Initial.Budget.initialRadiusSq_pos) :
    prepare current route =
      let prepared := fromRefinement current route receipt
      { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls } := by
  cases Process.Route.Refinement.unique receipt
    (route.refine current.state Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos)
  rfl

/-- Emit the exact original low-normalization chunk by projecting its retained preparation. -/
@[expose] def lowStep (current : Mode.Basic.LowState) : Emission :=
  (prepare current (.input : Process.Route current.process current.process)).emission

/-- The cached low preparation has the complete original branch result and original dependent next states. -/
theorem lowStep_eq (current : Mode.Basic.LowState) : lowStep current = (by
    let base := Initial.Preparation.initialRefinedState current.process current.state
    have accurate := Initial.Preparation.initialRefined_accurate current.process current.state
    have uniform := Initial.Preparation.initialRefined_uniform current.process current.state
    have centerUpper := Preparation.low_center_lt_extended_upper current
    by_cases normalized : 1 ≤ Norm.Basic.normSq (current.process.ball base).center
    · let sector := Sector.select
        (current.process.ball base).center
      have certificate : Sector.Safe.SafeBall sector
          (current.process.ball base) :=
        Sector.Safe.safeBall_of_extendedBand
          ⟨normalized, centerUpper.le⟩ uniform
      let nextProcess := Process.Sector.Residual.residualProcess current.process base sector
      let nextState := Process.Sector.Residual.residualInitial current.process base sector
      let upper := Process.Sector.Residual.safeResidualUpper sector (current.process.ball base)
      exact
        { bits := false :: sector.code
          nonempty := by
            intro empty
            cases empty
          next := .residual
            { process := nextProcess
              state := nextState
              count := 0
              upper := upper
              upperBound := by
                intro value possible
                exact Process.Sector.Residual.translated_based_norm_le_safeResidualUpper
                  current.process base sector certificate possible
              upperStrict := Process.Sector.Residual.safeResidualUpper_lt_half certificate } }
    · have centerSmall : Norm.Basic.normSq (current.process.ball base).center < 1 :=
        lt_of_not_ge normalized
      exact
        { bits := [true]
          nonempty := by decide
          next := .low (Preparation.nextLowState current.process base accurate
            centerSmall (current.count + 1)) }
) := by
  unfold lowStep prepare fromRefinement Initial.Preparation.initialRefinedState
  dsimp only [Process.Route.refine, Process.Route.Refinement.ofState, Process.Route.observe,
    Process.Route.observeFrom, Process.Route.sourceState,
    Process.Observation.build,
    Process.Observation.ofReadings]
  unfold Selection.decide
  split <;> rfl

/-- Every retained route yields the same complete original low-state emission. -/
theorem prepare_emission_eq {source : Process} (current : Mode.Basic.LowState)
    (route : Process.Route source current.process) : (prepare current route).emission = lowStep current := by
  let base := Initial.Preparation.initialRefinedState current.process current.state
  have accurate := Initial.Preparation.initialRefined_accurate current.process current.state
  have upper := Preparation.low_center_lt_extended_upper current
  change
    (let observed := route.observe base
     let selected := Selection.decide observed.ball (observed.ballEq.symm ▸ upper)
       ((observed.ballEq.symm ▸ accurate).trans Initial.Budget.initialRadiusSq_lt_uniform)
     selected.emission current base observed accurate) =
    (let observed := Process.Observation.build current.process base
     let selected := Selection.decide observed.ball (observed.ballEq.symm ▸ upper)
       ((observed.ballEq.symm ▸ accurate).trans Initial.Budget.initialRadiusSq_lt_uniform)
     selected.emission current base observed accurate)
  exact congrArg (fun observed : Process.Observation current.process base =>
    let selected := Selection.decide observed.ball (observed.ballEq.symm ▸ upper)
      ((observed.ballEq.symm ▸ accurate).trans Initial.Budget.initialRadiusSq_lt_uniform)
    selected.emission current base observed accurate) (Process.Observation.unique _ _)

/-- A low-state emission pays exactly one original supplied-source refinement, ball read and witness read. -/
theorem prepare_sourceCalls {source : Process} (current : Mode.Basic.LowState)
    (route : Process.Route source current.process) : (prepare current route).sourceCalls = 3 :=
  (route.refine current.state Initial.Budget.initialRadiusSq Initial.Budget.initialRadiusSq_pos).sourceCalls_eq

end Purelib.Data.CCL.Transducer.Emission.Low
