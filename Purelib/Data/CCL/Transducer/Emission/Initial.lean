module
public import Purelib.Data.CCL.Transducer.Emission.Preparation
import Purelib.Approximation.Gaussian.Process.Observation.Operations
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
public import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
public import Purelib.Data.CCL.Transducer.Emission.Low.Preparation
import Purelib.Data.CCL.Transducer.Mode.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

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

namespace Purelib.Data.CCL.Transducer.Emission.Initial

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Process.Based
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- The exact original initial norm decision, retaining its same cached ball and selected high-sector decision. -/
inductive Selection (ball : Ball) where
  /-- The original strict low-norm branch. -/ | low (small : Norm.Basic.normSq ball.center < 1)
  /-- The original high branch and exact unary or selected-sector decision. -/ | high (decision : Sector.Decision ball)

namespace Selection

/-- Select the original initial branch once from the same retained numerical ball. -/
@[expose] def decide (ball : Ball) (small : ball.radiusSq < Sector.Budget.uniformRadiusSq) : Selection ball :=
  if normalized : 1 ≤ Norm.Basic.normSq ball.center then
    .high (Sector.Decision.decide ball normalized small)
  else .low (lt_of_not_ge normalized)

/-- Construct the original nonempty emission from its retained initial branch and observation.

The selected sector, exact original process state, lower quadrance and loop
weight are unchanged. Bounds consume the same cached ball; no source ball,
witness or refinement function is called by this constructor.
-/
@[expose] def emission (current : Mode.Basic.InitialState) (base : current.process.State)
    (observation : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Budget.initialRadiusSq) :
    Selection observation.ball → Emission
  | .low small =>
      { bits := [false, true]
        nonempty := by decide
        next := .low (Low.Preparation.nextLowState current.process base accurate
          (observation.ballEq ▸ small) 1) }
  | .high (.unary certificate) =>
      let original : Sector.Large.UnaryBall (current.process.ball base) := observation.ballEq ▸ certificate
      { bits := [true]
        nonempty := by decide
        next := .loop
          { kind := .initialHigh
            count := 1
            process := Process.Gamma.Downscale.unaryScaledProcess current.process base
            state := Process.Gamma.Downscale.unaryScaledInitial current.process base
            domain := Process.Gamma.Downscale.unaryScaledLoopDomain.ofObservation
              current.process base observation original } }
  | .high (.sector sector certificate) =>
      { bits := false :: false :: sector.code
        nonempty := by intro empty; cases empty
        next := .residual (Mode.Basic.ResidualState.ofObservation current.process base sector observation certificate) }

/-- Reuse the same initial observation to construct the emitted mode's exact original observation. -/
@[expose] def observation (current : Mode.Basic.InitialState) (base : current.process.State)
    (observed : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Budget.initialRadiusSq) :
    (selected : Selection observed.ball) → Mode.Observation (selected.emission current base observed accurate).next
  | .low _ =>
      Process.Observation.mul (Process.Observation.exact (Power.natPow Basic.Canonical.gamma 1))
        (Process.Observation.based base (BasedState.initial current.process base) observed)
  | .high (.unary _) =>
      Process.Observation.mul (Process.Observation.exact Basic.Canonical.gamma⁻¹)
        (Process.Observation.based base (BasedState.initial current.process base) observed)
  | .high (.sector sector _) =>
      Process.Observation.translate
        (Process.Observation.based base (BasedState.initial current.process base) observed) sector.rep

/-- Retain the exact original source route through the same selected initial chart. -/
@[expose] def route {source : Process} (current : Mode.Basic.InitialState)
    (earlier : Process.Route source current.process) (base : current.process.State)
    (observed : Process.Observation current.process base)
    (accurate : (current.process.ball base).radiusSq < Budget.initialRadiusSq) :
    (selected : Selection observed.ball) →
      Process.Route source (selected.emission current base observed accurate).next.process
  | .low _ => .upscale earlier base 1
  | .high (.unary _) => .downscale earlier base
  | .high (.sector sector _) => .residual earlier base sector

end Selection

/-- Construct the initial emission from its exact retained original refinement.

The receipt supplies the complete state and cached observation for the original
initial request. Selection and next-chart construction make no further source
calls; the earlier receipt's payment remains separate.
-/
@[expose] public def fromRefinement {source : Process} (current : Mode.Basic.InitialState)
    (route : Process.Route source current.process)
    (receipt : Process.Route.Refinement route current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos) :
    Emission.Prepared source :=
  have accurate : (current.process.ball receipt.state).radiusSq < Budget.initialRadiusSq :=
    receipt.stateEq.symm ▸ current.process.accurate current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos
  have fine := receipt.observation.ballEq.symm ▸ accurate
  let selected := Selection.decide receipt.observation.ball (fine.trans Budget.initialRadiusSq_lt_uniform)
  let emission := selected.emission current receipt.state receipt.observation accurate
  ⟨emission, selected.route current route receipt.state receipt.observation accurate,
    selected.observation current receipt.state receipt.observation accurate, 0⟩

/-- Prepare the original initial emission and include its actual source-refinement payment. -/
@[expose] public def prepare {source : Process} (current : Mode.Basic.InitialState)
    (route : Process.Route source current.process) : Emission.Prepared source :=
  let receipt := route.refine current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos
  let prepared := fromRefinement current route receipt
  { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls }

/-- A retained refinement preserves the complete original initial preparation and separates its earlier payment. -/
public theorem prepare_eq_fromRefinement {source : Process} (current : Mode.Basic.InitialState)
    (route : Process.Route source current.process)
    (receipt : Process.Route.Refinement route current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos) :
    prepare current route =
      let prepared := fromRefinement current route receipt
      { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls } := by
  cases Process.Route.Refinement.unique receipt
    (route.refine current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos)
  rfl

/-- Emit the original exact initial chunk, retaining its actual preparation for shared source execution. -/
@[expose] public def initialStep (current : Mode.Basic.InitialState) : Emission :=
  (prepare current (.input : Process.Route current.process current.process)).emission

/-- Any retained original source route produces the same complete original initial emission. -/
public theorem prepare_emission_eq {source : Process} (current : Mode.Basic.InitialState)
    (route : Process.Route source current.process) : (prepare current route).emission = initialStep current := by
  let base := current.process.refine current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos
  have accurate : (current.process.ball base).radiusSq < Budget.initialRadiusSq :=
    current.process.accurate current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos
  change
    (let observed := route.observe base
     let selected := Selection.decide observed.ball
       ((observed.ballEq.symm ▸ accurate).trans Budget.initialRadiusSq_lt_uniform)
     selected.emission current base observed accurate) =
    (let observed := Process.Observation.build current.process base
     let selected := Selection.decide observed.ball
       ((observed.ballEq.symm ▸ accurate).trans Budget.initialRadiusSq_lt_uniform)
     selected.emission current base observed accurate)
  exact congrArg (fun observed : Process.Observation current.process base =>
    let selected := Selection.decide observed.ball
      ((observed.ballEq.symm ▸ accurate).trans Budget.initialRadiusSq_lt_uniform)
    selected.emission current base observed accurate) (Process.Observation.unique _ _)

/-- The initial emission pays one original supplied-source refinement, ball read and witness read. -/
public theorem prepare_sourceCalls {source : Process} (current : Mode.Basic.InitialState)
    (route : Process.Route source current.process) : (prepare current route).sourceCalls = 3 :=
  (route.refine current.state Budget.initialRadiusSq Budget.initialRadiusSq_pos).sourceCalls_eq

/-- Read back the exact original initial branch equation, including its original complete next mode.

The same strict low decision and high unary-or-sector decision retain their
original refined source, numerical bounds and dependent process state.
-/
public theorem initialStep_eq (current : Mode.Basic.InitialState) : initialStep current = (
    by
      let base := Emission.Initial.Preparation.initialRefinedState current.process current.state
      have accurate := Emission.Initial.Preparation.initialRefined_accurate current.process current.state
      have uniform := Emission.Initial.Preparation.initialRefined_uniform current.process current.state
      by_cases normalized : 1 ≤ Gaussian.Norm.Basic.normSq (current.process.ball base).center
      · match Enclosure.Sector.Decision.decide
            (current.process.ball base) normalized uniform with
        | .unary certificate =>
            let nextProcess := Process.Gamma.Downscale.unaryScaledProcess current.process base
            let nextState := Process.Gamma.Downscale.unaryScaledInitial current.process base
            let nextDomain := Process.Gamma.Downscale.unaryScaledLoopDomain current.process base
              certificate
            exact
              { bits := [true]
                nonempty := by decide
                next := .loop
                  { kind := .initialHigh
                    count := 1
                    process := nextProcess
                    state := nextState
                    domain := nextDomain } }
        | .sector sector certificate =>
            let nextProcess := Process.Sector.Residual.residualProcess current.process base sector
            let nextState := Process.Sector.Residual.residualInitial current.process base sector
            let upper := Process.Sector.Residual.safeResidualUpper sector (current.process.ball base)
            exact
              { bits := false :: false :: sector.code
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
      · have centerSmall : Gaussian.Norm.Basic.normSq (current.process.ball base).center < 1 :=
          lt_of_not_ge normalized
        exact
          { bits := [false, true]
            nonempty := by decide
            next := .low (Emission.Low.Preparation.nextLowState current.process base accurate
              centerSmall 1) }) := by
  let base := Preparation.initialRefinedState current.process current.state
  have accurate := Preparation.initialRefined_accurate current.process current.state
  have uniform := Preparation.initialRefined_uniform current.process current.state
  change Selection.emission current base (Process.Observation.build current.process base) accurate
    (Selection.decide (current.process.ball base) uniform) = _
  unfold Selection.decide
  split
  · rename_i normalized
    rewrite [dif_pos normalized]
    cases Enclosure.Sector.Decision.decide (current.process.ball base) normalized uniform with
    | unary certificate => rfl
    | sector sector certificate => rfl
  · rename_i normalized
    rewrite [dif_neg normalized]
    rfl

end Purelib.Data.CCL.Transducer.Emission.Initial
