module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
public import Purelib.Approximation.Gaussian.Process.Bounds
public import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
public import Purelib.Data.CCL.Encoding.Padding.Process
public import Purelib.Data.CCL.Transducer.Emission.Loop
import Purelib.Data.CCL.Transducer.Mode.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.List.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Data.Rat.Fraction.Order.Basic

public section

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

namespace Purelib.Data.CCL.Transducer.Emission.Residual

open Purelib.Approximation.Gaussian.Process.Gamma

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian

/-- Construct the original normalized-inverse loop state from its actual retained residual refinement.

The original inverse preparation performs its own apartness refinement once.
The returned mode retains that exact state, original count and upper bound.
-/
@[expose] def apartLoopState (current : Mode.Basic.ResidualState) (base : current.process.State)
    (persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value)
    (certificate : Enclosure.Ball.Apart (current.process.ball base)) : Mode.Basic.LoopState :=
  { kind := .loop
    count := current.count
    process := Inverse.Scale.normalizedInverseProcess current.process base certificate current.count
    state := Inverse.Scale.normalizedInverseInitial current.process base certificate current.count
    domain := Inverse.Scale.normalizedInverseLoopDomain current.process base certificate
      current.count current.upper (fun possible => current.upperBound (persists possible)) current.upperStrict }

/-- Reconstruct the original inverse loop state using its already returned setup refinement.

The supplied source state is bound to the original apartness target. The same
inverse process, padding count and loop domain are retained without repeating
that setup refinement or observing its source.
-/
def apartLoopStateOfRefinement (current : Mode.Basic.ResidualState) (base : current.process.State)
    (persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value)
    (certificate : Enclosure.Ball.Apart (current.process.ball base))
    (retained : { state : current.process.State // state = current.process.refine base
      ((Process.Apart.Based.possibleApartOfBall current.process base certificate).lowerSq / 12)
      (Process.Apart.Based.possibleApartOfBall current.process base certificate).twelfth_pos }) :
    { state : Mode.Basic.LoopState // state = apartLoopState current base persists certificate } :=
  let prepared := Inverse.Scale.normalizedInverseInitialOfRefinement
    current.process base certificate current.count retained
  let assemble (state : (Inverse.Scale.normalizedInverseProcess
      current.process base certificate current.count).State) : Mode.Basic.LoopState :=
    { kind := .loop
      count := current.count
      process := Inverse.Scale.normalizedInverseProcess current.process base certificate current.count
      state := state
      domain := Inverse.Scale.normalizedInverseLoopDomain current.process base certificate
        current.count current.upper (fun possible => current.upperBound (persists possible)) current.upperStrict }
  ⟨assemble prepared.val, congrArg assemble prepared.property⟩

/-- Read the exact original inverse state based at the successor padding refinement. -/
@[expose] def residualApartLoopState (current : Mode.Basic.ResidualState)
    (certificate : Enclosure.Ball.Apart
      (current.process.ball (Padding.Process.residualState current.process current.state (current.count + 1)))) :
    Mode.Basic.LoopState :=
  apartLoopState current (Padding.Process.residualState current.process current.state (current.count + 1))
    (fun possible => current.process.refine_persists current.state _ _ possible) certificate

namespace Selection

/-- Prepare the original residual decision using its exact retained source observation.

A small residual retains the same source state and cached observation. An
apart residual prepares its original inverse state and its actual loop chunk
once; the additional inverse-state refinement is included in its payment.
-/
@[expose] def prepare {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process) (base : current.process.State)
    (observed : Process.Observation current.process base)
    (persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value) :
    Enclosure.Residual.Decision observed.ball (Padding.Residual.paddingTarget (current.count + 1)) →
      Emission.Prepared source
  | .small certificate =>
      let original : Enclosure.Residual.SmallBall (current.process.ball base)
          (Padding.Residual.paddingTarget (current.count + 1)) := observed.ballEq ▸ certificate
      let upperEq := congrArg Enclosure.Ball.Bounds.smallUpper observed.ballEq
      let emission : Emission :=
        { bits := [true]
          nonempty := by decide
          next := .residual
            { process := current.process
              state := base
              count := current.count + 1
              upper := Enclosure.Ball.Bounds.smallUpper observed.ball
              upperBound := by
                intro value possible
                exact upperEq.symm ▸ Process.Bounds.smallUpper_bound original possible
              upperStrict := certificate } }
      ⟨emission, route, observed, 0⟩
  | .apart certificate =>
      let original : Enclosure.Ball.Apart (current.process.ball base) := observed.ballEq ▸ certificate
      let next := apartLoopState current base persists original
      let nested := Loop.prepare next (.inverse route base original current.count)
      ⟨nested.emission, nested.route, nested.observation, route.calls + nested.sourceCalls⟩

/-- Read back the original complete emission of a retained residual selection. -/
theorem prepare_emission_eq {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process) (base : current.process.State)
    (observed : Process.Observation current.process base)
    (persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value)
    (selected : Enclosure.Residual.Decision observed.ball (Padding.Residual.paddingTarget (current.count + 1))) :
    (prepare current route base observed persists selected).emission =
      match selected with
      | .small certificate =>
          { bits := [true]
            nonempty := by decide
            next := .residual
              { process := current.process
                state := base
                count := current.count + 1
                upper := Enclosure.Ball.Bounds.smallUpper observed.ball
                upperBound := by
                  intro value possible
                  exact (congrArg Enclosure.Ball.Bounds.smallUpper observed.ballEq).symm ▸
                    Process.Bounds.smallUpper_bound (observed.ballEq ▸ certificate) possible
                upperStrict := certificate } }
      | .apart certificate => Loop.loopStep (apartLoopState current base persists (observed.ballEq ▸ certificate)) := by
  cases selected with
  | small certificate => rfl
  | apart certificate => exact Loop.prepare_emission_eq _ _

/-- The paid work after selection is zero for padding and one setup refinement plus three loop calls for inversion. -/
theorem prepare_sourceCalls {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process) (base : current.process.State)
    (observed : Process.Observation current.process base)
    (persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value)
    (selected : Enclosure.Residual.Decision observed.ball (Padding.Residual.paddingTarget (current.count + 1))) :
    (prepare current route base observed persists selected).sourceCalls =
      match selected with | .small _ => 0 | .apart _ => 4 := by
  cases selected with
  | small certificate => rfl
  | apart certificate =>
      change route.calls + (Loop.prepare _ _).sourceCalls = 4
      rewrite [route.calls_eq_one, Loop.prepare_sourceCalls]
      rfl

end Selection

/-- Select the original residual branch using the same retained observation and positive padding request. -/
@[expose] def selectionOfRefinement {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process)
    (requestPositive : 0 < Padding.Residual.paddingTarget (current.count + 1) / 6)
    (receipt : Process.Route.Refinement route current.state
      (Padding.Residual.paddingTarget (current.count + 1) / 6) requestPositive) :
    Enclosure.Residual.Decision receipt.observation.ball (Padding.Residual.paddingTarget (current.count + 1)) :=
  let target := Padding.Residual.paddingTarget (current.count + 1)
  have targetPositive := Padding.Residual.paddingTarget_pos (current.count + 1)
  have fine : (current.process.ball receipt.state).radiusSq < target / 6 :=
    receipt.stateEq.symm ▸ current.process.accurate current.state (target / 6) requestPositive
  Enclosure.Residual.decide receipt.observation.ball target targetPositive
    (receipt.observation.ballEq.symm ▸ fine)

/-- Construct the original small-or-apart emission from its exact retained residual refinement.

The original padding target, half-open decision and inverse count are
unchanged. Padding needs no further source calls. The apart branch still
performs its original inverse-state setup and loop preparation; their payment
is retained separately from the supplied residual refinement.
-/
@[expose] def fromRefinement {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process)
    (requestPositive : 0 < Padding.Residual.paddingTarget (current.count + 1) / 6)
    (receipt : Process.Route.Refinement route current.state
      (Padding.Residual.paddingTarget (current.count + 1) / 6) requestPositive) : Emission.Prepared source :=
  let target := Padding.Residual.paddingTarget (current.count + 1)
  let selected := selectionOfRefinement current route requestPositive receipt
  have persists : ∀ {value}, current.process.Possible receipt.state value →
      current.process.Possible current.state value :=
    fun possible => current.process.refine_persists current.state (target / 6) requestPositive
      (receipt.stateEq ▸ possible)
  Selection.prepare current route receipt.state receipt.observation persists selected

/-- Prepare the original residual emission and include the same residual-refinement payment. -/
@[expose] def prepare {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process) : Emission.Prepared source :=
  let target := Padding.Residual.paddingTarget (current.count + 1)
  have requestPositive := Rat.Fraction.Order.Field.div_pos_direct
    (Padding.Residual.paddingTarget_pos (current.count + 1))
    (show (0 : Rat.Fraction.Rational) < 6 by decide)
  let receipt := route.refine current.state (target / 6) requestPositive
  let prepared := fromRefinement current route requestPositive receipt
  { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls }

/-- A retained refinement preserves the complete original residual preparation and separates its earlier payment. -/
theorem prepare_eq_fromRefinement {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process)
    (requestPositive : 0 < Padding.Residual.paddingTarget (current.count + 1) / 6)
    (receipt : Process.Route.Refinement route current.state
      (Padding.Residual.paddingTarget (current.count + 1) / 6) requestPositive) :
    prepare current route =
      let prepared := fromRefinement current route requestPositive receipt
      { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls } := by
  cases Process.Route.Refinement.unique receipt
    (route.refine current.state (Padding.Residual.paddingTarget (current.count + 1) / 6) requestPositive)
  rfl

/-- Emit the original residual chunk from its actual input-route preparation. -/
@[expose] def residualStep (current : Mode.Basic.ResidualState) : Emission :=
  (prepare current (.input : Process.Route current.process current.process)).emission

/-- Read back the exact original residual decision and its complete retained next mode.

The successor request is unchanged. Padding retains that original source
refinement; inversion uses the exact original inverse chart and count.
-/
theorem residualStep_eq (current : Mode.Basic.ResidualState) : residualStep current = (
    by
      let requestedCount := current.count + 1
      let refined := Padding.Process.residualState
        current.process current.state requestedCount
      match Padding.Process.decideResidual
          current.process current.state requestedCount with
      | .small certificate =>
          exact
            { bits := [true]
              nonempty := by decide
              next := .residual
                { process := current.process
                  state := refined
                  count := requestedCount
                  upper := Enclosure.Ball.Bounds.smallUpper (current.process.ball refined)
                  upperBound := fun possible =>
                    Process.Bounds.smallUpper_bound certificate possible
                  upperStrict := certificate } }
      | .apart certificate =>
          exact Emission.Loop.loopStep (residualApartLoopState current certificate)) := by
  change (Selection.prepare current (.input : Process.Route current.process current.process)
    (Padding.Process.residualState current.process current.state (current.count + 1))
    (Process.Observation.build current.process
      (Padding.Process.residualState current.process current.state (current.count + 1)))
    (fun possible => current.process.refine_persists current.state _ _ possible)
    (Padding.Process.decideResidual current.process current.state (current.count + 1))).emission = _
  rewrite [Selection.prepare_emission_eq]
  dsimp only
  cases Padding.Process.decideResidual current.process current.state (current.count + 1) with
  | small certificate => rfl
  | apart certificate => rfl

/-- Every retained original source route prepares the same complete original residual emission. -/
theorem prepare_emission_eq {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process) : (prepare current route).emission = residualStep current := by
  let base := Padding.Process.residualState current.process current.state (current.count + 1)
  let target := Padding.Residual.paddingTarget (current.count + 1)
  have positive := Padding.Residual.paddingTarget_pos (current.count + 1)
  have fine := Padding.Process.residual_accurate current.process current.state (current.count + 1)
  have persists : ∀ {value}, current.process.Possible base value → current.process.Possible current.state value :=
    fun possible => current.process.refine_persists current.state _ _ possible
  let observed := Process.Observation.build current.process base
  let selected := Enclosure.Residual.decide observed.ball target positive (observed.ballEq.symm ▸ fine)
  change (Selection.prepare current route base (route.observe base) persists
    (Enclosure.Residual.decide (route.observe base).ball target positive
      ((route.observe base).ballEq.symm ▸ fine))).emission =
      (Selection.prepare current (.input : Process.Route current.process current.process) base observed persists
        selected).emission
  calc
    _ = (Selection.prepare current route base observed persists selected).emission :=
      congrArg (fun value : Process.Observation current.process base =>
        (Selection.prepare current route base value persists
          (Enclosure.Residual.decide value.ball target positive (value.ballEq.symm ▸ fine))).emission)
        (Process.Observation.unique _ _)
    _ = _ := by rewrite [Selection.prepare_emission_eq, Selection.prepare_emission_eq]; rfl

/-- The actual residual preparation pays three calls for padding or seven calls for the original inverse transition.

The retained small-or-apart decision determines the payment. The inverse
case includes its extra original apart-state refinement and actual loop work.
-/
theorem prepare_sourceCalls {source : Process} (current : Mode.Basic.ResidualState)
    (route : Process.Route source current.process) :
    (prepare current route).sourceCalls = 3 ∨ (prepare current route).sourceCalls = 7 := by
  unfold prepare fromRefinement
  dsimp only
  rewrite [Process.Route.Refinement.sourceCalls_eq, Selection.prepare_sourceCalls]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end Purelib.Data.CCL.Transducer.Emission.Residual
