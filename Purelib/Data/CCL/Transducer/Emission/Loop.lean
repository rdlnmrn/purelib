module
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
public import Purelib.Data.CCL.Transducer.Emission.Preparation
import Purelib.Approximation.Gaussian.Process.Observation.Operations
public import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Approximation.Gaussian.Process.Normalization.Decision
public import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
import Purelib.Approximation.Gaussian.Process.Basic
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

namespace Purelib.Data.CCL.Transducer.Emission.Loop

section
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.ComplexContinuedFraction.Encoding
/-- Build the exact residual mode state from a retained loop state and safe sector-ball certificate.

Use the already selected refined state as the residual process base. Retain that process's initial state, zero count and
the safe-sector residual upper bound with its strict one-half comparison. -/
@[expose] public def loopSectorResidualState (current : Mode.Basic.LoopState)
    (sector : ComplexContinuedFraction.Encoding.Sector)
    (certificate : Enclosure.Sector.Safe.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) : Mode.Basic.ResidualState :=
  let base := current.domain.refinedState current.state
  let nextProcess := Process.Sector.Residual.residualProcess current.process base sector
  let nextState := Process.Sector.Residual.residualInitial current.process base sector
  let upper := Process.Sector.Residual.safeResidualUpper sector (current.process.ball base)
  { process := nextProcess
    state := nextState
    count := 0
    upper := upper
    upperBound := by
      intro value possible
      exact Process.Sector.Residual.translated_based_norm_le_safeResidualUpper
        current.process base sector certificate possible
    upperStrict := Process.Sector.Residual.safeResidualUpper_lt_half certificate }

/-- The residual state built from a loop sector starts at count zero.

The retained safe-sector construction stores zero in its original count
field. Reading that field reduces directly without replacing the process,
refined state or sector certificate. -/
@[simp] public theorem loopSectorResidualState_count (current : Mode.Basic.LoopState)
    (sector : ComplexContinuedFraction.Encoding.Sector)
    (certificate : Enclosure.Sector.Safe.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) :
    (Emission.Loop.loopSectorResidualState current sector certificate).count = 0 := rfl

end

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Process.Based
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian

namespace Selection

/-- Construct the original loop chunk from its retained sector decision and exact observation. -/
@[expose] def emission (current : Mode.Basic.LoopState) (base : current.process.State)
    (observed : Process.Observation current.process base) : Enclosure.Sector.Decision observed.ball → Emission
  | .unary certificate =>
      let original : Enclosure.Sector.Large.UnaryBall (current.process.ball base) := observed.ballEq ▸ certificate
      { bits := [true]
        nonempty := by decide
        next := .loop
          { kind := current.kind
            count := current.count + 1
            process := Process.Gamma.Downscale.unaryScaledProcess current.process base
            state := Process.Gamma.Downscale.unaryScaledInitial current.process base
            domain := Process.Gamma.Downscale.unaryScaledLoopDomain.ofObservation
              current.process base observed original } }
  | .sector sector certificate =>
      { bits := false :: sector.code
        nonempty := by intro empty; cases empty
        next := .residual (Mode.Basic.ResidualState.ofObservation current.process base sector observed certificate) }

/-- Reuse the same observed source to construct the selected loop chunk's exact next observation. -/
@[expose] def observation (current : Mode.Basic.LoopState) (base : current.process.State)
    (observed : Process.Observation current.process base) :
    (selected : Enclosure.Sector.Decision observed.ball) →
      Mode.Observation (emission current base observed selected).next
  | .unary _ =>
      Process.Observation.mul (Process.Observation.exact Basic.Canonical.gamma⁻¹)
        (Process.Observation.based base (BasedState.initial current.process base) observed)
  | .sector sector _ =>
      Process.Observation.translate
        (Process.Observation.based base (BasedState.initial current.process base) observed) sector.rep

/-- Retain the same original source route through the selected unary or sector chart. -/
@[expose] def route {source : Process} (current : Mode.Basic.LoopState)
    (earlier : Process.Route source current.process) (base : current.process.State)
    (observed : Process.Observation current.process base) :
    (selected : Enclosure.Sector.Decision observed.ball) →
      Process.Route source (emission current base observed selected).next.process
  | .unary _ => .downscale earlier base
  | .sector sector _ => .residual earlier base sector

end Selection

/-- Construct one original loop emission from its retained refinement and sector decision.

The same cached source ball and witness construct the output chart and its
observation without further source calls. The earlier receipt retains its
own payment through the unchanged nominal chart route.
-/
@[expose] def fromRefinement {source : Process} (current : Mode.Basic.LoopState)
    (route : Process.Route source current.process)
    (receipt : Process.Route.Refinement route current.state current.domain.decisionTarget
      current.domain.decisionTarget_pos) : Emission.Prepared source :=
  have normalized : 1 ≤ Norm.Basic.normSq (current.process.ball receipt.state).center :=
    receipt.stateEq.symm ▸ current.domain.refined_center_normalized current.state
  have fine : (current.process.ball receipt.state).radiusSq < Enclosure.Sector.Budget.uniformRadiusSq :=
    receipt.stateEq.symm ▸ current.domain.refined_accurate current.state
  let selected := Enclosure.Sector.Decision.decide receipt.observation.ball
    (receipt.observation.ballEq.symm ▸ normalized) (receipt.observation.ballEq.symm ▸ fine)
  let emission := Selection.emission current receipt.state receipt.observation selected
  ⟨emission, Selection.route current route receipt.state receipt.observation selected,
    Selection.observation current receipt.state receipt.observation selected, 0⟩

/-- Prepare the original loop emission and include the same source-refinement payment. -/
@[expose] def prepare {source : Process} (current : Mode.Basic.LoopState)
    (route : Process.Route source current.process) : Emission.Prepared source :=
  let receipt := route.refine current.state current.domain.decisionTarget current.domain.decisionTarget_pos
  let prepared := fromRefinement current route receipt
  { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls }

/-- A retained refinement preserves the complete original loop preparation and separates its earlier payment. -/
theorem prepare_eq_fromRefinement {source : Process} (current : Mode.Basic.LoopState)
    (route : Process.Route source current.process)
    (receipt : Process.Route.Refinement route current.state current.domain.decisionTarget
      current.domain.decisionTarget_pos) :
    prepare current route =
      let prepared := fromRefinement current route receipt
      { prepared with sourceCalls := receipt.sourceCalls + prepared.sourceCalls } := by
  cases Process.Route.Refinement.unique receipt
    (route.refine current.state current.domain.decisionTarget current.domain.decisionTarget_pos)
  rfl

/-- Emit the original loop chunk from its actual input-route preparation. -/
@[expose] def loopStep (current : Mode.Basic.LoopState) : Emission :=
  (prepare current (.input : Process.Route current.process current.process)).emission

/-- Every retained original route prepares the same complete original loop emission. -/
theorem prepare_emission_eq {source : Process} (current : Mode.Basic.LoopState)
    (route : Process.Route source current.process) : (prepare current route).emission = loopStep current := by
  let base := current.domain.refinedState current.state
  have normalized := current.domain.refined_center_normalized current.state
  have fine := current.domain.refined_accurate current.state
  change
    (let observed := route.observe base
     let selected := Enclosure.Sector.Decision.decide observed.ball
       (observed.ballEq.symm ▸ normalized) (observed.ballEq.symm ▸ fine)
     Selection.emission current base observed selected) =
    (let observed := Process.Observation.build current.process base
     let selected := Enclosure.Sector.Decision.decide observed.ball
       (observed.ballEq.symm ▸ normalized) (observed.ballEq.symm ▸ fine)
     Selection.emission current base observed selected)
  exact congrArg (fun observed : Process.Observation current.process base =>
    let selected := Enclosure.Sector.Decision.decide observed.ball
      (observed.ballEq.symm ▸ normalized) (observed.ballEq.symm ▸ fine)
    Selection.emission current base observed selected) (Process.Observation.unique _ _)

/-- A loop preparation pays one original supplied-source refinement, ball read and witness read. -/
theorem prepare_sourceCalls {source : Process} (current : Mode.Basic.LoopState)
    (route : Process.Route source current.process) : (prepare current route).sourceCalls = 3 :=
  (route.refine current.state current.domain.decisionTarget current.domain.decisionTarget_pos).sourceCalls_eq

/-- Read back the exact original unary-or-sector branch equation of the prepared loop emission.

The complete next mode keeps its original process, dependent refined state,
count and numerical domain. This equation lets mathematical clients use the
original branch shape without rebuilding the retained execution work.
-/
theorem loopStep_eq (current : Mode.Basic.LoopState) :
    loopStep current =
      match current.domain.decide current.state with
      | .unary certificate =>
          { bits := [true]
            nonempty := by decide
            next := .loop
              { kind := current.kind
                count := current.count + 1
                process := Process.Gamma.Downscale.unaryScaledProcess current.process
                  (current.domain.refinedState current.state)
                state := Process.Gamma.Downscale.unaryScaledInitial current.process
                  (current.domain.refinedState current.state)
                domain := Process.Gamma.Downscale.unaryScaledLoopDomain current.process
                  (current.domain.refinedState current.state) certificate } }
      | .sector sector certificate =>
          { bits := false :: sector.code
            nonempty := by intro empty; cases empty
            next := .residual (loopSectorResidualState current sector certificate) } := by
  change Selection.emission current (current.domain.refinedState current.state)
    (Process.Observation.build current.process (current.domain.refinedState current.state))
    (current.domain.decide current.state) = _
  cases current.domain.decide current.state with
  | unary certificate => rfl
  | sector sector certificate => rfl

end Purelib.Data.CCL.Transducer.Emission.Loop
