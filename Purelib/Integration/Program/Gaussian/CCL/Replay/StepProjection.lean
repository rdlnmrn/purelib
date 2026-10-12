module
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Approximation.Gaussian.Process.Normalization.Decision
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.Approximation.Gaussian.Process.Recipe.Inverse
import Purelib.Data.CCL.Encoding.Padding.Process
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.CCL.Transducer.Emission.Initial
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
import Purelib.Data.CCL.Transducer.Emission.Loop
import Purelib.Data.CCL.Transducer.Emission.Low
import Purelib.Data.CCL.Transducer.Emission.Low.Preparation
import Purelib.Data.CCL.Transducer.Emission.Residual
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Replay.Emission.Step
import Purelib.Data.CCL.Transducer.Replay.Mode
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Controller

import Purelib.Approximation.Gaussian.Enclosure.Residual.Data
import Purelib.Approximation.Gaussian.Process.Normalization.Data.Correspondence
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Computation
import Purelib.Data.Gaussian.Norm.Comparison
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Representation
import Purelib.Integration.Program.Gaussian.Query.CursorRepresentation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Computation.Query.Basic
import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation.Gaussian.Enclosure.Ball.Data (BallData)
open Purelib.Approximation.Gaussian.Process.Recipe (Cursor)

section
@[expose] public section

/-! # Certified projection of the recorded productive chunks -/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.StepProjection

open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The checked initial emission represents the original initial step when the cursor represents its exact refined
state. -/
theorem initialAfter_rep (program :
  Basic.CachedProgram) (actual : Mode.Basic.InitialState)
    (cursor : Cursor)
    (represented : CursorRepresentation.CursorRep program cursor actual.process
      (Emission.Initial.Preparation.initialRefinedState actual.process actual.state)) :
    Representation.EmissionRep program
      (Replay.Emission.Step.initialAfter (IntegrationReplay.control program) cursor (BallData.ofBall
        (actual.process.ball (Emission.Initial.Preparation.initialRefinedState actual.process actual.state))))
      (Emission.Initial.initialStep actual) := by
  unfold Replay.Emission.Step.initialAfter Emission.Initial.initialStep
  dsimp only [BallData.ofBall]
  by_cases normalized : 1 ≤ normSq
      (actual.process.ball (Emission.Initial.Preparation.initialRefinedState actual.process actual.state)).center
  · have normalizedAdapter := normalized
    rw [← Norm.Basic.normSq_eq_canonical] at normalizedAdapter
    rw [if_pos normalizedAdapter, dif_pos normalizedAdapter]
    unfold Enclosure.Sector.Decision.decide
    by_cases upper : normSq
        (actual.process.ball (Emission.Initial.Preparation.initialRefinedState actual.process actual.state)).center ≤ 13
          / 6
    · have upperAdapter := upper
      rw [← Norm.Basic.normSq_eq_canonical] at upperAdapter
      rw [if_pos upperAdapter, dif_pos upperAdapter]
      dsimp only [Representation.EmissionRep, Replay.Emission.Step.sectorNext]
      refine ⟨rfl, ?_⟩
      simp only [Enclosure.Ball.Data.Bounds.residualUpper, Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
      apply Representation.ModeRep.residual
      exact represented.residual _
    · have upperAdapter := upper
      rw [← Norm.Basic.normSq_eq_canonical] at upperAdapter
      rw [if_neg upperAdapter, dif_neg upperAdapter]
      dsimp only [Representation.EmissionRep, Replay.Emission.Step.unaryNext]
      refine ⟨rfl, ?_⟩
      simp only [Enclosure.Ball.Data.Bounds.unaryLower, Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
      apply Representation.ModeRep.loop
      exact represented.unary
  · have normalizedAdapter := normalized
    rw [← Norm.Basic.normSq_eq_canonical] at normalizedAdapter
    rw [if_neg normalizedAdapter, dif_neg normalizedAdapter]
    dsimp only [Representation.EmissionRep, Replay.Emission.Step.lowNext]
    refine ⟨rfl, ?_⟩
    apply Representation.ModeRep.low
    exact represented.upscaled 1

open Purelib.Computation.Query in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The retained initial replay query succeeds against the original program and represents its exact initial emission.
-/
theorem initialStep_rep (program :
  Basic.CachedProgram) (actual : Mode.Basic.InitialState)
    (cursor : Cursor) (represented : CursorRepresentation.CursorRep program cursor
        actual.process
      actual.state) :
    ∃ emission,
      ((Controller.initialStep (IntegrationReplay.control program) cursor).run program.stage).value = .ok emission ∧
      Representation.EmissionRep program emission (Emission.Initial.initialStep actual) := by
  unfold Controller.initialStep
  rw [Computation.Query.Protocol.map_run_value,
    represented.observe _ Emission.Initial.Budget.initialRadiusSq_pos]
  refine ⟨_, rfl, initialAfter_rep program actual _ ?_⟩
  exact represented.refined _ Emission.Initial.Budget.initialRadiusSq_pos

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The checked low-mode emission succeeds and represents the original low step at the exact refined state. -/
theorem lowAfter_rep (program :
  Basic.CachedProgram) (actual : Mode.Basic.LowState)
    (cursor : Cursor)
    (represented : CursorRepresentation.CursorRep program cursor actual.process
      (Emission.Initial.Preparation.initialRefinedState actual.process actual.state)) :
    ∃ emission,
      Replay.Emission.Step.lowAfter (IntegrationReplay.control program) actual.count cursor
        (BallData.ofBall
        (actual.process.ball (Emission.Initial.Preparation.initialRefinedState actual.process actual.state))) = .ok
          emission ∧
      Representation.EmissionRep program emission (Emission.Low.lowStep actual) := by
  unfold Replay.Emission.Step.lowAfter Emission.Low.lowStep
  dsimp only [BallData.ofBall]
  by_cases normalized : 1 ≤ normSq
      (actual.process.ball (Emission.Initial.Preparation.initialRefinedState actual.process actual.state)).center
  · have normalizedAdapter := normalized
    rw [← Norm.Basic.normSq_eq_canonical] at normalizedAdapter
    rw [if_pos normalizedAdapter, dif_pos normalizedAdapter,
      dif_pos (Emission.Low.Preparation.low_center_lt_extended_upper actual)]
    refine ⟨_, rfl, rfl, ?_⟩
    dsimp only [Replay.Emission.Step.sectorNext]
    simp only [Enclosure.Ball.Data.Bounds.residualUpper, Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
    apply Representation.ModeRep.residual
    exact represented.residual _
  · have normalizedAdapter := normalized
    rw [← Norm.Basic.normSq_eq_canonical] at normalizedAdapter
    rw [if_neg normalizedAdapter, dif_neg normalizedAdapter]
    refine ⟨_, rfl, rfl, ?_⟩
    dsimp only [Replay.Emission.Step.lowNext]
    apply Representation.ModeRep.low
    exact represented.upscaled 1

open Purelib.Computation.Query in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The retained low-mode replay query succeeds and represents the exact original low emission. -/
theorem lowStep_rep (program :
  Basic.CachedProgram) (actual : Mode.Basic.LowState)
    (cursor : Cursor) (represented : CursorRepresentation.CursorRep program cursor
        actual.process
      actual.state) :
    ∃ emission,
      ((Controller.lowStep (IntegrationReplay.control program) actual.count cursor).run program.stage).value = .ok
        emission ∧
      Representation.EmissionRep program emission (Emission.Low.lowStep actual) := by
  unfold Controller.lowStep
  rw [Computation.Query.Protocol.map_run_value,
    represented.observe _ Emission.Initial.Budget.initialRadiusSq_pos]
  exact lowAfter_rep program actual _ (represented.refined _ Emission.Initial.Budget.initialRadiusSq_pos)

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The checked loop emission succeeds and represents the original loop step at its exact domain-refined state. -/
theorem loopAfter_rep (program :
  Basic.CachedProgram) (actual : Mode.Basic.LoopState)
    (cursor : Cursor)
    (represented : CursorRepresentation.CursorRep program cursor actual.process (actual.domain.refinedState
      actual.state)) :
    ∃ emission,
      Replay.Emission.Step.loopAfter (IntegrationReplay.control program) actual.kind actual.count cursor
        (BallData.ofBall (actual.process.ball (actual.domain.refinedState actual.state))) = .ok
          emission ∧
      Representation.EmissionRep program emission (Emission.Loop.loopStep actual) := by
  unfold Replay.Emission.Step.loopAfter
  dsimp only [BallData.ofBall]
  rw [dif_pos (actual.domain.refined_center_normalized actual.state)]
  unfold Emission.Loop.loopStep Process.Normalization.Basic.LoopDomain.decide Enclosure.Sector.Decision.decide
  by_cases upper : normSq (actual.process.ball (actual.domain.refinedState actual.state)).center ≤ 13 / 6
  · have upperAdapter := upper
    rw [← Norm.Basic.normSq_eq_canonical] at upperAdapter
    rw [if_pos upperAdapter, dif_pos upperAdapter]
    refine ⟨_, rfl, rfl, ?_⟩
    dsimp only [Replay.Emission.Step.sectorNext]
    simp only [Enclosure.Ball.Data.Bounds.residualUpper, Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
    apply Representation.ModeRep.residual
    exact represented.residual _
  · have upperAdapter := upper
    rw [← Norm.Basic.normSq_eq_canonical] at upperAdapter
    rw [if_neg upperAdapter, dif_neg upperAdapter]
    refine ⟨_, rfl, rfl, ?_⟩
    dsimp only [Replay.Emission.Step.unaryNext]
    simp only [Enclosure.Ball.Data.Bounds.unaryLower, Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
    apply Representation.ModeRep.loop
    exact represented.unary

open Purelib.Computation.Query in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The retained loop query succeeds and represents the original loop emission with its exact kind, count and domain. -/
theorem loopStep_rep (program :
  Basic.CachedProgram) (actual : Mode.Basic.LoopState)
    (cursor : Cursor) (represented : CursorRepresentation.CursorRep program cursor
        actual.process
      actual.state) :
    ∃ emission,
      ((Controller.loopStep (IntegrationReplay.control program) actual.kind actual.count cursor
        (Process.Normalization.Data.Correspondence.Domain.ofActual actual.domain)).run program.stage).value = .ok
          emission ∧
      Representation.EmissionRep program emission (Emission.Loop.loopStep actual) := by
  unfold Controller.loopStep
  rw [Process.Normalization.Data.Correspondence.Domain.target_ofActual, Computation.Query.Protocol.map_run_value,
    represented.observe _ actual.domain.decisionTarget_pos]
  exact loopAfter_rep program actual _ (represented.refined _ actual.domain.decisionTarget_pos)

open Purelib.Computation.Query in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The retained residual query succeeds and represents the exact original residual emission.

The small-ball branch preserves padding and the original residual state; the apart branch preserves the exact inverse
preparation and loop continuation. -/
theorem residualStep_rep (program :
  Basic.CachedProgram) (actual : Mode.Basic.ResidualState)
    (cursor : Cursor) (represented : CursorRepresentation.CursorRep program cursor
        actual.process
      actual.state) :
    ∃ emission,
      ((Controller.residualStep (IntegrationReplay.control program) cursor actual.count actual.upper).run
        program.stage).value =
        .ok emission ∧ Representation.EmissionRep program emission (Emission.Residual.residualStep actual) := by
  let target := Padding.Residual.paddingTarget (actual.count + 1)
  have positive : 0 < target / 6 := Fraction.Order.Field.div_pos_direct
    (Padding.Residual.paddingTarget_pos (actual.count + 1)) (by decide)
  have refined := represented.refined (target / 6) positive
  have fields := Enclosure.Residual.Data.residualDecision_fields
    (actual.process.ball (Padding.Process.residualState actual.process actual.state (actual.count + 1)))
    target (Padding.Residual.paddingTarget_pos (actual.count + 1))
    (Padding.Process.residual_accurate actual.process actual.state (actual.count + 1))
  unfold Controller.residualStep
  rw [Computation.Query.Protocol.bind_run_value, represented.observe _ positive]
  change ∃ emission,
    ((Controller.residualAfter (IntegrationReplay.control program) actual.count actual.upper
      (cursor.refined (IntegrationReplay.control program) (target / 6))
      (BallData.ofBall (actual.process.ball
        (Padding.Process.residualState actual.process actual.state (actual.count + 1))))).run program.stage).value =
      .ok emission ∧ Representation.EmissionRep program emission (Emission.Residual.residualStep actual)
  cases decision : Enclosure.Residual.decide
    (actual.process.ball (Padding.Process.residualState actual.process actual.state (actual.count + 1)))
    target (Padding.Residual.paddingTarget_pos (actual.count + 1))
    (Padding.Process.residual_accurate actual.process actual.state (actual.count + 1)) with
  | small certificate =>
      rw [decision] at fields
      unfold Controller.residualAfter
      rw [if_pos fields]
      refine ⟨_, rfl, ?_⟩
      unfold Emission.Residual.residualStep Padding.Process.decideResidual
      dsimp only [Enclosure.Ball.Bounds.smallUpper, Enclosure.Residual.SmallBall]
      rw [decision]
      refine ⟨rfl, ?_⟩
      simp only [Enclosure.Ball.Data.Bounds.smallUpper, Basic.Canonical.Norm.Comparison.normSqFromReduced_eq,
        BallData.ofBall]
      apply Representation.ModeRep.residual
      exact refined
  | apart certificate =>
      rw [decision] at fields
      unfold Controller.residualAfter
      rw [if_neg fields.1]
      dsimp only [BallData.ofBall]
      rw [Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
      rw [← fields.2]
      let next := Emission.Residual.residualApartLoopState actual certificate
      have inverseRep : CursorRepresentation.CursorRep program
          (Process.Recipe.Inverse.inverseCursor (IntegrationReplay.control program)
            (cursor.refined (IntegrationReplay.control program) (target / 6)) certificate.lowerSq actual.count)
          next.process next.state := refined.inverse certificate actual.count
      have projected := loopStep_rep program next _ inverseRep
      unfold Emission.Residual.residualStep Padding.Process.decideResidual
      dsimp only [Enclosure.Ball.Bounds.smallUpper, Enclosure.Residual.SmallBall]
      rw [decision]
      exact projected

end

open Purelib.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Every represented replay mode takes a successful original-program query step whose emission represents the exact
actual transducer step. -/
theorem step_rep {program : Basic.CachedProgram}
  {actual : Data.CCL.Transducer.Mode} {mode : Data.CCL.Transducer.Replay.Mode}
    (represented : Representation.ModeRep program actual mode) :
    ∃ emission, ((Controller.step (IntegrationReplay.control program) mode).run program.stage).value = .ok emission ∧
      Representation.EmissionRep program emission (Emission.Step.step actual) := by
  cases represented with
  | initial actual cursor represented => exact initialStep_rep program actual cursor represented
  | low actual cursor represented => exact lowStep_rep program actual cursor represented
  | loop actual cursor represented => exact loopStep_rep program actual cursor represented
  | residual actual cursor represented => exact residualStep_rep program actual cursor represented

end Purelib.Integration.Program.Gaussian.CCL.Replay.StepProjection

end
