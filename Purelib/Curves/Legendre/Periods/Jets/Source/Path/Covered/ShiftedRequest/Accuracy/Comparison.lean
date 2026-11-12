module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Transport
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.List.Maximum
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Dependent

/-! # Original programme comparisons on one retained shifted geometry

The retained Request supplies its actual preparation family. Away from its
selected index, that family is the original prepareCovered operation on
the same cover and based chain. Comparisons retain the actual programme
samples and choose finite later indices before another Request is built.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Comparison Equivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Nat.List.Maximum (listMaximum member_le_listMaximum)
open Purelib.Data.List
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

namespace Request

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat} (request : Request geometry index floor rootStage)

/-- The original progressive programme retaining this Request's actual selected preparation family. -/
@[expose] def programme (channel : Fin 6) : RefinementProgram :=
  program (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
    request.covered request.chain request.attempt.preparationFamily channel

/-- The original progressive programme preparing this same retained cover and based chain at each stage. -/
@[expose] def originalProgramme (channel : Fin 6) : RefinementProgram :=
  program (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
    request.covered request.chain
    (fun stage => prepareCovered request.covered floor (CellEndpoints.Targets.build request.chain.path stage))
    channel

/-- The retained programme's actual model is the original model on the same preparation-family callback. -/
theorem programme_model (channel : Fin 6) (stage : Nat) :
    (request.programme channel).model stage =
      model (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
        (floor := floor) request.covered request.chain request.attempt.preparationFamily channel stage :=
  program_model (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
    (floor := floor) request.covered request.chain request.attempt.preparationFamily channel stage

/-- The unchanged factory programme reads its genuine prepareCovered product at the displayed stage. -/
theorem originalProgramme_model (channel : Fin 6) (stage : Nat) :
    (request.originalProgramme channel).model stage =
      model (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
        (floor := floor) request.covered request.chain
        (fun selected => prepareCovered request.covered floor
          (CellEndpoints.Targets.build request.chain.path selected)) channel stage :=
  program_model (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
    (floor := floor) request.covered request.chain
    (fun selected => prepareCovered request.covered floor
      (CellEndpoints.Targets.build request.chain.path selected)) channel stage

/-- Outside its retained index, the actual programme model is the unchanged original preparation model. -/
theorem programme_other (channel : Fin 6) (stage : Nat) (different : stage ≠ index) :
    (request.programme channel).model stage = (request.originalProgramme channel).model stage := by
  have prepared := request.attempt.preparationFamily_other stage different
  have actual := congrArg (fun kept : PreparedParents (parameter := parameter + increment)
      (frame := target) (basis := basis) (count := count) request.covered floor
      (CellEndpoints.Targets.build request.chain.path stage) =>
    (⟨(sources (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
      (floor := floor) request.covered kept request.chain).cells channel⟩ : PathModel)) prepared
  exact (request.programme_model channel stage).trans
    (actual.trans (request.originalProgramme_model channel stage).symm)

/-- The computed-index preparation of an actual Request retains its whole original source factory. -/
theorem preparations_eq : request.attempt.preparations =
    prepareCovered (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
      request.covered floor (CellEndpoints.Targets.build request.chain.path index) := by
  have first := congrArg (fun kept : StageAttempt (parameter := parameter + increment)
      (frame := target) (basis := basis) (count := count) request.covered request.chain index floor rootStage =>
    kept.preparations) request.attempt_eq
  have second := congrArg (fun kept : StageAttempt (parameter := parameter + increment)
      (frame := target) (basis := basis) (count := count) request.covered request.chain index floor rootStage =>
    kept.preparations)
    (StageAttempt.fromCovered_eq_ofPrepared (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) request.covered request.chain index floor rootStage)
  have third := StageAttempt.ofPrepared_preparations (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (index := index) (floor := floor) request.covered request.chain
    (CellEndpoints.Targets.build request.chain.path index) rfl
    (prepareCovered request.covered floor (CellEndpoints.Targets.build request.chain.path index)) rootStage
  exact first.trans (second.trans third)

/-- At the selected index, the actual programme consumes the stored source factory without another preparation. -/
theorem programme_at (channel : Fin 6) :
    (request.programme channel).model index = (request.originalProgramme channel).model index := by
  have prepared := request.attempt.preparationFamily_at.trans request.preparations_eq
  have actual := congrArg (fun kept : PreparedParents (parameter := parameter + increment)
      (frame := target) (basis := basis) (count := count) request.covered floor
      (CellEndpoints.Targets.build request.chain.path index) =>
    (⟨(sources (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
      (floor := floor) request.covered kept request.chain).cells channel⟩ : PathModel)) prepared
  exact (request.programme_model channel index).trans
    (actual.trans (request.originalProgramme_model channel index).symm)

/-- The two exact head views of one original geometry give identical factory-programme models.

Only the stored list and based-chain equations are eliminated. Neither
Request's source preparation, endpoint bank or checking data is rebuilt.
-/
theorem originalProgramme_model_eq {lastIndex lastRootStage : Nat}
    (last : Request geometry lastIndex floor lastRootStage) (channel : Fin 6) (stage : Nat) :
    (request.originalProgramme channel).model stage = (last.originalProgramme channel).model stage := by
  rcases request with ⟨firstShape, firstChain, _firstAttempt⟩
  rcases last with ⟨lastShape, lastChain, _lastAttempt⟩
  have parts := List.cons.inj (firstShape.property.symm.trans lastShape.property)
  have shapes : firstShape = lastShape := Subtype.ext (Prod.ext parts.1 parts.2)
  cases shapes
  have chains : firstChain = lastChain := Subtype.ext (firstChain.property.trans lastChain.property.symm)
  cases chains
  rfl

/-- Above both selected indices, the two retained families read identical original preparation models.

The explicit successor of the maximum excludes both exceptional selected
branches. The original Requests and their whole checking outcomes remain
separate retained data throughout this pointwise readback.
-/
theorem programmes_other {lastIndex lastRootStage : Nat}
    (last : Request geometry lastIndex floor lastRootStage) (channel : Fin 6) (stage : Nat)
    (after : Nat.max index lastIndex + 1 ≤ stage) :
    (request.programme channel).model stage = (last.programme channel).model stage := by
  have later := Nat.lt_of_succ_le after
  have firstDifferent : stage ≠ index := Nat.ne_of_gt
    (Nat.lt_of_le_of_lt (Order.le_max_left index lastIndex) later)
  have lastDifferent : stage ≠ lastIndex := Nat.ne_of_gt
    (Nat.lt_of_le_of_lt (Order.le_max_right index lastIndex) later)
  exact (request.programme_other channel stage firstDifferent).trans
    ((request.originalProgramme_model_eq last channel stage).trans
      (last.programme_other channel stage lastDifferent).symm)

/-- The actual reference programme and the unchanged source factory have executable all-later comparison indices.

The comparison starts strictly after the reference's retained index. It
uses the original factory programme's existing comparison and transfers
only scalar model readbacks at those later stages.
-/
def programme_equivalent (channel : Fin 6) :
    Equivalent (request.programme channel).approximation (request.originalProgramme channel).approximation where
  compare := by
    intro firstStart lastStart tolerance positive
    let start := Nat.max (Nat.max firstStart lastStart) (index + 1)
    let kept := (Equivalent.refl (request.originalProgramme channel).approximation).compare
      start start tolerance positive
    exact
      { leftIndex := kept.leftIndex
        rightIndex := kept.rightIndex
        left_ge := ((Order.le_max_left firstStart lastStart).trans
          (Order.le_max_left (Nat.max firstStart lastStart) (index + 1))).trans kept.left_ge
        right_ge := ((Order.le_max_right firstStart lastStart).trans
          (Order.le_max_left (Nat.max firstStart lastStart) (index + 1))).trans kept.right_ge
        close := by
          intro firstLater lastLater firstAfter lastAfter
          have beyond : index + 1 ≤ firstLater :=
            ((Order.le_max_right (Nat.max firstStart lastStart) (index + 1)).trans kept.left_ge).trans firstAfter
          have different : firstLater ≠ index := Nat.ne_of_gt (Nat.lt_of_succ_le beyond)
          have modelSame := request.programme_other channel firstLater different
          have sampleSame := ((request.programme channel).certifiedView_sample firstLater).trans
            ((congrArg (fun value : PathModel => value.integralSample) modelSame).trans
              ((request.originalProgramme channel).certifiedView_sample firstLater).symm)
          exact (congrArg (fun sample : Canonical => Norm.Basic.normSq
            (sample - (request.originalProgramme channel).approximation.sample lastLater)) sampleSame).trans_lt
              (kept.close firstAfter lastAfter) }

/-- A retained comparison pays the actual reference models against the same original factory's model.

Both sufficient stages come from the supplied comparison. The only
transports are original certifiedView sample readbacks.
-/
theorem comparison_models {firstStart lastStart : Nat} {accuracy : AccuracyRequest} {channel : Fin 6}
    (compared : Comparison (request.programme channel).approximation
      (request.originalProgramme channel).approximation firstStart lastStart accuracy.tolerance)
    {firstLater lastLater : Nat} (firstAfter : compared.leftIndex ≤ firstLater)
    (lastAfter : compared.rightIndex ≤ lastLater) :
    Norm.Basic.normSq (((request.programme channel).model firstLater).integralSample -
      ((request.originalProgramme channel).model lastLater).integralSample) < accuracy.tolerance := by
  have samples := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last))
    ((request.programme channel).certifiedView_sample firstLater)
    ((request.originalProgramme channel).certifiedView_sample lastLater)
  exact samples.symm.trans_lt (compared.close firstAfter lastAfter)

/-- The paid reference comparison also pays a fresh Request's actual selected model on this same geometry. -/
theorem comparison_selected {firstStart lastStart lastIndex lastRootStage : Nat}
    {accuracy : AccuracyRequest} {channel : Fin 6}
    (compared : Comparison (request.programme channel).approximation
      (request.originalProgramme channel).approximation firstStart lastStart accuracy.tolerance)
    (last : Request geometry lastIndex floor lastRootStage)
    {firstLater : Nat} (firstAfter : compared.leftIndex ≤ firstLater)
    (lastAfter : compared.rightIndex ≤ lastIndex) :
    Norm.Basic.normSq (((request.programme channel).model firstLater).integralSample -
      ((last.programme channel).model lastIndex).integralSample) < accuracy.tolerance := by
  have paid := request.comparison_models (accuracy := accuracy) (channel := channel)
    compared firstAfter lastAfter
  have same := (request.originalProgramme_model_eq last channel lastIndex).trans
    (last.programme_at channel).symm
  have scalar := congrArg (fun value : PathModel => value.integralSample) same
  exact (congrArg (fun sample : Canonical => Norm.Basic.normSq
    (((request.programme channel).model firstLater).integralSample - sample)) scalar).symm.trans_lt paid

/-- A materialized comparison for each of the same Request's six original channels.

Every entry retains both actual approximation owners and their own selected
indices. The dependent vector keeps the channel index in its original type.
-/
@[expose] def Comparisons (firstStart lastStart : Nat) (accuracy : AccuracyRequest) :=
  DependentVector fun channel : Fin 6 => Comparison (request.programme channel).approximation
    (request.originalProgramme channel).approximation firstStart lastStart accuracy.tolerance

namespace Comparisons

/-- Construct each original channel comparison once before selecting a new source stage. -/
def build (firstStart lastStart : Nat) (accuracy : AccuracyRequest) :
    request.Comparisons firstStart lastStart accuracy :=
  DependentVector.ofFn fun channel =>
    (request.programme_equivalent (parameter := parameter) (increment := increment)
      (basis := basis) (target := target) (count := count) (geometry := geometry)
      (index := index) (floor := floor) (rootStage := rootStage) channel).compare
        firstStart lastStart accuracy.tolerance accuracy.positive

variable {request} {firstStart lastStart : Nat} {accuracy : AccuracyRequest}
    (retained : request.Comparisons firstStart lastStart accuracy)

/-- Compute the largest original left sampling index from the stored comparisons. -/
def leftFloor : Nat :=
  listMaximum (List.ofFn fun channel : Fin 6 => (retained.get channel).leftIndex)

/-- Compute the largest original right sampling index before building a fresh Request. -/
def rightFloor : Nat :=
  listMaximum (List.ofFn fun channel : Fin 6 => (retained.get channel).rightIndex)

/-- Every original left comparison index is covered by the computed common floor. -/
theorem left_le (channel : Fin 6) :
    (retained.get channel).leftIndex ≤ leftFloor retained :=
  member_le_listMaximum _ _ (OfFn.Basic.mem_ofFn.mpr ⟨channel, rfl⟩)

/-- Every original right comparison index is covered by the computed common floor. -/
theorem right_le (channel : Fin 6) :
    (retained.get channel).rightIndex ≤ rightFloor retained :=
  member_le_listMaximum _ _ (OfFn.Basic.mem_ofFn.mpr ⟨channel, rfl⟩)

end Comparisons

end Request

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
