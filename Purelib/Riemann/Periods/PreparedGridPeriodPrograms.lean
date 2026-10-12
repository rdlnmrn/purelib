module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Riemann.Topology.PreparedBankRootChains

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
public import Purelib.Riemann.Integration.PreparedCoveredParentLists
public import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests

@[expose] public section

/-!
# Root-safe period programs on retained common-grid preparations

The centered parent list is extracted once from the grid walk's actual
prepared integration spine.  The exact same parents carry the operational
root chain and seed every later certified period sample.  Their primitive
cover is retained too, and supplies requested local primitive sums for
compatible refinements of those exact initial cells.  Neither a new owner
nor an independently prepared path is substituted by this bridge.

These are auxiliary grid programs for the cut-surface comparison.  Equality
with the original tour period names and geometric symplectic realization are
not asserted here.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Basis (CertifiedPeriodProgram)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName preparedPathRootChain)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (DirectSwitchedState SwitchedPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials
  standardDifferential_mem_standardDifferentials)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Readings.UniformPreparedRequests (PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodSample)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib
open Purelib.Riemann.Integration
open Purelib.Riemann.Periods

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Box}
    {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient} {base :
      Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner (curve.polynomial.eval base)}

section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.RootClosedWalk

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Geometry.Path.Gaussian.Lifted in
/-- Recasting a switched chain built from centered parents gives exactly the recast parent models. -/
private theorem recast_cells_of_centered (target : Basic.Differential genus) {source : Basic.Differential genus} :
    ∀ {parents : List (CenteredEdge curve source)} {start finish : Basic.LiftedPoint 2}
      (chain : CenteredPathChain parents (start := start) (finish := finish)),
      (SwitchedPathChain.ofCenteredPathChain chain).recastCells target =
        (parents.map (recastCenteredEdge target)).map CenteredEdge.model
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ tail => congrArg (List.cons _) (recast_cells_of_centered target tail)

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.RootClosedWalk

namespace Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
open Purelib.Riemann.Topology.PreparedBankRootChains in
/-- Extract a root-closed integration state from the retained grid-walk preparation.

Cache the exact centered parents and all standard-differential initial allowances once. The operational root chain
supplies closure, while sheet zero remains the local chart label of those original parents. -/
def initial
    (closed : RootClosedWalk grid base owner) (source : Basic.Differential genus) :
    RootClosedState curve source (ownerName owner) :=
  let data := CenteredPathChain.ofPreparedPath curve source 0 closed.traced.prepared
  let allowances := Vector.Basic.vectorOfFn fun index : Fin genus =>
    (PathModel.mk
      ((data.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential index))).map
        CenteredEdge.model)).aggregateAllowance
  let state : DirectSwitchedState curve source :=
    { start := ⟨base, 0⟩
      finish := ⟨base, 0⟩
      parents := data.parents
      proper := CenteredPathChain.ofPreparedPath_allParentsProper_of_allEdgesProper curve source 0
        closed.traced.prepared closed.proper
      chain := SwitchedPathChain.ofCenteredPathChain data.chain
      initialAllowanceBound := fun target => allowances target.index
      initialAllowance_le := by
        intro target
        change _ ≤ Vector.Basic.vectorOfFn _ target.index
        rw [Vector.Basic.vectorOfFn_apply]
        cases target
        exact le_rfl }
  ⟨state, rfl, RootChain.changeFinish
    (preparedPathRootChain curve source 0 closed.traced.prepared) (by
    rw [← closed.traced.finishOwner_eq]
    exact closed.rootReturn)⟩

end Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

section
open Purelib.Curves.Hyperelliptic.Differentials

namespace Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

/-- The initial state retains exactly the centered parents of the original prepared path. -/
theorem initial_parents
    (closed : RootClosedWalk grid base owner) (source : Basic.Differential genus) :
    (closed.initial source).state.parents =
      (CenteredPathChain.ofPreparedPath curve source 0 closed.traced.prepared).parents := rfl

/-- The initial parent count equals the number of actually accepted prepared integration steps. -/
theorem initial_parentCount
    (closed : RootClosedWalk grid base owner) (source : Basic.Differential genus) :
    (closed.initial source).state.parents.length = closed.traced.prepared.stepCount :=
  CenteredPathChain.ofPreparedPath_parents_length curve source 0 closed.traced.prepared

/-- The initial centered-parent state contains no switched handoffs. -/
theorem initial_switchCount
    (closed : RootClosedWalk grid base owner) (source : Basic.Differential genus) :
    (closed.initial source).state.chain.switchCount = 0 :=
  SwitchedPathChain.switchCount_ofCenteredPathChain _

/-- The initial model cells are exactly the original centered parents recast to the target differential. -/
theorem initial_cells
    (closed : RootClosedWalk grid base owner) (source target : Basic.Differential genus) :
    ((closed.initial source).state.model target).cells =
      ((closed.initial source).state.parents.map (recastCenteredEdge target)).map CenteredEdge.model :=
  PreparedGridPeriodPrograms.RootClosedWalk.recast_cells_of_centered target _

end Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

end

namespace Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
/-- Closing the retained operational root thread preserves the original centered-parent integral sample. -/
theorem initial_sample
    (closed : RootClosedWalk grid base owner) (source : Basic.Differential genus) :
    ((closed.initial source).state.model source).integralSample =
      (PathModel.mk
        ((CenteredPathChain.ofPreparedPath curve source 0 closed.traced.prepared).parents.map
          CenteredEdge.model)).integralSample := by
  rw [DirectSwitchedState.model, SwitchedPathChain.recastCells_integralSample]
  change (PathModel.mk
    (((CenteredPathChain.ofPreparedPath curve source 0 closed.traced.prepared).parents.map
      (recastCenteredEdge source)).map CenteredEdge.model)).integralSample = _
  rw [CenteredPathChain.ofPreparedPath_recast_self]

end Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

end

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Curves.Hyperelliptic.Integration.Observation in
open Purelib.Data in
open Purelib.Polynomial.Geometry.Grid in
/-- A retained grid preparation, its exact initial root-closed state and primitive parent cover.

The stored equality preserves the extraction constructor's result while allowing clients to consume a materialized cache
without reevaluating it. The cover belongs to those same initial parents. -/
structure PeriodWalk (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) (base :
  Gaussian.Basic.Canonical)
    (owner : Owner (curve.polynomial.eval base)) (source : Basic.Differential genus) where
  /-- The original prepared grid walk with certified operational root closure. -/ closed : RootClosedWalk grid base
    owner
  /-- The retained root-closed state with the requested source differential. -/ initial : RootClosedState curve source
    (ownerName owner)
  /-- The state is exactly the one extracted from the retained grid preparation. -/ initial_eq : initial =
    closed.initial source
  /-- The primitive cover of those exact retained initial parents. -/ covered : UniformPreparedMesh.CoveredParents genus
    initial.state.parents

constructive_injectivity PeriodWalk

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms

section

variable {source : Differential genus}

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration.PreparedCoveredParentLists in
/-- Retain the initial state and primitive cover of an existing root-closed grid walk. -/
def ofClosed (closed : RootClosedWalk grid base owner) (source : Basic.Differential genus) :
    PeriodWalk grid base owner source :=
  ⟨closed, closed.initial source, rfl,
    PrimitiveCover.coveredParents
      curve source 0 genus closed.cover⟩

/-- The retained period state at the requested stage of the standard-differential schedule. -/
def state (prepared : PeriodWalk grid base owner source) (stage : Nat) :
    RootClosedState curve source (ownerName owner) := prepared.initial.states (standardDifferentials genus) stage

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Topology.PreparedRecastRootChains in
/-- Retain operational root closure for the actual recast parents at a period stage.

The target differential changes the readings while the original owner name and root chain remain the endpoints of the
same retained cycle. -/
def roots (prepared : PeriodWalk grid base owner source) (target : Basic.Differential genus) (stage : Nat) :
    RootChain ((prepared.state stage).state.parents.map (recastCenteredEdge target))
      (ownerName owner) (ownerName owner) :=
  RootChain.recast target (prepared.state stage).roots

open Purelib.Geometry.Path.Gaussian.Lifted in
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- The lifted-cycle refinement determined by the retained initial state and standard-differential schedule. -/
def cycle (prepared : PeriodWalk grid base owner source) : Refinement.LiftedCycleRefinement 2 :=
  RootClosedState.cycle
    prepared.initial (standardDifferentials genus)

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period in
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- The certified period program for a standard differential on the retained grid cycle.

Its models use the original initial state and finite family schedule, with membership supplied by the actual standard
differential index. -/
def program (prepared : PeriodWalk grid base owner source) (differential : Fin genus) :
    Basis.CertifiedPeriodProgram curve (PeriodMatrix.standardDifferential differential) prepared.cycle :=
  RootClosedState.certifiedPeriodProgram
    prepared.initial (standardDifferentials genus) (PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential)

/-- The program's model at a stage is the model of the exact retained scheduled state. -/
theorem program_model (prepared : PeriodWalk grid base owner source) (differential : Fin genus) (stage : Nat) :
    ((prepared.program differential).integral.model stage) =
      (prepared.state stage).state.model (PeriodMatrix.standardDifferential differential) := rfl

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedRefinementRootEndpoints

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

/-- Retain all-query root agreement between successive recast period stages.

The refinement uses the actual predecessor and successor parent lists of the original schedule for the requested
differential. -/
def stepSubedges (prepared : PeriodWalk grid base owner source) (target : Basic.Differential genus) (stage : Nat) :
    RootSubedgeRefinement
      ((prepared.state stage).state.parents.map (recastCenteredEdge target))
      ((prepared.state (stage + 1)).state.parents.map (recastCenteredEdge target)) :=
  RootSubedgeRefinement.recast
    target (prepared.initial.scheduledStep (standardDifferentials genus) stage).subedgeRefinement

/-- Retain the initial primitive-cover grouping throughout a requested period stage.

Connected descendant blocks and their root-query agreement are inherited from the original schedule and recast to the
requested differential. -/
def stateSubedges (prepared : PeriodWalk grid base owner source) (target : Basic.Differential genus) (stage : Nat) :
    RootSubedgeRefinement (prepared.initial.state.parents.map (recastCenteredEdge target))
      ((prepared.state stage).state.parents.map (recastCenteredEdge target)) :=
  RootSubedgeRefinement.recast
    target (prepared.initial.statesSubedges (standardDifferentials genus) stage)

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

end

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

/-- The retained initial parent count is the original prepared path's accepted step count. -/
theorem initial_parentCount (prepared : PeriodWalk grid base owner source) :
    prepared.initial.state.parents.length = prepared.closed.traced.prepared.stepCount := by
  rw [prepared.initial_eq]
  exact prepared.closed.initial_parentCount source

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank in
/-- Every scheduled state retains the original base coordinate with local sheet label zero. -/
theorem state_base (prepared : PeriodWalk grid base owner source) (stage : Nat) :
    (prepared.state stage).state.start = ⟨base, 0⟩ := by
  rw [state, RootClosedState.states_start_eq, prepared.initial_eq]
  rfl

/-- Every retained scheduled state has zero switched handoffs. -/
theorem state_switchCount (prepared : PeriodWalk grid base owner source) (stage : Nat) :
    (prepared.state stage).state.chain.switchCount = 0 := by
  rw [state, RootClosedState.states_switchCount, prepared.initial_eq]
  exact prepared.closed.initial_switchCount source

/-- The actual period model has one cell per retained parent at every stage. -/
theorem program_cellCount (prepared : PeriodWalk grid base owner source) (differential : Fin genus) (stage : Nat) :
    ((prepared.program differential).integral.model stage).cells.length = (prepared.state stage).state.parents.length :=
      by
  rw [prepared.program_model, DirectSwitchedState.model_cells_length, prepared.state_switchCount, Nat.add_zero]

/-- The initial program cells are exactly the retained parents recast to the selected standard differential. -/
theorem program_initial_cells (prepared : PeriodWalk grid base owner source) (differential : Fin genus) :
    ((prepared.program differential).integral.model 0).cells =
      (prepared.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential differential))).map
        CenteredEdge.model := by
  rw [prepared.program_model]
  change (prepared.initial.state.model _).cells = _
  rw [prepared.initial_eq]
  exact prepared.closed.initial_cells source _

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

section
open Purelib.Data

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

open Purelib.Riemann.Integration.PreparedCoveredParentLists in
/-- Acquire a controlled primitive sum on the exact retained initial parents.

Reuse the existing primitive cover for the selected standard differential; its proper parents and positive target pay
both the local refinement error and polynomial floor. -/
def primitiveRequest (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    (target : Rat.Fraction.Rational) (positive : 0 < target) :
    ControlledSumRequest (prepared.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target :=
  ControlledSumRequest.acquire (CoveredParents.recast
    (PeriodMatrix.standardDifferential differential) prepared.covered)
    (PreparedDirectDyadicRefinements.allParentsProper_map_recast prepared.initial.state.proper) target positive

open Purelib.Data.Gaussian.Norm in
/-- The requested primitive sum and its retained local integral sample differ by less than the target in squared norm.
-/
theorem primitiveRequest_accurate (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    (target : Rat.Fraction.Rational) (positive : 0 < target) :
    Data.Gaussian.Norm.Basic.normSq
      ((prepared.primitiveRequest differential target positive).primitiveSum -
        (prepared.primitiveRequest differential target positive).integralSample) < target := by
  rw [Basic.normSq_eq_canonical]
  exact (prepared.primitiveRequest differential target positive).toPrimitiveSumRequest.accurate

open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
/-- The primitive request refines exactly the initial grid program's cells.

The compatibility witness uses the retained child blocks and exact parent-model readback, preserving cell identity as
well as the requested primitive sum. -/
def primitiveRequest_compatible (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    (target : Rat.Fraction.Rational) (positive : 0 < target) :
    PathModel.CompatibleConstantPathRefinement
      ((prepared.program differential).integral.model 0).cells
      ((prepared.primitiveRequest differential target positive).blocks.children.map CenteredEdge.model) := by
  rw [prepared.program_initial_cells]
  exact (prepared.primitiveRequest differential target positive).toPrimitiveSumRequest.compatible

open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison in
/-- Compare an existing primitive request with the actual descendant cells of a period stage.

The retained root-subedge refinement supplies the comparison and its computed error charge, preserving the original
stage and primitive request. -/
def comparePrimitiveRequest (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    {target : Rat.Fraction.Rational}
    (request : PrimitiveSumRequest (prepared.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target) (stage : Nat) :
    PrimitiveSumRequest.ComparedSample request.primitiveSum
      ((prepared.state stage).state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential differential)))
        :=
  PrimitiveSumRequest.compareRefinement
    request (prepared.stateSubedges (PeriodMatrix.standardDifferential differential) stage)

open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- The comparison's retained sample is exactly the selected program's integral sample. -/
theorem comparePrimitiveRequest_sample (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    {target : Rat.Fraction.Rational}
    (request : PrimitiveSumRequest (prepared.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target) (stage : Nat) :
    (prepared.comparePrimitiveRequest differential request stage).sample =
      ((prepared.program differential).integral.model stage).integralSample := by
  rw [(prepared.comparePrimitiveRequest differential request stage).sample_eq, prepared.program_model]
  exact (RootClosedState.sample_eq_flat
    prepared.initial (standardDifferentials genus) (PeriodMatrix.standardDifferential differential) stage).symm

open Purelib.Data.Gaussian.Norm in
/-- The computed comparison charge bounds the primitive sum's squared error against the actual period stage. -/
theorem comparePrimitiveRequest_accurate (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    {target : Rat.Fraction.Rational}
    (request : PrimitiveSumRequest (prepared.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target) (stage : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (request.primitiveSum - ((prepared.program differential).integral.model stage).integralSample) ≤
        (prepared.comparePrimitiveRequest differential request stage).errorBound := by
  rw [← prepared.comparePrimitiveRequest_sample differential request stage]
  rw [Basic.normSq_eq_canonical]
  exact (prepared.comparePrimitiveRequest differential request stage).accurate

/-- Select a period sample after the requested minimum stage within the controlled primitive tolerance.

The acquisition consumes the retained initial schedule and controlled primitive request for the same standard
differential. -/
def requestedPrimitiveComparison (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    {target : Rat.Fraction.Rational}
    (request : ControlledSumRequest (prepared.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target) (minimumStage : Nat) :
    PeriodSample prepared.initial (standardDifferentials genus) (PeriodMatrix.standardDifferential differential) request
      minimumStage :=
  PeriodSample.acquire prepared.initial (standardDifferentials genus) (PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential) request minimumStage

open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms in
/-- The requested comparison sample is the exact program reading at its retained selected stage. -/
theorem requestedPrimitiveComparison_sample (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    {target : Rat.Fraction.Rational}
    (request : ControlledSumRequest (prepared.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target) (minimumStage : Nat) :
    (prepared.requestedPrimitiveComparison differential request minimumStage).sample =
      ((prepared.program differential).integral.model
        (prepared.requestedPrimitiveComparison differential request minimumStage).stage).integralSample := by
  rw [(prepared.requestedPrimitiveComparison differential request minimumStage).sample_eq, prepared.program_model]
  exact (RootClosedState.sample_eq_flat
    prepared.initial (standardDifferentials genus) (PeriodMatrix.standardDifferential differential) _).symm

open Purelib.Data.Gaussian.Norm in
/-- The requested comparison's actual period reading has squared primitive-sum error strictly below the original target.
-/
theorem requestedPrimitiveComparison_accurate (prepared : PeriodWalk grid base owner source) (differential : Fin genus)
    {target : Rat.Fraction.Rational}
    (request : ControlledSumRequest (prepared.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target) (minimumStage : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (request.primitiveSum - ((prepared.program differential).integral.model
        (prepared.requestedPrimitiveComparison differential request minimumStage).stage).integralSample) < target := by
  rw [← prepared.requestedPrimitiveComparison_sample differential request minimumStage]
  rw [Basic.normSq_eq_canonical]
  exact (prepared.requestedPrimitiveComparison differential request minimumStage).accurate

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

end

end

end
