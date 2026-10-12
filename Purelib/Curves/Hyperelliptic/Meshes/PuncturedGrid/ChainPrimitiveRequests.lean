module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveDecay
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PreparedGridPeriodPrograms

open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms

open Purelib.Riemann.Readings

@[expose] public section

/-!
# Requested primitive comparisons for weighted cut-cycle periods

Each component retains its actual local polynomial requests and selected
period sample. A common later stage is computed from the finite cached
indices; movement to that stage is paid before the integer-row amplification.
The result certifies a requested comparison with the existing weighted
period stream. It does not supply globally compatible cut-face primitives.
-/

open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Periods.WeightedPeriods (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodSample)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgramBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples ChainPeriod)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge (map)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)

/-- A finite vector retaining its original entry count. -/
abbrev Vector := Data.Vector

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {source :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {cycles : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.Vector
    (Purelib.Topology.Surface.Sewing.CutCycleChains.ClosedCutCycle lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels))) count}
  {bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgramBank lifted source cycles}
    {differential : Fin genus}

set_option genInjectivity false in
/-- Index-tagged dependent requests can be materialized in one ordinary finite vector. The row request below checks
every tag against its position. -/
structure ComponentPrimitiveRequest (components : ChainPeriods.ComponentSamples bank differential) (target :
  WeightedPeriods.Coordinate) (minimumStage : Nat) where
  /-- The actual original component index selected by this local request. -/ index : Fin count
  /-- The retained controlled primitive request on the exact original recast period parents. -/ request :
    PreparedControlledPrimitiveRequests.ControlledSumRequest ((bank.programs index).period.initial.state.parents.map
    (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))) genus target
  /-- The cached original component period comparison at its selected stage. -/ comparison :
    PreparedPeriodPrimitiveRequests.PeriodSample (bank.programs index).period.initial
    (PreparedRefinementProgramCore.standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential) request minimumStage
  /-- The original component stream's remaining movement is below its retained local target. -/ movement_small :
    Geometric.Basic.quarterRadius (components.streams index).errorScale comparison.stage < target

constructive_injectivity ComponentPrimitiveRequest

namespace ComponentPrimitiveRequest

variable {components : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples bank
  differential} {target : Purelib.Riemann.Periods.WeightedPeriods.Coordinate} {minimumStage : Nat}

/-- Acquire the original component primitive requests once and retain a paid common stage above their exact selected
floors. -/
def acquire (components : ChainPeriods.ComponentSamples bank differential) (index : Fin count) (target :
  WeightedPeriods.Coordinate)
    (positive : 0 < target) (minimumStage : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.ComponentPrimitiveRequest components target
      minimumStage :=
  let period := (bank.programs index).period
  let stream := components.streams index
  let first := Search.firstQuarterBelow stream.errorScale minimumStage target
  let request := period.primitiveRequest differential target positive
  let selected := period.requestedPrimitiveComparison differential request first
  ⟨index, request,
    { selected with
      stage_ge := (Search.firstQuarterBelow_ge stream.errorScale minimumStage target).trans selected.stage_ge },
    (quarterRadius_antitone stream.errorScale_nonneg selected.stage_ge).trans_lt
      (Search.firstQuarterBelow_accurate stream.errorScale stream.errorScale_nonneg minimumStage target positive)⟩

/-- The retained comparison sample is exactly the corresponding original geometric stream sample. -/
theorem sample_eq (entry : Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.ComponentPrimitiveRequest
  components target minimumStage) :
    entry.comparison.sample = (components.streams entry.index).sample entry.comparison.stage := by
  rw [components.samples_eq, entry.comparison.sample_eq,
    CutCycleProgram.program,
    PeriodWalk.program_model]
  exact (RootClosedState.sample_eq_flat
    (bank.programs entry.index).period.initial (PreparedRefinementProgramCore.standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential) _).symm

/-- Every later original component sample remains within four local targets of the retained primitive sum. -/
theorem accurate_later (entry :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.ComponentPrimitiveRequest components target
  minimumStage) {stage : Nat}
    (later : entry.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (entry.request.primitiveSum - (components.streams entry.index).sample
      stage) < 4 * target := by
  have initial := entry.comparison.accurate
  rw [entry.sample_eq] at initial
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at initial
  have movement := ((components.streams entry.index).later_close later).trans_lt entry.movement_small
  calc
    _ = Data.Gaussian.Norm.Basic.normSq ((entry.request.primitiveSum - (components.streams entry.index).sample
      entry.comparison.stage) -
        ((components.streams entry.index).sample stage - (components.streams entry.index).sample
          entry.comparison.stage)) := by
      congr 1; ring1
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (entry.request.primitiveSum - (components.streams
      entry.index).sample entry.comparison.stage) +
        Data.Gaussian.Norm.Basic.normSq ((components.streams entry.index).sample stage - (components.streams
          entry.index).sample entry.comparison.stage)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ < 2 * (target + target) := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      (Fraction.Order.Arithmetic.add_lt_add_direct initial movement)
    _ = 4 * target := by ring1

end ComponentPrimitiveRequest

/-- Compute the maximum of the original finite natural-number vector, with zero for the empty vector. -/
def maximum : {size : Nat} → Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.Vector Nat size → Nat
  | _, .nil => 0
  | _, .cons first rest => max first (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.maximum
    rest)

/-- Every original finite-vector entry is bounded by the computed retained maximum. -/
theorem le_maximum : {size : Nat} → (values : Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.Vector
  Nat size) → (index : Fin size) → values index ≤
  Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.maximum values
  | _, .nil, index => Fin.elim0 index
  | _, .cons _ _, ⟨0, _⟩ => Nat.Order.le_max_left _ _
  | _, .cons _ rest, ⟨index + 1, bound⟩ =>
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.le_maximum rest ⟨index,
    Nat.lt_of_succ_lt_succ bound⟩).trans (Nat.Order.le_max_right _ _)

namespace ChainPeriod

variable {components : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples bank
  differential} {weights : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.Vector Int count}

set_option genInjectivity false in
/-- Cached local primitive requests and their original weighted period comparison.

The retained component tags match their vector positions, and one stage pays all original component floors before
applying the actual integer-weight amplification. -/
structure PrimitiveRequest (period : ChainPeriods.ChainPeriod components weights) (target : WeightedPeriods.Coordinate)
  (minimumStage : Nat) where
  /-- The cached per-component budget after paying the original integer-weight amplification. -/ budget :
    WeightedPeriods.Coordinate
  /-- The local budget is one quarter of the original coefficient certificate's per-component target. -/ budget_eq :
    budget = period.coefficients.perComponent target / 4
  /-- The cached primitive requests for all original component programs. -/ entries :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.Vector
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.ComponentPrimitiveRequest components budget
    minimumStage) count
  /-- Each cached component request retains exactly its original vector position. -/ indices_eq : ∀ index, (entries
    index).index = index
  /-- The cached selected stage of every original component request. -/ stages :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.Vector Nat count
  /-- Every cached stage is exactly its retained component comparison stage. -/ stages_eq : ∀ index, stages index =
    (entries index).comparison.stage
  /-- The cached common stage used by the original weighted period comparison. -/ stage : Nat
  /-- The common stage respects the original caller-supplied minimum. -/ stage_ge : minimumStage ≤ stage
  /-- The common stage is at least every original retained component stage. -/ entries_le : ∀ index, stages index ≤
    stage
  /-- The cached primitive sums of the original component requests. -/ primitives :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.Vector WeightedPeriods.Gaussian count
  /-- Every cached primitive value is its exact retained request sum. -/ primitives_eq : ∀ index, primitives index =
    (entries index).request.primitiveSum
  /-- The cached original coefficient-weighted primitive sum. -/ value : WeightedPeriods.Gaussian
  /-- The value is exactly the retained coefficient combination of original primitive entries. -/ value_eq : value =
    period.coefficients.combine primitives
  /-- The cached original chain-period approximation at the retained common stage. -/ sample : WeightedPeriods.Gaussian
  /-- The cached sample is exactly the original weighted period stream at the retained common stage. -/ sample_eq :
    sample = period.approximation.sample stage

constructive_injectivity PrimitiveRequest

namespace PrimitiveRequest

variable {period : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components weights}
  {target : Purelib.Riemann.Periods.WeightedPeriods.Coordinate} {minimumStage : Nat}

/-- Acquire the original component primitive requests once and retain a paid common stage above their exact selected
floors. -/
def acquire (period : ChainPeriods.ChainPeriod components weights) (target : WeightedPeriods.Coordinate) (positive : 0 <
  target) (minimumStage : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.ChainPeriod.PrimitiveRequest period target
      minimumStage :=
  let budget := period.coefficients.perComponent target / 4
  have budgetPositive := Fraction.Order.Field.div_pos_direct (period.coefficients.perComponent_positive positive) (by
    decide : (0 : WeightedPeriods.Coordinate) < 4)
  let entries := Data.Vector.Basic.vectorOfFn fun index =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.ComponentPrimitiveRequest.acquire components index
    budget budgetPositive minimumStage
  let stages := Data.Vector.Basic.vectorOfFn fun index => (entries index).comparison.stage
  let stage := max minimumStage (Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.maximum stages)
  let primitives := Data.Vector.Basic.vectorOfFn fun index => (entries index).request.primitiveSum
  ⟨budget, rfl, entries, fun index => by rw [Data.Vector.Basic.vectorOfFn_apply]; rfl,
    stages, Data.Vector.Basic.vectorOfFn_apply _, stage, Nat.Order.le_max_left _ _, fun index =>
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.le_maximum stages index).trans
      (Nat.Order.le_max_right _ _),
    primitives, Data.Vector.Basic.vectorOfFn_apply _, period.coefficients.combine primitives, rfl,
      period.approximation.sample stage, rfl⟩

/-- The actual retained weighted primitive value differs from its original chain-period sample by less than the
requested target. -/
theorem accurate (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests.ChainPeriod.PrimitiveRequest period target
  minimumStage) (positive : 0 < target) :
    Data.Gaussian.Norm.Basic.normSq (request.value - request.sample) < target := by
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  rw [request.value_eq, request.sample_eq, period.sample_eq]
  apply period.coefficients.normSq_difference_lt _ _ positive
  intro index
  have later : (request.entries index).comparison.stage ≤ request.stage := by
    rw [← request.stages_eq]; exact request.entries_le index
  have bounded := (request.entries index).accurate_later later
  rw [← request.primitives_eq index] at bounded
  rw [request.indices_eq index, request.budget_eq] at bounded
  have paid : 4 * (period.coefficients.perComponent target / 4) = period.coefficients.perComponent target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at bounded
  exact bounded.le.trans_eq paid

end PrimitiveRequest
end ChainPeriod
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ChainPrimitiveRequests
