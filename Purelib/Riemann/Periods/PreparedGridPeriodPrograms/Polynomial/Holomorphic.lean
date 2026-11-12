module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Models
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
public import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # The original holomorphic programme on the same high-floor polynomial work

One supplied original source observation is jointly viewed under its
actual primitive-request cover and target factories. The original
fixed-observation period comparison and polynomial-source comparison
then relate the old dx/y programme to the given new genuine numerator-one
Work. No observation family or second source preparation is fabricated.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedCoveredParentLists
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction.Cast.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement
  (movementMass movementMass_nonnegative movementMass_recast)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    (walk : PeriodWalk grid base owner source)
    {sourceStart periodStart : Nat} {tolerance : Rational} {positive : 0 < tolerance}
    (selection : PrimitiveSelection walk sourceStart periodStart tolerance positive)
    {point : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := point) (finish := point))
    {floor stage sourceFloor sourceStage periodStage : Nat}
    (targets : {value : CellEndpoints.Targets chain.path sourceStage //
      value = CellEndpoints.Targets.build chain.path sourceStage})
    (work : PolynomialWork selection.1.val.requests.covered floor (Jets.Specification.valueSpecification parameter 0))
    (models : work.Models stage)
    (prepared : PreparedParents (parameter := parameter) (frame := frame)
      selection.1.val.requests.covered sourceFloor targets.val)
    (sourceLater : selection.2.1.val.stage ≤ sourceStage) (periodLater : selection.2.2.val.stage ≤ periodStage)

/-- Exact actual programme, request, source observation, whole Work/Models and their independent stages. -/
@[expose] def HolomorphicComparison.Inputs : Type _ :=
  {inputs : PeriodWalk grid base owner source × PrimitiveSelection walk sourceStart periodStart tolerance positive ×
      CenteredPathChain
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
        (start := point) (finish := point) ×
      {value : CellEndpoints.Targets chain.path sourceStage //
        value = CellEndpoints.Targets.build chain.path sourceStage} ×
      PolynomialWork selection.1.val.requests.covered floor (Jets.Specification.valueSpecification parameter 0) ×
      work.Models stage × PreparedParents selection.1.val.requests.covered sourceFloor targets.val ×
      (Nat × Nat × Nat × Nat × Nat) //
    inputs = (walk, selection, chain, targets, work, models, prepared,
      (floor, stage, sourceFloor, sourceStage, periodStage)) ∧
      selection.2.1.val.stage ≤ sourceStage ∧ selection.2.2.val.stage ≤ periodStage}

/-- Whole original source/model cache transports with the derived genuine old-programme comparison bound. -/
@[expose] def HolomorphicComparison : Type _ :=
  HolomorphicComparison.Inputs (periodStage := periodStage) walk selection chain targets work models prepared ×
  (Σ sourceView : {value : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor targets.val //
    value = prepared.castCovered (walk.primitiveRequest_covered
      (Field.div_pos_direct positive (natCast_pos_direct (n := 64) (Nat.zero_lt_succ 63)))
      selection.1.val selection.1.property)},
  Σ _fixed : {value : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor
      (CellEndpoints.Targets.build chain.path sourceStage) //
    value = sourceView.val.castTargets targets.property},
  Σ viewedWork : {value : PolynomialWork
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
      (Jets.Specification.valueSpecification parameter 0) // HEq value work},
  Σ _viewedModels : {value : viewedWork.val.Models stage // HEq value models ∧
    (PathModel.mk (PolynomialWork.Models.cells
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
        viewedWork.val value)).integralSample =
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample},
  {bound : Rational // bound = 2 * (tolerance + 16 *
      (Geometric.Basic.quarterRadius 1 stage + targets.val.localBound) * movementMass
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))) ∧
    normSq (((walk.program 0).integral.model periodStage).integralSample -
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered
        work models)).integralSample) < bound})

/-- Two actual scalar comparisons retain their independent source and programme allowances. -/
private theorem source_model_bound (program source model : Canonical) (sourceAllowance modelAllowance : Rational)
    (sourceBound : normSq (source - program) < sourceAllowance)
    (modelBound : normSq (model - source) ≤ modelAllowance) :
    normSq (program - model) < 2 * (sourceAllowance + modelAllowance) := by
  have reverseSource : normSq (program - source) < sourceAllowance := by
    rewrite [show program - source = -(source - program) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact sourceBound
  have reverseModel : normSq (source - model) ≤ modelAllowance := by
    rewrite [show source - model = -(model - source) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact modelBound
  rewrite [show program - model = (program - source) + (source - model) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
      ((Arithmetic.add_lt_add_right_direct reverseSource _).trans_le
        (Arithmetic.add_le_add_direct (Basic.le_refl _) reverseModel)))

/-- The actual cached source and model views pay each later original programme sample without a new observation. -/
private theorem sample_bound
    (sourceView : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor targets.val)
    (fixed : {value : PreparedParents
        (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor
        (CellEndpoints.Targets.build chain.path sourceStage) // value = sourceView.castTargets targets.property})
    (actualWork : PolynomialWork
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
      (Jets.Specification.valueSpecification parameter 0))
    (actualModels : actualWork.Models stage)
    (integralEq : (PathModel.mk (PolynomialWork.Models.cells
        (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
        actualWork actualModels)).integralSample =
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample)
    (sourceAfter : selection.2.1.val.stage ≤ sourceStage) (periodAfter : selection.2.2.val.stage ≤ periodStage) :
    normSq (((walk.program 0).integral.model periodStage).integralSample -
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample) <
      2 * (tolerance + 16 * (Geometric.Basic.quarterRadius 1 stage + targets.val.localBound) * movementMass
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))) := by
  have sourcePath := PreparedParents.sources_castTargets
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
    sourceView targets.property chain
  have oldPaid := walk.primitiveSelection_sample selection chain sourceStage periodStage fixed.val
    sourceAfter periodAfter
  have fixedScalar := congrArg (fun actual : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor
      (CellEndpoints.Targets.build chain.path sourceStage) =>
    (PathModel.mk ((PreparedParents.sources
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
      actual chain).cells 0)).integralSample) fixed.property
  have sourceScalar := fixedScalar.trans
    (congrArg (fun actual => (PathModel.mk (actual.cells 0)).integralSample) sourcePath)
  have sourcePaid := Eq.mp (congrArg (fun actual : Canonical => normSq (actual -
    ((walk.program 0).integral.model periodStage).integralSample) < tolerance) sourceScalar) oldPaid
  have modelPaid := PreparedParents.polynomial_integral_difference_le
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) 0
    actualWork actualModels sourceView chain
  let charge := 16 * (Geometric.Basic.quarterRadius 1 stage + targets.val.localBound) * movementMass
    (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
  have both := source_model_bound
    (((walk.program 0).integral.model periodStage).integralSample)
    ((PathModel.mk ((PreparedParents.sources
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
      sourceView chain).cells 0)).integralSample)
    ((PathModel.mk (PolynomialWork.Models.cells
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
      actualWork actualModels)).integralSample)
    tolerance charge sourcePaid modelPaid
  have original := Eq.mp (congrArg (fun actual : Canonical =>
    normSq (((walk.program 0).integral.model periodStage).integralSample - actual) <
      2 * (tolerance + charge)) integralEq) both
  exact original

/-- Compare the original dx/y programme sample with the supplied high-floor model using ONE source cache. -/
def compareHolomorphic :
    HolomorphicComparison (periodStage := periodStage) walk selection chain targets work models prepared :=
  let coverEq := walk.primitiveRequest_covered
    (Field.div_pos_direct positive (natCast_pos_direct (n := 64) (Nat.zero_lt_succ 63)))
    selection.1.val selection.1.property
  let sourceView : {value : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor targets.val //
      value = prepared.castCovered coverEq} := ⟨prepared.castCovered coverEq, rfl⟩
  let fixed : {value : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor
      (CellEndpoints.Targets.build chain.path sourceStage) //
      value = sourceView.val.castTargets targets.property} :=
    ⟨sourceView.val.castTargets targets.property, rfl⟩
  PolynomialWork.Models.withCovered coverEq work models
    (fun viewedWork workHEq viewedModels modelsHEq integralEq =>
      let inputs : HolomorphicComparison.Inputs (periodStage := periodStage) walk selection chain targets work models
        prepared :=
        ⟨(walk, selection, chain, targets, work, models, prepared,
          (floor, stage, sourceFloor, sourceStage, periodStage)), rfl, sourceLater, periodLater⟩
      let actualWork : {value : PolynomialWork
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
          (Jets.Specification.valueSpecification parameter 0) // HEq value work} := ⟨viewedWork, workHEq⟩
      let actualModels : {value : actualWork.val.Models stage // HEq value models ∧
          (PathModel.mk (PolynomialWork.Models.cells
            (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
              actualWork.val value)).integralSample =
            (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample} :=
        ⟨viewedModels, modelsHEq, integralEq⟩
      let charge := 16 * (Geometric.Basic.quarterRadius 1 stage + targets.val.localBound) * movementMass
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      have original := sample_bound (walk := walk) (selection := selection) (chain := chain)
        (targets := targets) (work := work) (models := models)
        sourceView.val fixed actualWork.val actualModels.val integralEq sourceLater periodLater
      ⟨inputs, sourceView, fixed, actualWork, actualModels, 2 * (tolerance + charge), rfl, original⟩)

namespace HolomorphicComparison

variable {walk selection chain targets work models prepared}
    (kept : HolomorphicComparison (periodStage := periodStage) walk selection chain targets work models prepared)

/-- Read the complete actual input owner/cache product and all five independent indices. -/
@[expose] def inputs : PeriodWalk grid base owner source × PrimitiveSelection walk sourceStart periodStart tolerance
  positive ×
      CenteredPathChain
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
        (start := point) (finish := point) ×
      {value : CellEndpoints.Targets chain.path sourceStage //
        value = CellEndpoints.Targets.build chain.path sourceStage} ×
      PolynomialWork selection.1.val.requests.covered floor (Jets.Specification.valueSpecification parameter 0) ×
      work.Models stage × PreparedParents selection.1.val.requests.covered sourceFloor targets.val ×
      (Nat × Nat × Nat × Nat × Nat) :=
  kept.1.val

/-- The supplied old period, source, target and model owners remain exactly the original inputs. -/
theorem inputs_eq : kept.inputs = (walk, selection, chain, targets, work, models, prepared,
    (floor, stage, sourceFloor, sourceStage, periodStage)) := kept.1.property.1

/-- Read the SAME original source bank after its actual whole-cover transport. -/
@[expose] def sourceView : PreparedParents
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor targets.val :=
      kept.2.1.val

/-- Read the actual fixed given observation after its whole original cover and target transports. -/
@[expose] def observation : PreparedParents
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) sourceFloor
    (CellEndpoints.Targets.build chain.path sourceStage) := kept.2.2.1.val

/-- The fixed observation retains its actual original target-index transport. -/
theorem observation_eq : kept.observation = kept.sourceView.castTargets targets.property := kept.2.2.1.property

/-- Read the SAME high-floor comparison work under its complete original-source-cover transport. -/
@[expose] def viewedWork : PolynomialWork
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
    (Jets.Specification.valueSpecification parameter 0) := kept.2.2.2.1.val

/-- Read the actual dependent model cache under that same joint whole-cover transport. -/
@[expose] def viewedModels : kept.viewedWork.Models stage := kept.2.2.2.2.1.val

/-- The joint transport preserves the supplied original high-floor integral sample. -/
theorem model_integral : (PathModel.mk (PolynomialWork.Models.cells
    (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
      kept.viewedWork kept.viewedModels)).integralSample =
    (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample :=
  kept.2.2.2.2.1.property.2

/-- Read the computed model/source/programme charge at the unchanged original stages. -/
@[expose] def bound : Rational := kept.2.2.2.2.2.val

/-- The charge retains the old period tolerance and independent high-floor model/source allowance. -/
theorem bound_eq : kept.bound = 2 * (tolerance + 16 *
    (Geometric.Basic.quarterRadius 1 stage + targets.val.localBound) * movementMass
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))) :=
  kept.2.2.2.2.2.property.1

/-- The true original dx/y programme model and supplied high-floor model satisfy the derived bound. -/
theorem accurate : normSq (((walk.program 0).integral.model periodStage).integralSample -
    (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample) <
      kept.bound := kept.2.2.2.2.2.property.2

/-- Every later original programme sample uses the SAME fixed source and high-floor model caches. -/
theorem later_bound (laterStage : Nat) (periodAfter : selection.2.2.val.stage ≤ laterStage) :
    normSq (((walk.program 0).integral.model laterStage).integralSample -
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample) <
      kept.bound := by
  have actual := sample_bound (walk := walk) (selection := selection) (chain := chain)
    (periodStage := laterStage) (targets := targets) (work := work) (models := models)
    kept.sourceView ⟨kept.observation, kept.observation_eq⟩ kept.viewedWork kept.viewedModels kept.model_integral
    kept.1.property.2.1 periodAfter
  exact Eq.mpr (congrArg (fun amount : Rational => normSq
    (((walk.program 0).integral.model laterStage).integralSample -
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered
        work models)).integralSample) < amount)
    kept.bound_eq) actual

include kept in
/-- The retained source search pays the actual high-floor model/source contribution, including zero movement. -/
theorem model_charge_lt (modelLater : selection.2.1.val.stage ≤ stage) :
    16 * (Geometric.Basic.quarterRadius 1 stage + targets.val.localBound) * movementMass
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) <
      tolerance / 4 := by
  let mass := movementMass walk.initial.state.parents
  have nonnegative : 0 ≤ 16 * mass :=
    Arithmetic.mul_nonneg_direct (natCast_le_direct (Nat.zero_le 16))
      (movementMass_nonnegative walk.initial.state.parents)
  have modelPaid : 16 * mass * Geometric.Basic.quarterRadius 1 stage ≤
      Geometric.Basic.quarterRadius (16 * mass) selection.2.1.val.stage := by
    apply (show 16 * mass * Geometric.Basic.quarterRadius 1 stage =
      Geometric.Basic.quarterRadius (16 * mass) stage by
        rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1).trans_le
    exact Geometric.Basic.quarterRadius_antitone nonnegative modelLater
  have sourcePaid := (targets.val.mul_localBound_le_quarterRadius (16 * mass) nonnegative).trans
    (Geometric.Basic.quarterRadius_antitone nonnegative kept.1.property.2.1)
  have chargeEq : 16 * (Geometric.Basic.quarterRadius 1 stage + targets.val.localBound) * movementMass
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) =
      16 * mass * Geometric.Basic.quarterRadius 1 stage + 16 * mass * targets.val.localBound := by
    rewrite [movementMass_recast]
    ring1
  have sumEq : Geometric.Basic.quarterRadius (16 * mass) selection.2.1.val.stage +
      Geometric.Basic.quarterRadius (16 * mass) selection.2.1.val.stage =
      Geometric.Basic.quarterRadius (32 * mass) selection.2.1.val.stage := by
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact (chargeEq.trans_le ((Arithmetic.add_le_add_direct modelPaid sourcePaid).trans_eq sumEq)).trans_lt
    (selection.2.1.val.later_accurate (Nat.le_refl selection.2.1.val.stage))

include kept in
/-- The SAME actual old programme and high-floor model meet the strict internally selected source/period payment. -/
theorem paid (modelLater : selection.2.1.val.stage ≤ stage) :
    normSq (((walk.program 0).integral.model periodStage).integralSample -
      (PathModel.mk (PolynomialWork.Models.cells selection.1.val.requests.covered work models)).integralSample) <
      2 * (tolerance + tolerance / 4) :=
  kept.accurate.trans (kept.bound_eq.trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (natCast_pos_direct (n := 2) (Nat.zero_lt_succ 1))
      (Arithmetic.add_lt_add_left_direct (kept.model_charge_lt modelLater) tolerance)))

end HolomorphicComparison

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
