module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # The same retained primitive requests compare source value-zero cells with grid periods

Both original input owners remain: the PeriodWalk keeps its initial closed
state and cover, and the source bank keeps its actual prepared cells.
Request-patch identities follow the original controlled acquisition. They
transport only the source product's indices, without preparing it again.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedCoveredParentLists
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_recast)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore
  (standardDifferentials standardDifferential_mem_standardDifferentials)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodTail)
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}

/-- The source error scale reads only the same original geometric mass, without constructing another recast list. -/
theorem sourceErrorScale_eq (walk : PeriodWalk grid base owner source) :
    PreparedParents.errorScale (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) =
        32 * movementMass walk.initial.state.parents := by
  have exactMass := PreparedParents.countCost_eq_movementMass
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
    (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
  calc
    _ = 32 * ((walk.initial.state.parents.map
        (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))).length : Rational) *
        PreparedParents.displacementCost
          (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) := rfl
    _ = 32 * movementMass
        (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) := by
      rewrite [← exactMass]
      ring1
    _ = _ := congrArg (32 * ·)
      (movementMass_recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.initial.state.parents)

/-- An original primitive-request factory identifies its patch spine with the same retained initial cover. -/
theorem primitiveRequest_covered (walk : PeriodWalk grid base owner source) {target : Rational}
    (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) :
    request.requests.covered = CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered :=
  (congrArg (fun retained => retained.requests.covered) factory_eq).trans
    (Riemann.Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest.acquire_covered
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
      (Riemann.Integration.PreparedDirectDyadicRefinements.allParentsProper_map_recast walk.initial.state.proper)
      target positive 0)

/-- View the same complete original source bank on its actual retained primitive request's patch spine. -/
def primitiveSources (walk : PeriodWalk grid base owner source) {target : Rational} (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) {floor : Nat}
    {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor targets) :
    PreparedParents request.requests.covered floor targets :=
  prepared.castCovered
    (walk.primitiveRequest_covered (parameter := parameter) (frame := frame) positive request factory_eq).symm

/-- The request-patch view keeps the complete supplied source bank heterogeneously. -/
private theorem packaged_primitiveSources_heq (walk : PeriodWalk grid base owner source)
    {target : Rational} (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) {floor : Nat}
    {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor targets) :
    HEq (walk.primitiveSources (parameter := parameter) (frame := frame)
      positive request factory_eq prepared) prepared :=
  prepared.castCovered_heq
    (walk.primitiveRequest_covered (parameter := parameter) (frame := frame) positive request factory_eq).symm

/-- The request-patch view keeps the complete supplied source bank heterogeneously. -/
theorem primitiveSources_heq (walk : PeriodWalk grid base owner source)
    {target : Rational} (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) {floor : Nat}
    {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor targets) :
    HEq (walk.primitiveSources (parameter := parameter) (frame := frame)
      positive request factory_eq prepared) prepared :=
  packaged_primitiveSources_heq walk positive request factory_eq prepared

/-- The whole original source path is unchanged by its acquired request-patch index view. -/
private theorem packaged_primitiveSources_sources (walk : PeriodWalk grid base owner source)
    {target : Rational} (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) {floor : Nat}
    {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor targets)
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := start) (finish := finish)) :
    PreparedParents.sources request.requests.covered
      (walk.primitiveSources (parameter := parameter) (frame := frame) positive request factory_eq prepared) chain =
      PreparedParents.sources
        (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) prepared chain :=
  prepared.sources_castCovered
    (walk.primitiveRequest_covered (parameter := parameter) (frame := frame) positive request factory_eq).symm chain

/-- The whole original source path is unchanged by its acquired request-patch index view. -/
theorem primitiveSources_sources (walk : PeriodWalk grid base owner source)
    {target : Rational} (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) {floor : Nat}
    {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor targets)
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := start) (finish := finish)) :
    PreparedParents.sources request.requests.covered
      (walk.primitiveSources (parameter := parameter) (frame := frame) positive request factory_eq prepared) chain =
      PreparedParents.sources
        (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) prepared chain :=
  packaged_primitiveSources_sources walk positive request factory_eq prepared chain

/-- The acquired original primitive sum and actual source value-zero bank satisfy their derived finite mass bound. -/
theorem primitive_source_error_le (walk : PeriodWalk grid base owner source)
    {target : Rational} (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) {floor : Nat}
    {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor targets)
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := start) (finish := finish)) :
    Norm.Basic.normSq (request.primitiveSum -
      (PathModel.mk
        ((PreparedParents.sources
          (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
          prepared chain).cells 0)).integralSample) ≤
      16 * (targets.localBound + request.coefficientTarget) *
        movementMass
          (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) := by
  have original := PreparedParents.primitive_error_le
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
    (count := 1) (floor := floor) (baseStart := first) (baseFinish := last)
    (original := original) (stage := stage) (targets := targets) request.requests
    (walk.primitiveSources (parameter := parameter) (frame := frame) positive request factory_eq prepared)
    (by rfl) request.coefficient_accurate chain
  rewrite [walk.primitiveSources_sources (parameter := parameter) (frame := frame)
    positive request factory_eq prepared chain] at original
  have increments : request.primitiveSum = gaussianSum request.requests.increments :=
    request.primitiveSum_eq.trans (congrArg gaussianSum request.increments_eq)
  rewrite [← increments] at original
  have mass := PreparedParents.countCost_eq_movementMass
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
    (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
  exact original.trans_eq (by rewrite [← mass]; ring1)

/-- The original source stage and every paid canonical period-tail stage compare through the same primitive sum. -/
theorem source_period_error_le (walk : PeriodWalk grid base owner source)
    {target : Rational} (positive : 0 < target)
    (request : ControlledSumRequest
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) 1 target)
    (factory_eq : request = walk.primitiveRequest 0 target positive) {floor : Nat}
    {point : LiftedPoint 2}
    (chain : CenteredPathChain
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
      (start := point) (finish := point)) (sourceStage : Nat)
    (prepared : PreparedParents
      (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered) floor
      (CellEndpoints.Targets.build chain.path sourceStage)) {minimum : Nat}
    (tail : PeriodTail walk.initial (standardDifferentials 1) (PeriodMatrix.standardDifferential (0 : Fin 1))
      request minimum) (periodStage : Nat) (later : tail.stage ≤ periodStage) :
    Norm.Basic.normSq
      ((PathModel.mk
          ((PreparedParents.sources
            (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
            prepared chain).cells 0)).integralSample - ((walk.program 0).integral.model periodStage).integralSample) ≤
      Geometric.Basic.quarterRadius
        (PreparedParents.errorScale (parameter := parameter) (frame := frame)
          (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
          (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))))
        sourceStage + 18 * target := by
  let mass := movementMass
    (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
  have sourceBound := walk.primitive_source_error_le (parameter := parameter) (frame := frame)
    positive request factory_eq prepared chain
  have canonical := tail.accurate (standardDifferential_mem_standardDifferentials (0 : Fin 1)) periodStage later
  rewrite [← Norm.Basic.normSq_eq_canonical] at canonical
  rewrite [← RootClosedState.sample_eq_flat walk.initial (standardDifferentials 1)
    (PeriodMatrix.standardDifferential (0 : Fin 1)) periodStage] at canonical
  rewrite [← walk.state_eq periodStage, ← walk.program_model 0 periodStage] at canonical
  have triangle := Norm.Bounds.normSq_sub_le_via
    (PathModel.mk
      ((PreparedParents.sources
        (CoveredParents.recast (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.covered)
        prepared chain).cells 0)).integralSample
    request.primitiveSum ((walk.program 0).integral.model periodStage).integralSample
  have sourceReverse := sourceBound
  rewrite [Norm.Bounds.normSq_sub_symm] at sourceReverse
  have joined := triangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct sourceReverse canonical.le) (by decide +kernel))
  have primitivePayment := request.mass_mul_coefficientTarget_le
  have coefficientPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct primitivePayment
    (by decide +kernel : (0 : Rational) ≤ 32)
  have geometryPayment := (CellEndpoints.Targets.build chain.path sourceStage).mul_localBound_le_quarterRadius
    (PreparedParents.errorScale (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))))
    (PreparedParents.errorScale_nonnegative (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))))
  have scale : PreparedParents.errorScale (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) =
        32 * mass := by
    dsimp only [PreparedParents.errorScale, mass]
    rewrite [← PreparedParents.countCost_eq_movementMass (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (walk.initial.state.parents.map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))]
    ring1
  rewrite [scale] at geometryPayment
  calc
    _ ≤ 2 * (16 * ((CellEndpoints.Targets.build chain.path sourceStage).localBound + request.coefficientTarget) *
        mass + target) := joined
    _ = 32 * mass * (CellEndpoints.Targets.build chain.path sourceStage).localBound +
        (32 * (mass * request.coefficientTarget) + 2 * target) := by ring1
    _ ≤ Geometric.Basic.quarterRadius (32 * mass) sourceStage +
        (32 * (target / 2) + 2 * target) := Arithmetic.add_le_add_direct geometryPayment
          (Arithmetic.add_le_add_direct coefficientPayment (Data.Rat.Fraction.Order.Basic.le_refl _))
    _ = Geometric.Basic.quarterRadius (32 * mass) sourceStage +
        (16 * ((target / 2) * 2) + 2 * target) := by ring1
    _ = _ := by
      rewrite [Data.Rat.Fraction.Field.div_mul_cancel_of_ne target 2 (by decide +kernel), scale]
      ring1

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

end
