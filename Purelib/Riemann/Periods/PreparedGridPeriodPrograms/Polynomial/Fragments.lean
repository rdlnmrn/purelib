module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Subedges
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial.Subedges
import Purelib.Approximation.Gaussian.Equivalence

/-! # Given polynomial programme models on their actual rooted child source

The parent model bank is a GIVEN cache with its original whole factory.
The original withParents operation reindexes the complete cover/work/models
jointly. The actual rooted subedge comparison then pays the given child
source bank without executing a model, period, source or cover producer.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source}

variable (spine : PolynomialSpine walk) {polynomialFloor polynomialStage : Nat}
variable (value : PolynomialValue walk spine polynomialFloor 1)
variable (parentModels : {models : value.1.Models polynomialStage // models = value.1.models polynomialStage})
variable {children : List (CenteredEdge (Fibre.frameCurve frame) source)}
variable (refinement : RootSubedgeRefinement walk.initial.state.parents children)
variable {count floor : Nat} (covered : CoveredParents count children)
variable {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable (prepared : PreparedParents covered floor targets)
variable {point : LiftedPoint 2} (chain : CenteredPathChain children (start := point) (finish := point))

/-- Actual supplied canonical/source owners, exact transported model caches, and their computed signed-model bound.

The original period, spine, polynomial programme and parent model factory
remain data. All viewed cover/work/model values are the SAME complete
objects under original parent-list equality, with whole HEq readbacks.
-/
abbrev SubedgeModelComparison :=
  {inputs : PeriodWalk grid base owner source × PolynomialSpine walk ×
      PolynomialValue walk spine polynomialFloor 1 ×
      {models : value.1.Models polynomialStage // models = value.1.models polynomialStage} ×
      RootSubedgeRefinement walk.initial.state.parents children ×
      CoveredParents count children × PreparedParents covered floor targets ×
      CenteredPathChain children (start := point) (finish := point) ×
      CellEndpoints.Targets original stage × (Nat × Nat × Nat × Nat × Nat) //
    inputs = (walk, spine, value, parentModels, refinement, covered, prepared, chain, targets,
      (polynomialFloor, polynomialStage, stage, floor, count))} ×
  (Σ viewedCover : {actual : CoveredParents 1 (walk.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) //
      actual = spine.covered.castParents spine.parents_eq ∧ HEq actual spine.covered},
  Σ viewedWork : {actual : PolynomialWork viewedCover.val polynomialFloor
      (Jets.Specification.valueSpecification parameter 1) // HEq actual value.1},
  Σ viewedModels : {actual : viewedWork.val.Models polynomialStage // HEq actual parentModels.val},
  {bound : Rational // bound = 16 * (targets.localBound + Geometric.Basic.quarterRadius 1 polynomialStage) *
      movementMass children ∧
    (PathModel.mk (PolynomialWork.Models.cells viewedCover.val viewedWork.val viewedModels.val)).integralSample =
      (value.2.val.integral.model polynomialStage).integralSample ∧
    Norm.Basic.normSq ((value.2.val.integral.model polynomialStage).integralSample -
      (PathModel.mk ((PreparedParents.sources covered prepared chain).cells 1)).integralSample) ≤ bound})

/-- Compare the GIVEN canonical coordinate programme model with the GIVEN actual child-source bank.

Only the complete original withParents transport and original rooted
polynomial finite fold run. The source and canonical model factories occur
in proof/readback contracts; no source, model or period factory is executed
for data. Both independent model/source stages remain literal inputs.
-/
def compareSubedgeModels : SubedgeModelComparison spine value parentModels refinement covered prepared chain :=
  PolynomialWork.Models.withParents spine.parents_eq spine.covered value.1 parentModels.val
    (fun viewedCover coverEq coverHEq viewedWork workHEq viewedModels modelsHEq integralEq =>
      let inputs : {inputs : PeriodWalk grid base owner source × PolynomialSpine walk ×
          PolynomialValue walk spine polynomialFloor 1 ×
          {models : value.1.Models polynomialStage // models = value.1.models polynomialStage} ×
          RootSubedgeRefinement walk.initial.state.parents children × CoveredParents count children ×
          PreparedParents covered floor targets ×
          CenteredPathChain children (start := point) (finish := point) ×
          CellEndpoints.Targets original stage × (Nat × Nat × Nat × Nat × Nat) //
          inputs = (walk, spine, value, parentModels, refinement, covered, prepared, chain, targets,
            (polynomialFloor, polynomialStage, stage, floor, count))} :=
        ⟨(walk, spine, value, parentModels, refinement, covered, prepared, chain, targets,
          (polynomialFloor, polynomialStage, stage, floor, count)), rfl⟩
      let cover : {actual : CoveredParents 1 (walk.initial.state.parents.map
          (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))) //
          actual = spine.covered.castParents spine.parents_eq ∧ HEq actual spine.covered} :=
        ⟨viewedCover, coverEq, coverHEq⟩
      let work : {actual : PolynomialWork cover.val polynomialFloor
          (Jets.Specification.valueSpecification parameter 1) // HEq actual value.1} := ⟨viewedWork, workHEq⟩
      let models : {actual : work.val.Models polynomialStage // HEq actual parentModels.val} :=
        ⟨viewedModels, modelsHEq⟩
      have actualModel := (walk.polynomialValue_model value polynomialStage).trans
        (congrArg PathModel.mk (PolynomialWork.model_cells value.1 value.1.models polynomialStage))
      have givenModel := congrArg (fun actual : value.1.Models polynomialStage =>
        (PathModel.mk (PolynomialWork.Models.cells spine.covered value.1 actual)).integralSample)
        parentModels.property
      have scalarEq := integralEq.trans (givenModel.trans
        (congrArg PathModel.integralSample actualModel).symm)
      have bounded := PreparedParents.rooted_polynomial_error_le
        (parameter := parameter) (frame := frame) (basis := source)
        (parentBasis := PeriodMatrix.standardDifferential (0 : Fin 1))
        cover.val work.val models.val refinement covered prepared chain
      let bound := 16 * (targets.localBound + Geometric.Basic.quarterRadius 1 polynomialStage) * movementMass children
      ⟨inputs, cover, work, models, bound, rfl, scalarEq,
        Eq.mp (congrArg (fun actual : Canonical => Norm.Basic.normSq (actual -
          (PathModel.mk ((PreparedParents.sources covered prepared chain).cells 1)).integralSample) ≤ bound)
          scalarEq) bounded⟩)

namespace SubedgeModelComparison

variable {spine value parentModels refinement covered prepared chain}
variable (kept : SubedgeModelComparison spine value parentModels refinement covered prepared chain)

/-- Read the SAME actual original canonical parent model bank before its whole nominal transport. -/
@[expose] def originalModels : value.1.Models polynomialStage := kept.1.val.2.2.2.1.val

/-- The same original parent model cache retains its actual whole model factory. -/
theorem originalModels_factory : kept.originalModels = value.1.models polynomialStage :=
  (congrArg (fun inputs : PeriodWalk grid base owner source × PolynomialSpine walk ×
      PolynomialValue walk spine polynomialFloor 1 ×
      {models : value.1.Models polynomialStage // models = value.1.models polynomialStage} ×
      RootSubedgeRefinement walk.initial.state.parents children × CoveredParents count children ×
      PreparedParents covered floor targets ×
      CenteredPathChain children (start := point) (finish := point) ×
      CellEndpoints.Targets original stage × (Nat × Nat × Nat × Nat × Nat) => inputs.2.2.2.1.val)
    kept.1.property).trans parentModels.property

/-- Read the SAME actual child-source preparation, with its original bound and query/Point owners. -/
@[expose] def sourcePreparation : PreparedParents covered floor targets := kept.1.val.2.2.2.2.2.2.1

/-- Read the SAME actual source Targets object, rather than recreating its allowance or stage. -/
@[expose] def sourceTargets : CellEndpoints.Targets original stage := kept.1.val.2.2.2.2.2.2.2.2.1

/-- Read the computed finite source/parent bound, without another comparison. -/
@[expose] def bound : Rational := kept.2.2.2.2.val

/-- The computed bound retains the original independent canonical stage and source allowance. -/
theorem bound_eq : kept.bound = 16 * (targets.localBound + Geometric.Basic.quarterRadius 1 polynomialStage) *
    movementMass children := kept.2.2.2.2.property.1

/-- The actual old programme sample and actual child-source integral satisfy the retained signed-refinement bound. -/
theorem accurate : Norm.Basic.normSq ((value.2.val.integral.model polynomialStage).integralSample -
    (PathModel.mk ((PreparedParents.sources covered prepared chain).cells 1)).integralSample) ≤ kept.bound :=
  kept.2.2.2.2.property.2.2

end SubedgeModelComparison

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
