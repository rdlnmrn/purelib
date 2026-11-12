module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Polynomial
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive
import Purelib.Integration.Program.Comparison
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Ordered polynomial/source programme agreement for both original value channels

The error list reads both actual occurrence products without invoking their
factories. Every head estimate is derived from the original query and Point
readbacks. Finite Cauchy summation charges the literal count and movement mass.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianNormSqSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement
  (movementSum movementMass movementMass_eq movementMass_nonnegative)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count sourceFloor polynomialFloor polynomialStage : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {sourceStage : Nat} {targets : CellEndpoints.Targets original sourceStage}

/-- Read the actual new-minus-original value samples on the same original occurrence spine. -/
private def polynomialErrors (coordinate : Fin 2) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) →
    (work : PolynomialWork covered polynomialFloor (Specification.valueSpecification parameter coordinate)) →
    work.Models polynomialStage →
    PreparedParents (parameter := parameter) (frame := frame) covered sourceFloor targets → List Canonical
  | [], .nil, _, _, _ => []
  | _ :: _, .cons _ _ covered, work, models, prepared =>
      (models.1.2.val.pullback.model.integralSample -
        (prepared.1.preparation.cell.models.cell (Specification.Table.valueIndex coordinate)).integralSample) ::
          polynomialErrors coordinate covered work.2 models.2 prepared.2

/-- Both real model products have one retained error entry for every original occurrence. -/
private theorem polynomialErrors_length (coordinate : Fin 2) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) →
    (work : PolynomialWork covered polynomialFloor (Specification.valueSpecification parameter coordinate)) →
    (models : work.Models polynomialStage) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) covered sourceFloor targets) →
    (polynomialErrors coordinate covered work models prepared).length = parents.length
  | [], .nil, _, _, _ => rfl
  | _ :: _, .cons _ _ covered, work, models, prepared =>
      congrArg Nat.succ (polynomialErrors_length coordinate covered work.2 models.2 prepared.2)

/-- The ordered error sum is the difference of both complete original path samples. -/
private theorem polynomialErrors_sum (coordinate : Fin 2) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) →
    (work : PolynomialWork covered polynomialFloor (Specification.valueSpecification parameter coordinate)) →
    (models : work.Models polynomialStage) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) covered sourceFloor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    gaussianSum (polynomialErrors coordinate covered work models prepared) =
      (PathModel.mk (PolynomialWork.Models.cells covered work models)).integralSample -
        (PathModel.mk ((sources covered prepared chain).cells
          (Specification.Table.valueIndex coordinate))).integralSample
  | [], .nil, _, _, .unit, _, _, .nil point => by
      have sample := congrArg (fun cells => (PathModel.mk cells).integralSample)
        (Path.cells_nil (parameter := parameter) point (Specification.Table.valueIndex coordinate))
      exact (show (0 : Canonical) = 0 - 0 by ring1).trans
        (congrArg (fun value : Canonical => 0 - value) sample.symm)
  | _ :: _, .cons _ _ covered, work, models, ⟨head, remaining⟩, _, _, .cons _ chain => by
      let polynomialHead := models.1.2.val.pullback.model.integralSample
      let sourceHead := (head.preparation.cell.models.cell (Specification.Table.valueIndex coordinate)).integralSample
      have sample := congrArg (fun cells => (PathModel.mk cells).integralSample)
        (Path.cells_cons head.preparation.cell (sources covered remaining chain)
          (Specification.Table.valueIndex coordinate))
      have tail := polynomialErrors_sum coordinate covered work.2 models.2 remaining chain
      change (polynomialHead - sourceHead) +
        gaussianSum (polynomialErrors coordinate covered work.2 models.2 remaining) = _
      exact (congrArg (fun value : Canonical => (polynomialHead - sourceHead) + value) tail).trans
        ((show _ = (PathModel.mk (PolynomialWork.Models.cells _ work models)).integralSample -
            (sourceHead + (PathModel.mk ((sources covered remaining chain).cells
              (Specification.Table.valueIndex coordinate))).integralSample) by
                change _ =
                  (polynomialHead +
                    (PathModel.mk (PolynomialWork.Models.cells covered work.2 models.2)).integralSample) -
                    (sourceHead + (PathModel.mk ((sources covered remaining chain).cells
                      (Specification.Table.valueIndex coordinate))).integralSample)
                ring1).trans
          (congrArg (fun value : Canonical =>
            (PathModel.mk (PolynomialWork.Models.cells _ work models)).integralSample - value) sample.symm))

/-- The genuine local query comparison pays the squared-norm error sum on the original movement spine. -/
private theorem polynomialErrors_normSum_le (coordinate : Fin 2) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) →
    (work : PolynomialWork covered polynomialFloor (Specification.valueSpecification parameter coordinate)) →
    (models : work.Models polynomialStage) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) covered sourceFloor targets) →
    gaussianNormSqSum (polynomialErrors coordinate covered work models prepared) ≤
      16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementSum parents
  | [], .nil, _, _, _ => by
      change (0 : Rational) ≤ _ * 0
      rewrite [Field.mul_zero_direct]
      exact Order.Basic.le_refl 0
  | _ :: _, .cons _ _ covered, work, models, prepared => by
      have head := PreparedParent.polynomial_value_difference_le coordinate work models prepared.1
      have tail := polynomialErrors_normSum_le coordinate covered work.2 models.2 prepared.2
      change Canonical.normSq (_ - _) +
        gaussianNormSqSum (polynomialErrors coordinate covered work.2 models.2 prepared.2) ≤ _
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact (Order.Arithmetic.add_le_add_direct head tail).trans_eq (by rewrite [movementSum]; ring1)

/-- The actual two occurrence products obey their internally derived count-and-movement comparison. -/
theorem polynomial_integral_difference_le {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (coordinate : Fin 2)
    (work : PolynomialWork covered polynomialFloor (Specification.valueSpecification parameter coordinate))
    (models : work.Models polynomialStage)
    (prepared : PreparedParents (parameter := parameter) (frame := frame) covered sourceFloor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    Norm.Basic.normSq
      ((PathModel.mk (PolynomialWork.Models.cells covered work models)).integralSample -
        (PathModel.mk ((sources covered prepared chain).cells
          (Specification.Table.valueIndex coordinate))).integralSample) ≤
      16 * (quarterRadius 1 polynomialStage + targets.localBound) * movementMass parents := by
  have original := Norm.Sum.Basic.normSq_gaussianSum_le (polynomialErrors coordinate covered work models prepared)
  rewrite [← Norm.Basic.normSq_eq_canonical, polynomialErrors_sum coordinate covered work models prepared chain,
    polynomialErrors_length coordinate covered work models prepared] at original
  have sum := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (polynomialErrors_normSum_le coordinate covered work models prepared)
    (Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le _))
  exact (original.trans sum).trans_eq (by rewrite [movementMass_eq]; ring1)

/-- Two independently floored polynomial banks compare through the SAME actual prepared source observations.

The two actual work/model owners and their primitive constants remain
independent. Both original same-cover difference laws consume the supplied
preparation. The factor-two squared-norm estimate charges both model-stage
allowances and the actual source target twice; no model or query is rebuilt.
-/
theorem polynomial_models_difference_le
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (coordinate : Fin 2)
    {firstFloor firstStage lastFloor lastStage : Nat}
    (first : PolynomialWork covered firstFloor (Specification.valueSpecification parameter coordinate))
    (firstModels : first.Models firstStage)
    (last : PolynomialWork covered lastFloor (Specification.valueSpecification parameter coordinate))
    (lastModels : last.Models lastStage)
    (prepared : PreparedParents (parameter := parameter) (frame := frame) covered sourceFloor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    Norm.Basic.normSq
      ((PathModel.mk (PolynomialWork.Models.cells covered first firstModels)).integralSample -
        (PathModel.mk (PolynomialWork.Models.cells covered last lastModels)).integralSample) ≤
      32 * (quarterRadius 1 firstStage + quarterRadius 1 lastStage + 2 * targets.localBound) *
        movementMass parents := by
  let middle := (PathModel.mk ((sources covered prepared chain).cells
    (Specification.Table.valueIndex coordinate))).integralSample
  let firstValue := (PathModel.mk (PolynomialWork.Models.cells covered first firstModels)).integralSample
  let lastValue := (PathModel.mk (PolynomialWork.Models.cells covered last lastModels)).integralSample
  have firstBound := polynomial_integral_difference_le covered coordinate first firstModels prepared chain
  have lastBound := polynomial_integral_difference_le covered coordinate last lastModels prepared chain
  have reversed : Norm.Basic.normSq (middle - lastValue) ≤
      16 * (quarterRadius 1 lastStage + targets.localBound) * movementMass parents :=
    (Norm.Bounds.normSq_sub_symm middle lastValue).trans_le lastBound
  have triangle := Norm.Bounds.normSq_add_le_two (firstValue - middle) (middle - lastValue)
  have sum := Order.Arithmetic.add_le_add_direct firstBound reversed
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sum
    (by decide : (0 : Rational) ≤ 2)
  have budget : 2 * (16 * (quarterRadius 1 firstStage + targets.localBound) * movementMass parents +
      16 * (quarterRadius 1 lastStage + targets.localBound) * movementMass parents) =
      32 * (quarterRadius 1 firstStage + quarterRadius 1 lastStage + 2 * targets.localBound) *
        movementMass parents := by ring1
  have difference : firstValue - lastValue = (firstValue - middle) + (middle - lastValue) := by ring1
  exact (Eq.mpr (congrArg (fun value : Canonical => Norm.Basic.normSq value ≤
      2 * (Norm.Basic.normSq (firstValue - middle) + Norm.Basic.normSq (middle - lastValue))) difference)
    triangle).trans (scaled.trans_eq budget)

variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} (covered : CoveredParents count parents)
    {point : LiftedPoint 2} (chain : CenteredPathChain parents (start := point) (finish := point))
    (coordinate : Fin 2)
    (work : PolynomialWork covered polynomialFloor (Specification.valueSpecification parameter coordinate))
    (models : (stage : Nat) → work.Models stage)
    (prepared : (stage : Nat) → PreparedParents (parameter := parameter) (frame := frame) covered sourceFloor
      (CellEndpoints.Targets.build chain.path stage))
    (actual : RefinementProgram)
    (actual_eq : actual = PolynomialWork.program work models
      (Specification.valueSpecification_denominatorPairs parameter coordinate))

include actual_eq in
/-- Both actual value programmes obey the same internally derived bridge scale 32G at every original request. -/
theorem polynomial_samples_close (stage : Nat) :
    Norm.Basic.normSq
      ((actual.model stage).integralSample -
        ((certified covered chain prepared (Specification.Table.valueIndex coordinate)).integral.model
          stage).integralSample) ≤
      quarterRadius (32 * movementMass parents) stage := by
  rewrite [actual_eq, PolynomialWork.program_model]
  have displayed : PolynomialWork.model work models stage =
      PathModel.mk (PolynomialWork.Models.cells covered work (models stage)) :=
    congrArg PathModel.mk (PolynomialWork.model_cells work models stage)
  rewrite [displayed]
  have readback : ((certified covered chain prepared (Specification.Table.valueIndex coordinate)).integral.model
      stage) = PathModel.mk ((sources covered (prepared stage) chain).cells
        (Specification.Table.valueIndex coordinate)) :=
    congrArg PathModel.mk (certified_cells covered chain prepared (Specification.Table.valueIndex coordinate) stage)
  rewrite [readback]
  have original := polynomial_integral_difference_le covered coordinate work (models stage) (prepared stage) chain
  have localPayment := (CellEndpoints.Targets.build chain.path stage).localBound_le_quarterRadius
  have allowances := Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl (quarterRadius 1 stage)) localPayment
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allowances (by decide +kernel : (0 : Rational) ≤ 16))
    (movementMass_nonnegative parents)
  exact original.trans (scaled.trans_eq (by simp only [quarterRadius_eq_mul_pow]; ring1))

/-- The ordinary polynomial programme and independent original source programme name the same actual value channel.

The bridge is derived from both retained request/model banks. The existing
programme comparison selects finite common floors and pays all later samples;
no equality or closeness of whole programmes is supplied as an input.
-/
def polynomial_outputEquivalent : NamedEquivalent
    actual.output.name
    (certified covered chain prepared (Specification.Table.valueIndex coordinate)).integral.output.name :=
  Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_close
    actual
    (certified covered chain prepared (Specification.Table.valueIndex coordinate)).integral
    (32 * movementMass parents)
    (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative parents))
    (polynomial_samples_close covered chain coordinate work models prepared actual actual_eq)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
