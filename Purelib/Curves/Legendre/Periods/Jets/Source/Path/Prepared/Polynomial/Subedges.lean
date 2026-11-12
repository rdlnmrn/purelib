module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Polynomial
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Comparison
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Cast
import Purelib.Tactic.Ring

/-! # A retained coordinate-numerator polynomial on actual rooted child sources

The original parent model retains its numerator, inverse, powers, primitive
and spatial pullback. Its existing observation factory is queried at the
actual parent location of each child point. Original signed root relations
compare that observation with the child's independent value-one query;
finite polynomial residuals then control the actual child integral.
-/

public section

attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge)
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedDirectDyadicRefinements
  (recastPreparedEdge_rootName)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis parentBasis : Differential 1}
    {parent child : CenteredEdge (Fibre.frameCurve frame) basis} {count childCount floor polynomialFloor : Nat}
    {parentPatch : PreparedPatch (recastCenteredEdge parentBasis parent)}
    {parentCovered : (parentPatch.neighborhood count).box.Contains
      ((recastCenteredEdge parentBasis parent).edge.point 1)}
    {bounds : UniformBounds (parentPatch.neighborhood count)}
    {coordinate : Spatial.Coordinate (startPoint (recastCenteredEdge parentBasis parent)).coordinate
      (finishPoint (recastCenteredEdge parentBasis parent)).coordinate}
    {allowance : Rational} {positive : 0 < allowance}
    {request : UniformRequest bounds 0
      ((Specification.valueSpecification parameter 1).numerator.scale
        (Specification.valueSpecification parameter 1).scale) polynomialFloor (allowance / 4)}
    {patch : PreparedPatch child} {covered : (patch.neighborhood childCount).box.Contains (child.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

include parentCovered in
/-- Actual same-point observations compare the child value-one coefficient with the retained parent spatial coefficient.

The child query is given with its complete original factory and six signed
attachments. The parent model observes its SAME retained primitive at the
rooted parent fraction, using one genuine Point on its original patch.
Different local parameters and independent reading states remain distinct.
-/
theorem subedge_polynomial_valueOne_difference_le
    (model : PolynomialModel (curve := Fibre.frameCurve frame)
      (patch := parentPatch.neighborhood count) (bounds := bounds)
      (differential := Specification.valueSpecification parameter 1) request coordinate positive)
    (relation : RootSubedge parent child) (prepared : PreparedParent patch childCount floor covered targets)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : RootedQuery (frame := frame) prepared input inside) :
    Norm.Basic.normSq
      (Evaluation.eval prepared.preparation.cell.models.valueOne.model.polynomial ⟨input, 0⟩ -
        model.primitive.coefficient.eval (prepared.preparation.cell.models.coordinate.point input)) ≤
      8 * (prepared.preparation.cell.models.valueOne.model.localAllowance + allowance) := by
  let location := relation.location input inside
  have parentInside := coordinate.point_inside (start_inside parentPatch count)
    (finish_inside parentPatch count parentCovered) location.inside.1 location.inside.2
  let sample := PolynomialWork.Models.points parentPatch parentCovered coordinate
    location.fraction location.inside.1 location.inside.2
  let parentQuery := model.observe (curve := Fibre.frameCurve frame)
    (differential := Specification.valueSpecification parameter 1) (coordinate := coordinate)
    (request := request) (positive := positive) (Specification.valueSpecification_denominatorPairs parameter 1)
    (liftedCell (recastCenteredEdge parentBasis parent)) location.fraction sample parentInside
  have queryName := model.observe_root_name (curve := Fibre.frameCurve frame)
    (differential := Specification.valueSpecification parameter 1) (coordinate := coordinate)
    (request := request) (positive := positive) (Specification.valueSpecification_denominatorPairs parameter 1)
    (liftedCell (recastCenteredEdge parentBasis parent)) location.fraction sample parentInside
  have parentPoint : (recastCenteredEdge parentBasis parent).edge.point location.fraction =
      coordinate.point location.fraction :=
    (coordinate_point_eq (parameter := parameter) (frame := frame) (basis := parentBasis)
      (parent := recastCenteredEdge parentBasis parent) coordinate location.fraction).symm
  have parentRoot := parentPatch.point_equivalent_at count location.fraction location.inside
    parentPoint parentInside sample
  have parentName := recastPreparedEdge_rootName parentBasis parent.edge location.fraction location.inside
  have parentAttached : NamedEquivalent (parent.edge.rootName location.fraction location.inside)
      parentQuery.algebraic.sheetValue.value.name :=
    NamedEquivalent.transport parentName queryName.symm parentRoot
  have childAttached : NamedEquivalent (child.edge.rootName input inside)
      queried.observed.valueOne.algebraic.sheetValue.value.name :=
    NamedEquivalent.transport queried.direct.name_eq.symm rfl (queried.roots.get 1)
  have roots : NamedEquivalent queried.observed.valueOne.algebraic.sheetValue.value.name
      parentQuery.algebraic.sheetValue.value.name :=
    childAttached.symm.trans ((relation.equivalent input inside).symm.trans parentAttached)
  have parentPointEq : parentQuery.algebraic.point = coordinate.point location.fraction :=
    parentQuery.algebraic.point_eq.trans
      ((model.pullback.observationPoint_eq parentQuery.observation).trans
        (congrArg coordinate.point parentQuery.parameter_eq))
  have samePoint : coordinate.point location.fraction =
      prepared.preparation.cell.models.coordinate.point input :=
    parentPoint.symm.trans (location.point_eq.trans (prepared.queryPoint_eq input).symm)
  have points : queried.observed.valueOne.algebraic.point = parentQuery.algebraic.point :=
    (queried.observed.channel_point 1).trans (samePoint.symm.trans parentPointEq.symm)
  have sumPositive : 0 < prepared.preparation.cell.models.valueOne.model.localAllowance +
      model.pullback.model.localAllowance := by
    rewrite [model.pullback.allowance_eq]
    exact Arithmetic.add_pos_of_nonneg_of_pos_direct
      prepared.preparation.cell.models.valueOne.model.localAllowance_nonneg positive
  have bounded := UniformObservation.polynomial_difference_le (curve := Fibre.frameCurve frame)
    (differential := Specification.valueSpecification parameter 1) queried.observed.valueOne parentQuery
    points roots sumPositive
  have evaluated := (model.pullback.eval_point location.fraction).trans
    (congrArg model.primitive.coefficient.eval samePoint)
  have scalar := congrArg (fun value : Canonical => Norm.Basic.normSq
    (Evaluation.eval prepared.preparation.cell.models.valueOne.model.polynomial ⟨input, 0⟩ - value)) evaluated
  rewrite [model.pullback.allowance_eq] at bounded
  exact scalar.symm.trans_le bounded

include parentCovered in
/-- Compile the SAME retained parent primitive in the actual child value-one source coordinate.

One child RootedQuery is bound for each requested rational input. Its whole
observation and signed attachment caches feed the local comparison; the
source, model, request and parent primitive are not reconstructed.
-/
def subedgePolynomialComparison
    (model : PolynomialModel (curve := Fibre.frameCurve frame)
      (patch := parentPatch.neighborhood count) (bounds := bounds)
      (differential := Specification.valueSpecification parameter 1) request coordinate positive)
    (relation : RootSubedge parent child) (prepared : PreparedParent patch childCount floor covered targets) :
    Primitive.Comparison prepared.preparation.cell.models.valueOne.model :=
  Primitive.Comparison.ofSpatialBound prepared.preparation.cell.models.valueOne.model model.primitive.primitive.value
    (Norm.Basic.normSq prepared.preparation.cell.models.valueOne.model.displacement *
      (8 * (prepared.preparation.cell.models.valueOne.model.localAllowance + allowance))) (by
      intro input inside
      let queried := RootedQuery.build (frame := frame) prepared input inside
      have bounded := subedge_polynomial_valueOne_difference_le (parentCovered := parentCovered)
        model relation prepared input inside queried
      have pointEq : Geometry.Rational.Affine.line prepared.preparation.cell.models.valueOne.model.start
          prepared.preparation.cell.models.valueOne.model.displacement input =
          prepared.preparation.cell.models.coordinate.point input := by
        change prepared.preparation.cell.models.valueOne.model.start + (⟨input, 0⟩ : Canonical) *
          (prepared.preparation.cell.models.valueOne.model.finish -
            prepared.preparation.cell.models.valueOne.model.start) = _
        rewrite [prepared.preparation.cell.models.valueOne.start_eq,
          prepared.preparation.cell.models.valueOne.finish_eq, prepared.preparation.cell.models.coordinate.point_eq]
        rfl
      have reverse := Norm.Bounds.normSq_sub_symm
        (model.primitive.coefficient.eval (prepared.preparation.cell.models.coordinate.point input))
        (Evaluation.eval prepared.preparation.cell.models.valueOne.model.polynomial ⟨input, 0⟩)
      rewrite [model.primitive.primitive.derivative_eq, pointEq, Norm.Basic.normSq_mul,
        Cast.Path.ofCoordinate, reverse]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (Norm.Basic.normSq_nonneg _))

include parentCovered in
/-- The exact parent primitive and independent actual child integral obey their two-cache displacement bound. -/
theorem subedge_polynomial_error_le
    (model : PolynomialModel (curve := Fibre.frameCurve frame)
      (patch := parentPatch.neighborhood count) (bounds := bounds)
      (differential := Specification.valueSpecification parameter 1) request coordinate positive)
    (relation : RootSubedge parent child) (prepared : PreparedParent patch childCount floor covered targets) :
    Norm.Basic.normSq (model.primitive.primitive.value.eval (child.edge.point 1) -
      model.primitive.primitive.value.eval (child.edge.point 0) -
        prepared.preparation.cell.models.valueOne.model.integralSample) ≤
      16 * (targets.localBound + allowance) * cost child := by
  let comparison := subedgePolynomialComparison (parentCovered := parentCovered) model relation prepared
  have bounded := comparison.integral_error_le
  change Norm.Basic.normSq
    ((Primitive.spatialPrimitive prepared.preparation.cell.models.valueOne.model
        model.primitive.primitive.value).eval 1 -
      (Primitive.spatialPrimitive prepared.preparation.cell.models.valueOne.model
        model.primitive.primitive.value).eval 0 -
      prepared.preparation.cell.models.valueOne.model.integralSample) ≤
      2 * (Norm.Basic.normSq prepared.preparation.cell.models.valueOne.model.displacement *
        (8 * (prepared.preparation.cell.models.valueOne.model.localAllowance + allowance))) at bounded
  have allowanceEq := prepared.preparation.cell.models.valueOne.allowance_eq.trans prepared.allowance_eq
  rewrite [Primitive.spatialPrimitive_start, Primitive.spatialPrimitive_finish,
    prepared.preparation.cell.models.valueOne.start_eq, prepared.preparation.cell.models.valueOne.finish_eq,
    allowanceEq] at bounded
  have displacement : prepared.preparation.cell.models.valueOne.model.displacement =
      (finishPoint child).coordinate - (startPoint child).coordinate := by
    change prepared.preparation.cell.models.valueOne.model.finish -
      prepared.preparation.cell.models.valueOne.model.start = _
    rewrite [prepared.preparation.cell.models.valueOne.start_eq, prepared.preparation.cell.models.valueOne.finish_eq]
    rfl
  rewrite [displacement] at bounded
  rewrite [child.edge.point_one, child.edge.point_zero]
  exact bounded.trans_eq (by
    unfold cost
    ring1)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
