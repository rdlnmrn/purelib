module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive.Subedges
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Polynomial.Subedges
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

/-! # Given original coordinate-numerator models on a rooted child refinement

Each original bounded parent occurrence projects its own retained model's
primitive. The shared rooted fold preserves those occurrence indices and
original block chains. The complete actual parent model integral equals
its own ordered primitive increments exactly, with every constant retained.
-/

public section

attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Data.List.Map (length_map)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge RootSubedgeRefinement)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis parentBasis : Differential 1}
    {count childCount floor polynomialFloor polynomialStage : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Project the cached parent polynomial at each original occurrence, without running a model factory. -/
private def polynomialPrimitives {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parents.map (recastCenteredEdge parentBasis)))
    (work : PolynomialWork (curve := Fibre.frameCurve frame) covered polynomialFloor
      (Specification.valueSpecification parameter 1))
    (models : PolynomialWork.Models (curve := Fibre.frameCurve frame) (covered := covered) work polynomialStage)
    (index : Fin parents.length) : Canonical → Canonical :=
  let position : Fin (parents.map (recastCenteredEdge parentBasis)).length :=
    ⟨index.val, by rewrite [length_map]; exact index.isLt⟩
  (PolynomialWork.Models.primitivePolynomial covered work models position).eval

/-- Original bounded projections give the same ordered cached primitive increment list. -/
private theorem polynomialPrimitives_increments :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count (parents.map (recastCenteredEdge parentBasis))) →
    (work : PolynomialWork (curve := Fibre.frameCurve frame) covered polynomialFloor
      (Specification.valueSpecification parameter 1)) →
    (models : PolynomialWork.Models (curve := Fibre.frameCurve frame) (covered := covered) work polynomialStage) →
    primitiveIncrements parents (polynomialPrimitives covered work models) =
      PolynomialWork.Models.increments covered work models
  | [], .nil, _, _ => rfl
  | parent :: _, .cons patch inside covered, work, models => by
      let primitive := PolynomialWork.Models.primitivePolynomial (.cons patch inside covered) work models 0
      have head := PolynomialWork.Models.primitivePolynomial_zero (.cons patch inside covered) work models
      have tail := polynomialPrimitives_increments covered work.2 models.2
      change (primitive.eval (parent.edge.point 1) - primitive.eval (parent.edge.point 0)) ::
        primitiveIncrements _ (polynomialPrimitives covered work.2 models.2) =
          ((PolynomialModel.primitive (curve := Fibre.frameCurve frame) models.1.2.val).primitive.value.eval
            (parent.edge.point 1) -
          (PolynomialModel.primitive (curve := Fibre.frameCurve frame) models.1.2.val).primitive.value.eval
            (parent.edge.point 0)) :: PolynomialWork.Models.increments covered work.2 models.2
      exact (congrArg (fun polynomial =>
        (polynomial.eval (parent.edge.point 1) - polynomial.eval (parent.edge.point 0)) ::
          primitiveIncrements _ (polynomialPrimitives covered work.2 models.2)) head).trans
        (congrArg (List.cons _) tail)

/-- The occurrence-indexed primitive increments are exactly the SAME original parent model's integral sample. -/
private theorem polynomialPrimitives_integral {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parents.map (recastCenteredEdge parentBasis)))
    (work : PolynomialWork (curve := Fibre.frameCurve frame) covered polynomialFloor
      (Specification.valueSpecification parameter 1))
    (models : PolynomialWork.Models (curve := Fibre.frameCurve frame) (covered := covered) work polynomialStage) :
    gaussianSum (primitiveIncrements parents (polynomialPrimitives covered work models)) =
      (PathModel.mk (PolynomialWork.Models.cells covered work models)).integralSample :=
  (congrArg gaussianSum (polynomialPrimitives_increments covered work models)).trans
    (PolynomialWork.Models.increments_integral covered work models)

/-- Actual parent models derive every original-occurrence child error from their retained query factories. -/
private theorem polynomialPrimitives_local :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count (parents.map (recastCenteredEdge parentBasis))) →
    (work : PolynomialWork (curve := Fibre.frameCurve frame) covered polynomialFloor
      (Specification.valueSpecification parameter 1)) →
    (models : PolynomialWork.Models (curve := Fibre.frameCurve frame) (covered := covered) work polynomialStage) →
    (index : Fin parents.length) →
    {child : CenteredEdge (Fibre.frameCurve frame) basis} → RootSubedge (parents[index.val]'index.isLt) child →
    (patch : PreparedPatch child) → (inside : (patch.neighborhood childCount).box.Contains (child.edge.point 1)) →
    (prepared : PreparedParent patch childCount floor inside targets) →
    Norm.Basic.normSq (polynomialPrimitives covered work models index (child.edge.point 1) -
      polynomialPrimitives covered work models index (child.edge.point 0) -
        prepared.preparation.cell.models.valueOne.model.integralSample) ≤
      16 * (targets.localBound + quarterRadius 1 polynomialStage) * PreparedParent.cost child
  | [], .nil, _work, _models, index => Fin.elim0 index
  | parent :: _, .cons parentPatch parentInside covered, work, models, index => by
      refine Fin.cases ?_ ?_ index
      · intro relation patch inside prepared
        exact PreparedParent.subedge_polynomial_error_le
          (parameter := parameter) (frame := frame) (basis := basis) (parentBasis := parentBasis)
          (parent := parent) (parentPatch := parentPatch) (count := count)
          (parentCovered := parentInside) (bounds := work.1.2.1.val) (coordinate := work.1.1.val)
          (request := models.1.1.val) models.1.2.val relation prepared
      · intro index
        exact polynomialPrimitives_local covered work.2 models.2 index

/-- Actual coordinate-numerator parent models and raw child source models obey a derived finite comparison.

Both complete input banks are given caches. The original rooted refinement
supplies every signed point relation and per-block oriented chain. The
parent primitives are projections from original ordered model occurrences;
no model, inverse, primitive, request, source or endpoint owner is rebuilt.
-/
theorem rooted_polynomial_error_le {parents children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (parentCover : CoveredParents count (parents.map (recastCenteredEdge parentBasis)))
    (work : PolynomialWork (curve := Fibre.frameCurve frame) parentCover polynomialFloor
      (Specification.valueSpecification parameter 1))
    (models : PolynomialWork.Models (curve := Fibre.frameCurve frame) (covered := parentCover) work polynomialStage)
    (refinement : RootSubedgeRefinement parents children)
    (covered : CoveredParents childCount children) (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain children (start := start) (finish := finish)) :
    Norm.Basic.normSq ((PathModel.mk (PolynomialWork.Models.cells parentCover work models)).integralSample -
      (PathModel.mk ((sources covered prepared chain).cells 1)).integralSample) ≤
      16 * (targets.localBound + quarterRadius 1 polynomialStage) * movementMass children := by
  have original := rooted_increment_error_le (polynomialPrimitives parentCover work models) 1
    (16 * (targets.localBound + quarterRadius 1 polynomialStage)) refinement covered prepared
    (polynomialPrimitives_local parentCover work models) chain
  rewrite [polynomialPrimitives_integral parentCover work models] at original
  exact original

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
