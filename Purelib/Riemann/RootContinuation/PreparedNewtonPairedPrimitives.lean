module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive.Dyadic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Integration.UniformPreparedPrimitives
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Polynomial.Dense.Evaluation

public section

/-! Primitive comparison consumes the already retained Newton refinement. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request

open Purelib
open Purelib.Data.Rat
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Paths.PreparedPrimitivePaths
open Purelib.Riemann.Integration.PreparedModelAccuracy (Profile Request)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {profile : Profile parent} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Bound the original primitive increment against the retained prepared integral sample.

The actual patch model and endpoint containment give separate dyadic remainder and coefficient-error terms, preserving
the original factors two, four and forty. -/
theorem primitive_error_le (request : Request profile target) (patch : PreparedPatch parent)
    {index : Nat} (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator differential))
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
    Data.Gaussian.Norm.Basic.normSq (model.primitive.value.eval (parent.edge.point 1) - model.primitive.value.eval
      (parent.edge.point 0) -
      (Basic.PathModel.mk (request.block.children.map CenteredEdge.model)).integralSample) ≤
        2 * model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
          request.block.depth +
          (4 * Bounds.Box.denseEvalNormBound (differentialNumerator differential) (patch.neighborhood count).box *
            Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale index + 40 * target) * movement
              parent := by
  have starts := PreparedPrimitivePaths.block_starts_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  have finishes := PreparedPrimitivePaths.block_finishes_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  have bounded := UniformPreparedPrimitives.children_bounded patch model request.block.roots
    (Bounds.Box.denseEvalNormBound (differentialNumerator differential) (patch.neighborhood count).box)
    target (Geometric.Basic.quarterRadius (movement parent) request.block.depth)
  have estimate := Primitive.Dyadic.dyadic_integral_error_le model.primitive.value.eval
    (Basic.PathModel.mk (request.block.children.map CenteredEdge.model))
    (PreparedPrimitivePaths.incrementSum_eq _ request.block.chain) request.block.depth
    (by rw [Data.List.Map.length_map, request.block.childCount]) (movement parent) (2 * model.primitive.remainderBound)
    (4 * Bounds.Box.denseEvalNormBound (differentialNumerator differential) (patch.neighborhood count).box *
      Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale index + 40 * target)
    (by
      intro cell member
      obtain ⟨child, inChildren, rfl⟩ := Map.mem_map.mp member
      have numeratorLe := Bounds.Box.normSq_eval_le_denseEvalNormBound
        (differentialNumerator differential) (starts child inChildren)
      rw [Norm.Basic.normSq_eq_canonical] at numeratorLe
      exact bounded child inChildren (starts child inChildren) (finishes child inChildren) numeratorLe
        (request.child_error inChildren) (PreparedPrimitivePaths.block_movement_le request.block inChildren))
  rw [parent.edge.point_one, parent.edge.point_zero]
  rw [Norm.Basic.normSq_eq_canonical]
  exact estimate

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedModelAccuracy (Profile Request)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {profile : Profile parent} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A cached original increment and error bound compared to one retained numerical value.

Exact readbacks identify the expected increment and error formula, while the stored inequality concerns their actual
difference. -/
structure IncrementComparison (expected actual : Basic.Canonical) (error : Fraction.Rational) where
  /-- The cached original expected primitive increment. -/ increment : Basic.Canonical
  /-- The cached increment is exactly the original expected value. -/ increment_eq : increment = expected
  /-- The cached quantitative comparison bound. -/ bound : Fraction.Rational
  /-- The cached bound is exactly the retained error formula. -/ bound_eq : bound = error
  /-- The squared difference from the original numerical sample is bounded by the cached error. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (increment - actual) ≤ bound

constructive_injectivity IncrementComparison

set_option genInjectivity false in
/-- An original prepared patch with containment of the exact parent endpoint.

The neighborhood count and original parent remain indices of the retained patch and finish witness. -/
structure PrimitivePatchCoverage (parent : CenteredEdge curve differential) (count : Nat) where
  /-- The retained prepared patch for the original parent. -/ patch : PreparedPatch parent
  /-- The original parent endpoint belongs to the retained patch neighborhood. -/ finishInside : (patch.neighborhood
    count).box.Contains (parent.edge.point 1)

constructive_injectivity PrimitivePatchCoverage

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original covered patch, indexed model and certified increment comparison.

The dependent tuple retains the actual neighborhood owner and model index together with the exact prepared-child
integral and quantitative error formula. -/
@[expose] def PrimitiveComparison (request : Request profile target) (count index : Nat) :=
  (coverage : PrimitivePatchCoverage parent count) ×
  (model : PrimitiveModel (coverage.patch.neighborhood count) index (differentialNumerator differential)) ×
  IncrementComparison
    (model.primitive.value.eval (parent.edge.point 1) - model.primitive.value.eval (parent.edge.point 0))
    (Basic.PathModel.mk (request.block.children.map CenteredEdge.model)).integralSample
    (2 * model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
      request.block.depth +
      (4 * Bounds.Box.denseEvalNormBound (differentialNumerator differential) (coverage.patch.neighborhood count).box *
        Geometric.Basic.quarterRadius (coverage.patch.neighborhood count).inverseErrorScale index + 40 * target) *
          movement parent)

open Purelib.Riemann.RootContinuation in
/-- Retain an original primitive model and certify its prepared increment comparison.

The supplied finish containment and exact patch model provide the stored increment, bound and proof without rebuilding
the model. -/
@[expose] def PrimitiveComparison.ofModel (request : Request profile target) (count index : Nat)
    (patch : PreparedPatch parent)
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator differential))
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
    PrimitiveComparison request count index :=
  ⟨⟨patch, finishInside⟩, model, _, rfl, _, rfl,
    PreparedNewtonPairedPrimitives.Request.primitive_error_le request patch model finishInside⟩

/-- Build the original patch model at the requested index and retain its increment comparison.

The supplied patch and finish containment remain the exact coverage owner of the newly constructed model. -/
@[expose] def PrimitiveComparison.build (request : Request profile target) (count index : Nat)
    (patch : PreparedPatch parent)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) :
    PrimitiveComparison request count index :=
  ofModel request count index patch
    (PrimitiveModel.ofIndex (patch.neighborhood count) index (differentialNumerator differential)) finishInside

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request (PrimitiveComparison)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide (PairedBoundarySide)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}

open Purelib.Curves.Hyperelliptic in
/-- Recast the differential while retaining the original patch bounds and seed. -/
@[expose] def recastPrimitivePatch {parent : CenteredEdge curve differential}
    (patch : PreparedPatch parent) (other : Differentials.Basic.Differential genus) : PreparedPatch (recastCenteredEdge
      other parent) :=
  ⟨patch.bounds, patch.seed⟩

set_option genInjectivity false in
/-- Primitive comparisons for both differential rows of the original paired-parent bank.

Each head retains the same count and model index for its actual first and second refinements; the tail stays indexed by
the exact remaining bank. -/
inductive PairedParentPrimitives (count : Nat) :
    {parents : List (CenteredEdge curve differential)} → PairedBoundaryParents request other parents → Type 2
  /-- The empty primitive comparisons for the exact empty paired bank. -/ | nil : PairedParentPrimitives count .nil
  /-- Prepend both original indexed primitive comparisons to the retained tail. -/ | cons {parent : CenteredEdge curve
    differential} {parents : List (CenteredEdge curve differential)}
      {head : PairedBoundaryParent request parent other} {tail : PairedBoundaryParents request other parents}
      {index : Nat}
      (first : PrimitiveComparison head.refinement.first count index)
      (second : PrimitiveComparison head.refinement.second count index)
      (rest : PairedParentPrimitives count tail) :
      PairedParentPrimitives count (.cons head tail)

constructive_injectivity PairedParentPrimitives

namespace PairedParentPrimitives

open Purelib.Curves.Hyperelliptic.Integration in
/-- Build paired primitive comparisons from the original bank and covered parent list.

Both differential rows use the same requested model index; the second retains the exact recast original patch, and
recursion follows the stored bank and coverage together. -/
@[expose] def build (count index : Nat) : {parents : List (CenteredEdge curve differential)} →
    (bank : PairedBoundaryParents request other parents) → Observation.UniformPreparedMesh.CoveredParents count parents
      →
      PairedParentPrimitives count bank
  | _, .nil, .nil => .nil
  | _, .cons head tail, .cons patch finishInside remaining =>
      .cons (PrimitiveComparison.build head.refinement.first count index patch finishInside)
        (PrimitiveComparison.build head.refinement.second count index (recastPrimitivePatch patch other) finishInside)
        (build count index tail remaining)

end PairedParentPrimitives

namespace PairedBoundarySide

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- Build both primitive rows at the requested index using the original side's retained coverage. -/
@[expose] def primitives {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
    {within : segment.WithinAmbient} {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    {sheet : Fin 2} (side : PairedBoundarySide request other segment within owner sheet) (index : Nat) :
    PairedParentPrimitives 0 side.refined :=
  PairedParentPrimitives.build 0 index side.refined side.covered.covered

end PairedBoundarySide
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds
