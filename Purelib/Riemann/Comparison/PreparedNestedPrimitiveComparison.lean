module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot

import Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
public import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Retained primitive sums compared with actual later period cells

The same per-parent primitive polynomial is evaluated on a connected nested
refinement.  Only the final children's model errors and movements are charged;
the initial coarse model contributes no fixed error allowance.  Both finite
cell-count factors remain explicit.  A decay theorem for these computed
charges, not compatibility alone, is still needed for period identification.
-/

namespace Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison

open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge RootSubedgeBlock RootSubedgeRefinement)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Paths.PreparedPrimitivePaths (point_inside_of_endpoints)
open Purelib.Riemann.Integration.PreparedPrimitiveEquivalence (integral_error_le)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained primitive comparison bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the retained primitive readings. -/
private abbrev Gaussian := Basic.Canonical

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

namespace LocalRequest

variable {parent : CenteredEdge curve differential} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Gaussian in
/-- The original requested primitive polynomial's endpoint increment on its retained parent edge. -/
def increment (localRequest : LocalRequest parent count target) : Basic.Canonical :=
  localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
    localRequest.request.model.primitive.value.eval (parent.edge.point 0)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- The explicit remainder and root-reading charge for one original child edge.

The formula retains the parent request's primitive remainder bound and refinement stage, the child's exact movement and
model allowance, and the original differential numerator at its starting point. -/
def childCharge (localRequest : LocalRequest parent count target) (child : CenteredEdge curve differential) :
  Fraction.Rational :=
  2 * localRequest.request.model.primitive.remainderBound * child.edge.pointMovement ^ 2 +
    (4 * normSq ((PreparedPrimitiveSamples.differentialNumerator differential).eval (child.edge.point 0)) *
      Geometric.Basic.quarterRadius localRequest.neighborhood.inverseErrorScale localRequest.request.index +
        40 * child.edge.modelErrorAllowance) * child.edge.pointMovement

open Purelib.Data.Rat in
open Purelib.Riemann.Paths in
/-- Every point on the retained child edge lies in its original parent request's primitive neighborhood. -/
theorem child_inside (localRequest : LocalRequest parent count target)
    {child : CenteredEdge curve differential} (relation : RootSubedge parent child)
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    localRequest.neighborhood.box.Contains (child.edge.point fraction) := by
  rw [← (relation.location fraction inside).point_eq]
  have first : localRequest.neighborhood.box.Contains (parent.edge.point 0) := by
    rw [localRequest.neighborhood_eq]
    exact localRequest.patch.start_inside count
  exact PreparedPrimitivePaths.point_inside_of_endpoints parent _ first localRequest.finishInside
    (relation.location fraction inside).inside

open Purelib.Riemann.Integration in
open Purelib.Riemann.Normalization in
/-- The original child integral sample is close to the retained parent primitive increment on that child.

The root-subedge witness supplies the exact point location and operational root equivalence, while the bound is the
child's retained remainder and reading charge. -/
theorem child_error_le (localRequest : LocalRequest parent count target)
    {child : CenteredEdge curve differential} (relation : RootSubedge parent child) :
    normSq (localRequest.request.model.primitive.value.eval (child.edge.point 1) -
      localRequest.request.model.primitive.value.eval (child.edge.point 0) - child.model.integralSample) ≤
        LocalRequest.childCharge localRequest child := by
  rcases localRequest with ⟨patch, neighborhood, neighborhoodEq, request, finishInside⟩
  subst neighborhood
  let retained : LocalRequest parent count target := ⟨patch, patch.neighborhood count, rfl, request, finishInside⟩
  have first := LocalRequest.child_inside retained relation 0 child.edge.baseInside
  have last := LocalRequest.child_inside retained relation 1 (by decide)
  let sample := ContinuedInverseRoot.ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (child.edge.point 0)
    first
  let location := relation.location 0 child.edge.baseInside
  let equivalent := (relation.equivalent 0 child.edge.baseInside).symm.trans
    (patch.point_equivalent_at count location.fraction location.inside location.point_eq first sample)
  exact PreparedPrimitiveEquivalence.integral_error_le request.model child.edge child.center sample first last
    equivalent

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- The original child count times the finite sum of retained child error charges. -/
def blockCharge (localRequest : LocalRequest parent count target) (children : List (CenteredEdge curve differential)) :
  Fraction.Rational :=
  (children.length : Fraction.Rational) * FiniteSum.Rational.Squares.coordinateSum (children.map
    (LocalRequest.childCharge localRequest))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
open Purelib.Data.List in
/-- A retained child chain approximates the original parent primitive increment within its block charge.

The original endpoint chain and root-subedge block preserve the ordered children, parent sheet and exact integral
samples; the finite norm-sum estimate uses that same child count. -/
theorem block_error_le (localRequest : LocalRequest parent count target)
    {children : List (CenteredEdge curve differential)}
    (chain : DirectPathChain children
      (start := ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩)
      (finish := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩))
    (roots : RootSubedgeBlock parent children) :
    normSq (LocalRequest.increment localRequest - (Basic.PathModel.mk (children.map CenteredEdge.model)).integralSample)
      ≤
      LocalRequest.blockCharge localRequest children := by
  have bounded : Norm.Sum.Basic.gaussianNormSqSum (Primitive.errorTerms localRequest.request.model.primitive.value.eval
      (children.map CenteredEdge.model)) ≤ FiniteSum.Rational.Squares.coordinateSum (children.map
        (LocalRequest.childCharge localRequest)) := by
    clear chain
    induction roots with
    | nil => exact le_rfl
    | cons head tail ih => exact add_le_add (LocalRequest.child_error_le localRequest head) ih
  have total := Norm.Sum.Basic.normSq_gaussianSum_le
    (Primitive.errorTerms localRequest.request.model.primitive.value.eval (children.map CenteredEdge.model))
  rw [Primitive.errorTerms_sum, PreparedPrimitivePaths.incrementSum_eq _ chain] at total
  simp only [Primitive.errorTerms, Map.length_map] at total
  rw [← parent.edge.point_one, ← parent.edge.point_zero] at total
  exact total.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

end LocalRequest

namespace RequestedParents

variable {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The ordered original parent-primitive minus child-block integral differences for a retained root refinement. -/
def refinementErrors : ∀ {parents children : List (CenteredEdge curve differential)},
    RequestedParents count target parents → RootSubedgeRefinement parents children → List Basic.Canonical
  | _, _, .nil, .nil => []
  | _, _, .cons request tail, .cons (block := block) _ _ remaining =>
      (LocalRequest.increment request - (Basic.PathModel.mk (block.map CenteredEdge.model)).integralSample) ::
        RequestedParents.refinementErrors tail remaining

open Purelib.Data.Rat in
/-- The ordered original child-block charges for the exact retained parent request refinement. -/
def refinementCharges : ∀ {parents children : List (CenteredEdge curve differential)},
    RequestedParents count target parents → RootSubedgeRefinement parents children → List Fraction.Rational
  | _, _, .nil, .nil => []
  | _, _, .cons request tail, .cons (block := block) _ _ remaining =>
      LocalRequest.blockCharge request block :: RequestedParents.refinementCharges tail remaining

/-- The retained refinement error list has exactly one entry per original parent edge. -/
private theorem refinementErrors_length : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    (RequestedParents.refinementErrors requests refinement).length = parents.length
  | _, _, .nil, .nil => rfl
  | _, _, .cons _ tail, .cons _ _ remaining => congrArg Nat.succ (refinementErrors_length tail remaining)

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Readings in
open Purelib.Data.List in
/-- The sum of original refinement errors equals the parent primitive sum minus the exact child-path integral. -/
private theorem refinementErrors_sum : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (RequestedParents.refinementErrors requests refinement) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments -
      (Basic.PathModel.mk (children.map CenteredEdge.model)).integralSample
  | _, _, .nil, .nil => by change (0 : Basic.Canonical) = 0 - 0; ring1
  | _, _, .cons request tail, .cons _ _ remaining => by
      simp only [refinementErrors, UniformPreparedRequests.RequestedParents.increments,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        Map.map_append, Basic.PathModel.integralSample_mk_append]
      rw [refinementErrors_sum tail remaining]
      unfold LocalRequest.increment
      ring1

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- The sum of squared original refinement errors is bounded by their retained block charges. -/
private theorem refinementErrors_bounded : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    Norm.Sum.Basic.gaussianNormSqSum (RequestedParents.refinementErrors requests refinement) ≤
      FiniteSum.Rational.Squares.coordinateSum (RequestedParents.refinementCharges requests refinement)
  | _, _, .nil, .nil => le_rfl
  | _, _, .cons request tail, .cons chain roots remaining =>
      add_le_add (LocalRequest.block_error_le request chain roots) (refinementErrors_bounded tail remaining)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained parent primitive sum approximates the original refined child-path integral.

The squared error is bounded by the original parent count times the sum of its exact child-block charges, preserving the
root-refinement witnesses and ordered edge lists. -/
theorem refinement_error_le {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments - (Basic.PathModel.mk (children.map
      CenteredEdge.model)).integralSample) ≤
      (parents.length : Fraction.Rational) * FiniteSum.Rational.Squares.coordinateSum
        (RequestedParents.refinementCharges requests refinement) := by
  rw [← RequestedParents.refinementErrors_sum requests refinement]
  have total := Norm.Sum.Basic.normSq_gaussianSum_le (RequestedParents.refinementErrors requests refinement)
  rw [RequestedParents.refinementErrors_length requests refinement] at total
  exact total.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (RequestedParents.refinementErrors_bounded requests refinement) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
      _)))

end RequestedParents

namespace PrimitiveSumRequest

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A retained child-path integral sample with its exact primitive-sum error bound.

The sample equality names the original ordered child models, while the accuracy certificate compares that same cached
readback to the supplied parent primitive sum. -/
structure ComparedSample (primitiveSum : Basic.Canonical) (children : List (CenteredEdge curve differential)) where
  /-- The cached integral readback of the exact original refined child path. -/ sample : Basic.Canonical
  /-- The cached readback equals the integral sample of the original ordered child models. -/ sample_eq : sample =
    (Basic.PathModel.mk (children.map CenteredEdge.model)).integralSample
  /-- The retained rational squared-error bound for this exact primitive-sum comparison. -/ errorBound :
    Fraction.Rational
  /-- The supplied original primitive sum and exact cached child sample differ within the retained bound. -/ accurate :
    normSq (primitiveSum - sample) ≤ errorBound

constructive_injectivity ComparedSample

open Purelib.Algebra in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the original refined child-path sample and certify its error against the retained primitive sum.

The executable tail-integral readback is kept with its exact equality, and the bound uses the same original parent
requests and retained child-block charges. -/
def compareRefinement {parents children : List (CenteredEdge curve differential)} {target : Fraction.Rational}
    (request : PrimitiveSumRequest parents count target) (refinement : RootSubedgeRefinement parents children) :
    ComparedSample request.primitiveSum children :=
  let path := Basic.PathModel.mk (children.map CenteredEdge.model)
  let charges := RequestedParents.refinementCharges request.requests refinement
  { sample := path.tailIntegralSample
    sample_eq := path.integralSample_eq_tailIntegralSample.symm
    errorBound := (parents.length : Fraction.Rational) * FiniteSum.Rational.Squares.coordinateSum charges
    accurate := by
      rw [← path.integralSample_eq_tailIntegralSample, request.primitiveSum_eq, request.increments_eq]
      exact RequestedParents.refinement_error_le request.requests refinement }

end PrimitiveSumRequest

end Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
