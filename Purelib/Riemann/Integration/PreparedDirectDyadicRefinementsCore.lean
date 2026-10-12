module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
public import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Algebra.NatCast
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Power.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
public import Purelib.Integration.Program.Gaussian.Sequential
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
public import Purelib.Riemann.Integration.CheckedDirectGeometry
public import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.Data.Task.Parallel
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Direct dyadic refinements of prepared edges

Every child in this module is anchored directly to its coarse parent's fixed
prepared occurrence.  Consequently no staged child-owner congruence search is
needed: the accepted coarse move supplies every direct point query, while the
uniform preparation floor supplies every sufficiently fine child move.
-/

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Rat
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration

open Purelib.Data.List

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedEdgeRecasting
  (Owner Endpoint StepRequest CenteredEdge directRequest recastCenteredEdge recastPreparedEdge
    recastCenteredEdge_segment recastCenteredEdge_request recastCenteredEdge_left
    recastPreparedEdge_self CompatibleConstantPathRefinement)
open Purelib.Geometry.Rational (Box)

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
private abbrev Gaussian := Basic.Canonical

/-- The original parent's query owner transported to the retained current endpoint radicand. -/
@[expose] def directOwner {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) (current : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition
      parent.edge current) :
    Owner
      (curve.polynomial.eval
        (parent.edge.segment.pointAt current.parameter)) :=
  CheckedDirectGeometry.queryOwnerAt parent.edge current position

/-- Construct a direct child edge using the parent's original query owner and canonical prepared cache.

The supplied position, endpoint order, positive diameter and clearance bound retain the original segment and sheet while
fixing the exact child request. -/
@[expose] def directChildEdge {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (small : ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    PreparedSubdivisionModelCore.PreparedEdge curve differential where
  ambient := parent.edge.ambient
  start := parent.edge.start
  finish := parent.edge.finish
  segment := parent.edge.segment
  within := parent.edge.within
  left := current
  owner := directOwner parent current position
  request := directRequest right rootDiameter rootDiameterPositive
  cached := PreparedSheetContinuation.CachedSource.canonical
    parent.edge.segment current (directOwner parent current position)
      (directRequest right rootDiameter rootDiameterPositive)
  ordered := ordered
  small := small
  sheet := parent.edge.sheet

/-- Equip the exact direct child edge with its canonical coefficient center state. -/
@[expose] def directChild {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (small : ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    CenteredEdge curve differential :=
  let edge := directChildEdge parent current right position ordered rootDiameter
    rootDiameterPositive small
  { edge := edge
    center :=
      PreparedConstantModels.PreparedEdge.CenterState.canonical edge }

/-- Relate the original parent and its direct child through the exact queried root owner.

The retained parent position and canonical child preparation form the actual checked leaf used by the root comparison.
-/
@[expose] def directChildAt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (small : ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    PreparedSubdivisionModelCore.RootChildAt parent
      (directChild parent current right position ordered rootDiameter
        rootDiameterPositive small) := by
  let owner := directOwner parent current position
  let request := directRequest right rootDiameter rootDiameterPositive
  let cached := PreparedSheetContinuation.CachedSource.canonical
    parent.edge.segment current owner request
  let leaf : CheckedDirectGeometry.Leaf parent.edge current right rootDiameter :=
    { position := position
      owner := owner
      owner_eq := rfl
      positive := rootDiameterPositive
      ordered := ordered
      prepared := { cached := cached, small := small } }
  exact leaf.rootChildAt parent

/-- Variation below the uniform prepared-clearance floor pays the exact direct child's clearance condition. -/
theorem directChildSmall_of_variation_lt_uniform {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition
      parent.edge current)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (below : ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        PreparedSheetContinuation.uniformPreparedClearanceFloor
          parent.edge.segment rootDiameter) :
    ClearSheetContinuation.variationBound parent.edge.segment
      current.parameter right.parameter <
        (PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound := by
  exact below.trans_le (by
    calc
      PreparedSheetContinuation.uniformPreparedClearanceFloor
          parent.edge.segment rootDiameter <=
        PreparedSheetContinuation.preparedClearanceLower
          parent.edge.segment current
            (directRequest right rootDiameter rootDiameterPositive) :=
        PreparedSheetContinuation.uniformPreparedClearanceFloor_le_predicted
          parent.edge.segment rootDiameter
      _ <=
          (PreparedSheetContinuation.prepared parent.edge.segment
            current (directOwner parent current position)
            (directRequest right rootDiameter
              rootDiameterPositive)).track.initial.clearance.bound :=
        PreparedSheetContinuation.preparedClearanceLower_le
          parent.edge.segment current (directOwner parent current position)
            (directRequest right rootDiameter rootDiameterPositive))

open Purelib.Algebra in
open Purelib.Approximation.Rational in
/-- Dividing the geometric radius scale by four equals increasing its index by one. -/
public theorem quarterRadius_div_four (scale : Fraction.Rational) (index : Nat) :
    Geometric.Basic.quarterRadius (scale / 4) index =
      Geometric.Basic.quarterRadius scale (index + 1) := by
  have scaleDiv : scale / 4 = scale * (1 / 4 : Fraction.Rational) := by
    rw [Field.ExplicitField.div_eq_mul_inv,
      Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, scaleDiv, pow_succ]
  ring1

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The displacement sum of concatenated original cell lists is the sum of their displacements. -/
private theorem displacementSum_append
    (first second : List Basic.CellModel) :
    Basic.PathModel.displacementSum
        (first ++ second) =
      Basic.PathModel.displacementSum first +
        Basic.PathModel.displacementSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        Basic.PathModel.displacementSum_nil]
      exact (zero_add _).symm
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append,
        Basic.PathModel.displacementSum_cons]
      rw [inductionHypothesis]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The squared Gaussian distance between the original segment's two parameter readings. -/
@[expose] def geometricMovement
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Fraction.Rational) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq
    (segment.pointAt right - segment.pointAt left)

/-- The rational midpoint's distance from the left endpoint is half the original interval width. -/
private theorem midpoint_sub_left (left right : Fraction.Rational) :
    ClearSheetContinuation.midpoint left right - left =
      (right - left) / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (2 : Fraction.Rational) ≠ 0 by decide)
  calc
    (ClearSheetContinuation.midpoint left right - left) * 2 =
        ClearSheetContinuation.midpoint left right * 2 -
          left * 2 := by ring1
    _ = (left + right) - left * 2 := by
      rw [ClearSheetContinuation.midpoint,
        Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = right - left := by ring1
    _ = ((right - left) / 2) * 2 :=
      (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)).symm

/-- The right endpoint's distance from the rational midpoint is half the original interval width. -/
private theorem right_sub_midpoint (left right : Fraction.Rational) :
    right - ClearSheetContinuation.midpoint left right =
      (right - left) / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (2 : Fraction.Rational) ≠ 0 by decide)
  calc
    (right - ClearSheetContinuation.midpoint left right) * 2 =
        right * 2 -
          ClearSheetContinuation.midpoint left right * 2 := by
      ring1
    _ = right * 2 - (left + right) := by
      rw [ClearSheetContinuation.midpoint,
        Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = right - left := by ring1
    _ = ((right - left) / 2) * 2 :=
      (Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)).symm

/-- A strictly ordered rational interval's midpoint is strictly above its left endpoint. -/
public theorem left_lt_midpoint {left right : Fraction.Rational}
    (proper : left < right) :
    left < ClearSheetContinuation.midpoint left right := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (2 : Fraction.Rational))
  · calc
      left * 2 = left + left := by ring1
      _ < left + right :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct proper left
      _ = ClearSheetContinuation.midpoint left right * 2 := by
        rw [ClearSheetContinuation.midpoint,
          Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
  · decide

/-- A strictly ordered rational interval's midpoint is strictly below its right endpoint. -/
public theorem midpoint_lt_right {left right : Fraction.Rational}
    (proper : left < right) :
    ClearSheetContinuation.midpoint left right < right := by
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (2 : Fraction.Rational))
  · calc
      ClearSheetContinuation.midpoint left right * 2 =
          left + right := by
        rw [ClearSheetContinuation.midpoint,
          Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
      _ < right + right :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct proper right
      _ = right * 2 := by ring1
  · decide

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- The original segment's squared movement over the left half interval is one quarter of its full movement. -/
public theorem geometricMovement_left_midpoint
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Fraction.Rational) :
    geometricMovement segment left
        (ClearSheetContinuation.midpoint left right) =
      geometricMovement segment left right / 4 := by
  unfold geometricMovement
  rw [segment.normSq_pointAt_sub_pointAt,
    segment.normSq_pointAt_sub_pointAt, midpoint_sub_left, pow_two,
    Fraction.Field.div_mul_div_direct,
    show (2 : Fraction.Rational) * 2 = 4 by decide]
  rw [Fraction.Field.div_eq_mul_inv_direct
      ((right - left) * (right - left)) 4]
  simp only [pow_two]
  rw [Fraction.Field.div_eq_mul_inv_direct
      ((right - left) * (right - left) *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) 4]
  ring1

/-- The original segment's squared movement over the right half interval is one quarter of its full movement. -/
public theorem geometricMovement_midpoint_right
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Fraction.Rational) :
    geometricMovement segment
        (ClearSheetContinuation.midpoint left right) right =
      geometricMovement segment left right / 4 := by
  unfold geometricMovement
  rw [segment.normSq_pointAt_sub_pointAt,
    segment.normSq_pointAt_sub_pointAt, right_sub_midpoint, pow_two,
    Fraction.Field.div_mul_div_direct,
    show (2 : Fraction.Rational) * 2 = 4 by decide]
  rw [Fraction.Field.div_eq_mul_inv_direct
      ((right - left) * (right - left)) 4]
  simp only [pow_two]
  rw [Fraction.Field.div_eq_mul_inv_direct
      ((right - left) * (right - left) *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) 4]
  ring1

end

/-- A common bound on the actual point movement of every retained centered child edge. -/
inductive ChildMovementBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (bound : Fraction.Rational) :
    List (CenteredEdge curve differential) -> Prop
  /-- The empty child list satisfies the movement bound. -/ | nil : ChildMovementBound bound []
  /-- Retain the exact head child's movement inequality and the bound for the original tail. -/ | cons {child :
    CenteredEdge curve differential}
      {children : List (CenteredEdge curve differential)}
      (head : child.edge.pointMovement <= bound)
      (tail : ChildMovementBound bound children) :
      ChildMovementBound bound (child :: children)

/-- Concatenate movement certificates at the same bound for the original child lists. -/
public theorem appendChildMovementBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {bound : Fraction.Rational} :
    forall {first second : List (CenteredEdge curve differential)},
      ChildMovementBound bound first -> ChildMovementBound bound second ->
        ChildMovementBound bound (first ++ second)
  | [], _second, .nil, secondBound => secondBound
  | _ :: _, _second, .cons head tail, secondBound =>
      .cons head (appendChildMovementBound tail secondBound)

/-- Transport the retained child movement certificate along an equality of its scalar bound. -/
public theorem castChildMovementBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {first second : Fraction.Rational}
    {children : List (CenteredEdge curve differential)}
    (equal : first = second) :
    ChildMovementBound first children -> ChildMovementBound second children := by
  subst second
  exact fun bounded => bounded

/-- A common bound on every retained child's actual model-error allowance. -/
inductive ChildModelErrorBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (bound : Fraction.Rational) :
    List (CenteredEdge curve differential) -> Prop
  /-- The empty child list satisfies the model-error bound. -/ | nil : ChildModelErrorBound bound []
  /-- Retain the exact head child's model-error inequality and the bound for the original tail. -/ | cons {child :
    CenteredEdge curve differential}
      {children : List (CenteredEdge curve differential)}
      (head : child.edge.modelErrorAllowance <= bound)
      (tail : ChildModelErrorBound bound children) :
      ChildModelErrorBound bound (child :: children)

/-- Concatenate model-error certificates at the same bound for the original child lists. -/
public theorem appendChildModelErrorBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {bound : Fraction.Rational} :
    forall {first second : List (CenteredEdge curve differential)},
      ChildModelErrorBound bound first -> ChildModelErrorBound bound second ->
        ChildModelErrorBound bound (first ++ second)
  | [], _second, .nil, secondBound => secondBound
  | _ :: _, _second, .cons head tail, secondBound =>
      .cons head (appendChildModelErrorBound tail secondBound)

/-- Transport the retained child model-error certificate along an equality of bounds. -/
public theorem castChildModelErrorBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {first second : Fraction.Rational}
    {children : List (CenteredEdge curve differential)}
    (equal : first = second) :
    ChildModelErrorBound first children ->
      ChildModelErrorBound second children := by
  subst second
  exact fun bounded => bounded

/-- Increase the common bound on the original children's model-error allowances. -/
private theorem ChildModelErrorBound.mono {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {first second : Fraction.Rational}
    {children : List (CenteredEdge curve differential)}
    (bounded : ChildModelErrorBound first children)
    (less : first <= second) : ChildModelErrorBound second children := by
  induction bounded with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (head.trans less) inductionHypothesis

/-! ### Compact bounds for already accepted dyadic segments

The executable prepared-path checker transports a genuinely dependent root
owner from one edge to the next.  Its retained integration cells therefore
must not be replaced by the owner-independent direct-refinement cells above.
For scheduling, however, only a numerical upper bound is required.  The
following finite predicates recover that bound from the displayed dyadic
request geometry without folding the expensive coefficient model of every
accepted leaf.
-/

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- A common squared-movement bound between successive original target endpoints on the segment. -/
private inductive EndpointMovementBound
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (bound : Fraction.Rational) : Endpoint -> List Endpoint -> Prop
  /-- There are no further target movements to bound. -/ | nil (current : Endpoint) : EndpointMovementBound segment
    bound current []
  /-- Retain the movement inequality from the current endpoint to the next target and continue from that target. -/ |
    cons {current endpoint : Endpoint} {remaining : List Endpoint}
      (head : geometricMovement segment current.parameter endpoint.parameter <=
        bound)
      (tail : EndpointMovementBound segment bound endpoint remaining) :
      EndpointMovementBound segment bound current (endpoint :: remaining)

/-- Concatenate endpoint movement certificates through the first list's exact final target. -/
private theorem endpointMovementBound_append
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (bound : Fraction.Rational) :
    forall (current : Endpoint) (first second : List Endpoint),
      EndpointMovementBound segment bound current first ->
      EndpointMovementBound segment bound
        (ClearSheetContinuation.Subdivision.finalTarget current
          first) second ->
      EndpointMovementBound segment bound current (first ++ second)
  | _current, [], _second, .nil _, secondBound => secondBound
  | _current, _endpoint :: _remaining, _second, .cons head tail,
      secondBound =>
    .cons head
      (endpointMovementBound_append segment bound _ _ _ tail secondBound)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Every original dyadic target step satisfies the full segment movement scaled by the corresponding quarter-radius. -/
private theorem dyadicTargets_endpointMovementBound
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    forall (depth : Nat) (left right : Endpoint),
      EndpointMovementBound segment
        (Geometric.Basic.quarterRadius
          (geometricMovement segment left.parameter right.parameter) depth)
        left
        (ClearSheetContinuation.Subdivision.dyadicTargets depth
          left right)
  | 0, left, right => by
      apply EndpointMovementBound.cons
      · simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct] using
            (le_refl (geometricMovement segment left.parameter
              right.parameter))
      · exact .nil right
  | depth + 1, left, right => by
      let middle : Endpoint :=
        ⟨ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      have first := dyadicTargets_endpointMovementBound segment depth left
        middle
      have second := dyadicTargets_endpointMovementBound segment depth middle
        right
      have firstScale :
          Geometric.Basic.quarterRadius
              (geometricMovement segment left.parameter middle.parameter)
                depth =
            Geometric.Basic.quarterRadius
              (geometricMovement segment left.parameter right.parameter)
                (depth + 1) := by
        change Geometric.Basic.quarterRadius
            (geometricMovement segment left.parameter
              (ClearSheetContinuation.midpoint left.parameter
                right.parameter)) depth = _
        rw [geometricMovement_left_midpoint]
        exact quarterRadius_div_four _ _
      have secondScale :
          Geometric.Basic.quarterRadius
              (geometricMovement segment middle.parameter right.parameter)
                depth =
            Geometric.Basic.quarterRadius
              (geometricMovement segment left.parameter right.parameter)
                (depth + 1) := by
        change Geometric.Basic.quarterRadius
            (geometricMovement segment
              (ClearSheetContinuation.midpoint left.parameter
                right.parameter) right.parameter) depth = _
        rw [geometricMovement_midpoint_right]
        exact quarterRadius_div_four _ _
      rw [firstScale] at first
      rw [secondScale] at second
      change EndpointMovementBound segment _ left
        (ClearSheetContinuation.Subdivision.dyadicTargets depth
            left middle ++
          ClearSheetContinuation.Subdivision.dyadicTargets depth
            middle right)
      apply endpointMovementBound_append segment _ left _ _ first
      simpa only
        [ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget]
        using second

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- Bounds on both geometric movement and requested root diameter for the actual ordered request list. -/
private inductive RequestTargets
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (movementBound rootDiameter : Fraction.Rational) :
    Endpoint -> List StepRequest -> Prop
  /-- The empty request list satisfies the common movement and diameter bounds. -/ | nil (current : Endpoint) :
      RequestTargets segment movementBound rootDiameter current []
  /-- Retain the next request's endpoint movement and root-diameter bounds and continue from its exact endpoint. -/ |
    cons {current : Endpoint} {request : StepRequest}
      {remaining : List StepRequest}
      (movement : geometricMovement segment current.parameter
        request.endpoint.parameter <= movementBound)
      (diameter : request.rootDiameter <= rootDiameter)
      (tail : RequestTargets segment movementBound rootDiameter
        request.endpoint remaining) :
      RequestTargets segment movementBound rootDiameter current
        (request :: remaining)

/-- Attach the fixed positive diameter to the original targets while retaining their movement bounds. -/
private theorem requestsAtDiameter_targets
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (movementBound rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall (current : Endpoint) (endpoints : List Endpoint),
      EndpointMovementBound segment movementBound current endpoints ->
      RequestTargets segment movementBound rootDiameter current
        (PreparedSheetContinuation.Subdivision.requestsAtDiameter
          rootDiameter rootDiameterPositive endpoints)
  | _current, [], .nil _ => .nil _
  | _current, _endpoint :: _remaining, .cons head tail =>
      .cons head le_rfl
        (requestsAtDiameter_targets segment movementBound rootDiameter
          rootDiameterPositive _ _ tail)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The exact dyadic requests satisfy the geometric movement and retained diameter bounds. -/
private theorem dyadicRequests_targets
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (depth : Nat) (left right : Endpoint)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    RequestTargets segment
      (Geometric.Basic.quarterRadius
        (geometricMovement segment left.parameter right.parameter) depth)
      rootDiameter left
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth
        left right rootDiameter rootDiameterPositive) := by
  unfold PreparedSheetContinuation.Subdivision.dyadicRequests
  exact requestsAtDiameter_targets segment _ rootDiameter
    rootDiameterPositive left _
      (dyadicTargets_endpointMovementBound segment depth left right)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The point-error coefficient times the dyadic movement bound plus the root-error coefficient times the diameter
target.

Both coefficients use the original differential and segment; the movement term retains the requested interval and depth
separately from the root-diameter contribution. -/
@[expose] def localModelErrorBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) (left right : Fraction.Rational) :
    Fraction.Rational :=
  PreparedConstantModels.PreparedEdge.pointErrorCoefficient
      differential segment *
      Geometric.Basic.quarterRadius
        (geometricMovement segment left right) depth +
    PreparedConstantModels.PreparedEdge.rootErrorCoefficient
      differential segment * rootDiameter

set_option genInjectivity false in
/-- Retained point and root coefficients with their combined local error value.

The two retained error coefficients are nonnegative and bounded at the displayed
segment and request indices. They describe the same prepared movement and root
diameter used by each child certificate. -/
structure PreparedSegmentLocalErrorBounds where
  /-- The retained scalar coefficient multiplying geometric movement in the local-error formula. -/ pointCoefficient :
    Fraction.Rational
  /-- The retained scalar coefficient multiplying the root diameter in the local-error formula. -/ rootCoefficient :
    Fraction.Rational
  /-- The local model-error bound computed from those retained coefficients. -/ error : Fraction.Rational

constructive_injectivity PreparedSegmentLocalErrorBounds

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Compute the two local error coefficients and their combined bound with a shared denominator square.

The calculation retains the original segment's denominator floor, ambient power bounds, requested depth and diameter;
its fields expose the exact coefficient and error values. -/
@[expose] def preparedSegmentLocalErrorBounds {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) (left right : Fraction.Rational) :
    PreparedSegmentLocalErrorBounds :=
  let denominator :=
    PreparedModels.segmentDenominatorLower segment
  let denominatorSq := denominator * denominator
  let pointCoefficient :=
    (2 *
        (Power.Bounds.IntegrationQuotientVariation.powerSlope ambient.normSqBound
            differential.exponent *
          (UniformSquareRootPreparation.rootAmbient
            segment).normSqBound)) /
      denominatorSq
  let rootCoefficient :=
    (2 * ambient.normSqBound ^ differential.exponent) / denominatorSq + 1
  { pointCoefficient := pointCoefficient
    rootCoefficient := rootCoefficient
    error := pointCoefficient *
        Geometric.Basic.quarterRadius
          (geometricMovement segment left right) depth +
      rootCoefficient * rootDiameter }

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- The retained point coefficient is exactly the original segment's point-error coefficient. -/
@[simp] theorem preparedSegmentLocalErrorBounds_pointCoefficient
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) (left right : Fraction.Rational) :
    (preparedSegmentLocalErrorBounds differential segment rootDiameter depth
      left right).pointCoefficient =
        PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment := rfl

/-- The retained root coefficient is exactly the original segment's root-error coefficient. -/
@[simp] theorem preparedSegmentLocalErrorBounds_rootCoefficient
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) (left right : Fraction.Rational) :
    (preparedSegmentLocalErrorBounds differential segment rootDiameter depth
      left right).rootCoefficient =
        PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment := rfl

/-- The retained computed error is exactly the specified local model-error bound. -/
@[simp] theorem preparedSegmentLocalErrorBounds_error
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) (left right : Fraction.Rational) :
    (preparedSegmentLocalErrorBounds differential segment rootDiameter depth
      left right).error =
        localModelErrorBound differential segment rootDiameter depth left
          right := rfl

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The local model-error bound is nonnegative when the diameter target is nonnegative. -/
theorem localModelErrorBound_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Fraction.Rational} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) (left right : Fraction.Rational) :
    0 <= localModelErrorBound differential segment rootDiameter depth
      left right := by
  unfold localModelErrorBound
  exact add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative
        differential segment)
      (Geometric.Basic.quarterRadius_nonneg
        (Norm.Basic.normSq_nonneg _) depth))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
        differential segment) rootDiameterNonnegative)

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- The finite maximum of the actual cached prepared-box squared diagonals, with terminal value zero. -/
@[expose] def subdivisionPreparedRootDiameterMaximum
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    PreparedSheetContinuation.Subdivision segment within left
        owner -> Fraction.Rational
  | .stop _ _ => 0
  | .next _ _ _ cached _ _ remaining =>
      max cached.preparedOwner.track.initial.box.diagonalSq
        (subdivisionPreparedRootDiameterMaximum remaining)

/-- The maximum of the actual cached prepared-root diameters is nonnegative. -/
theorem subdivisionPreparedRootDiameterMaximum_nonnegative
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    forall subdivision :
        PreparedSheetContinuation.Subdivision segment within left
          owner,
      0 <= subdivisionPreparedRootDiameterMaximum subdivision
  | .stop _ _ => le_rfl
  | .next _ _ _ _ _ _ remaining =>
      (subdivisionPreparedRootDiameterMaximum_nonnegative remaining).trans
        (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _)

end

open Purelib.Data.Gaussian in
/-- The prepared edge's point movement is exactly its original segment's endpoint movement. -/
private theorem preparedEdge_pointMovement_eq_geometric {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edge : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) :
    edge.pointMovement = geometricMovement edge.segment edge.left.parameter
      edge.request.endpoint.parameter := by
  unfold PreparedConstantModels.PreparedEdge.pointMovement
    geometricMovement
  change Data.Gaussian.Norm.Basic.normSq
      (edge.localSegment.pointAt 1 - edge.localSegment.pointAt 0) = _
  rw [edge.localSegment.pointAt_one, edge.localSegment.pointAt_zero]

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- Bound every retained centered child's error using the common movement bound and the actual cached-root diameter
maximum.

The estimate uses the original segment coefficients and each cached prepared box; the requested diameter is not
substituted for the observed maximum. -/
private theorem centeredEdges_childModelErrorBound_at_actualMaximum
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound : Fraction.Rational) :
    forall {left : Endpoint}
      {owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter))}
      (subdivision : PreparedSheetContinuation.Subdivision segment
        within left owner)
      (centers : PreparedSubdivisionModelCore.CenterStates curve
        differential sheet subdivision),
      ChildMovementBound movementBound
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet subdivision centers) ->
        ChildModelErrorBound
          (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
            PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum subdivision)
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet subdivision centers)
  | _, _, .stop _ _, _, bounded => by
      simp only [PreparedSubdivisionModelCore.centeredEdges] at bounded
      cases bounded
      exact .nil
  | _, _, .next left owner request cached ordered small remaining, centers,
      .cons headMovement tailMovement => by
      let edge := PreparedSubdivisionModelCore.edgeOfStep curve
        differential segment within left owner request cached ordered small
          sheet
      have headRoot : edge.preparedRootDiameter <=
          subdivisionPreparedRootDiameterMaximum
            (.next left owner request cached ordered small remaining) := by
        exact Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _
      have headError : edge.modelErrorAllowance <=
          PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
            PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum
                (.next left owner request cached ordered small remaining) :=
        edge.modelErrorAllowance_le_of_separate_targets movementBound _
          headMovement headRoot
      have tailBound :=
        centeredEdges_childModelErrorBound_at_actualMaximum curve differential
          segment within sheet movementBound remaining centers.2 tailMovement
      have tailMaximumLe :
          subdivisionPreparedRootDiameterMaximum remaining <=
            subdivisionPreparedRootDiameterMaximum
              (.next left owner request cached ordered small remaining) :=
        Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _
      have scaledTailMaximumLe :
          PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum remaining <=
            PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment *
              subdivisionPreparedRootDiameterMaximum
                (.next left owner request cached ordered small remaining) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          tailMaximumLe
          (PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
            differential segment)
      exact .cons headError
        (tailBound.mono (add_le_add le_rfl scaledTailMaximumLe))

/-- Successful execution of the original request list retains the supplied movement and diameter-derived model-error
bounds.

The success equation identifies the actual canonical caches and recursive tail. The result holds for every center family
of that exact returned subdivision. -/
private theorem trySteps_childBounds {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound rootDiameter : Fraction.Rational) :
    forall (requests : List StepRequest) (left : Endpoint)
      (owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter)))
      {subdivision : PreparedSheetContinuation.Subdivision segment
        within left owner},
      RequestTargets segment movementBound rootDiameter left requests ->
      PreparedSheetContinuation.Subdivision.trySteps segment
          within left owner requests = some subdivision ->
      forall centers : PreparedSubdivisionModelCore.CenterStates curve
        differential sheet subdivision,
        ChildMovementBound movementBound
            (PreparedSubdivisionModelCore.centeredEdges curve
              differential sheet subdivision centers) /\
          ChildModelErrorBound
            (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
              PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment * rootDiameter)
            (PreparedSubdivisionModelCore.centeredEdges curve
              differential sheet subdivision centers)
  | [], left, owner, _subdivision, .nil _, success, centers => by
      simp only
        [PreparedSheetContinuation.Subdivision.trySteps] at success
      cases success
      exact ⟨ChildMovementBound.nil, ChildModelErrorBound.nil⟩
  | request :: remaining, left, owner, _subdivision,
      .cons movement diameter tailTargets, success, centers => by
      simp only
        [PreparedSheetContinuation.Subdivision.trySteps] at success
      split at success
      next ordered =>
        split at success
        next cachedSmall =>
          split at success
          next => contradiction
          next tail tailSuccess =>
            cases success
            let edge :=
              PreparedSubdivisionModelCore.edgeOfStep curve
                differential segment within left owner request
                  (PreparedSheetContinuation.CachedSource.canonical
                    segment left owner request) ordered cachedSmall sheet
            have edgeMovement : edge.pointMovement <= movementBound := by
              rw [preparedEdge_pointMovement_eq_geometric]
              exact movement
            have edgeError : edge.modelErrorAllowance <=
                PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential segment * movementBound +
                  PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential segment * rootDiameter := by
              exact edge.modelErrorAllowance_le_of_separate_targets
                movementBound rootDiameter edgeMovement
                  (edge.preparedRootDiameter_lt_requested.le.trans diameter)
            have tailBounds := trySteps_childBounds curve differential segment
              within sheet movementBound rootDiameter remaining request.endpoint
                (PreparedSheetContinuation.advanceCached segment
                  within left owner request
                    (PreparedSheetContinuation.CachedSource.canonical
                      segment left owner request) cachedSmall)
                tailTargets tailSuccess centers.2
            exact ⟨ChildMovementBound.cons edgeMovement tailBounds.1,
              ChildModelErrorBound.cons edgeError tailBounds.2⟩
        next => contradiction
      next => contradiction

/-- The original subdivision's request bounds imply movement and model-error bounds for every supplied center family. -/
private theorem subdivision_childBounds {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound rootDiameter : Fraction.Rational) :
    forall {left : Endpoint}
      {owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter))}
      (subdivision : PreparedSheetContinuation.Subdivision segment
        within left owner),
      RequestTargets segment movementBound rootDiameter left
          subdivision.requests ->
      forall centers : PreparedSubdivisionModelCore.CenterStates curve
        differential sheet subdivision,
        ChildMovementBound movementBound
            (PreparedSubdivisionModelCore.centeredEdges curve
              differential sheet subdivision centers) /\
          ChildModelErrorBound
            (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
              PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment * rootDiameter)
            (PreparedSubdivisionModelCore.centeredEdges curve
              differential sheet subdivision centers)
  | _, _, .stop left owner, .nil _, centers =>
      ⟨ChildMovementBound.nil, ChildModelErrorBound.nil⟩
  | _, _, .next left owner request cached ordered small remaining,
      .cons movement diameter tailTargets, centers => by
      let edge := PreparedSubdivisionModelCore.edgeOfStep curve
        differential segment within left owner request cached ordered small
          sheet
      have edgeMovement : edge.pointMovement <= movementBound := by
        rw [preparedEdge_pointMovement_eq_geometric]
        exact movement
      have edgeError : edge.modelErrorAllowance <=
          PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                differential segment * movementBound +
            PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                differential segment * rootDiameter :=
        edge.modelErrorAllowance_le_of_separate_targets movementBound
          rootDiameter edgeMovement
            (edge.preparedRootDiameter_lt_requested.le.trans diameter)
      have tailBounds := subdivision_childBounds curve differential segment
        within sheet movementBound rootDiameter remaining tailTargets centers.2
      exact ⟨ChildMovementBound.cons edgeMovement tailBounds.1,
        ChildModelErrorBound.cons edgeError tailBounds.2⟩

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The direct child's point movement is exactly the original segment's requested endpoint movement. -/
private theorem directChild_pointMovement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) (current right : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition
      parent.edge current)
    (ordered : current.parameter <= right.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (small : ClearSheetContinuation.variationBound
      parent.edge.segment current.parameter right.parameter <
        (PreparedSheetContinuation.prepared parent.edge.segment
          current (directOwner parent current position)
          (directRequest right rootDiameter
            rootDiameterPositive)).track.initial.clearance.bound) :
    (directChild parent current right position ordered rootDiameter
      rootDiameterPositive small).edge.pointMovement =
        geometricMovement parent.edge.segment current.parameter
          right.parameter := by
  unfold PreparedConstantModels.PreparedEdge.pointMovement
    geometricMovement directChild directChildEdge
  change Data.Gaussian.Norm.Basic.normSq
      ((PreparedModels.edge curve parent.edge.segment
        parent.edge.within current
          (directRequest right rootDiameter rootDiameterPositive)).pointAt 1 -
       (PreparedModels.edge curve parent.edge.segment
        parent.edge.within current
          (directRequest right rootDiameter rootDiameterPositive)).pointAt 0) = _
  unfold PreparedModels.edge
  rw [Geometry.ClearPath.ClearSegment.pointAt_one,
    Geometry.ClearPath.ClearSegment.pointAt_zero]
  dsimp only [directRequest]

/-- Append root comparison blocks at the same original parent while retaining the actual ordered children. -/
@[expose] public def appendRootChildBlock {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential} :
    forall {first second : List (CenteredEdge curve differential)},
      PreparedSubdivisionModelCore.RootChildBlock parent first ->
      PreparedSubdivisionModelCore.RootChildBlock parent second ->
        PreparedSubdivisionModelCore.RootChildBlock parent
          (first ++ second)
  | [], _second, .nil, secondBlock => secondBlock
  | _ :: _, _second, .cons head tail, secondBlock =>
      .cons head (appendRootChildBlock tail secondBlock)

/-- Concatenating strictly ordered centered edge lists preserves strictness of every original edge. -/
public theorem allParentsProper_append {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {first second : List (CenteredEdge curve differential)},
      PreparedDyadicRefinements.AllParentsProper first ->
      PreparedDyadicRefinements.AllParentsProper second ->
      PreparedDyadicRefinements.AllParentsProper (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _ :: _, _second, firstProper, secondProper =>
      ⟨firstProper.1,
        allParentsProper_append firstProper.2 secondProper⟩

/-- Recasting the original centered edges preserves their strict endpoint ordering. -/
theorem allParentsProper_map_recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source target : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve source)},
      PreparedDyadicRefinements.AllParentsProper parents ->
      PreparedDyadicRefinements.AllParentsProper
        (parents.map (recastCenteredEdge target))
  | [], _proper => trivial
  | _ :: _, proper =>
      ⟨proper.1, allParentsProper_map_recast proper.2⟩

set_option linter.unusedVariables false in
set_option genInjectivity false in
open Purelib.Geometry.Path.Gaussian in
/-- Original centered edges joined at their exact lifted coordinate and sheet endpoints.

The dependent chain retains each actual edge and its successor endpoint rather than rebuilding an unindexed path
description. -/
inductive DirectPathChain {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    (parents : List (CenteredEdge curve differential)) ->
      {start finish : Lifted.Basic.LiftedPoint 2} -> Type 2
  /-- The empty chain at the original lifted point. -/ | nil (point : Lifted.Basic.LiftedPoint 2) : DirectPathChain []
    (start := point)
      (finish := point)
  /-- Join the original head edge to the retained tail at its exact requested lifted endpoint. -/ | cons (parent :
    CenteredEdge curve differential)
      {remaining : List (CenteredEdge curve differential)}
      {finish : Lifted.Basic.LiftedPoint 2}
      (tail : DirectPathChain remaining
        (start :=
          { coordinate := parent.edge.segment.pointAt
              parent.edge.request.endpoint.parameter
            sheet := parent.edge.sheet })
        (finish := finish)) :
      DirectPathChain (parent :: remaining)
        (start :=
          { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
            sheet := parent.edge.sheet })
        (finish := finish)

constructive_injectivity DirectPathChain

namespace DirectPathChain

section
open Purelib.Geometry.Path.Gaussian
/-- The first original child starts at the actual retained chain's initial coordinate.

The supplied nonempty chain begins with this retained child, whose
original starting-point equation identifies the same coordinate. -/
theorem head_coordinate {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {child : CenteredEdge curve differential} {children : List (CenteredEdge curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (DirectPathChain (child :: children) (start := first) (finish := last))) :
    child.edge.point 0 = first.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain
  exact child.edge.point_zero

/-- Removing the first original child retains a chain from its actual terminal coordinate.

The supplied chain's tail retains the original remaining children and
finish endpoint, starting at the exact head child's terminal point. -/
theorem tail_chain {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {child : CenteredEdge curve differential} {children : List (CenteredEdge curve differential)}
    {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (DirectPathChain (child :: children) (start := first) (finish := last))) :
    Nonempty (DirectPathChain children
      (start := ⟨child.edge.segment.pointAt child.edge.request.endpoint.parameter, child.edge.sheet⟩) (finish := last))
        := by
  obtain ⟨chain⟩ := chain
  cases chain with
  | cons _ tail => exact ⟨tail⟩

/-- A singleton original child chain ends at its actual child terminal coordinate.

The retained chain has no remaining child after its head. Its endpoint
equation identifies that original child's final coordinate. -/
theorem single_last {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {child : CenteredEdge curve differential} {first last : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (DirectPathChain [child] (start := first) (finish := last))) :
    child.edge.point 1 = last.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain with
  | cons _ tail =>
      cases tail
      exact child.edge.point_one

/-- Append original direct path chains at their identical retained lifted endpoint. -/
@[expose] def append {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : Lifted.Basic.LiftedPoint 2},
      DirectPathChain first (start := start) (finish := middle) ->
      DirectPathChain second (start := middle) (finish := finish) ->
        DirectPathChain (first ++ second) (start := start) (finish := finish)
  | [], _, _, _, _, .nil _, second => second
  | _ :: _, _, _, _, _, .cons parent tail, second =>
      .cons parent (append tail second)

end

/-- The centered model starts at its original segment's left request parameter. -/
public theorem model_start {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.start =
      parent.edge.segment.pointAt parent.edge.left.parameter := by
  change parent.edge.point 0 = _
  change
    (PreparedModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 0 = _
  unfold PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_zero] using
    (PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 0).symm

/-- The centered model finishes at its original segment's request endpoint parameter. -/
public theorem model_finish {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.finish =
      parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter := by
  change parent.edge.point 1 = _
  change
    (PreparedModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 1 = _
  unfold PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_one] using
    (PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 1).symm

open Purelib.Geometry.Path.Gaussian
/-- Read the lifted path by concatenating the original parent segments on their retained sheets. -/
@[expose] def path {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      DirectPathChain parents (start := start) (finish := finish) ->
        Lifted.Basic.LiftedPath 2 start finish
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons
        (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet
          parent.edge.localSegment)
        tail.path

/-- Read uniform certificates for the original parent models along their retained direct chain. -/
@[expose] def certificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : DirectPathChain parents (start := start) (finish := finish)),
      Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
        (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
        chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons (model_start parent) (model_finish parent)
        (parent.edge.centeredValidCertificate curve differential parent.center)
        tail.certificates

/-- Recast the original chain to a target differential while preserving all lifted endpoint indices. -/
@[expose] def recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      DirectPathChain parents (start := start) (finish := finish) ->
        DirectPathChain (parents.map (recastCenteredEdge target))
          (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons (recastCenteredEdge target parent) (recast target tail)

/-- Recasting the differential preserves the exact original lifted chain path. -/
theorem path_recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : DirectPathChain parents (start := start) (finish := finish)),
      (chain.recast target).path = chain.path
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons parent tail => by
      change
        Lifted.Basic.LiftedPath.cons
            (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet
              parent.edge.sheet parent.edge.localSegment)
            (recast target tail).path =
          Lifted.Basic.LiftedPath.cons
            (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet
              parent.edge.sheet parent.edge.localSegment)
            tail.path
      rw [path_recast target tail]

end DirectPathChain

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The actual dyadic children with their original root comparisons, geometry and separate movement and error bounds.

The block retains its child count, strict parameter ordering, lifted chain and certified path, together with the exact
total displacement of the requested interval. -/
structure LocalBlock {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) (left right : Endpoint)
    (depth : Nat) (rootDiameter : Fraction.Rational) where
  /-- The original ordered centered children retained by this block. -/ children : List (CenteredEdge curve
    differential)
  /-- There are exactly two to the retained depth child entries. -/ childCount : children.length = 2 ^ depth
  /-- Every retained parent or child interval is strictly increasing, as indexed by this record. -/ proper :
    PreparedDyadicRefinements.AllParentsProper children
  /-- The chain of this record's exact retained edge list at its original lifted endpoint indices. -/ chain :
    DirectPathChain children
    (start :=
      { coordinate := parent.edge.segment.pointAt left.parameter
        sheet := parent.edge.sheet })
    (finish :=
      { coordinate := parent.edge.segment.pointAt right.parameter
        sheet := parent.edge.sheet })
  /-- Root comparison certificates relating this exact parent to its retained child list. -/ roots :
    PreparedSubdivisionModelCore.RootChildBlock parent children
  /-- The retained lifted path through the block's original interval endpoints and sheet. -/ lifted :
    Lifted.Basic.LiftedPath 2
    ({ coordinate := parent.edge.segment.pointAt left.parameter
       sheet := parent.edge.sheet } : Lifted.Basic.LiftedPoint 2)
    ({ coordinate := parent.edge.segment.pointAt right.parameter
       sheet := parent.edge.sheet } : Lifted.Basic.LiftedPoint 2)
  /-- Uniform algebraic certificates for the exact child models on the retained lifted path. -/ certificates :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
    (children.map PreparedSubdivisionModelCore.CenteredEdge.model)
      lifted
  /-- Each child movement is bounded by the retained depth's quarter-scale original interval movement. -/ movements :
    ChildMovementBound
    (Geometric.Basic.quarterRadius
      (geometricMovement parent.edge.segment left.parameter right.parameter)
      depth) children
  /-- Each child model error is bounded by the original segment's retained diameter-and-depth local bound. -/ errors :
    ChildModelErrorBound
    (localModelErrorBound differential parent.edge.segment rootDiameter depth
      left.parameter right.parameter) children
  /-- The sum of the retained child model displacements equals the original interval displacement. -/ displacement_eq :
    Basic.PathModel.displacementSum
        (children.map
          PreparedSubdivisionModelCore.CenteredEdge.model) =
      parent.edge.segment.pointAt right.parameter -
        parent.edge.segment.pointAt left.parameter

constructive_injectivity LocalBlock

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Build a depth-zero local block from the actual accepted leaf and its strict endpoint order.

The original leaf cache supplies the canonical child, root comparison and lifted certificate; its movement and
prepared-root bound supply the separate local error estimate. -/
@[expose] def localBlockOfLeaf {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    (left right : Endpoint) (rootDiameter : Fraction.Rational)
    (leaf : CheckedDirectGeometry.Leaf parent.edge left right rootDiameter)
    (localProper : left.parameter < right.parameter) :
    LocalBlock parent left right 0 rootDiameter := by
  let child := leaf.centered
  have startEqual : child.model.start =
      parent.edge.segment.pointAt left.parameter := by
    change
      (PreparedModels.edge curve
        parent.edge.segment parent.edge.within left
          (directRequest right rootDiameter leaf.positive)).pointAt
          0 = parent.edge.segment.pointAt left.parameter
    unfold PreparedModels.edge
    simpa only [PreparedSheetContinuation.parameterAt_zero]
      using
        (PreparedSheetContinuation.pointAt_parameterAt
          parent.edge.segment parent.edge.within left
            (directRequest right rootDiameter leaf.positive) 0).symm
  have finishEqual : child.model.finish =
      parent.edge.segment.pointAt right.parameter := by
    change
      (PreparedModels.edge curve
        parent.edge.segment parent.edge.within left
          (directRequest right rootDiameter leaf.positive)).pointAt
          1 = parent.edge.segment.pointAt right.parameter
    unfold PreparedModels.edge
    simpa only [directRequest,
      PreparedSheetContinuation.parameterAt_one]
      using
        (PreparedSheetContinuation.pointAt_parameterAt
          parent.edge.segment parent.edge.within left
            (directRequest right rootDiameter leaf.positive) 1).symm
  have movementEqual : child.edge.pointMovement =
      geometricMovement parent.edge.segment left.parameter right.parameter := by
    unfold PreparedConstantModels.PreparedEdge.pointMovement geometricMovement
    change Data.Gaussian.Norm.Basic.normSq
      (child.model.finish - child.model.start) = _
    rw [startEqual, finishEqual]
  let lifted : Lifted.Basic.LiftedPath 2
      ({ coordinate := parent.edge.segment.pointAt left.parameter,
         sheet := parent.edge.sheet } : Lifted.Basic.LiftedPoint 2)
      ({ coordinate := parent.edge.segment.pointAt right.parameter,
         sheet := parent.edge.sheet } : Lifted.Basic.LiftedPoint 2) :=
    .cons
      (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet child.edge.sheet
        child.edge.localSegment)
      (.nil _)
  have childError : child.edge.modelErrorAllowance <=
      localModelErrorBound differential parent.edge.segment rootDiameter 0
        left.parameter right.parameter := by
    unfold localModelErrorBound
    apply child.edge.modelErrorAllowance_le_of_separate_targets
    · calc
        child.edge.pointMovement =
            geometricMovement parent.edge.segment left.parameter
              right.parameter :=
          movementEqual
        _ = Geometric.Basic.quarterRadius
            (geometricMovement parent.edge.segment left.parameter
              right.parameter) 0 := by
          rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
            Fraction.Field.mul_one_direct]
          exact Eq.refl _
        _ <= Geometric.Basic.quarterRadius
            (geometricMovement parent.edge.segment left.parameter
              right.parameter) 0 := le_rfl
    · exact child.edge.preparedRootDiameter_lt_requested.le
  exact
    { children := [child]
      childCount := rfl
      proper := ⟨localProper, trivial⟩
      chain := .cons child (.nil _)
      roots := .cons (leaf.rootChildAt parent) .nil
      lifted := lifted
      certificates := .cons startEqual finishEqual
        (child.edge.centeredValidCertificate curve differential child.center)
        (.nil _)
      movements := .cons (by
        rw [movementEqual]
        simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct] using
            (le_refl
              (geometricMovement parent.edge.segment left.parameter
                right.parameter))) .nil
      errors := .cons childError .nil
      displacement_eq := by
        simp only [List.map_cons, List.map_nil,
          Basic.PathModel.displacementSum_cons,
          Basic.PathModel.displacementSum_nil,
          add_zero]
        exact
          PreparedSubdivisionModelCore.CenteredEdge.model_displacement
            child }

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- Join the exact left and right midpoint blocks to form the next dyadic level.

The constructor concatenates the original children, roots and certified geometry, transports each half's quarter-radius
bounds, and telescopes the retained displacement equations. -/
@[expose] def localBlockAppend {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    (depth : Nat) (left right : Endpoint) (rootDiameter : Fraction.Rational)
    (first : LocalBlock parent left (CheckedDirectGeometry.midpoint left right)
      depth rootDiameter)
    (second : LocalBlock parent (CheckedDirectGeometry.midpoint left right) right
      depth rootDiameter) : LocalBlock parent left right (depth + 1) rootDiameter := by
  have firstMovements : ChildMovementBound
      (Geometric.Basic.quarterRadius
        (geometricMovement parent.edge.segment left.parameter
          right.parameter) (depth + 1)) first.children := by
    apply castChildMovementBound _ first.movements
    dsimp only [CheckedDirectGeometry.midpoint]
    rw [geometricMovement_left_midpoint, quarterRadius_div_four]
  have secondMovements : ChildMovementBound
      (Geometric.Basic.quarterRadius
        (geometricMovement parent.edge.segment left.parameter
          right.parameter) (depth + 1)) second.children := by
    apply castChildMovementBound _ second.movements
    dsimp only [CheckedDirectGeometry.midpoint]
    rw [geometricMovement_midpoint_right, quarterRadius_div_four]
  have firstErrors : ChildModelErrorBound
      (localModelErrorBound differential parent.edge.segment rootDiameter
        (depth + 1) left.parameter right.parameter) first.children := by
    apply castChildModelErrorBound _ first.errors
    unfold localModelErrorBound
    dsimp only [CheckedDirectGeometry.midpoint]
    rw [geometricMovement_left_midpoint, quarterRadius_div_four]
  have secondErrors : ChildModelErrorBound
      (localModelErrorBound differential parent.edge.segment rootDiameter
        (depth + 1) left.parameter right.parameter) second.children := by
    apply castChildModelErrorBound _ second.errors
    unfold localModelErrorBound
    dsimp only [CheckedDirectGeometry.midpoint]
    rw [geometricMovement_midpoint_right, quarterRadius_div_four]
  exact
    { children := first.children ++ second.children
      childCount := by
        rw [Append.length_append, first.childCount, second.childCount,
          pow_succ]
        omega
      proper := allParentsProper_append first.proper second.proper
      chain := first.chain.append second.chain
      roots := appendRootChildBlock first.roots second.roots
      lifted := first.lifted.append second.lifted
      certificates := by
        simpa only [Map.map_append] using
          Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates.append first.lifted
            first.certificates
            second.certificates
      movements := appendChildMovementBound firstMovements secondMovements
      errors := appendChildModelErrorBound firstErrors secondErrors
      displacement_eq := by
        rw [Map.map_append, displacementSum_append,
          first.displacement_eq, second.displacement_eq]
        apply Basic.ext <;>
          simp only [Basic.add_re,
            Basic.add_im,
            Basic.sub_re,
            Basic.sub_im] <;> ring1 }

/-- Read a certified local block from the actual checked dyadic mesh.

Each leaf is retained directly, and each original midpoint split is combined with its exact left and right block
certificates. -/
@[expose] def checkedLocalBlock {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    (rootDiameter : Fraction.Rational) : {depth : Nat} → {left right : Endpoint} →
    CheckedDirectGeometry.Mesh parent.edge rootDiameter depth left right →
      LocalBlock parent left right depth rootDiameter
  | _, left, right, .leaf data proper => localBlockOfLeaf parent left right rootDiameter data proper
  | depth + 1, left, right, .split first second =>
      localBlockAppend parent depth left right rootDiameter
        (checkedLocalBlock parent rootDiameter first) (checkedLocalBlock parent rootDiameter second)

/-- The certified local block retains exactly the original checked mesh's centered children. -/
private theorem checkedLocalBlock_children {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    {rootDiameter : Fraction.Rational} {depth : Nat} {left right : Endpoint}
    (mesh : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth left right) :
    (checkedLocalBlock parent rootDiameter mesh).children = mesh.children := by
  induction mesh with
  | leaf => rfl
  | split first second ihFirst ihSecond =>
      exact congrArg₂ List.append ihFirst ihSecond

section
open Purelib.Approximation.Rational
/-- Construct the exact direct dyadic mesh when the retained quarter-radius variation lies below the uniform preparation
floor.

Each leaf uses its original parent query owner and canonical cache. Midpoint recursion transports the bound to the two
original half intervals and retains strict endpoint order. -/
@[expose] public def uniformLocalMesh {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    (depth : Nat) -> (left right : Endpoint) ->
    parent.edge.left.parameter <= left.parameter ->
    right.parameter <= parent.edge.request.endpoint.parameter ->
    left.parameter <= right.parameter ->
    left.parameter < right.parameter ->
    Geometric.Basic.quarterRadius
        (ClearSheetContinuation.variationBound parent.edge.segment
          left.parameter right.parameter) depth <
      PreparedSheetContinuation.uniformPreparedClearanceFloor
        parent.edge.segment rootDiameter ->
          CheckedDirectGeometry.Mesh parent.edge rootDiameter depth left right
  | 0, left, right, lower, upper, ordered, localProper, below => by
      let position := PreparedSubdivisionModelCore.ParentPosition.ofBetween
        proper ⟨lower, ordered.trans upper⟩
      have variationBelow :
          ClearSheetContinuation.variationBound parent.edge.segment
              left.parameter right.parameter <
            PreparedSheetContinuation.uniformPreparedClearanceFloor
              parent.edge.segment rootDiameter := by
        simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct] using below
      let small := directChildSmall_of_variation_lt_uniform parent left right
        position rootDiameter rootDiameterPositive variationBelow
      let owner := directOwner parent left position
      let cached := PreparedSheetContinuation.CachedSource.canonical
        parent.edge.segment left owner (directRequest right rootDiameter rootDiameterPositive)
      let leaf : CheckedDirectGeometry.Leaf parent.edge left right rootDiameter :=
        { position := position
          owner := owner
          owner_eq := rfl
          positive := rootDiameterPositive
          ordered := ordered
          prepared := { cached := cached, small := small } }
      exact .leaf leaf localProper
  | depth + 1, left, right, lower, upper, ordered, localProper, below => by
      let middle : Endpoint :=
        ⟨ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      have leftOrdered : left.parameter <= middle.parameter :=
        ClearSheetContinuation.left_le_midpoint ordered
      have rightOrdered : middle.parameter <= right.parameter :=
        ClearSheetContinuation.midpoint_le_right ordered
      have leftProper : left.parameter < middle.parameter :=
        left_lt_midpoint localProper
      have rightProper : middle.parameter < right.parameter :=
        midpoint_lt_right localProper
      have leftBelow :
          Geometric.Basic.quarterRadius
              (ClearSheetContinuation.variationBound
                parent.edge.segment left.parameter middle.parameter) depth <
            PreparedSheetContinuation.uniformPreparedClearanceFloor
              parent.edge.segment rootDiameter := by
        change Geometric.Basic.quarterRadius
            (ClearSheetContinuation.variationBound
              parent.edge.segment left.parameter
                (ClearSheetContinuation.midpoint
                  left.parameter right.parameter)) depth < _
        rw [ClearSheetContinuation.variationBound_left_midpoint,
          quarterRadius_div_four]
        exact below
      have rightBelow :
          Geometric.Basic.quarterRadius
              (ClearSheetContinuation.variationBound
                parent.edge.segment middle.parameter right.parameter) depth <
            PreparedSheetContinuation.uniformPreparedClearanceFloor
              parent.edge.segment rootDiameter := by
        change Geometric.Basic.quarterRadius
            (ClearSheetContinuation.variationBound
              parent.edge.segment
                (ClearSheetContinuation.midpoint
                  left.parameter right.parameter) right.parameter) depth < _
        rw [ClearSheetContinuation.variationBound_midpoint_right,
          quarterRadius_div_four]
        exact below
      let first := uniformLocalMesh parent proper rootDiameter
        rootDiameterPositive depth left middle lower
          (rightOrdered.trans upper) leftOrdered leftProper leftBelow
      let second := uniformLocalMesh parent proper rootDiameter
        rootDiameterPositive depth middle right (lower.trans leftOrdered) upper
          rightOrdered rightProper rightBelow
      exact .split first second

/-- Certify the exact uniform direct mesh using its retained variation and endpoint bounds. -/
@[expose] public def localDyadicBlock {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    (depth : Nat) -> (left right : Endpoint) ->
    parent.edge.left.parameter <= left.parameter ->
    right.parameter <= parent.edge.request.endpoint.parameter ->
    left.parameter <= right.parameter ->
    left.parameter < right.parameter ->
    Geometric.Basic.quarterRadius
        (ClearSheetContinuation.variationBound parent.edge.segment
          left.parameter right.parameter) depth <
      PreparedSheetContinuation.uniformPreparedClearanceFloor
        parent.edge.segment rootDiameter ->
          LocalBlock parent left right depth rootDiameter
  | depth, left, right, lower, upper, ordered, localProper, below =>
      checkedLocalBlock parent rootDiameter
        (uniformLocalMesh parent proper rootDiameter rootDiameterPositive depth left right
          lower upper ordered localProper below)

/-- Recasting the differential preserves the actual local dyadic children up to the corresponding centered-edge recast.
-/
private theorem localDyadicBlock_children_recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (parent : CenteredEdge curve source)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    forall (depth : Nat) (left right : Endpoint)
      (lower : parent.edge.left.parameter <= left.parameter)
      (upper : right.parameter <= parent.edge.request.endpoint.parameter)
      (ordered : left.parameter <= right.parameter)
      (localProper : left.parameter < right.parameter)
      (below :
        Geometric.Basic.quarterRadius
            (ClearSheetContinuation.variationBound
              parent.edge.segment left.parameter right.parameter) depth <
          PreparedSheetContinuation.uniformPreparedClearanceFloor
            parent.edge.segment rootDiameter),
      (localDyadicBlock (recastCenteredEdge target parent) proper rootDiameter
          rootDiameterPositive depth left right lower upper ordered localProper
            below).children =
        (localDyadicBlock parent proper rootDiameter rootDiameterPositive depth
          left right lower upper ordered localProper below).children.map
            (recastCenteredEdge target) := by
  intro depth
  induction depth with
  | zero =>
      intro left right lower upper ordered localProper below
      dsimp only [localDyadicBlock, uniformLocalMesh, checkedLocalBlock, localBlockOfLeaf,
        CheckedDirectGeometry.Leaf.centered,
        CheckedDirectGeometry.Leaf.edge, directOwner]
      delta CheckedDirectGeometry.queryOwnerAt
      rfl
  | succ depth ih =>
      intro left right lower upper ordered localProper below
      dsimp only [localDyadicBlock, uniformLocalMesh, checkedLocalBlock,
        localBlockAppend]
      rw [Map.map_append]
      apply congrArg₂ List.append
      · exact ih _ _ _ _ _ _ _
      · exact ih _ _ _ _ _ _ _

end

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A complete direct dyadic child block retaining its depth, diameter and exact parent comparison.

The actual children carry their count, strict parameter order, lifted chain, root comparisons, uniform certificates and
separate movement and model-error bounds. Their total displacement is the original parent's displacement. -/
structure DirectParentBlock {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) where
  /-- The retained common dyadic subdivision depth. -/ depth : Nat
  /-- The retained requested root diameter indexing the checked construction. -/ rootDiameter : Fraction.Rational
  /-- The original ordered centered children retained by this block. -/ children : List (CenteredEdge curve
    differential)
  /-- There are exactly two to the retained depth child entries. -/ childCount : children.length = 2 ^ depth
  /-- Every retained parent or child interval is strictly increasing, as indexed by this record. -/ proper :
    PreparedDyadicRefinements.AllParentsProper children
  /-- The chain of this record's exact retained edge list at its original lifted endpoint indices. -/ chain :
    DirectPathChain children
    (start :=
      { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
        sheet := parent.edge.sheet })
    (finish :=
      { coordinate := parent.edge.segment.pointAt
          parent.edge.request.endpoint.parameter
        sheet := parent.edge.sheet })
  /-- Root comparison certificates relating this exact parent to its retained child list. -/ roots :
    PreparedSubdivisionModelCore.RootChildBlock parent children
  /-- The retained lifted path through the block's original interval endpoints and sheet. -/ lifted :
    Lifted.Basic.LiftedPath 2
    ({ coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
       sheet := parent.edge.sheet } : Lifted.Basic.LiftedPoint 2)
    ({ coordinate := parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter
       sheet := parent.edge.sheet } : Lifted.Basic.LiftedPoint 2)
  /-- Uniform algebraic certificates for the exact child models on the retained lifted path. -/ certificates :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
    (children.map PreparedSubdivisionModelCore.CenteredEdge.model)
      lifted
  /-- Each child movement is bounded by the retained depth's quarter-scale original interval movement. -/ movements :
    ChildMovementBound
    (Geometric.Basic.quarterRadius
      (geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter) depth) children
  /-- Each child model error is bounded by the original segment's retained diameter-and-depth local bound. -/ errors :
    ChildModelErrorBound
    (localModelErrorBound differential parent.edge.segment rootDiameter depth
      parent.edge.left.parameter parent.edge.request.endpoint.parameter)
    children
  /-- The sum of the exact child model displacements equals the original parent model displacement. -/ displacement_eq :
    Basic.PathModel.displacementSum
        (children.map
          PreparedSubdivisionModelCore.CenteredEdge.model) =
      parent.model.displacement

constructive_injectivity DirectParentBlock

/-- Package the exact endpoint-spanning local block as a complete parent block.

All child data and bounds are retained; the original parent displacement equation transports the existing local
displacement certificate. -/
@[expose] def parentBlockOfLocal {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    (depth : Nat) (rootDiameter : Fraction.Rational)
    (localBlock : LocalBlock parent parent.edge.left parent.edge.request.endpoint depth rootDiameter) :
    DirectParentBlock parent := by
  exact
    { depth := depth
      rootDiameter := rootDiameter
      children := localBlock.children
      childCount := localBlock.childCount
      proper := localBlock.proper
      chain := localBlock.chain
      roots := localBlock.roots
      lifted := localBlock.lifted
      certificates := localBlock.certificates
      movements := localBlock.movements
      errors := localBlock.errors
      displacement_eq := localBlock.displacement_eq.trans
        (PreparedSubdivisionModelCore.CenteredEdge.model_displacement
          parent).symm }

/-- Certify the original checked mesh over the parent's full endpoint interval as a direct parent block. -/
@[expose] def checkedParentBlock {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    (mesh : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
      parent.edge.left parent.edge.request.endpoint) : DirectParentBlock parent :=
  parentBlockOfLocal parent depth rootDiameter (checkedLocalBlock parent rootDiameter mesh)

/-- The certified parent block retains the exact input mesh depth. -/
@[simp] theorem checkedParentBlock_depth {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    (mesh : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
      parent.edge.left parent.edge.request.endpoint) :
    (checkedParentBlock parent mesh).depth = depth := rfl

/-- The certified parent block retains the exact input root-diameter target. -/
@[simp] theorem checkedParentBlock_rootDiameter {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve
  genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    (mesh : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
      parent.edge.left parent.edge.request.endpoint) :
    (checkedParentBlock parent mesh).rootDiameter = rootDiameter := rfl

/-- The certified parent block retains the exact original checked mesh children. -/
theorem checkedParentBlock_children {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    (mesh : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
      parent.edge.left parent.edge.request.endpoint) :
    (checkedParentBlock parent mesh).children = mesh.children :=
  checkedLocalBlock_children parent mesh

open Purelib.Approximation.Rational in
/-- Construct the parent's direct mesh at any depth above its original sufficient-depth bound.

The geometric quarter-radius estimate supplies uniform preparation clearance for the exact parent endpoint interval and
positive diameter target. -/
@[expose] def uniformParentMesh {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat)
    (enough :
      PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          rootDiameter <= depth) :
    CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
      parent.edge.left parent.edge.request.endpoint := by
  have laterLe := quarterRadius_antitone
    (ClearSheetContinuation.variationBound_nonneg
      parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter) enough
  have below := laterLe.trans_lt
    (PreparedSheetContinuation.Subdivision.sufficientDyadicDepth_variation_lt
      parent.edge.segment parent.edge.left parent.edge.request.endpoint
        rootDiameterPositive)
  let localBlock := uniformLocalMesh parent proper rootDiameter
    rootDiameterPositive depth parent.edge.left parent.edge.request.endpoint
      (le_refl _) (le_refl _) parent.edge.ordered proper below
  exact localBlock

/-- Construct the complete direct parent block at a certified sufficient depth. -/
@[expose] def directParentBlockAtDepth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat)
    (enough :
      PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          rootDiameter <= depth) :
    DirectParentBlock parent :=
  checkedParentBlock parent
    (uniformParentMesh parent proper rootDiameter rootDiameterPositive depth enough)

/-- Constructing the sufficient-depth block after recasting gives exactly the recast original children. -/
theorem directParentBlockAtDepth_children_recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (parent : CenteredEdge curve source)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat)
    (enough :
      PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          rootDiameter <= depth) :
    (directParentBlockAtDepth (recastCenteredEdge target parent) proper
        rootDiameter rootDiameterPositive depth enough).children =
      (directParentBlockAtDepth parent proper rootDiameter
        rootDiameterPositive depth enough).children.map
          (recastCenteredEdge target) := by
  unfold directParentBlockAtDepth checkedParentBlock parentBlockOfLocal uniformParentMesh
  apply localDyadicBlock_children_recast

/-- Construct the complete direct block at the original parent's sufficient depth for the positive diameter target. -/
@[expose] def directParentBlock {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    DirectParentBlock parent := by
  let depth :=
    PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
      parent.edge.segment parent.edge.left parent.edge.request.endpoint
        rootDiameter
  exact directParentBlockAtDepth parent proper rootDiameter
    rootDiameterPositive depth (le_refl _)

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- The centered cell allowance is its point movement times sixteen model-error allowances. -/
private theorem centeredEdge_weightedAllowance_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (child : CenteredEdge curve differential) :
    child.model.weightedAllowance =
      child.edge.pointMovement * (16 * child.edge.modelErrorAllowance) := by
  unfold PreparedSubdivisionModelCore.CenteredEdge.model
    Basic.CellModel.weightedAllowance
    Basic.CellModel.displacement
    PreparedConstantModels.PreparedEdge.centeredModel
    PreparedConstantModels.PreparedEdge.pointMovement
  rw [Norm.Basic.normSq_eq_canonical]

/-- The centered cell allowance is the original segment movement times its exact local allowance. -/
private theorem centeredEdge_weightedAllowance_eq_geometric {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.weightedAllowance =
      geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter *
          parent.model.localAllowance := by
  unfold Basic.CellModel.weightedAllowance
    geometricMovement
  rw [PreparedSubdivisionModelCore.CenteredEdge.model_displacement]
  rw [Norm.Basic.normSq_eq_canonical]

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The actual comparison allowance is child movement times twice the sum of the parent and child local allowances. -/
private theorem comparisonCenteredEdge_weightedAllowance_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : CenteredEdge curve differential) :
    (Basic.PathModel.comparisonCell
      parent.model child.model).weightedAllowance =
      child.edge.pointMovement *
        (2 * (parent.model.localAllowance +
          16 * child.edge.modelErrorAllowance)) := by
  unfold Basic.PathModel.comparisonCell
    Basic.PathModel.parentChildAllowance
    Basic.CellModel.withAllowance
    Basic.CellModel.weightedAllowance
    Basic.CellModel.displacement
    PreparedSubdivisionModelCore.CenteredEdge.model
    PreparedConstantModels.PreparedEdge.centeredModel
    PreparedConstantModels.PreparedEdge.pointMovement
  rw [Norm.Basic.normSq_eq_canonical]

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Separate bounds on the child's movement and model error bound its comparison allowance with the original parent. -/
private theorem comparisonCenteredEdge_weightedAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : CenteredEdge curve differential)
    (movementBound errorBound : Fraction.Rational)
    (movementLe : child.edge.pointMovement <= movementBound)
    (errorLe : child.edge.modelErrorAllowance <= errorBound) :
    (Basic.PathModel.comparisonCell
      parent.model child.model).weightedAllowance <=
      movementBound *
        (2 * (parent.model.localAllowance + 16 * errorBound)) := by
  have movementNonnegative : 0 <= child.edge.pointMovement :=
    Norm.Basic.normSq_nonneg _
  have movementBoundNonnegative : 0 <= movementBound :=
    movementNonnegative.trans movementLe
  have scaledErrorLe :
      16 * child.edge.modelErrorAllowance <= 16 * errorBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe
      (by decide)
  have allowanceLe :
      2 * (parent.model.localAllowance +
          16 * child.edge.modelErrorAllowance) <=
        2 * (parent.model.localAllowance + 16 * errorBound) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl scaledErrorLe) (by decide)
  have allowanceNonnegative :
      0 <= 2 * (parent.model.localAllowance +
        16 * child.edge.modelErrorAllowance) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg parent.model.localAllowance_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          child.edge.modelErrorAllowance_positive.le))
  rw [comparisonCenteredEdge_weightedAllowance_eq]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct movementLe allowanceLe
    allowanceNonnegative movementBoundNonnegative

/-- The sum of child weighted allowances is bounded by the child count times the retained movement and scaled-error
product. -/
private theorem totalWeightedAllowance_le_of_childBounds {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (movementBound errorBound : Fraction.Rational) :
    forall (children : List (CenteredEdge curve differential)),
      ChildMovementBound movementBound children ->
      ChildModelErrorBound errorBound children ->
      (Basic.PathModel.mk
        (children.map
          PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
        (children.length : Fraction.Rational) *
          (movementBound * (16 * errorBound))
  | [], .nil, .nil => by
      simp only [List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, List.length_nil, Nat.cast_zero,
        Fraction.Field.zero_mul_direct]
      exact le_rfl
  | child :: children, .cons movementHead movementTail,
      .cons errorHead errorTail => by
      have movementNonnegative : 0 <= child.edge.pointMovement :=
        Norm.Basic.normSq_nonneg _
      have movementBoundNonnegative : 0 <= movementBound :=
        movementNonnegative.trans movementHead
      have errorNonnegative : 0 <= child.edge.modelErrorAllowance :=
        child.edge.modelErrorAllowance_positive.le
      have scaledError :
          16 * child.edge.modelErrorAllowance <= 16 * errorBound :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorHead
          (by decide)
      have scaledErrorNonnegative :
          0 <= 16 * child.edge.modelErrorAllowance :=
        Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          errorNonnegative
      have headBound : child.model.weightedAllowance <=
          movementBound * (16 * errorBound) := by
        rw [centeredEdge_weightedAllowance_eq]
        exact Fraction.Order.Arithmetic.mul_le_mul_direct movementHead
          scaledError scaledErrorNonnegative movementBoundNonnegative
      have tailBound := totalWeightedAllowance_le_of_childBounds
        movementBound errorBound children movementTail errorTail
      simp only [List.map_cons,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons, List.length_cons, Nat.cast_succ]
      calc
        child.model.weightedAllowance +
            (children.map
              PreparedSubdivisionModelCore.CenteredEdge.model).foldr
                (fun cell total => cell.weightedAllowance + total) 0 <=
          movementBound * (16 * errorBound) +
            (children.length : Fraction.Rational) *
              (movementBound * (16 * errorBound)) :=
          add_le_add headBound tailBound
        _ = ((children.length : Fraction.Rational) + 1) *
            (movementBound * (16 * errorBound)) := by ring1

/-- The squared norm of the actual child integral sample is bounded by its movement bound times the retained
center-value bound.

The model uses its original constant center value; the supplied error allowance bounds that value and the movement bound
pays its exact displacement factor. -/
private theorem centeredEdge_integralSample_normSq_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (child : CenteredEdge curve differential)
    (movementBound errorBound : Fraction.Rational)
    (movementLe : child.edge.pointMovement <= movementBound)
    (errorLe : child.edge.modelErrorAllowance <= errorBound)
    (movementBoundNonnegative : 0 <= movementBound) :
    Data.Gaussian.Norm.Basic.normSq child.model.integralSample <=
      movementBound *
        PreparedConstantModels.PreparedEdge.centerValueNormSqBound
          differential child.edge.segment errorBound := by
  have centerLe := child.center.value_normSq_le errorBound errorLe
  have centerNonnegative :
      0 <= Data.Gaussian.Norm.Basic.normSq child.center.value :=
    Norm.Basic.normSq_nonneg _
  rw [Cell.Basic.CellModel.integralSample_constant
      child.model child.center.value (by rfl),
    Norm.Basic.normSq_mul]
  have displacementNorm :
      Data.Gaussian.Norm.Basic.normSq child.model.displacement =
        child.edge.pointMovement := by
    rfl
  rw [displacementNorm]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct movementLe centerLe
    centerNonnegative movementBoundNonnegative

end

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- Bound the sum of squared integral samples along the original prepared subdivision.

Common movement and model-error bounds give one scalar contribution per retained step, using the supplied center states
on the same segment and sheet. -/
private theorem centeredEdges_integralNormSqSum_le_of_childBounds
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    (movementBound errorBound : Fraction.Rational)
    (movementBoundNonnegative : 0 <= movementBound) :
    forall {left : Endpoint}
      {owner : Owner (curve.polynomial.eval
        (segment.pointAt left.parameter))}
      (subdivision : PreparedSheetContinuation.Subdivision segment
        within left owner)
      (centers : PreparedSubdivisionModelCore.CenterStates curve
        differential sheet subdivision),
      ChildMovementBound movementBound
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet subdivision centers) ->
      ChildModelErrorBound errorBound
          (PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet subdivision centers) ->
      Norm.Sum.Basic.gaussianNormSqSum
          ((PreparedSubdivisionModelCore.centeredEdges curve
            differential sheet subdivision centers).map
              fun child => child.model.integralSample) <=
        (subdivision.stepCount : Fraction.Rational) *
          (movementBound *
            PreparedConstantModels.PreparedEdge.centerValueNormSqBound
              differential segment errorBound)
  | _, _, .stop _ _, _, movementBounds, errorBounds => by
      simp only [PreparedSubdivisionModelCore.centeredEdges]
        at movementBounds errorBounds ⊢
      cases movementBounds
      cases errorBounds
      simp only [List.map_nil,
        Norm.Sum.Basic.gaussianNormSqSum,
        PreparedSheetContinuation.Subdivision.stepCount_stop,
        Nat.cast_zero, Fraction.Field.zero_mul_direct]
      exact le_rfl
  | _, _, .next left owner request cached ordered small remaining, centers,
      .cons movementHead movementTail, .cons errorHead errorTail => by
      let child : CenteredEdge curve differential :=
        { edge := PreparedSubdivisionModelCore.edgeOfStep curve
            differential segment within left owner request cached ordered small
              sheet
          center := centers.1 }
      have headBound := centeredEdge_integralSample_normSq_le child
        movementBound errorBound movementHead errorHead
          movementBoundNonnegative
      have tailBound :=
        centeredEdges_integralNormSqSum_le_of_childBounds curve differential
          segment within sheet movementBound errorBound
            movementBoundNonnegative remaining centers.2 movementTail errorTail
      simp only [Norm.Basic.normSq_eq_canonical] at headBound
      simp only [PreparedSubdivisionModelCore.centeredEdges,
        List.map_cons, Norm.Sum.Basic.gaussianNormSqSum,
        PreparedSheetContinuation.Subdivision.stepCount_next,
        Nat.cast_succ]
      calc
        Basic.Canonical.normSq child.model.integralSample +
            Norm.Sum.Basic.gaussianNormSqSum
              ((PreparedSubdivisionModelCore.centeredEdges curve
                differential sheet remaining centers.2).map
                  fun child => child.model.integralSample) <=
          movementBound *
              PreparedConstantModels.PreparedEdge.centerValueNormSqBound
                differential segment errorBound +
            (remaining.stepCount : Fraction.Rational) *
              (movementBound *
                PreparedConstantModels.PreparedEdge.centerValueNormSqBound
                  differential segment errorBound) :=
          add_le_add headBound tailBound
        _ = ((remaining.stepCount : Fraction.Rational) + 1) *
            (movementBound *
              PreparedConstantModels.PreparedEdge.centerValueNormSqBound
                differential segment errorBound) := by ring1

/-- The centered-edge list has exactly one entry per retained subdivision step. -/
private theorem centeredEdges_length_eq_stepCount {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision :
        PreparedSheetContinuation.Subdivision segment within left
          owner)
      (centers : PreparedSubdivisionModelCore.CenterStates curve
        differential sheet subdivision),
      (PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).length = subdivision.stepCount
  | .stop _ _, _ => rfl
  | .next _ _ _ _ _ _ remaining, centers => by
      simp only [PreparedSubdivisionModelCore.centeredEdges,
        List.length_cons,
        PreparedSheetContinuation.Subdivision.stepCount_next]
      exact congrArg Nat.succ
        (centeredEdges_length_eq_stepCount curve differential sheet remaining
          centers.2)

end

/-- Natural-number casts into the rational coordinate field are nonnegative. -/
theorem acceptedCoordinateNatCast_nonnegative (value : Nat) :
    (0 : Fraction.Rational) <= (value : Fraction.Rational) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- The total weighted-allowance bound for a complete dyadic segment at the requested root diameter.

Multiply the dyadic cell count by the quarter-scale movement and sixteen times the local model-error bound on the full
unit interval. -/
@[expose] def completeDyadicTotalWeightedBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) : Fraction.Rational :=
  ((2 ^ depth : Nat) : Fraction.Rational) *
    (Geometric.Basic.quarterRadius
        (geometricMovement segment
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter) depth *
      (16 * localModelErrorBound differential segment rootDiameter depth
        PreparedClearPathModels.zeroEndpoint.parameter
        PreparedClearPathModels.oneEndpoint.parameter))

/-- The fixed dyadic rounding precision, equal to thirty-two bits. -/
@[expose] def preflightDyadicPrecision : Nat := 32

/-- The rational power of two corresponding to the preflight rounding precision. -/
@[expose] def preflightDyadicScale : Fraction.Rational :=
  (2 : Fraction.Rational) ^ preflightDyadicPrecision

/-- Round a rational quantity upward to the fixed preflight dyadic grid using a natural ceiling.

For a nonnegative input, the result is an upper bound with denominator equal to the retained power-of-two scale. -/
@[expose] def dyadicPreflightUpper (source : Fraction.Rational) : Fraction.Rational :=
  Fraction.Cast.fromInt
      (Int.ofNat
        (Rounding.Floor.ceilNat
          (source * preflightDyadicScale))) /
    preflightDyadicScale

/-- The preflight power-of-two scale is strictly positive. -/
private theorem preflightDyadicScale_positive :
    (0 : Fraction.Rational) < preflightDyadicScale := by
  unfold preflightDyadicScale
  exact Fraction.Order.Arithmetic.pow_pos_direct (by decide)
    preflightDyadicPrecision

/-- A nonnegative rational quantity is at most its upward preflight dyadic rounding. -/
theorem le_dyadicPreflightUpper {source : Fraction.Rational}
    (nonnegative : 0 <= source) : source <= dyadicPreflightUpper source := by
  unfold dyadicPreflightUpper
  apply (Fraction.Order.Field.le_div_iff_pos
    preflightDyadicScale_positive).2
  have ceilingBound :=
    Rounding.Floor.le_natCast_ceilNat_of_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative
      preflightDyadicScale_positive.le)
  rw [Fraction.Cast.natCast_eq_fromInt] at ceilingBound
  exact ceilingBound

/-- The upward preflight rounding of a nonnegative input is nonnegative. -/
theorem dyadicPreflightUpper_nonnegative {source : Fraction.Rational}
    (nonnegative : 0 <= source) : 0 <= dyadicPreflightUpper source :=
  nonnegative.trans (le_dyadicPreflightUpper nonnegative)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- A nonnegative requested root diameter gives a nonnegative complete-segment weighted bound. -/
theorem completeDyadicTotalWeightedBound_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Fraction.Rational} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    0 <= completeDyadicTotalWeightedBound differential segment rootDiameter
      depth := by
  unfold completeDyadicTotalWeightedBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Geometric.Basic.quarterRadius_nonneg
        (Norm.Basic.normSq_nonneg _) depth)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (localModelErrorBound_nonnegative differential segment
          rootDiameterNonnegative depth
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter)))

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- Round the requested-diameter complete-segment weighted bound upward to the preflight dyadic grid. -/
@[expose] def completeDyadicTotalWeightedDyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) : Fraction.Rational :=
  dyadicPreflightUpper
    (completeDyadicTotalWeightedBound differential segment rootDiameter depth)

/-- For a nonnegative requested diameter, the dyadic preflight bound dominates the unrounded weighted bound. -/
theorem completeDyadicTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Fraction.Rational} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    completeDyadicTotalWeightedBound differential segment rootDiameter depth <=
      completeDyadicTotalWeightedDyadicBound differential segment rootDiameter
        depth :=
  le_dyadicPreflightUpper
    (completeDyadicTotalWeightedBound_nonnegative differential segment
      rootDiameterNonnegative depth)

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- The complete-segment weighted bound using the actual cached root-diameter maximum.

The retained prepared subdivision supplies its actual maximum diameter; the specified dyadic depth supplies the cell
count and geometric movement factor. -/
@[expose] def completePreparedDyadicTotalWeightedBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Fraction.Rational :=
  ((2 ^ depth : Nat) : Fraction.Rational) *
    (Geometric.Basic.quarterRadius
        (geometricMovement segment
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter) depth *
      (16 * localModelErrorBound differential segment
        (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter))

/-- The complete-segment weighted bound computed from actual prepared root diameters is nonnegative. -/
theorem completePreparedDyadicTotalWeightedBound_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    0 <= completePreparedDyadicTotalWeightedBound differential segment within
      owner prepared depth := by
  unfold completePreparedDyadicTotalWeightedBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Geometric.Basic.quarterRadius_nonneg
        (Norm.Basic.normSq_nonneg _) depth)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (localModelErrorBound_nonnegative differential segment
          (subdivisionPreparedRootDiameterMaximum_nonnegative
            prepared.subdivision) depth
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter)))

end

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Round the actual-cache complete-segment weighted bound upward to the preflight dyadic grid. -/
@[expose] def completePreparedDyadicTotalWeightedDyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Fraction.Rational :=
  dyadicPreflightUpper
    (completePreparedDyadicTotalWeightedBound differential segment within owner
      prepared depth)

/-- The dyadic preflight rounding dominates the weighted bound computed from actual caches. -/
theorem completePreparedDyadicTotalWeightedBound_le_dyadicBound
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    completePreparedDyadicTotalWeightedBound differential segment within owner
        prepared depth <=
      completePreparedDyadicTotalWeightedDyadicBound differential segment
        within owner prepared depth :=
  le_dyadicPreflightUpper
    (completePreparedDyadicTotalWeightedBound_nonnegative differential segment
      within owner prepared depth)

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A bound for the sum of squared integral samples at a requested root diameter and dyadic depth.

Each of the dyadic cells contributes its quarter-scale movement times the center-value squared-norm bound at the
corresponding local model error. -/
@[expose] def completeDyadicIntegralNormSqSumBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) : Fraction.Rational :=
  ((2 ^ depth : Nat) : Fraction.Rational) *
    (Geometric.Basic.quarterRadius
        (geometricMovement segment
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter) depth *
      PreparedConstantModels.PreparedEdge.centerValueNormSqBound
        differential segment
          (localModelErrorBound differential segment rootDiameter depth
            PreparedClearPathModels.zeroEndpoint.parameter
            PreparedClearPathModels.oneEndpoint.parameter))

/-- The requested-diameter squared-integral bound with the center-value residual estimate.

The dyadic count and movement are unchanged; the residual center-value bound provides an upper estimate for the original
center-value expression. -/
@[expose] def completeDyadicIntegralNormSqResidualBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) : Fraction.Rational :=
  ((2 ^ depth : Nat) : Fraction.Rational) *
    (Geometric.Basic.quarterRadius
        (geometricMovement segment
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter) depth *
      PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound
        differential segment
          (localModelErrorBound differential segment rootDiameter depth
            PreparedClearPathModels.zeroEndpoint.parameter
            PreparedClearPathModels.oneEndpoint.parameter))

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The residual center-value estimate dominates the requested-diameter sum-of-squared-integrals bound. -/
theorem completeDyadicIntegralNormSqSumBound_le_residual {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) :
    completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth <=
      completeDyadicIntegralNormSqResidualBound differential segment
        rootDiameter depth := by
  unfold completeDyadicIntegralNormSqSumBound
    completeDyadicIntegralNormSqResidualBound
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (PreparedConstantModels.PreparedEdge.centerValueNormSqBound_le_residual
        differential segment _)
    exact Geometric.Basic.quarterRadius_nonneg
      (Norm.Basic.normSq_nonneg _) depth
  · exact acceptedCoordinateNatCast_nonnegative _

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- A nonnegative requested root diameter makes the squared-integral residual bound nonnegative. -/
theorem completeDyadicIntegralNormSqResidualBound_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Fraction.Rational} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    0 <= completeDyadicIntegralNormSqResidualBound differential segment
      rootDiameter depth := by
  unfold completeDyadicIntegralNormSqResidualBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Geometric.Basic.quarterRadius_nonneg
        (Norm.Basic.normSq_nonneg _) depth)
      (PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound_nonnegative
        differential segment
        (localModelErrorBound_nonnegative differential segment
          rootDiameterNonnegative depth
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter)))

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- The natural-ceiling rational upper estimate of the requested-diameter squared-integral residual bound. -/
@[expose] def completeDyadicIntegralNormSqCeilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) : Fraction.Rational :=
  Fraction.Cast.fromInt
    (Int.ofNat
      (Rounding.Floor.ceilNat
        (completeDyadicIntegralNormSqResidualBound differential segment
          rootDiameter depth)))

/-- The natural-ceiling estimate bounds the squared-integral sum expression for a nonnegative requested diameter. -/
theorem completeDyadicIntegralNormSqSumBound_le_ceilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    {rootDiameter : Fraction.Rational} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) :
    completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth <=
      completeDyadicIntegralNormSqCeilBound differential segment rootDiameter
        depth := by
  unfold completeDyadicIntegralNormSqCeilBound
  have ceilingBound :=
    Rounding.Floor.le_natCast_ceilNat_of_nonneg
      (completeDyadicIntegralNormSqResidualBound_nonnegative differential
        segment rootDiameterNonnegative depth)
  rw [Fraction.Cast.natCast_eq_fromInt] at ceilingBound
  exact (completeDyadicIntegralNormSqSumBound_le_residual differential segment
    rootDiameter depth).trans ceilingBound

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- The sum-of-squared-integrals bound computed from the actual prepared root-diameter maximum.

The retained subdivision fixes the root error input, while the supplied depth determines the dyadic count and geometric
movement. -/
@[expose] def completePreparedDyadicIntegralNormSqSumBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Fraction.Rational :=
  ((2 ^ depth : Nat) : Fraction.Rational) *
    (Geometric.Basic.quarterRadius
        (geometricMovement segment
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter) depth *
      PreparedConstantModels.PreparedEdge.centerValueNormSqBound
        differential segment
          (localModelErrorBound differential segment
            (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
              PreparedClearPathModels.zeroEndpoint.parameter
              PreparedClearPathModels.oneEndpoint.parameter))

/-- The actual-cache sum-of-squared-integrals bound is nonnegative. -/
theorem completePreparedDyadicIntegralNormSqSumBound_nonnegative
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    0 <= completePreparedDyadicIntegralNormSqSumBound differential segment
      within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqSumBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Geometric.Basic.quarterRadius_nonneg
        (Norm.Basic.normSq_nonneg _) depth)
      (PreparedConstantModels.PreparedEdge.centerValueNormSqBound_nonnegative
        differential segment
        (localModelErrorBound_nonnegative differential segment
          (subdivisionPreparedRootDiameterMaximum_nonnegative
            prepared.subdivision) depth
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter)))

/-- The actual-cache sum-of-squared-integrals bound using the residual center-value estimate. -/
@[expose] def completePreparedDyadicIntegralNormSqResidualBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Fraction.Rational :=
  ((2 ^ depth : Nat) : Fraction.Rational) *
    (Geometric.Basic.quarterRadius
        (geometricMovement segment
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter) depth *
      PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound
        differential segment
          (localModelErrorBound differential segment
            (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
              PreparedClearPathModels.zeroEndpoint.parameter
              PreparedClearPathModels.oneEndpoint.parameter))

/-- The residual estimate dominates the actual-cache squared-integral sum bound. -/
theorem completePreparedDyadicIntegralNormSqSumBound_le_residual
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth <=
      completePreparedDyadicIntegralNormSqResidualBound differential segment
        within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqSumBound
    completePreparedDyadicIntegralNormSqResidualBound
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (PreparedConstantModels.PreparedEdge.centerValueNormSqBound_le_residual
        differential segment _)
    exact Geometric.Basic.quarterRadius_nonneg
      (Norm.Basic.normSq_nonneg _) depth
  · exact acceptedCoordinateNatCast_nonnegative _

/-- The actual-cache squared-integral residual bound is nonnegative. -/
theorem completePreparedDyadicIntegralNormSqResidualBound_nonnegative
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    0 <= completePreparedDyadicIntegralNormSqResidualBound differential segment
      within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqResidualBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (acceptedCoordinateNatCast_nonnegative _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Geometric.Basic.quarterRadius_nonneg
        (Norm.Basic.normSq_nonneg _) depth)
      (PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound_nonnegative
        differential segment
        (localModelErrorBound_nonnegative differential segment
          (subdivisionPreparedRootDiameterMaximum_nonnegative
            prepared.subdivision) depth
          PreparedClearPathModels.zeroEndpoint.parameter
          PreparedClearPathModels.oneEndpoint.parameter)))

end

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- The natural-ceiling rational estimate of the actual-cache squared-integral residual bound. -/
@[expose] def completePreparedDyadicIntegralNormSqCeilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : Fraction.Rational :=
  Fraction.Cast.fromInt
    (Int.ofNat
      (Rounding.Floor.ceilNat
        (completePreparedDyadicIntegralNormSqResidualBound differential segment
          within owner prepared depth)))

/-- The natural-ceiling estimate dominates the actual-cache squared-integral sum bound. -/
theorem completePreparedDyadicIntegralNormSqSumBound_le_ceilBound
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth <=
      completePreparedDyadicIntegralNormSqCeilBound differential segment
        within owner prepared depth := by
  unfold completePreparedDyadicIntegralNormSqCeilBound
  have ceilingBound :=
    Rounding.Floor.le_natCast_ceilNat_of_nonneg
      (completePreparedDyadicIntegralNormSqResidualBound_nonnegative
        differential segment within owner prepared depth)
  rw [Fraction.Cast.natCast_eq_fromInt] at ceilingBound
  exact (completePreparedDyadicIntegralNormSqSumBound_le_residual differential
    segment within owner prepared depth).trans ceilingBound

end

set_option genInjectivity false in
/-- The two scalar preflight estimates for a complete prepared segment.

The record stores a total weighted-allowance estimate and an estimate for the sum of squared integral samples; the
construction and projection laws specify their relation to the original prepared data. -/
structure PreparedSegmentPreflightBounds where
  /-- The upward rounded estimate of the retained total weighted allowance. -/ totalWeighted : Fraction.Rational
  /-- The natural-ceiling estimate for the retained sum of squared integral samples. -/ integralNormSqSum :
    Fraction.Rational

constructive_injectivity PreparedSegmentPreflightBounds

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Compute both complete-segment preflight estimates with shared local bounds.

Reuse the actual cached root-diameter maximum, dyadic movement and local-error coefficients. Round the weighted estimate
on the fixed dyadic grid and the squared-integral residual estimate to a natural ceiling. -/
@[expose] def completePreparedDyadicPreflightBounds {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) : PreparedSegmentPreflightBounds :=
  let count : Fraction.Rational := ((2 ^ depth : Nat) : Fraction.Rational)
  let movement := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let rootMaximum :=
    subdivisionPreparedRootDiameterMaximum prepared.subdivision
  let localBounds := preparedSegmentLocalErrorBounds differential segment rootMaximum
    depth PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let error := localBounds.error
  { totalWeighted :=
      dyadicPreflightUpper (count * (movement * (16 * error)))
    integralNormSqSum :=
      Fraction.Cast.fromInt
        (Int.ofNat
          (Rounding.Floor.ceilNat
            (count *
              (movement *
                PreparedConstantModels.PreparedEdge.centerValueNormSqResidualBound
                  differential segment error)))) }

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- The shared preflight computation returns the specified dyadic weighted-allowance estimate. -/
@[simp] theorem completePreparedDyadicPreflightBounds_totalWeighted
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    (completePreparedDyadicPreflightBounds differential segment within owner
      prepared depth).totalWeighted =
        completePreparedDyadicTotalWeightedDyadicBound differential segment within
          owner prepared depth := rfl

/-- The shared preflight computation returns the specified natural-ceiling squared-integral estimate. -/
@[simp] theorem completePreparedDyadicPreflightBounds_integralNormSqSum
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (depth : Nat) :
    (completePreparedDyadicPreflightBounds differential segment within owner
      prepared depth).integralNormSqSum =
        completePreparedDyadicIntegralNormSqCeilBound differential segment
          within owner prepared depth := rfl

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The requested-diameter aggregate allowance bound: dyadic count times the total weighted bound. -/
@[expose] def completeDyadicAggregateBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (rootDiameter : Fraction.Rational) (depth : Nat) : Fraction.Rational :=
  ((2 ^ depth : Nat) : Fraction.Rational) *
    completeDyadicTotalWeightedBound differential segment rootDiameter depth

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A successful complete dyadic preparation satisfies the requested-diameter total weighted bound.

The success equation identifies the original retained subdivision; its canonical centers and exact dyadic step count
supply the movement and model-error estimates. -/
theorem completeSegmentOfTryDyadic_totalWeightedAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSheetContinuation.Subdivision segment
      within PreparedClearPathModels.zeroEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      PreparedSheetContinuation.Subdivision.tryDyadic segment
          within PreparedClearPathModels.zeroEndpoint
            PreparedClearPathModels.oneEndpoint
              (PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    (Basic.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
      completeDyadicTotalWeightedBound differential segment rootDiameter
        depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential sheet subdivision
  have bounds := trySteps_childBounds curve differential segment within sheet
    movementBound rootDiameter
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      PreparedClearPathModels.zeroEndpoint
      (PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  change
    (Basic.PathModel.mk
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ bounds.1 bounds.2
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
          (PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at totalBound
  simpa only [completeDyadicTotalWeightedBound, movementBound, errorBound]
    using totalBound

/-- A successful complete dyadic preparation satisfies the weighted bound computed from its actual cached diameters. -/
theorem completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSheetContinuation.Subdivision segment
      within PreparedClearPathModels.zeroEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      PreparedSheetContinuation.Subdivision.tryDyadic segment
          within PreparedClearPathModels.zeroEndpoint
            PreparedClearPathModels.oneEndpoint
              (PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    (Basic.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
      completePreparedDyadicTotalWeightedBound differential segment within
        owner prepared depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum subdivision) depth
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential sheet subdivision
  have requestBounds := trySteps_childBounds curve differential segment within
    sheet movementBound rootDiameter
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      PreparedClearPathModels.zeroEndpoint
      (PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  change
    (Basic.PathModel.mk
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ requestBounds.1 actualErrorBound
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
          (PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at totalBound
  simpa only [completePreparedDyadicTotalWeightedBound, movementBound,
    errorBound, PreparedClearPathModels.CompleteSegment.ofTryDyadic]
    using totalBound

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A successful complete dyadic preparation satisfies the requested-diameter sum-of-squared-integrals bound. -/
theorem completeSegmentOfTryDyadic_integralNormSqSum_le
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSheetContinuation.Subdivision segment
      within PreparedClearPathModels.zeroEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      PreparedSheetContinuation.Subdivision.tryDyadic segment
          within PreparedClearPathModels.zeroEndpoint
            PreparedClearPathModels.oneEndpoint
              (PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    Norm.Sum.Basic.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential sheet subdivision
  have requestBounds := trySteps_childBounds curve differential segment within
    sheet movementBound rootDiameter
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      PreparedClearPathModels.zeroEndpoint
      (PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  have movementBoundNonnegative : 0 <= movementBound :=
    Geometric.Basic.quarterRadius_nonneg
      (Norm.Basic.normSq_nonneg _) depth
  change
    Norm.Sum.Basic.gaussianNormSqSum
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 requestBounds.2
  rw [PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
          (PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at sampleBound
  simpa only [completeDyadicIntegralNormSqSumBound, movementBound, errorBound,
    PreparedClearPathModels.CompleteSegment.ofTryDyadic]
    using sampleBound

/-- A successful complete dyadic preparation satisfies the sum-of-squared-integrals bound computed from its actual
caches. -/
theorem completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSheetContinuation.Subdivision segment
      within PreparedClearPathModels.zeroEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      PreparedSheetContinuation.Subdivision.tryDyadic segment
          within PreparedClearPathModels.zeroEndpoint
            PreparedClearPathModels.oneEndpoint
              (PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    Norm.Sum.Basic.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum subdivision) depth
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let centers :=
    PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential sheet subdivision
  have requestBounds := trySteps_childBounds curve differential segment within
    sheet movementBound rootDiameter
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      PreparedClearPathModels.zeroEndpoint
      (PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  have movementBoundNonnegative : 0 <= movementBound :=
    Geometric.Basic.quarterRadius_nonneg
      (Norm.Basic.normSq_nonneg _) depth
  change
    Norm.Sum.Basic.gaussianNormSqSum
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 actualErrorBound
  rw [PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
          (PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at sampleBound
  simpa only [completePreparedDyadicIntegralNormSqSumBound, movementBound,
    errorBound, PreparedClearPathModels.CompleteSegment.ofTryDyadic]
    using sampleBound

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A complete preparation with exactly the stated dyadic requests satisfies the requested-diameter weighted bound.

The request-list equality retains the original subdivision and supplies its exact dyadic count and movement estimates
without rerunning preparation. -/
theorem completePreparedSegment_totalWeightedAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    (Basic.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
      completeDyadicTotalWeightedBound differential segment rootDiameter
        depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := PreparedSubdivisionAutomaticModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have bounds := subdivision_childBounds curve differential segment within
    sheet movementBound rootDiameter subdivision targets centers
  change
    (Basic.PathModel.mk
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ bounds.1 bounds.2
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    dsimp only [PreparedSheetContinuation.Subdivision.dyadicRequests]
    rewrite [PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      ClearSheetContinuation.Subdivision.dyadicTargets_length]
    exact Eq.refl _
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers, stepCount] at totalBound
  simpa only [completeDyadicTotalWeightedBound, movementBound, errorBound]
    using totalBound

/-- A complete preparation with the stated dyadic requests satisfies the weighted bound using its actual cached
diameters. -/
theorem completePreparedSegment_preparedTotalWeightedAllowance_le
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    (Basic.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
      completePreparedDyadicTotalWeightedBound differential segment within
        owner prepared depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := PreparedSubdivisionAutomaticModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have requestBounds := subdivision_childBounds curve differential segment
    within sheet movementBound rootDiameter subdivision targets centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  change
    (Basic.PathModel.mk
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <= _
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ requestBounds.1 actualErrorBound
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    dsimp only [PreparedSheetContinuation.Subdivision.dyadicRequests]
    rewrite [PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      ClearSheetContinuation.Subdivision.dyadicTargets_length]
    exact Eq.refl _
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers, stepCount] at totalBound
  simpa only [completePreparedDyadicTotalWeightedBound, movementBound,
    errorBound, subdivision] using totalBound

end

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A complete preparation with the stated dyadic requests satisfies the requested-diameter squared-integral sum bound.
-/
theorem completePreparedSegment_integralNormSqSum_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    Norm.Sum.Basic.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completeDyadicIntegralNormSqSumBound differential segment rootDiameter
        depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := PreparedSubdivisionAutomaticModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have requestBounds := subdivision_childBounds curve differential segment
    within sheet movementBound rootDiameter subdivision targets centers
  have movementBoundNonnegative : 0 <= movementBound :=
    Geometric.Basic.quarterRadius_nonneg
      (Norm.Basic.normSq_nonneg _) depth
  change
    Norm.Sum.Basic.gaussianNormSqSum
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 requestBounds.2
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    dsimp only [PreparedSheetContinuation.Subdivision.dyadicRequests]
    rewrite [PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      ClearSheetContinuation.Subdivision.dyadicTargets_length]
    exact Eq.refl _
  rw [stepCount] at sampleBound
  simpa only [completeDyadicIntegralNormSqSumBound, movementBound, errorBound]
    using sampleBound

/-- A complete preparation with the stated dyadic requests satisfies the actual-cache squared-integral sum bound. -/
theorem completePreparedSegment_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (prepared : PreparedClearPathModels.CompleteSegment segment
      within owner)
    (requests_eq : prepared.subdivision.requests =
      PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive) :
    Norm.Sum.Basic.gaussianNormSqSum
      ((prepared.centeredEdges curve differential sheet).map
        fun child => child.model.integralSample) <=
      completePreparedDyadicIntegralNormSqSumBound differential segment within
        owner prepared depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment
    (subdivisionPreparedRootDiameterMaximum prepared.subdivision) depth
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let subdivision := prepared.subdivision
  let centers := PreparedSubdivisionAutomaticModels.canonicalCenterStates
    curve differential sheet subdivision
  have targets : RequestTargets segment movementBound rootDiameter
      PreparedClearPathModels.zeroEndpoint subdivision.requests := by
    rw [requests_eq]
    exact dyadicRequests_targets segment depth
      PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint rootDiameter
          rootDiameterPositive
  have requestBounds := subdivision_childBounds curve differential segment
    within sheet movementBound rootDiameter subdivision targets centers
  have actualErrorBound :=
    centeredEdges_childModelErrorBound_at_actualMaximum curve differential
      segment within sheet movementBound subdivision centers requestBounds.1
  have movementBoundNonnegative : 0 <= movementBound :=
    Geometric.Basic.quarterRadius_nonneg
      (Norm.Basic.normSq_nonneg _) depth
  change
    Norm.Sum.Basic.gaussianNormSqSum
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          fun child => child.model.integralSample) <= _
  have sampleBound :=
    centeredEdges_integralNormSqSum_le_of_childBounds curve differential
      segment within sheet movementBound errorBound movementBoundNonnegative
        subdivision centers requestBounds.1 actualErrorBound
  have stepCount : subdivision.stepCount = 2 ^ depth := by
    rw [← PreparedSheetContinuation.Subdivision.requests_length,
      requests_eq]
    dsimp only [PreparedSheetContinuation.Subdivision.dyadicRequests]
    rewrite [PreparedSheetContinuation.Subdivision.requestsAtDiameter_length,
      ClearSheetContinuation.Subdivision.dyadicTargets_length]
    exact Eq.refl _
  rw [stepCount] at sampleBound
  simpa only [completePreparedDyadicIntegralNormSqSumBound, movementBound,
    errorBound, subdivision] using sampleBound

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- A successful complete dyadic preparation satisfies the requested-diameter aggregate allowance bound.

Scale the total weighted bound by the exact retained dyadic cell count, matching the definition of aggregate allowance.
-/
theorem completeSegmentOfTryDyadic_aggregateAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : PreparedSheetContinuation.Subdivision segment
      within PreparedClearPathModels.zeroEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      PreparedSheetContinuation.Subdivision.tryDyadic segment
          within PreparedClearPathModels.zeroEndpoint
            PreparedClearPathModels.oneEndpoint
              (PreparedClearPathModels.ownerAtStart segment owner)
                depth rootDiameter rootDiameterPositive = some subdivision) :
    let prepared :=
      PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
        within owner depth rootDiameter rootDiameterPositive success
    (Basic.PathModel.mk
      ((prepared.centeredEdges curve differential sheet).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      completeDyadicAggregateBound differential segment rootDiameter depth := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement segment
      PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter) depth
  let errorBound := localModelErrorBound differential segment rootDiameter
    depth PreparedClearPathModels.zeroEndpoint.parameter
      PreparedClearPathModels.oneEndpoint.parameter
  let prepared :=
    PreparedClearPathModels.CompleteSegment.ofTryDyadic segment
      within owner depth rootDiameter rootDiameterPositive success
  let centers :=
    PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential sheet subdivision
  have bounds := trySteps_childBounds curve differential segment within sheet
    movementBound rootDiameter
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      PreparedClearPathModels.zeroEndpoint
      (PreparedClearPathModels.ownerAtStart segment owner)
      (dyadicRequests_targets segment depth
        PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint rootDiameter
            rootDiameterPositive)
      success centers
  change
    (Basic.PathModel.mk
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <= _
  unfold Basic.PathModel.aggregateAllowance
  rw [Map.length_map]
  have totalBound := totalWeightedAllowance_le_of_childBounds movementBound
    errorBound _ bounds.1 bounds.2
  have countNonnegative : (0 : Fraction.Rational) <=
      ((PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers).length : Fraction.Rational) :=
    acceptedCoordinateNatCast_nonnegative _
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
          (PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success] at scaled
  rw [centeredEdges_length_eq_stepCount curve differential sheet subdivision
      centers,
    PreparedSheetContinuation.Subdivision.tryDyadic_stepCount
      segment within PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
          (PreparedClearPathModels.ownerAtStart segment owner)
            depth rootDiameter rootDiameterPositive success]
  simpa only [completeDyadicAggregateBound,
    completeDyadicTotalWeightedBound, movementBound, errorBound] using scaled

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Bound the total parent-child comparison allowance from common child movement and model-error bounds.

Each retained child contributes its movement bound times twice the sum of the original parent's local allowance and
sixteen times the child-error bound. -/
private theorem totalComparisonAllowance_le_of_childBounds {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (movementBound errorBound : Fraction.Rational) :
    forall (children : List (CenteredEdge curve differential)),
      ChildMovementBound movementBound children ->
      ChildModelErrorBound errorBound children ->
      (Basic.PathModel.mk
        (children.map (fun child =>
          Basic.PathModel.comparisonCell
            parent.model child.model))).totalWeightedAllowance <=
        (children.length : Fraction.Rational) *
          (movementBound *
            (2 * (parent.model.localAllowance + 16 * errorBound)))
  | [], .nil, .nil => by
      simp only [List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, List.length_nil, Nat.cast_zero,
        Fraction.Field.zero_mul_direct]
      exact le_rfl
  | child :: children, .cons movementHead movementTail,
      .cons errorHead errorTail => by
      have headBound := comparisonCenteredEdge_weightedAllowance_le
        parent child movementBound errorBound movementHead errorHead
      have tailBound := totalComparisonAllowance_le_of_childBounds
        parent movementBound errorBound children movementTail errorTail
      simp only [List.map_cons,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons, List.length_cons, Nat.cast_succ]
      calc
        (Basic.PathModel.comparisonCell
            parent.model child.model).weightedAllowance +
            (children.map (fun remaining =>
              Basic.PathModel.comparisonCell
                parent.model remaining.model)).foldr
                (fun cell total => cell.weightedAllowance + total) 0 <=
          movementBound *
              (2 * (parent.model.localAllowance + 16 * errorBound)) +
            (children.length : Fraction.Rational) *
              (movementBound *
                (2 * (parent.model.localAllowance + 16 * errorBound))) :=
          add_le_add headBound tailBound
        _ = ((children.length : Fraction.Rational) + 1) *
            (movementBound *
              (2 * (parent.model.localAllowance + 16 * errorBound))) := by
          ring1

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Total weighted allowance is additive under concatenation of the original cell lists. -/
theorem totalWeightedAllowance_append
    (first second :
      List Basic.CellModel) :
    (Basic.PathModel.mk
      (first ++ second)).totalWeightedAllowance =
      (Basic.PathModel.mk
        first).totalWeightedAllowance +
      (Basic.PathModel.mk
        second).totalWeightedAllowance := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      rw [zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      change
        (remaining ++ second).foldr
            (fun resourceModel total => resourceModel.weightedAllowance + total) 0 =
          remaining.foldr
              (fun resourceModel total => resourceModel.weightedAllowance + total) 0 +
            second.foldr
              (fun resourceModel total => resourceModel.weightedAllowance + total) 0 at inductionHypothesis
      rw [inductionHypothesis]
      ring1

open Purelib.Data.Gaussian in
/-- The sum of squared Gaussian norms is additive under list concatenation. -/
theorem gaussianNormSqSum_append (first second : List Basic.Canonical) :
    Norm.Sum.Basic.gaussianNormSqSum (first ++ second) =
      Norm.Sum.Basic.gaussianNormSqSum first +
        Norm.Sum.Basic.gaussianNormSqSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        Norm.Sum.Basic.gaussianNormSqSum]
      rw [zero_add]
  | cons value remaining inductionHypothesis =>
      simp only [List.cons_append,
        Norm.Sum.Basic.gaussianNormSqSum]
      rw [inductionHypothesis]
      ring1

open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Transport a compatible constant-path refinement along an equality of its child-cell list. -/
@[expose] public def castCompatibleChildren
    {parents first second :
      List Basic.CellModel}
    (refinement : CompatibleConstantPathRefinement parents first)
    (equal : first = second) :
    CompatibleConstantPathRefinement parents second :=
  equal ▸ refinement

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Transport along a child-list equality preserves the original refinement's comparison allowance. -/
private theorem castCompatibleChildren_comparisonAllowance_eq
    {parents first second :
      List Basic.CellModel}
    (refinement : CompatibleConstantPathRefinement parents first)
    (equal : first = second) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (castCompatibleChildren
      refinement equal)) =
      (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance refinement) := by
  cases equal
  rfl

namespace DirectParentBlock

/-- Natural-number casts into the rational coordinate field are nonnegative. -/
private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Fraction.Rational) <= (value : Fraction.Rational) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

/-- Every natural power of a nonzero rational coordinate is nonzero. -/
private theorem coordinatePow_ne_zero (value : Fraction.Rational)
    (nonzero : value ≠ 0) : forall exponent : Nat, value ^ exponent ≠ 0
  | 0 => by
      change (1 : Fraction.Rational) ≠ 0
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact Fraction.Field.mul_ne_zero_direct
        (coordinatePow_ne_zero value nonzero exponent) nonzero

open Purelib.Approximation.Rational in
/-- The square of the dyadic cell count cancels the quarter-radius scaling exactly.

Both occurrences of the dyadic count use the displayed depth. The existing
quarter-radius cancellation applies to the original scalar without a sign condition. -/
private theorem dyadicCountSquare_mul_quarterRadius
    (scale : Fraction.Rational) (depth : Nat) :
    ((2 ^ depth : Nat) : Fraction.Rational) *
        (((2 ^ depth : Nat) : Fraction.Rational) *
          Geometric.Basic.quarterRadius scale depth) =
      scale :=
  Purelib.Approximation.Rational.Geometric.DyadicCount.dyadic_count_cancel scale depth

open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Replace each retained child model's local allowance by the same supplied nonnegative value.

The original child displacements and samples remain those of their models; only the common allowance is specified anew.
-/
@[expose] def constantAllowanceCells {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) (allowance : Fraction.Rational)
    (allowanceNonnegative : 0 <= allowance) :
    List Basic.CellModel :=
  block.children.map fun child =>
    child.model.withAllowance allowance allowanceNonnegative

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Common child movement bounds control total weighted allowance after assigning one nonnegative local allowance. -/
private theorem totalConstantAllowance_le_of_movements {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (movementBound allowance : Fraction.Rational)
    (allowanceNonnegative : 0 <= allowance) :
    forall (children : List (CenteredEdge curve differential)),
      ChildMovementBound movementBound children ->
      (Basic.PathModel.mk
        (children.map fun child =>
          child.model.withAllowance allowance
            allowanceNonnegative)).totalWeightedAllowance <=
        (children.length : Fraction.Rational) * (movementBound * allowance)
  | [], .nil => by
      simp only [List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, List.length_nil, Nat.cast_zero,
        Fraction.Field.zero_mul_direct]
      exact le_rfl
  | child :: children, .cons head tail => by
      have headBound :
          (child.model.withAllowance allowance
            allowanceNonnegative).weightedAllowance <=
            movementBound * allowance := by
        unfold Basic.CellModel.weightedAllowance
        rw [Basic.CellModel.withAllowance_displacement]
        rw [PreparedSubdivisionModelCore.CenteredEdge.model_displacement, ← Norm.Basic.normSq_eq_canonical]
        change geometricMovement child.edge.segment child.edge.left.parameter
          child.edge.request.endpoint.parameter * allowance <= movementBound * allowance
        rw [← preparedEdge_pointMovement_eq_geometric child.edge]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct head
          allowanceNonnegative
      have tailBound := totalConstantAllowance_le_of_movements movementBound
        allowance allowanceNonnegative children tail
      simp only [List.map_cons,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons, List.length_cons, Nat.cast_succ]
      calc
        (child.model.withAllowance allowance
              allowanceNonnegative).weightedAllowance +
            (children.map fun remaining =>
              remaining.model.withAllowance allowance
                allowanceNonnegative).foldr
              (fun resourceModel total => resourceModel.weightedAllowance + total) 0 <=
          movementBound * allowance +
            (children.length : Fraction.Rational) *
              (movementBound * allowance) :=
          add_le_add headBound tailBound
        _ = ((children.length : Fraction.Rational) + 1) *
            (movementBound * allowance) := by ring1

section
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Uniform-allowance child models have aggregate allowance at most the original interval movement times that allowance.

The retained child count and quarter-scale movement bounds cancel their dyadic factors exactly. -/
theorem constantAllowanceCells_aggregateAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) (allowance : Fraction.Rational)
    (allowanceNonnegative : 0 <= allowance) :
    (Basic.PathModel.mk
      (block.constantAllowanceCells allowance
        allowanceNonnegative)).aggregateAllowance <=
      geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter * allowance := by
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) block.depth
  have totalBound := totalConstantAllowance_le_of_movements movementBound
    allowance allowanceNonnegative block.children block.movements
  unfold Basic.PathModel.aggregateAllowance
  unfold constantAllowanceCells
  rw [Map.length_map, block.childCount]
  have countNonnegative :
      (0 : Fraction.Rational) <= ((2 ^ block.depth : Nat) : Fraction.Rational) :=
    coordinateNatCast_nonnegative _
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  rw [block.childCount] at scaled
  calc
    ((2 ^ block.depth : Nat) : Fraction.Rational) *
        (block.children.map fun child =>
          child.model.withAllowance allowance
            allowanceNonnegative).foldr
          (fun cell total => cell.weightedAllowance + total) 0 <=
      ((2 ^ block.depth : Nat) : Fraction.Rational) *
        (((2 ^ block.depth : Nat) : Fraction.Rational) *
          (movementBound * allowance)) := scaled
    _ = (((2 ^ block.depth : Nat) : Fraction.Rational) *
          (((2 ^ block.depth : Nat) : Fraction.Rational) * movementBound)) *
        allowance := by ring1
    _ = geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter * allowance := by
      rw [dyadicCountSquare_mul_quarterRadius]

/-- Bound a direct parent block's aggregate allowance by its dyadic count and common movement-error product. -/
theorem aggregateAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) :
    (Basic.PathModel.mk
      (block.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      ((2 ^ block.depth : Nat) : Fraction.Rational) *
        (((2 ^ block.depth : Nat) : Fraction.Rational) *
          (Geometric.Basic.quarterRadius
            (geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter) block.depth *
            (16 * localModelErrorBound differential parent.edge.segment
              block.rootDiameter block.depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter))) := by
  unfold Basic.PathModel.aggregateAllowance
  rw [Map.length_map, block.childCount]
  let movementBound := Geometric.Basic.quarterRadius
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) block.depth
  let errorBound := localModelErrorBound differential parent.edge.segment
    block.rootDiameter block.depth parent.edge.left.parameter
      parent.edge.request.endpoint.parameter
  have totalBound := totalWeightedAllowance_le_of_childBounds
    movementBound errorBound block.children block.movements block.errors
  have lengthNonnegative :
      (0 : Fraction.Rational) <= (block.children.length : Fraction.Rational) := by
    exact coordinateNatCast_nonnegative block.children.length
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
      lengthNonnegative
  rw [block.childCount] at scaled
  simpa only [movementBound, errorBound] using scaled

/-- A direct parent block's aggregate allowance is bounded by the original interval movement times sixteen times its
local model-error bound. -/
theorem aggregateAllowance_le_local {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) :
    (Basic.PathModel.mk
      (block.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (16 * localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) := by
  calc
    (Basic.PathModel.mk
        (block.children.map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      ((2 ^ block.depth : Nat) : Fraction.Rational) *
        (((2 ^ block.depth : Nat) : Fraction.Rational) *
          (Geometric.Basic.quarterRadius
            (geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter) block.depth *
            (16 * localModelErrorBound differential parent.edge.segment
              block.rootDiameter block.depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter))) :=
      block.aggregateAllowance_le
    _ = (((2 ^ block.depth : Nat) : Fraction.Rational) *
          (((2 ^ block.depth : Nat) : Fraction.Rational) *
            Geometric.Basic.quarterRadius
              (geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter) block.depth)) *
        (16 * localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) := by
      ring1
    _ = geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (16 * localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) := by
      rw [dyadicCountSquare_mul_quarterRadius]

end

/-- Read the compatible constant-path refinement from the retained root comparisons and displacement equalities. -/
@[expose] def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : CenteredEdge curve differential}
    (block : DirectParentBlock parent) :
    CompatibleConstantPathRefinement [parent.model]
      (block.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model) := by
  let refinement :=
    PreparedSubdivisionModelCore.CenteredEdgeRefinement.cons parent
      block.roots block.displacement_eq
      (PreparedSubdivisionModelCore.CenteredEdgeRefinement.nil
        (curve := curve) (differential := differential))
  simpa only [List.map_cons, List.map_nil, Purelib.Data.List.Append.append_nil] using
    refinement.toCompatible

end DirectParentBlock

set_option genInjectivity false in
/-- A direct refinement block for each entry of the original parent-edge list.

The dependent list retains each parent's own dyadic child block, including its geometric, root-comparison and
quantitative certificates. -/
inductive DirectBlockRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    List (CenteredEdge curve differential) -> Type 2
  /-- The empty original parent list has no refinement blocks. -/ | nil : DirectBlockRefinement []
  /-- Retain the direct block of the original head parent and the refinement of the original tail. -/ | cons {parent :
    CenteredEdge curve differential}
      {remaining : List (CenteredEdge curve differential)}
      (block : DirectParentBlock parent)
      (tail : DirectBlockRefinement remaining) :
      DirectBlockRefinement (parent :: remaining)

constructive_injectivity DirectBlockRefinement

namespace DirectBlockRefinement

/-- Concatenate the child-edge lists of the retained direct refinement blocks in parent order. -/
@[expose] def children {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    {parents : List (CenteredEdge curve differential)} ->
      DirectBlockRefinement parents ->
        List (CenteredEdge curve differential)
  | [], .nil => []
  | _ :: _, .cons block tail => block.children ++ tail.children

/-- Read the original centered-edge refinement from each direct block's root comparisons and displacement equality. -/
@[expose] def toCenteredEdgeRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      (blocks : DirectBlockRefinement parents),
      PreparedSubdivisionModelCore.CenteredEdgeRefinement parents
        blocks.children
  | [], .nil => .nil
  | _ :: _, .cons block tail =>
      .cons _ block.roots block.displacement_eq
        tail.toCenteredEdgeRefinement

/-- Read the compatible constant-path refinement from the retained root comparisons and displacement equalities. -/
@[expose] def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    (blocks : DirectBlockRefinement parents) :
    CompatibleConstantPathRefinement
      (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
      (blocks.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model) :=
  blocks.toCenteredEdgeRefinement.toCompatible

/-- Every child retained by a direct block refinement has a strictly increasing parameter interval. -/
theorem childrenProper {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      (blocks : DirectBlockRefinement parents),
      PreparedDyadicRefinements.AllParentsProper blocks.children
  | [], .nil => trivial
  | _ :: _, .cons block tail =>
      allParentsProper_append block.proper tail.childrenProper

open Purelib.Geometry.Path.Gaussian in
/-- Replace each parent of the supplied direct path chain by its retained child chain.

The resulting chain uses the exact concatenated child list and preserves the original lifted start and finish indices.
-/
@[expose] def refinedChain {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (blocks : DirectBlockRefinement parents),
      DirectPathChain parents (start := start) (finish := finish) ->
        DirectPathChain blocks.children (start := start) (finish := finish)
  | [], _, _, .nil, .nil point => .nil point
  | _ :: _, _, _, .cons block tailBlocks, .cons _ tailChain =>
      block.chain.append (refinedChain tailBlocks tailChain)

end DirectBlockRefinement

/-! ## Common-depth direct refinements -/

/-- The maximum sufficient dyadic preparation depth among the original parent edges.

Each parent's segment and endpoint interval is evaluated at the same requested root diameter; the empty parent list has
depth zero. -/
@[expose] def commonSufficientDepth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (rootDiameter : Fraction.Rational) :
    List (CenteredEdge curve differential) -> Nat
  | [] => 0
  | parent :: remaining =>
      max
        (PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
          parent.edge.segment parent.edge.left parent.edge.request.endpoint
            rootDiameter)
        (commonSufficientDepth rootDiameter remaining)

/-- Recasting the differential preserves the common sufficient preparation depth of the original edge list. -/
@[simp] theorem commonSufficientDepth_map_recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus) (rootDiameter : Fraction.Rational) :
    forall (parents : List (CenteredEdge curve source)),
      commonSufficientDepth rootDiameter
          (parents.map (recastCenteredEdge target)) =
        commonSufficientDepth rootDiameter parents
  | [] => rfl
  | _ :: remaining => by
      simp only [List.map, commonSufficientDepth,
        commonSufficientDepth_map_recast target rootDiameter remaining,
        recastCenteredEdge_segment, recastCenteredEdge_request,
        recastCenteredEdge_left]
      rfl

/-- The first parent's sufficient depth is bounded by the common maximum depth. -/
public theorem headSufficientDepth_le_common {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential))
    (rootDiameter : Fraction.Rational) :
    PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          rootDiameter <=
      commonSufficientDepth rootDiameter (parent :: remaining) :=
  Purelib.Data.Nat.Order.le_max_left _ _

/-- The remaining parents' common sufficient depth is bounded by that of the full list. -/
public theorem tailSufficientDepth_le_common {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential))
    (rootDiameter : Fraction.Rational) :
    commonSufficientDepth rootDiameter remaining <=
      commonSufficientDepth rootDiameter (parent :: remaining) :=
  Purelib.Data.Nat.Order.le_max_right _ _

set_option genInjectivity false in
/-- Direct parent blocks sharing the same retained dyadic depth and root-diameter request.

Each block keeps its original parent, children and certificates, together with equalities to the common numerical
indices. -/
inductive SynchronizedDirectBlockRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (depth : Nat) (rootDiameter : Fraction.Rational) :
    List (CenteredEdge curve differential) -> Type 2
  /-- The empty original parent list satisfies the common refinement indices. -/ | nil :
    SynchronizedDirectBlockRefinement depth rootDiameter []
  /-- Retain the original head block, equalities to the common depth and diameter, and the synchronized tail. -/ | cons
    {parent : CenteredEdge curve differential}
      {remaining : List (CenteredEdge curve differential)}
      (block : DirectParentBlock parent)
      (depth_eq : block.depth = depth)
      (rootDiameter_eq : block.rootDiameter = rootDiameter)
      (tail : SynchronizedDirectBlockRefinement depth rootDiameter remaining) :
      SynchronizedDirectBlockRefinement depth rootDiameter
        (parent :: remaining)

constructive_injectivity SynchronizedDirectBlockRefinement

namespace SynchronizedDirectBlockRefinement

/-- Forget the synchronization equalities while retaining every original direct parent block. -/
@[expose] def toDirect {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational} :
    {parents : List (CenteredEdge curve differential)} ->
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        DirectBlockRefinement parents
  | [], .nil => .nil
  | _ :: _, .cons block _ _ tail => .cons block tail.toDirect

/-- Concatenate the child-edge lists of the retained direct refinement blocks in parent order. -/
@[expose] def children {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational} :
    {parents : List (CenteredEdge curve differential)} ->
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        List (CenteredEdge curve differential)
  | [], .nil => []
  | _ :: _, .cons block _ _ tail => block.children ++ tail.children

/-- Forgetting synchronization preserves the exact concatenated child list. -/
theorem toDirect_children {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.toDirect.children = blocks.children
  | _, _, [], .nil => rfl
  | _, _, _ :: _, .cons block _ _ tail => by
      change block.children ++ tail.toDirect.children = block.children ++ tail.children
      exact congrArg (block.children ++ ·) (toDirect_children tail)

/-- The synchronized child list has the parent count times the common dyadic cell count entries.

Each retained block contributes its certified dyadic child count. Appending
the unchanged tail adds its original count to that of the head block. -/
theorem children_length {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.children.length = parents.length * 2 ^ depth
  | _, _, [], .nil => by
      change 0 = 0 * _
      exact (Nat.zero_mul _).symm
  | depth, _, _ :: remaining,
      .cons block depth_eq _ tail => by
      simp only [children]
      rw [Append.length_append, block.childCount, depth_eq,
        children_length tail]
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- Every child retained by a direct block refinement has a strictly increasing parameter interval. -/
theorem childrenProper {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    PreparedDyadicRefinements.AllParentsProper blocks.children := by
  induction blocks with
  | nil => trivial
  | cons block _ _ tail inductionHypothesis =>
      exact allParentsProper_append block.proper inductionHypothesis

open Purelib.Geometry.Path.Gaussian in
/-- Replace each parent of the supplied direct path chain by its retained child chain.

The resulting chain uses the exact concatenated child list and preserves the original lifted start and finish indices.
-/
@[expose] def refinedChain {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents)
    (chain : DirectPathChain parents (start := start) (finish := finish)) :
    DirectPathChain blocks.children (start := start) (finish := finish) := by
  rw [<- blocks.toDirect_children]
  exact blocks.toDirect.refinedChain chain

open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Concatenate the retained child models in original parent and child order. -/
@[expose] def models {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        List Basic.CellModel
  | _, _, [], .nil => []
  | _, _, _ :: _, .cons block _ _ tail =>
      block.children.map
          PreparedSubdivisionModelCore.CenteredEdge.model ++
        tail.models

/-- The synchronized model list is exactly the model projection of the retained child list.

The model projection is applied to the same concatenated child list.
The append certificate and retained tail equality preserve every occurrence. -/
theorem models_eq_children_map {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.models =
        blocks.children.map
          PreparedSubdivisionModelCore.CenteredEdge.model
  | _, _, [], .nil => rfl
  | _, _, _ :: _, .cons _ _ _ tail => by
      rewrite [models, children, Map.map_append, models_eq_children_map tail]
      exact Eq.refl _

/-- Read the compatible constant-path refinement from the retained root comparisons and displacement equalities. -/
@[expose] def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational} :
    {parents : List (CenteredEdge curve differential)} ->
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) ->
      CompatibleConstantPathRefinement
        (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
        blocks.models
  | [], .nil => .nil
  | _ :: _, .cons block _ _ tail =>
      .cons (block.roots.partitionCertificate block.displacement_eq)
        tail.toCompatible

/-- Transport the compatible refinement to the exact model projection of the retained child list. -/
@[expose] def toCompatibleChildren {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    CompatibleConstantPathRefinement
      (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
      (blocks.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model) :=
  castCompatibleChildren blocks.toCompatible blocks.models_eq_children_map

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Transporting to the child model projection preserves the original comparison allowance. -/
theorem toCompatibleChildren_comparisonAllowance_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance blocks.toCompatibleChildren) =
      (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance blocks.toCompatible) :=
  castCompatibleChildren_comparisonAllowance_eq _ _

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Construct each comparison cell from its own retained parent model and child model.

Concatenation follows the original parent blocks, so comparisons keep the parent associated with each child. -/
@[expose] def comparisonCells {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        List Basic.CellModel
  | _, _, [], .nil => []
  | _, _, parent :: _, .cons block _ _ tail =>
      block.children.map
          (Basic.PathModel.comparisonCell
            parent.model ∘
              PreparedSubdivisionModelCore.CenteredEdge.model) ++
        tail.comparisonCells

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The compatible refinement's comparison cells are exactly the synchronized parent-child comparison list.

The compatible refinement uses the same parent-child comparison operation.
Composition of the two displayed maps and the retained tail equality identify
the exact ordered comparison list. -/
theorem toCompatible_comparisonCells {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonCells blocks.toCompatible) =
        blocks.comparisonCells
  | _, _, [], .nil => rfl
  | _, _, parent :: _, .cons block _ _ tail => by
      change (block.children.map PreparedSubdivisionModelCore.CenteredEdge.model).map
          (Basic.PathModel.comparisonCell parent.model) ++
        CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonCells
          tail.toCompatible =
        block.children.map (Basic.PathModel.comparisonCell parent.model ∘
          PreparedSubdivisionModelCore.CenteredEdge.model) ++ tail.comparisonCells
      rewrite [Map.map_map, toCompatible_comparisonCells tail]
      exact Eq.refl _

open Purelib.Approximation.Rational in
/-- Sum one quarter-scale comparison contribution per original parent block.

Each contribution uses twice the sum of the parent's original local allowance and sixteen times the common-diameter
child model-error bound. -/
@[expose] def leafComparisonSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Fraction.Rational
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      Geometric.Basic.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) depth *
        (2 * (parent.model.localAllowance +
          16 * localModelErrorBound differential parent.edge.segment
            rootDiameter depth parent.edge.left.parameter
              parent.edge.request.endpoint.parameter)) +
        tail.leafComparisonSum

/-- Sum the comparison contributions with each original parent's full interval movement. -/
@[expose] def baseComparisonSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Fraction.Rational
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (2 * (parent.model.localAllowance +
          16 * localModelErrorBound differential parent.edge.segment
            rootDiameter depth parent.edge.left.parameter
              parent.edge.request.endpoint.parameter)) +
        tail.baseComparisonSum

/-- Sum original parent movements times thirty-two times the corresponding child model-error bound. -/
@[expose] def refinementErrorSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Fraction.Rational
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (32 * localModelErrorBound differential parent.edge.segment
          rootDiameter depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) +
        tail.refinementErrorSum

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The base comparison sum equals twice the original parents' total weighted allowance plus the refinement error sum.
-/
theorem baseComparisonSum_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.baseComparisonSum =
        2 * (Basic.PathModel.mk
          (parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance +
          blocks.refinementErrorSum
  | _, _, [], .nil => by
      simp only [baseComparisonSum, refinementErrorSum, List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, Fraction.Field.mul_zero_direct]
      ring1
  | _, _, parent :: _, .cons _ _ _ tail => by
      simp only [baseComparisonSum, refinementErrorSum, List.map_cons,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      rw [baseComparisonSum_eq tail,
        centeredEdge_weightedAllowance_eq_geometric]
      unfold Basic.PathModel.totalWeightedAllowance
      ring1

open Purelib.Approximation.Rational in
/-- Scaling the leaf comparison sum by the square of the dyadic count gives the base comparison sum.

The square of the common dyadic count cancels the quarter-radius factor in
each retained parent contribution, leaving the original comparison weights. -/
theorem scaledLeafComparisonSum_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      ((2 ^ depth : Nat) : Fraction.Rational) *
          (((2 ^ depth : Nat) : Fraction.Rational) * blocks.leafComparisonSum) =
        blocks.baseComparisonSum
  | _, _, [], .nil => by
      change _ * (_ * 0) = 0
      ring1
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail => by
      simp only [leafComparisonSum, baseComparisonSum]
      calc
        ((2 ^ depth : Nat) : Fraction.Rational) *
            (((2 ^ depth : Nat) : Fraction.Rational) *
              (Geometric.Basic.quarterRadius
                    (geometricMovement parent.edge.segment
                      parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) depth *
                  (2 * (parent.model.localAllowance +
                    16 * localModelErrorBound differential parent.edge.segment
                      rootDiameter depth parent.edge.left.parameter
                        parent.edge.request.endpoint.parameter)) +
                tail.leafComparisonSum)) =
          (((2 ^ depth : Nat) : Fraction.Rational) *
              (((2 ^ depth : Nat) : Fraction.Rational) *
                Geometric.Basic.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) depth)) *
              (2 * (parent.model.localAllowance +
                16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter)) +
            ((2 ^ depth : Nat) : Fraction.Rational) *
              (((2 ^ depth : Nat) : Fraction.Rational) *
                tail.leafComparisonSum) := by
          ring1
        _ = geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
              (2 * (parent.model.localAllowance +
                16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter)) +
            tail.baseComparisonSum := by
          rw [DirectParentBlock.dyadicCountSquare_mul_quarterRadius,
            scaledLeafComparisonSum_eq tail]

/-- The synchronized comparison list has one cell per retained child: parent count times the common dyadic count.

Every original child contributes one comparison cell against its own parent.
The count follows those same cached child blocks and the common dyadic depth. -/
theorem comparisonCells_length {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      blocks.comparisonCells.length = parents.length * 2 ^ depth
  | _, _, [], .nil => by
      change 0 = 0 * _
      exact (Nat.zero_mul _).symm
  | depth, _, _ :: remaining, .cons block depth_eq _ tail => by
      rewrite [comparisonCells, Append.length_append, Map.length_map, block.childCount, depth_eq,
        comparisonCells_length tail]
      change 2 ^ depth + remaining.length * 2 ^ depth = (remaining.length + 1) * 2 ^ depth
      rewrite [Nat.succ_mul]
      exact Nat.add_comm _ _

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The total weighted comparison allowance is bounded by the dyadic count times the leaf comparison sum. -/
theorem totalComparisonWeightedAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      (Basic.PathModel.mk
        blocks.comparisonCells).totalWeightedAllowance <=
        ((2 ^ depth : Nat) : Fraction.Rational) * blocks.leafComparisonSum
  | _, _, [], .nil => by
      simp only [comparisonCells, leafComparisonSum,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, Fraction.Field.mul_zero_direct]
      exact le_rfl
  | depth, rootDiameter, parent :: _,
      .cons block depth_eq rootDiameter_eq tail => by
      have headBound := totalComparisonAllowance_le_of_childBounds parent
        (Geometric.Basic.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) block.depth)
        (localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter)
        block.children block.movements block.errors
      rw [block.childCount, depth_eq, rootDiameter_eq] at headBound
      have normalizedHead :
          (Basic.PathModel.mk
            (block.children.map
              (Basic.PathModel.comparisonCell
                parent.model ∘
                PreparedSubdivisionModelCore.CenteredEdge.model))).totalWeightedAllowance <=
            ((2 ^ depth : Nat) : Fraction.Rational) *
              (Geometric.Basic.quarterRadius
                (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) depth *
                (2 * (parent.model.localAllowance +
                  16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter))) := by
        simpa only [Function.comp_def] using headBound
      have tailBound := totalComparisonWeightedAllowance_le tail
      simp only [comparisonCells, leafComparisonSum]
      rw [totalWeightedAllowance_append]
      calc
        (Basic.PathModel.mk
              (block.children.map
                (Basic.PathModel.comparisonCell
                  parent.model ∘
                  PreparedSubdivisionModelCore.CenteredEdge.model))).totalWeightedAllowance +
            (Basic.PathModel.mk
              tail.comparisonCells).totalWeightedAllowance <=
          ((2 ^ depth : Nat) : Fraction.Rational) *
                (Geometric.Basic.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) depth *
                  (2 * (parent.model.localAllowance +
                    16 * localModelErrorBound differential parent.edge.segment
                      rootDiameter depth parent.edge.left.parameter
                        parent.edge.request.endpoint.parameter))) +
            ((2 ^ depth : Nat) : Fraction.Rational) * tail.leafComparisonSum :=
          add_le_add normalizedHead tailBound
        _ = ((2 ^ depth : Nat) : Fraction.Rational) *
            (Geometric.Basic.quarterRadius
                (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) depth *
                (2 * (parent.model.localAllowance +
                  16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter)) +
              tail.leafComparisonSum) := by
          ring1

/-- Natural-number casts into the rational coordinate field are nonnegative. -/
private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Fraction.Rational) <= (value : Fraction.Rational) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The compatible refinement comparison allowance is bounded by the original parent count times its base comparison
sum. -/
theorem comparisonAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance blocks.toCompatible) <=
      (parents.length : Fraction.Rational) * blocks.baseComparisonSum := by
  unfold CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
    Basic.PathModel.aggregateAllowance
  rw [blocks.toCompatible_comparisonCells, blocks.comparisonCells_length]
  have totalBound := blocks.totalComparisonWeightedAllowance_le
  have countNonnegative :
      (0 : Fraction.Rational) <=
        ((parents.length * 2 ^ depth : Nat) : Fraction.Rational) :=
    coordinateNatCast_nonnegative _
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  calc
    ((parents.length * 2 ^ depth : Nat) : Fraction.Rational) *
          (Basic.PathModel.mk
            blocks.comparisonCells).totalWeightedAllowance <=
        ((parents.length * 2 ^ depth : Nat) : Fraction.Rational) *
          (((2 ^ depth : Nat) : Fraction.Rational) *
            blocks.leafComparisonSum) := scaled
    _ = (parents.length : Fraction.Rational) *
        (((2 ^ depth : Nat) : Fraction.Rational) *
          (((2 ^ depth : Nat) : Fraction.Rational) * blocks.leafComparisonSum)) := by
      rw [Purelib.Algebra.NatCast.mul]
      ring1
    _ = (parents.length : Fraction.Rational) * blocks.baseComparisonSum := by
      rw [blocks.scaledLeafComparisonSum_eq]

open Purelib.Approximation.Rational in
/-- Sum one quarter-scale child-allowance contribution per original parent block.

Each contribution uses sixteen times the local model-error bound at the synchronized diameter and depth. -/
@[expose] def leafChildAllowanceSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Fraction.Rational
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      Geometric.Basic.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) depth *
        (16 * localModelErrorBound differential parent.edge.segment
          rootDiameter depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) +
        tail.leafChildAllowanceSum

/-- Sum original parent movements times sixteen times their synchronized local model-error bounds. -/
@[expose] def baseChildAllowanceSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)},
      SynchronizedDirectBlockRefinement depth rootDiameter parents ->
        Fraction.Rational
  | _, _, [], .nil => 0
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (16 * localModelErrorBound differential parent.edge.segment
          rootDiameter depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) +
        tail.baseChildAllowanceSum

open Purelib.Approximation.Rational in
/-- The square of the dyadic count converts the leaf child-allowance sum into the base sum.

The cancellation uses the same common depth in every cached child block.
The remaining summands retain their original parent movement and error bound. -/
theorem scaledLeafChildAllowanceSum_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      ((2 ^ depth : Nat) : Fraction.Rational) *
          (((2 ^ depth : Nat) : Fraction.Rational) * blocks.leafChildAllowanceSum) =
        blocks.baseChildAllowanceSum
  | _, _, [], .nil => by
      change _ * (_ * 0) = 0
      ring1
  | depth, rootDiameter, parent :: _, .cons _ _ _ tail => by
      simp only [leafChildAllowanceSum, baseChildAllowanceSum]
      calc
        ((2 ^ depth : Nat) : Fraction.Rational) *
            (((2 ^ depth : Nat) : Fraction.Rational) *
              (Geometric.Basic.quarterRadius
                    (geometricMovement parent.edge.segment
                      parent.edge.left.parameter
                        parent.edge.request.endpoint.parameter) depth *
                  (16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) +
                tail.leafChildAllowanceSum)) =
          (((2 ^ depth : Nat) : Fraction.Rational) *
              (((2 ^ depth : Nat) : Fraction.Rational) *
                Geometric.Basic.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) depth)) *
              (16 * localModelErrorBound differential parent.edge.segment
                rootDiameter depth parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) +
            ((2 ^ depth : Nat) : Fraction.Rational) *
              (((2 ^ depth : Nat) : Fraction.Rational) *
                tail.leafChildAllowanceSum) := by
          ring1
        _ = geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
              (16 * localModelErrorBound differential parent.edge.segment
                rootDiameter depth parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) +
            tail.baseChildAllowanceSum := by
          rw [DirectParentBlock.dyadicCountSquare_mul_quarterRadius,
            scaledLeafChildAllowanceSum_eq tail]

/-- The synchronized model list has parent count times the common dyadic count entries. -/
theorem models_length {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    blocks.models.length = parents.length * 2 ^ depth := by
  rw [blocks.models_eq_children_map, Map.length_map,
    blocks.children_length]

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The child models' total weighted allowance is bounded by the dyadic count times the leaf child-allowance sum. -/
theorem totalModelWeightedAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      (Basic.PathModel.mk
        blocks.models).totalWeightedAllowance <=
        ((2 ^ depth : Nat) : Fraction.Rational) * blocks.leafChildAllowanceSum
  | _, _, [], .nil => by
      simp only [models, leafChildAllowanceSum,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, Fraction.Field.mul_zero_direct]
      exact le_rfl
  | depth, rootDiameter, parent :: _,
      .cons block depth_eq rootDiameter_eq tail => by
      have headBound := totalWeightedAllowance_le_of_childBounds
        (Geometric.Basic.quarterRadius
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) block.depth)
        (localModelErrorBound differential parent.edge.segment
          block.rootDiameter block.depth parent.edge.left.parameter
            parent.edge.request.endpoint.parameter)
        block.children block.movements block.errors
      rw [block.childCount, depth_eq, rootDiameter_eq] at headBound
      have tailBound := totalModelWeightedAllowance_le tail
      simp only [models, leafChildAllowanceSum]
      rw [totalWeightedAllowance_append]
      calc
        (Basic.PathModel.mk
              (block.children.map
                PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance +
            (Basic.PathModel.mk
              tail.models).totalWeightedAllowance <=
          ((2 ^ depth : Nat) : Fraction.Rational) *
                (Geometric.Basic.quarterRadius
                  (geometricMovement parent.edge.segment
                    parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter) depth *
                  (16 * localModelErrorBound differential parent.edge.segment
                    rootDiameter depth parent.edge.left.parameter
                      parent.edge.request.endpoint.parameter)) +
            ((2 ^ depth : Nat) : Fraction.Rational) *
              tail.leafChildAllowanceSum :=
          add_le_add headBound tailBound
        _ = ((2 ^ depth : Nat) : Fraction.Rational) *
            (Geometric.Basic.quarterRadius
                (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) depth *
                (16 * localModelErrorBound differential parent.edge.segment
                  rootDiameter depth parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter) +
              tail.leafChildAllowanceSum) := by
          ring1

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The child models' aggregate allowance is bounded by the original parent count times the base child-allowance sum. -/
theorem modelAllowance_le_baseChildAllowance {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    (Basic.PathModel.mk
      blocks.models).aggregateAllowance <=
      (parents.length : Fraction.Rational) * blocks.baseChildAllowanceSum := by
  unfold Basic.PathModel.aggregateAllowance
  rw [blocks.models_length]
  have totalBound := blocks.totalModelWeightedAllowance_le
  have countNonnegative :
      (0 : Fraction.Rational) <=
        ((parents.length * 2 ^ depth : Nat) : Fraction.Rational) :=
    coordinateNatCast_nonnegative _
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
      countNonnegative
  calc
    ((parents.length * 2 ^ depth : Nat) : Fraction.Rational) *
          (Basic.PathModel.mk
            blocks.models).totalWeightedAllowance <=
        ((parents.length * 2 ^ depth : Nat) : Fraction.Rational) *
          (((2 ^ depth : Nat) : Fraction.Rational) *
            blocks.leafChildAllowanceSum) := scaled
    _ = (parents.length : Fraction.Rational) *
        (((2 ^ depth : Nat) : Fraction.Rational) *
          (((2 ^ depth : Nat) : Fraction.Rational) *
            blocks.leafChildAllowanceSum)) := by
      rw [Purelib.Algebra.NatCast.mul]
      ring1
    _ = (parents.length : Fraction.Rational) * blocks.baseChildAllowanceSum := by
      rw [blocks.scaledLeafChildAllowanceSum_eq]

/-- Twice the base child-allowance sum equals the refinement error sum. -/
private theorem twice_baseChildAllowanceSum {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    2 * blocks.baseChildAllowanceSum = blocks.refinementErrorSum := by
  induction blocks with
  | nil =>
      change (2 : Fraction.Rational) * 0 = 0
      exact Fraction.Field.mul_zero_direct _
  | cons block depthEq diameterEq tail ih =>
      simp only [baseChildAllowanceSum, refinementErrorSum, mul_add]
      rw [ih]
      ring1

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Twice the child models' aggregate allowance is bounded by the parent count times the refinement error sum. -/
theorem twice_modelAllowance_le_refinementError {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents) :
    2 * (Basic.PathModel.mk blocks.models).aggregateAllowance ≤
      (parents.length : Fraction.Rational) * blocks.refinementErrorSum := by
  calc
    2 * (Basic.PathModel.mk blocks.models).aggregateAllowance ≤
        2 * ((parents.length : Fraction.Rational) * blocks.baseChildAllowanceSum) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        blocks.modelAllowance_le_baseChildAllowance (by decide)
    _ = (parents.length : Fraction.Rational) * blocks.refinementErrorSum := by
      rw [← blocks.twice_baseChildAllowanceSum]
      ring1

end SynchronizedDirectBlockRefinement

/-! ## Accuracy-selected synchronized refinements -/

/-- The sum of parent movement factors times sixty-four times their point and root error coefficients.

This retained-parent expression collects the coefficient of a common positive accuracy in the refinement-error estimate.
-/
@[expose] def refinementCoefficientSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) :
    List (CenteredEdge curve differential) -> Fraction.Rational
  | [] => 0
  | parent :: remaining =>
      geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter *
        (64 *
          (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
              differential parent.edge.segment +
            PreparedConstantModels.PreparedEdge.rootErrorCoefficient
              differential parent.edge.segment)) +
        refinementCoefficientSum differential remaining

open Purelib.Data.Gaussian in
/-- The sum of refinement coefficients of the original parent list is nonnegative. -/
theorem refinementCoefficientSum_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) :
    forall (parents : List (CenteredEdge curve differential)),
      0 <= refinementCoefficientSum differential parents
  | [] => le_rfl
  | parent :: remaining => by
      unfold refinementCoefficientSum
      have movementNonnegative :
          0 <= geometricMovement parent.edge.segment
            parent.edge.left.parameter
              parent.edge.request.endpoint.parameter := by
        unfold geometricMovement
        exact Norm.Basic.normSq_nonneg _
      have pointCoefficientNonnegative :=
        PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative
          differential parent.edge.segment
      have rootCoefficientNonnegative :=
        PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
          differential parent.edge.segment
      have coefficientNonnegative := add_nonneg pointCoefficientNonnegative
        rootCoefficientNonnegative
      have sixtyFourNonnegative : (0 : Fraction.Rational) <= 64 := by
        calc
          (0 : Fraction.Rational) <= 8 * 8 :=
            Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide)
          _ = 64 := by ring1
      have scaledCoefficientNonnegative :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          sixtyFourNonnegative coefficientNonnegative
      have headNonnegative :=
        Fraction.Order.Arithmetic.mul_nonneg_direct movementNonnegative
          scaledCoefficientNonnegative
      exact add_nonneg headNonnegative
        (refinementCoefficientSum_nonnegative differential remaining)

/-- Natural-number casts into the rational coordinate field are nonnegative. -/
private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Fraction.Rational) <= (value : Fraction.Rational) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

/-- The original parent count times the sum of refinement coefficients. -/
@[expose] def aggregateRefinementCoefficient {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    (parents : List (CenteredEdge curve differential)) : Fraction.Rational :=
  (parents.length : Fraction.Rational) *
    refinementCoefficientSum differential parents

/-- The aggregate refinement coefficient is nonnegative. -/
theorem aggregateRefinementCoefficient_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    (parents : List (CenteredEdge curve differential)) :
    0 <= aggregateRefinementCoefficient differential parents := by
  unfold aggregateRefinementCoefficient
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (coordinateNatCast_nonnegative parents.length)
    (refinementCoefficientSum_nonnegative differential parents)

open Purelib.Approximation.Rational in
/-- The maximum first quarter-scale index below the requested accuracy across the original parents.

Each search begins at zero and uses that parent's full interval movement; an empty parent list returns zero. -/
@[expose] def commonAccuracyDepth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (accuracy : Fraction.Rational) :
    List (CenteredEdge curve differential) -> Nat
  | [] => 0
  | parent :: remaining =>
      max
        (Geometric.Search.firstQuarterBelow
          (geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter) 0 accuracy)
        (commonAccuracyDepth accuracy remaining)

/-- Changing the differential preserves the common geometric accuracy depth. -/
@[simp] theorem commonAccuracyDepth_map_recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus) (accuracy : Fraction.Rational) :
    forall (parents : List (CenteredEdge curve source)),
      commonAccuracyDepth accuracy
          (parents.map (recastCenteredEdge target)) =
        commonAccuracyDepth accuracy parents
  | [] => rfl
  | _ :: remaining => by
      simp only [List.map, commonAccuracyDepth,
        commonAccuracyDepth_map_recast target accuracy remaining,
        recastCenteredEdge_segment, recastCenteredEdge_request,
        recastCenteredEdge_left]
      rfl

/-- Sum aggregate refinement coefficients over the supplied target differentials.

Each coefficient is computed on the original parent edges recast to that differential, retaining their geometry and root
owners. -/
@[expose] def differentialRefinementCoefficient {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source)) :
    List (Basic.Differential genus) -> Fraction.Rational
  | [] => 0
  | target :: remaining =>
      aggregateRefinementCoefficient target
          (parents.map (recastCenteredEdge target)) +
        differentialRefinementCoefficient parents remaining

/-- The sum of target-differential refinement coefficients is nonnegative. -/
theorem differentialRefinementCoefficient_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source)) :
    forall (targets : List (Basic.Differential genus)),
      0 <= differentialRefinementCoefficient parents targets
  | [] => le_rfl
  | target :: remaining =>
      add_nonneg
        (aggregateRefinementCoefficient_nonnegative target
          (parents.map (recastCenteredEdge target)))
        (differentialRefinementCoefficient_nonnegative parents remaining)

/-- A listed target differential's aggregate coefficient is bounded by the full target-list coefficient sum. -/
theorem aggregateRefinementCoefficient_leDifferential {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source))
    (target : Basic.Differential genus) :
    forall (targets : List (Basic.Differential genus)), target ∈ targets ->
      aggregateRefinementCoefficient target
          (parents.map (recastCenteredEdge target)) <=
        differentialRefinementCoefficient parents targets
  | [], member => by cases member
  | head :: remaining, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · subst head
        exact le_add_of_nonneg_right
          (differentialRefinementCoefficient_nonnegative parents remaining)
      · exact
          (aggregateRefinementCoefficient_leDifferential parents target
              remaining member).trans
            (le_add_of_nonneg_left
              (aggregateRefinementCoefficient_nonnegative head
                (parents.map (recastCenteredEdge head))))

/-- Divide the target error budget by one plus the sum of target-differential coefficients.

The common accuracy uses the same original parents for every recast differential; the extra one makes the denominator
positive. -/
@[expose] def differentialRefinementAccuracy {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source))
    (targets : List (Basic.Differential genus)) (target : Fraction.Rational) : Fraction.Rational :=
  target / (differentialRefinementCoefficient parents targets + 1)

/-- A positive target budget gives a positive common differential-refinement accuracy.

The coefficient sum is nonnegative, so adding one makes its denominator
strictly positive. Dividing the positive target by that denominator preserves positivity. -/
theorem differentialRefinementAccuracy_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source))
    (targets : List (Basic.Differential genus))
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < differentialRefinementAccuracy parents targets target := by
  unfold differentialRefinementAccuracy
  exact Fraction.Order.Field.div_pos_direct targetPositive
    (Purelib.Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (differentialRefinementCoefficient_nonnegative parents targets)
      (by decide))

/-- The common accuracy pays the aggregate coefficient of every listed target differential.

Membership supplies the original target coefficient bound. Multiplication
by the same positive common accuracy and exact division cancellation pay
that coefficient from the displayed target budget. -/
theorem differentialRefinementAccuracy_mul_coefficient_le
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source))
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (member : differential ∈ targets)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    differentialRefinementAccuracy parents targets target *
        aggregateRefinementCoefficient differential
          (parents.map (recastCenteredEdge differential)) <= target := by
  let coefficient := differentialRefinementCoefficient parents targets
  have coefficientNonnegative : 0 <= coefficient :=
    differentialRefinementCoefficient_nonnegative parents targets
  have denominatorPositive : 0 < coefficient + 1 :=
    Purelib.Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct coefficientNonnegative (by decide)
  have memberCoefficientLe :
      aggregateRefinementCoefficient differential
          (parents.map (recastCenteredEdge differential)) <= coefficient :=
    aggregateRefinementCoefficient_leDifferential parents differential
      targets member
  have coefficientLe : coefficient <= coefficient + 1 :=
    le_add_of_nonneg_right (by decide)
  have accuracyNonnegative :
      0 <= differentialRefinementAccuracy parents targets target :=
    (differentialRefinementAccuracy_positive parents targets
      targetPositive).le
  calc
    differentialRefinementAccuracy parents targets target *
          aggregateRefinementCoefficient differential
            (parents.map (recastCenteredEdge differential)) <=
        differentialRefinementAccuracy parents targets target *
          coefficient :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        memberCoefficientLe accuracyNonnegative
    _ <= differentialRefinementAccuracy parents targets target *
          (coefficient + 1) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientLe
        accuracyNonnegative
    _ = target := by
      unfold differentialRefinementAccuracy
      change (target / (coefficient + 1)) * (coefficient + 1) = target
      exact Fraction.Field.div_mul_cancel_of_ne target
        (coefficient + 1) (ne_of_gt denominatorPositive)

open Purelib.Approximation.Rational in
/-- The first parent's geometric accuracy depth is bounded by the common maximum. -/
private theorem headAccuracyDepth_le_common {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (accuracy : Fraction.Rational) (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential)) :
    Geometric.Search.firstQuarterBelow
        (geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter) 0 accuracy <=
      commonAccuracyDepth accuracy (parent :: remaining) :=
  Purelib.Data.Nat.Order.le_max_left _ _

/-- The remaining parents' common accuracy depth is bounded by that of the full list. -/
private theorem tailAccuracyDepth_le_common {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (accuracy : Fraction.Rational) (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential)) :
    commonAccuracyDepth accuracy remaining <=
      commonAccuracyDepth accuracy (parent :: remaining) :=
  Purelib.Data.Nat.Order.le_max_right _ _

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- A depth beyond the common accuracy depth bounds the first parent's quarter-scale movement by the positive accuracy.
-/
private theorem quarterRadius_le_accuracy_of_commonDepth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (accuracy : Fraction.Rational) (accuracyPositive : 0 < accuracy)
    (parent : CenteredEdge curve differential)
    (remaining : List (CenteredEdge curve differential))
    (depth : Nat)
    (enough : commonAccuracyDepth accuracy (parent :: remaining) <= depth) :
    Geometric.Basic.quarterRadius
        (geometricMovement parent.edge.segment parent.edge.left.parameter
          parent.edge.request.endpoint.parameter) depth <= accuracy := by
  let first := Geometric.Search.firstQuarterBelow
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter) 0 accuracy
  have firstEnough : first <= depth :=
    (headAccuracyDepth_le_common accuracy parent remaining).trans enough
  have movementNonnegative :
      0 <= geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter := by
    unfold geometricMovement
    exact Norm.Basic.normSq_nonneg _
  have laterLe := quarterRadius_antitone
    movementNonnegative firstEnough
  have firstBelow := Geometric.Search.firstQuarterBelow_accurate
    (geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter)
    movementNonnegative 0 accuracy accuracyPositive
  exact (laterLe.trans_lt firstBelow).le

/-- Build synchronized direct parent blocks at a supplied sufficient common depth.

The original proper parent intervals and positive diameter are retained; each parent receives its own checked block at
the exact shared indices. -/
@[expose] def synchronizedDirectBlockRefinementAtDepth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) :
    (parents : List (CenteredEdge curve differential)) ->
    PreparedDyadicRefinements.AllParentsProper parents ->
    commonSufficientDepth rootDiameter parents <= depth ->
      SynchronizedDirectBlockRefinement depth rootDiameter parents
  | [], _proper, _enough => .nil
  | parent :: remaining, proper, enough => by
      have headEnough :=
        (headSufficientDepth_le_common parent remaining rootDiameter).trans
          enough
      have tailEnough :=
        (tailSufficientDepth_le_common parent remaining rootDiameter).trans
          enough
      let block := directParentBlockAtDepth parent proper.1 rootDiameter
        rootDiameterPositive depth headEnough
      exact .cons block rfl rfl
        (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth remaining proper.2 tailEnough)

/-- Constructing synchronized children commutes with recasting the differential at the same depth and diameter. -/
theorem synchronizedDirectBlockRefinementAtDepth_children_recast
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) :
    forall (parents : List (CenteredEdge curve source))
      (proper : PreparedDyadicRefinements.AllParentsProper parents)
      (sourceEnough : commonSufficientDepth rootDiameter parents <= depth)
      (targetEnough : commonSufficientDepth rootDiameter
        (parents.map (recastCenteredEdge target)) <= depth),
      (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth
          (parents.map (recastCenteredEdge target))
          (allParentsProper_map_recast proper) targetEnough).children =
        (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth parents proper sourceEnough).children.map
            (recastCenteredEdge target)
  | [], _proper, _sourceEnough, _targetEnough => rfl
  | parent :: remaining, proper, sourceEnough, targetEnough => by
      simp only [synchronizedDirectBlockRefinementAtDepth,
        SynchronizedDirectBlockRefinement.children, List.map,
        Map.map_append]
      rw [directParentBlockAtDepth_children_recast target]
      rw [synchronizedDirectBlockRefinementAtDepth_children_recast target
        rootDiameter rootDiameterPositive depth remaining]

/-- Build synchronized blocks for a target differential on the original recast parent list.

The common sufficient-depth equality transports the source depth evidence without changing the geometry or diameter
request. -/
@[expose] def recastSynchronizedDirectBlockRefinementAtDepth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (enough : commonSufficientDepth rootDiameter parents <= depth) :
    SynchronizedDirectBlockRefinement depth rootDiameter
      (parents.map (recastCenteredEdge target)) :=
  synchronizedDirectBlockRefinementAtDepth rootDiameter rootDiameterPositive
    depth (parents.map (recastCenteredEdge target))
      (allParentsProper_map_recast proper) (by
        simpa only [commonSufficientDepth_map_recast] using enough)

/-- The recast synchronized construction has exactly the recast original child list. -/
@[simp] theorem recastSynchronizedDirectBlockRefinementAtDepth_children
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (depth : Nat) (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (enough : commonSufficientDepth rootDiameter parents <= depth) :
    (recastSynchronizedDirectBlockRefinementAtDepth target rootDiameter
      rootDiameterPositive depth parents proper enough).children =
        (synchronizedDirectBlockRefinementAtDepth rootDiameter
          rootDiameterPositive depth parents proper enough).children.map
            (recastCenteredEdge target) := by
  apply synchronizedDirectBlockRefinementAtDepth_children_recast

/-- Build synchronized direct blocks at the maximum sufficient depth of the original proper parents. -/
@[expose] def synchronizedDirectBlockRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter)
    (parents : List (CenteredEdge curve differential))
    (proper : PreparedDyadicRefinements.AllParentsProper parents) :
    SynchronizedDirectBlockRefinement
      (commonSufficientDepth rootDiameter parents) rootDiameter parents :=
  synchronizedDirectBlockRefinementAtDepth rootDiameter rootDiameterPositive
    (commonSufficientDepth rootDiameter parents) parents proper (le_refl _)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Bound local model error when quarter-scale movement and requested diameter are both controlled by the same accuracy.

The estimate is twice the accuracy times the sum of the segment's point and root error coefficients. -/
private theorem localModelErrorBound_le_accuracy {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (accuracy : Fraction.Rational)
    (depth : Nat) (left right : Fraction.Rational)
    (movementLe :
      Geometric.Basic.quarterRadius
        (geometricMovement segment left right) depth <= accuracy) :
    localModelErrorBound differential segment accuracy depth left right <=
      (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment +
        PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment) * (2 * accuracy) := by
  unfold localModelErrorBound
  have pointCoefficientNonnegative :=
    PreparedConstantModels.PreparedEdge.pointErrorCoefficient_nonnegative
      differential segment
  have rootCoefficientNonnegative :=
    PreparedConstantModels.PreparedEdge.rootErrorCoefficient_nonnegative
      differential segment
  have accuracyNonnegative : 0 <= accuracy :=
    (Geometric.Basic.quarterRadius_nonneg
      (Norm.Basic.normSq_nonneg _) depth).trans
        movementLe
  have accuracyLeDouble : accuracy <= 2 * accuracy := by
    calc
      accuracy = 1 * accuracy := by ring1
      _ <= 2 * accuracy :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide) accuracyNonnegative
  calc
    PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment *
          Geometric.Basic.quarterRadius
            (geometricMovement segment left right) depth +
        PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment * accuracy <=
      PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment * accuracy +
        PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment * accuracy :=
      add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementLe
          pointCoefficientNonnegative) le_rfl
    _ = (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment +
        PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment) * accuracy := by
      ring1
    _ <= (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
          differential segment +
        PreparedConstantModels.PreparedEdge.rootErrorCoefficient
          differential segment) * (2 * accuracy) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        accuracyLeDouble (add_nonneg pointCoefficientNonnegative
          rootCoefficientNonnegative)

namespace SynchronizedDirectBlockRefinement

open Purelib.Data.Gaussian in
/-- At a sufficient common accuracy depth, the refinement error sum is bounded by accuracy times the original
coefficient sum. -/
theorem refinementErrorSum_le_accuracy {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {depth : Nat} {accuracy : Fraction.Rational}
      {parents : List (CenteredEdge curve differential)}
      (blocks : SynchronizedDirectBlockRefinement depth accuracy parents),
      0 < accuracy -> commonAccuracyDepth accuracy parents <= depth ->
      blocks.refinementErrorSum <=
        accuracy * refinementCoefficientSum differential parents
  | _, _, [], .nil, _accuracyPositive, _enough => by
      simp only [refinementErrorSum, refinementCoefficientSum,
        Fraction.Field.mul_zero_direct]
      exact le_rfl
  | depth, accuracy, parent :: remaining,
      .cons _ _ _ tail, accuracyPositive, enough => by
      have movementLe := quarterRadius_le_accuracy_of_commonDepth accuracy
        accuracyPositive parent remaining depth enough
      have localBound := localModelErrorBound_le_accuracy differential
        parent.edge.segment accuracy depth
          parent.edge.left.parameter parent.edge.request.endpoint.parameter
            movementLe
      have thirtyTwoNonnegative : (0 : Fraction.Rational) <= 32 := by
        calc
          (0 : Fraction.Rational) <= 8 * 4 :=
            Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (by decide)
          _ = 32 := by ring1
      have scaledLocal :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localBound
          thirtyTwoNonnegative
      have movementNonnegative :
          0 <= geometricMovement parent.edge.segment
            parent.edge.left.parameter
              parent.edge.request.endpoint.parameter := by
        unfold geometricMovement
        exact Norm.Basic.normSq_nonneg _
      have headBound :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct scaledLocal
          movementNonnegative
      have normalizedHead :
          geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
            (32 * localModelErrorBound differential parent.edge.segment
              accuracy depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter) <=
          accuracy *
            (geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (64 *
                (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential parent.edge.segment +
                  PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential parent.edge.segment))) := by
        calc
          geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (32 * localModelErrorBound differential parent.edge.segment
                accuracy depth parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) <=
            geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (32 *
                ((PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential parent.edge.segment +
                  PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential parent.edge.segment) *
                  (2 * accuracy))) := headBound
          _ = accuracy *
              (geometricMovement parent.edge.segment parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter *
                (64 *
                  (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                      differential parent.edge.segment +
                    PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                      differential parent.edge.segment))) := by
            ring1
      have tailEnough : commonAccuracyDepth accuracy remaining <= depth :=
        (tailAccuracyDepth_le_common accuracy parent remaining).trans enough
      have tailBound := refinementErrorSum_le_accuracy tail accuracyPositive
        tailEnough
      simp only [refinementErrorSum, refinementCoefficientSum]
      calc
        geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter *
            (32 * localModelErrorBound differential parent.edge.segment
              accuracy depth parent.edge.left.parameter
                parent.edge.request.endpoint.parameter) +
            tail.refinementErrorSum <=
          accuracy *
              (geometricMovement parent.edge.segment
                  parent.edge.left.parameter
                    parent.edge.request.endpoint.parameter *
                (64 *
                  (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                      differential parent.edge.segment +
                    PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                      differential parent.edge.segment))) +
            accuracy * refinementCoefficientSum differential remaining :=
          add_le_add normalizedHead tailBound
        _ = accuracy *
            (geometricMovement parent.edge.segment parent.edge.left.parameter
                parent.edge.request.endpoint.parameter *
              (64 *
                (PreparedConstantModels.PreparedEdge.pointErrorCoefficient
                    differential parent.edge.segment +
                  PreparedConstantModels.PreparedEdge.rootErrorCoefficient
                    differential parent.edge.segment)) +
              refinementCoefficientSum differential remaining) := by
          ring1

/-- The parent-count-scaled refinement error is bounded by accuracy times the aggregate refinement coefficient. -/
theorem aggregateRefinementError_le_accuracy {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {depth : Nat} {accuracy : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth accuracy parents)
    (accuracyPositive : 0 < accuracy)
    (enough : commonAccuracyDepth accuracy parents <= depth) :
    (parents.length : Fraction.Rational) * blocks.refinementErrorSum <=
      accuracy * aggregateRefinementCoefficient differential parents := by
  have errorBound := blocks.refinementErrorSum_le_accuracy accuracyPositive
    enough
  have countNonnegative : (0 : Fraction.Rational) <= (parents.length : Fraction.Rational) :=
    coordinateNatCast_nonnegative parents.length
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorBound
      countNonnegative
  unfold aggregateRefinementCoefficient
  calc
    (parents.length : Fraction.Rational) * blocks.refinementErrorSum <=
        (parents.length : Fraction.Rational) *
          (accuracy * refinementCoefficientSum differential parents) := scaled
    _ = accuracy *
        ((parents.length : Fraction.Rational) *
          refinementCoefficientSum differential parents) := by
      ring1

end SynchronizedDirectBlockRefinement

set_option genInjectivity false in
/-- A checked direct mesh for every original parent at shared depth and root diameter.

The dependent list retains the original parent's full endpoint interval and each successful mesh, ready for reuse in
synchronized blocks. -/
inductive CheckedDirectMeshes {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational) :
    List (CenteredEdge curve differential) → Type 2
  /-- No meshes are needed for the empty original parent list. -/ | nil : CheckedDirectMeshes depth rootDiameter []
  /-- Retain the checked full-interval mesh for the original head parent and the meshes of the original tail. -/ | cons
    {parent : CenteredEdge curve differential} {remaining : List (CenteredEdge curve differential)}
      (mesh : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
        parent.edge.left parent.edge.request.endpoint)
      (tail : CheckedDirectMeshes depth rootDiameter remaining) :
      CheckedDirectMeshes depth rootDiameter (parent :: remaining)

constructive_injectivity CheckedDirectMeshes

namespace CheckedDirectMeshes

set_option genInjectivity false in
/-- An unresolved mesh attempt together with every preceding accepted parent mesh.

The head case retains the exact current mesh's inconclusive report; the tail case preserves the accepted head while
locating the unresolved attempt in the remaining original parents. -/
inductive Failure {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) : List (CenteredEdge curve differential) → Type 2
  /-- Retain the first unresolved mesh attempt on this exact proper parent interval. -/ | head {parent : CenteredEdge
    curve differential} {remaining : List (CenteredEdge curve differential)}
      (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
      (report : CheckedDirectGeometry.MeshInconclusive parent.edge proper
        rootDiameter positive depth parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper) :
      Failure depth rootDiameter positive (parent :: remaining)
  /-- Retain an accepted head mesh before the unresolved attempt in the original tail. -/ | tail {parent : CenteredEdge
    curve differential} {remaining : List (CenteredEdge curve differential)}
      (accepted : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
        parent.edge.left parent.edge.request.endpoint)
      (failure : Failure depth rootDiameter positive remaining) :
      Failure depth rootDiameter positive (parent :: remaining)

constructive_injectivity Failure

/-- Count the retained accepted parent meshes preceding the unresolved attempt. -/
@[expose] def Failure.completedParents {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} : {parents : List (CenteredEdge curve differential)} →
    Failure depth rootDiameter positive parents → Nat
  | _, .head .. => 0
  | _, .tail _ failure => failure.completedParents + 1

/-- The accepted prefix ends strictly before the end of the original parent list. -/
theorem Failure.completedParents_lt {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {parents : List (CenteredEdge curve differential)}
    (failure : Failure depth rootDiameter positive parents) :
    failure.completedParents < parents.length := by
  induction failure with
  | head => simp only [completedParents, List.length_cons]; omega
  | tail _ _ ih => simp only [completedParents, List.length_cons]; omega

/-- Combine an attempted head mesh with a deferred attempt on the remaining parents.

A failed head returns its original report. A successful head is retained in either the completed mesh list or the
remaining failure report. -/
@[expose] def prependAttempt {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {positive : 0 < rootDiameter} {parent : CenteredEdge curve differential}
    {remaining : List (CenteredEdge curve differential)}
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (head : Except (CheckedDirectGeometry.MeshInconclusive parent.edge proper
      rootDiameter positive depth parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper)
      (CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
        parent.edge.left parent.edge.request.endpoint))
    (rest : Unit → Except (Failure depth rootDiameter positive remaining)
      (CheckedDirectMeshes depth rootDiameter remaining)) :
    Except (Failure depth rootDiameter positive (parent :: remaining))
      (CheckedDirectMeshes depth rootDiameter (parent :: remaining)) :=
  match head with
  | .error report => .error (.head proper report)
  | .ok mesh =>
      match rest () with
      | .error failure => .error (.tail mesh failure)
      | .ok meshes => .ok (.cons mesh meshes)

/-- Attempt the original proper parent meshes in order, preserving successes before the first unresolved mesh. -/
@[expose] def sequentialAttempt {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) :
    (parents : List (CenteredEdge curve differential)) →
    PreparedDyadicRefinements.AllParentsProper parents →
    Except (Failure depth rootDiameter positive parents) (CheckedDirectMeshes depth rootDiameter parents)
  | [], _ => .ok .nil
  | parent :: remaining, proper =>
      prependAttempt proper.1
        (CheckedDirectGeometry.attemptMesh parent.edge proper.1 rootDiameter positive
          depth parent.edge.left parent.edge.request.endpoint le_rfl le_rfl proper.1)
        (fun _ => sequentialAttempt depth rootDiameter positive remaining proper.2)

set_option backward.match.sparseCases false in
open Purelib.Data in
/-- Attempt parent meshes in groups of four parallel computations, with sequential result assembly.

Successful meshes and the earliest unresolved report follow original parent order; the final shorter group uses the
sequential procedure. -/
@[expose] def attemptRaw {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) :
    (parents : List (CenteredEdge curve differential)) →
    PreparedDyadicRefinements.AllParentsProper parents →
    Except (Failure depth rootDiameter positive parents) (CheckedDirectMeshes depth rootDiameter parents)
  | first :: second :: third :: fourth :: remaining, proper =>
      let one := fun (_ : Unit) =>
        CheckedDirectGeometry.attemptMesh first.edge proper.1 rootDiameter positive
          depth first.edge.left first.edge.request.endpoint le_rfl le_rfl proper.1
      let two := fun (_ : Unit) =>
        CheckedDirectGeometry.attemptMesh second.edge proper.2.1 rootDiameter positive
          depth second.edge.left second.edge.request.endpoint le_rfl le_rfl proper.2.1
      let three := fun (_ : Unit) =>
        CheckedDirectGeometry.attemptMesh third.edge proper.2.2.1 rootDiameter positive
          depth third.edge.left third.edge.request.endpoint le_rfl le_rfl proper.2.2.1
      let four := fun (_ : Unit) =>
        CheckedDirectGeometry.attemptMesh fourth.edge proper.2.2.2.1 rootDiameter positive
          depth fourth.edge.left fourth.edge.request.endpoint le_rfl le_rfl proper.2.2.2.1
      let results := Task.Parallel.four one two three four
      prependAttempt proper.1 results.1 (fun _ =>
        prependAttempt proper.2.1 results.2.1 (fun _ =>
          prependAttempt proper.2.2.1 results.2.2.1 (fun _ =>
            prependAttempt proper.2.2.2.1 results.2.2.2 (fun _ =>
              attemptRaw depth rootDiameter positive remaining proper.2.2.2.2))))
  | parents, proper => sequentialAttempt depth rootDiameter positive parents proper

open Purelib.Data in
/-- The grouped parallel mesh procedure returns exactly the sequential procedure's dependent result. -/
theorem attemptRaw_eq_sequential {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) :
    ∀ (parents : List (CenteredEdge curve differential))
      (proper : PreparedDyadicRefinements.AllParentsProper parents),
      attemptRaw depth rootDiameter positive parents proper =
        sequentialAttempt depth rootDiameter positive parents proper
  | first :: second :: third :: fourth :: remaining, proper => by
      simp only [attemptRaw, Task.Parallel.four_eq, sequentialAttempt]
      rw [attemptRaw_eq_sequential depth rootDiameter positive remaining proper.2.2.2.2]
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

set_option genInjectivity false in
/-- A mesh-attempt report retaining the exact request, accepted-prefix length and observed failure.

The depth, diameter and parent count are tied to the original inputs, and the observed equation identifies the actual
raw procedure result. -/
structure Inconclusive {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) (parents : List (CenteredEdge curve differential))
    (proper : PreparedDyadicRefinements.AllParentsProper parents) where
  /-- The dyadic depth used by this actual attempt. -/ attemptedDepth : Nat
  /-- The recorded attempted depth is the original requested depth. -/ attemptedDepth_eq : attemptedDepth = depth
  /-- The root diameter used by this actual attempt. -/ requestedDiameter : Fraction.Rational
  /-- The recorded diameter is the original requested diameter. -/ requestedDiameter_eq : requestedDiameter =
    rootDiameter
  /-- The recorded number of original parent edges. -/ parentCount : Nat
  /-- The recorded parent count equals the original list length. -/ parentCount_eq : parentCount = parents.length
  /-- The original unresolved mesh attempt together with all accepted preceding meshes. -/ failure : Failure depth
    rootDiameter positive parents
  /-- The number of accepted parent meshes preceding the unresolved attempt. -/ completedParents : Nat
  /-- The recorded accepted-prefix count equals the retained failure's count. -/ completedParents_eq : completedParents
    = failure.completedParents
  /-- The exact raw mesh attempt returned this retained failure. -/ observed : attemptRaw depth rootDiameter positive
    parents proper = .error failure

constructive_injectivity Inconclusive

/-- Return the checked meshes or an inconclusive report tied to the exact raw attempt.

The report retains numerical requests, completed parents and the original failure data with an equation identifying the
outcome. -/
@[expose] def attempt {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) (parents : List (CenteredEdge curve differential))
    (proper : PreparedDyadicRefinements.AllParentsProper parents) :
    Except (Inconclusive depth rootDiameter positive parents proper)
      (CheckedDirectMeshes depth rootDiameter parents) :=
  match observed : attemptRaw depth rootDiameter positive parents proper with
  | .ok meshes => .ok meshes
  | .error failure => .error
      { attemptedDepth := depth, attemptedDepth_eq := rfl
        requestedDiameter := rootDiameter, requestedDiameter_eq := rfl
        parentCount := parents.length, parentCount_eq := rfl
        failure := failure, completedParents := failure.completedParents
        completedParents_eq := rfl, observed := observed }

/-- An inconclusive report reproduces the exact public mesh-attempt error result. -/
theorem Inconclusive.attempt_error
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential
      genus}
    {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {parents : List (CenteredEdge curve differential)}
    {proper : PreparedDyadicRefinements.AllParentsProper parents}
    (report : Inconclusive depth rootDiameter positive parents proper) :
    attempt depth rootDiameter positive parents proper = .error report := by
  cases report with
  | mk attemptedDepth depthEq requestedDiameter diameterEq parentCount countEq
      failure completedParents completedEq observed =>
      cases depthEq
      cases diameterEq
      cases countEq
      cases completedEq
      unfold attempt
      split
      · rename_i meshes found
        have impossible := found.symm.trans observed
        cases impossible
      · rename_i other found
        have equal : other = failure := Except.error.inj (found.symm.trans observed)
        cases equal
        rfl

/-- The unresolved parent lies strictly within the retained original parent count. -/
theorem Inconclusive.unresolvedIndex_lt_count
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential
      genus}
    {depth : Nat} {rootDiameter : Fraction.Rational} {positive : 0 < rootDiameter}
    {parents : List (CenteredEdge curve differential)}
    {proper : PreparedDyadicRefinements.AllParentsProper parents}
    (report : Inconclusive depth rootDiameter positive parents proper) :
    report.completedParents < report.parentCount := by
  rw [report.completedParents_eq, report.parentCount_eq]
  exact report.failure.completedParents_lt

/-- Erasing mesh failure reports gives the same successful result as the sequential procedure. -/
theorem attempt_success_eq_sequential
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential
      genus}
    (depth : Nat) (rootDiameter : Fraction.Rational) (positive : 0 < rootDiameter)
    (parents : List (CenteredEdge curve differential))
    (proper : PreparedDyadicRefinements.AllParentsProper parents) :
    (attempt depth rootDiameter positive parents proper).toOption =
      (sequentialAttempt depth rootDiameter positive parents proper).toOption := by
  have erase : (attempt depth rootDiameter positive parents proper).toOption =
      (attemptRaw depth rootDiameter positive parents proper).toOption := by
    unfold attempt
    split <;> rename_i _ found <;> exact (congrArg Except.toOption found).symm
  rw [erase, attemptRaw_eq_sequential]

/-- Construct checked meshes at a common depth already sufficient for every original proper parent. -/
@[expose] def uniform {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) :
    (parents : List (CenteredEdge curve differential)) →
    PreparedDyadicRefinements.AllParentsProper parents →
    commonSufficientDepth rootDiameter parents ≤ depth →
    CheckedDirectMeshes depth rootDiameter parents
  | [], _, _ => .nil
  | parent :: remaining, proper, enough =>
      .cons (uniformParentMesh parent proper.1 rootDiameter positive depth
        ((headSufficientDepth_le_common parent remaining rootDiameter).trans enough))
        (uniform depth rootDiameter positive remaining proper.2
          ((tailSufficientDepth_le_common parent remaining rootDiameter).trans enough))

/-- Convert the retained checked meshes into synchronized direct blocks at their original shared indices. -/
@[expose] def toBlocks {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational} :
    {parents : List (CenteredEdge curve differential)} →
    CheckedDirectMeshes depth rootDiameter parents →
    SynchronizedDirectBlockRefinement depth rootDiameter parents
  | [], .nil => .nil
  | parent :: _, .cons mesh tail =>
      .cons (checkedParentBlock parent mesh) rfl rfl tail.toBlocks

/-- The converted head mesh contributes its exact child list before the retained tail's children. -/
theorem toBlocks_cons_children {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parent : CenteredEdge curve differential} {remaining : List (CenteredEdge curve differential)}
    (mesh : CheckedDirectGeometry.Mesh parent.edge rootDiameter depth
      parent.edge.left parent.edge.request.endpoint)
    (tail : CheckedDirectMeshes depth rootDiameter remaining) :
    (CheckedDirectMeshes.cons mesh tail).toBlocks.children = mesh.children ++ tail.toBlocks.children := by
  change (checkedParentBlock parent mesh).children ++ tail.toBlocks.children = _
  rw [checkedParentBlock_children]

/-- Converting uniformly constructed meshes gives exactly the synchronized construction at the supplied depth. -/
theorem uniform_toBlocks {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (depth : Nat) (rootDiameter : Fraction.Rational)
    (positive : 0 < rootDiameter) :
    ∀ (parents : List (CenteredEdge curve differential))
      (proper : PreparedDyadicRefinements.AllParentsProper parents)
      (enough : commonSufficientDepth rootDiameter parents ≤ depth),
    (uniform depth rootDiameter positive parents proper enough).toBlocks =
      synchronizedDirectBlockRefinementAtDepth rootDiameter positive depth parents proper enough
  | [], _, _ => rfl
  | parent :: remaining, proper, enough => by
      simp only [uniform, toBlocks, synchronizedDirectBlockRefinementAtDepth,
        directParentBlockAtDepth]
      rw [uniform_toBlocks depth rootDiameter positive remaining]

/-- Sum the weighted allowances already retained by the checked parent meshes. -/
@[expose] def weightedAllowance {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational} :
    {parents : List (CenteredEdge curve differential)} →
    CheckedDirectMeshes depth rootDiameter parents → Fraction.Rational
  | [], .nil => 0
  | _ :: _, .cons mesh tail => mesh.weightedAllowance + tail.weightedAllowance

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained mesh allowance sum equals the converted child models' total weighted allowance. -/
theorem weightedAllowance_eq {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (meshes : CheckedDirectMeshes depth rootDiameter parents) :
    meshes.weightedAllowance =
      (Basic.PathModel.mk meshes.toBlocks.models).totalWeightedAllowance := by
  induction meshes with
  | nil => rfl
  | cons mesh tail ih =>
      simp only [weightedAllowance, toBlocks, SynchronizedDirectBlockRefinement.models,
        totalWeightedAllowance_append, checkedParentBlock_children]
      rw [mesh.weightedAllowance_eq, ih]

/-- Scale the retained mesh allowance sum by the exact original-parent count times the dyadic count. -/
@[expose] def aggregateAllowance {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (meshes : CheckedDirectMeshes depth rootDiameter parents) : Fraction.Rational :=
  Fraction.Cast.fromInt (Int.ofNat (parents.length * 2 ^ depth)) * meshes.weightedAllowance

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The direct mesh aggregate allowance equals the converted child models' aggregate allowance. -/
theorem aggregateAllowance_eq {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve differential)}
    (meshes : CheckedDirectMeshes depth rootDiameter parents) :
    meshes.aggregateAllowance =
      (Basic.PathModel.mk meshes.toBlocks.models).aggregateAllowance := by
  rw [aggregateAllowance, weightedAllowance_eq,
    Basic.PathModel.aggregateAllowance,
    meshes.toBlocks.models_length]
  exact congrArg (fun count : Fraction.Rational => count *
    (Basic.PathModel.mk meshes.toBlocks.models).totalWeightedAllowance)
    (Fraction.Cast.natCast_eq_fromInt (parents.length * 2 ^ depth)).symm

/-- Recast each original checked parent mesh to the target differential at the same depth and diameter.

The original geometric mesh is retained through its recasting operation, and the dependent parent list is its exact
recast list. -/
@[expose] def recast {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    (target : Basic.Differential genus) :
    {parents : List (CenteredEdge curve source)} →
    CheckedDirectMeshes depth rootDiameter parents →
    CheckedDirectMeshes depth rootDiameter (parents.map (recastCenteredEdge target))
  | [], .nil => .nil
  | parent :: _, .cons mesh tail =>
      .cons (parent := recastCenteredEdge target parent) (mesh.recast target) (tail.recast target)

/-- Recasting the checked meshes gives exactly the recast original child list after block conversion. -/
theorem recast_children {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve source)} (target : Basic.Differential genus)
    (meshes : CheckedDirectMeshes depth rootDiameter parents) :
    (meshes.recast target).toBlocks.children =
      meshes.toBlocks.children.map (recastCenteredEdge target) := by
  induction meshes with
  | nil => rfl
  | @cons parent remaining mesh tail ih =>
      have headEqual := toBlocks_cons_children
        (parent := recastCenteredEdge target parent) (mesh.recast target) (tail.recast target)
      have appendEqual := congrArg₂ List.append (mesh.recast_children target) ih
      exact headEqual.trans (appendEqual.trans (by
        rw [toBlocks_cons_children, Map.map_append]
        rfl))

/-- Sum the target differential's allowances on the original retained mesh geometry. -/
@[expose] def weightedAllowanceFor {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    (target : Basic.Differential genus) :
    {parents : List (CenteredEdge curve source)} →
    CheckedDirectMeshes depth rootDiameter parents → Fraction.Rational
  | [], .nil => 0
  | _ :: _, .cons mesh tail => mesh.weightedAllowanceFor target + tail.weightedAllowanceFor target

/-- The direct target-differential allowance sum equals the allowance of the recast meshes. -/
theorem weightedAllowanceFor_eq {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve source)} (target : Basic.Differential genus)
    (meshes : CheckedDirectMeshes depth rootDiameter parents) :
    meshes.weightedAllowanceFor target = (meshes.recast target).weightedAllowance := by
  induction meshes with
  | nil => rfl
  | cons mesh tail ih =>
      change mesh.weightedAllowanceFor target + tail.weightedAllowanceFor target =
        (mesh.recast target).weightedAllowance + (tail.recast target).weightedAllowance
      rw [ih]
      rfl

/-- Scale the target differential's retained mesh allowance sum by the exact dyadic child count. -/
@[expose] def aggregateAllowanceFor {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve source)} (target : Basic.Differential genus)
    (meshes : CheckedDirectMeshes depth rootDiameter parents) : Fraction.Rational :=
  Fraction.Cast.fromInt (Int.ofNat (parents.length * 2 ^ depth)) *
    meshes.weightedAllowanceFor target

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The direct target-differential aggregate equals the aggregate allowance of the recast child models. -/
theorem aggregateAllowanceFor_eq {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {depth : Nat} {rootDiameter : Fraction.Rational}
    {parents : List (CenteredEdge curve source)} (target : Basic.Differential genus)
    (meshes : CheckedDirectMeshes depth rootDiameter parents) :
    meshes.aggregateAllowanceFor target =
      (Basic.PathModel.mk
        (meshes.recast target).toBlocks.models).aggregateAllowance := by
  rw [← (meshes.recast target).aggregateAllowance_eq, aggregateAllowanceFor,
    aggregateAllowance, Map.length_map, weightedAllowanceFor_eq]

end CheckedDirectMeshes

namespace ActualChildAllowance

/-- The exact rational field used for allowance comparisons. -/
public abbrev Q := Fraction.Rational

/-- The original centered-edge model projection, with its curve and differential indices retained. -/
public abbrev model {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :=
  @Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge.model genus curve differential

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Sum child displacement squared norms weighted by the original parent's local allowance. -/
private def inherited (parent : Basic.CellModel) : List Basic.CellModel → Q
  | [] => 0
  | child :: rest =>
      Data.Gaussian.Norm.Basic.normSq child.displacement * parent.localAllowance +
        inherited parent rest

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A comparison cell's weighted allowance splits into twice its inherited parent contribution plus twice its own child
allowance. -/
private theorem comparison_weighted (parent child : Basic.CellModel) :
    (Basic.PathModel.comparisonCell parent child).weightedAllowance =
      2 * (Data.Gaussian.Norm.Basic.normSq child.displacement *
        parent.localAllowance + child.weightedAllowance) := by
  simp only [Basic.CellModel.weightedAllowance, Basic.CellModel.displacement, Basic.PathModel.comparisonCell,
    Basic.CellModel.withAllowance, ← Norm.Basic.normSq_eq_canonical]
  change Data.Gaussian.Norm.Basic.normSq child.displacement *
      (2 * (parent.localAllowance + child.localAllowance)) =
    2 * (Data.Gaussian.Norm.Basic.normSq child.displacement *
      parent.localAllowance +
        Data.Gaussian.Norm.Basic.normSq child.displacement * child.localAllowance)
  ring1

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Total comparison allowance splits into twice the inherited parent sum and twice the actual child weighted sum. -/
private theorem comparison_total (parent : Basic.CellModel) (children : List Basic.CellModel) :
    (Basic.PathModel.mk (children.map (Basic.PathModel.comparisonCell parent))).totalWeightedAllowance =
      2 * inherited parent children + 2 * (Basic.PathModel.mk children).totalWeightedAllowance := by
  induction children with
  | nil =>
      simp only [List.map_nil, inherited, Basic.PathModel.totalWeightedAllowance, List.foldr_nil]
      ring1
  | cons child rest ih =>
      simp only [List.map_cons, inherited, Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons] at ih ⊢
      rw [comparison_weighted, ih]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- A common child movement bound controls the inherited contribution from the original parent's nonnegative allowance.
-/
private theorem inherited_le {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : Basic.CellModel) (bound : Q) :
    ∀ (children : List (CenteredEdge curve differential)),
      (∀ child ∈ children, child.edge.pointMovement ≤ bound) →
      inherited parent (children.map model) ≤
        (children.length : Q) * (bound * parent.localAllowance)
  | [], _ => by
      change (0 : Q) ≤ (0 : Q) * (bound * parent.localAllowance)
      rewrite [Fraction.Field.zero_mul_direct]
      exact Fraction.Order.Basic.le_refl _
  | child :: rest, bounded => by
      have head := bounded child (List.Mem.head rest)
      have tail := fun c hc => bounded c (List.mem_cons_of_mem child hc)
      have actual : Data.Gaussian.Norm.Basic.normSq
          child.model.displacement = child.edge.pointMovement := by rfl
      have headBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        head parent.localAllowance_nonneg
      have tailBound := inherited_le parent bound rest tail
      simp only [List.map_cons, inherited, List.length_cons, Nat.cast_succ]
      change Data.Gaussian.Norm.Basic.normSq child.model.displacement *
        parent.localAllowance + inherited parent (rest.map model) ≤ _
      rw [actual]
      calc
        child.edge.pointMovement * parent.localAllowance + inherited parent (rest.map model) ≤
            bound * parent.localAllowance + (rest.length : Q) *
              (bound * parent.localAllowance) := add_le_add headBound tailBound
        _ = _ := by ring1

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Total weighted allowance is additive under concatenation of the original cell lists. -/
private theorem weighted_append (first second : List Basic.CellModel) :
    (Basic.PathModel.mk (first ++ second)).totalWeightedAllowance =
      (Basic.PathModel.mk first).totalWeightedAllowance +
        (Basic.PathModel.mk second).totalWeightedAllowance := by
  induction first with
  | nil =>
      change _ = 0 + _
      exact (Purelib.Data.Rat.Fraction.Field.zero_add _).symm
  | cons cell rest ih =>
      simp only [List.cons_append, Basic.PathModel.totalWeightedAllowance, List.foldr_cons] at ih ⊢
      rw [ih]
      ring1

/-- Natural-number casts into the rational allowance field are nonnegative. -/
private theorem cast_nonneg (n : Nat) : (0 : Q) ≤ (n : Q) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Nat.cast_succ]
      exact add_nonneg ih (by decide)

open Purelib.Approximation.Rational in
/-- The square of the dyadic cell count exactly cancels quarter-radius scaling.

Both occurrences of the dyadic count use the displayed depth. The existing
quarter-radius cancellation applies to the original scalar without a sign condition. -/
private theorem count_square (scale : Q) (depth : Nat) :
    ((2 ^ depth : Nat) : Q) * (((2 ^ depth : Nat) : Q) *
      Geometric.Basic.quarterRadius scale depth) = scale :=
  Purelib.Approximation.Rational.Geometric.DyadicCount.dyadic_count_cancel scale depth

/-- Sum the inherited parent-allowance contributions of the original synchronized child blocks. -/
private def inheritedBlocks {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {diameter : Q} :
    {parents : List (CenteredEdge curve differential)} →
      SynchronizedDirectBlockRefinement depth diameter parents → Q
  | [], .nil => 0
  | parent :: _, .cons block _ _ tail =>
      inherited parent.model (block.children.map model) + inheritedBlocks tail

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The synchronized comparison weighted total splits into inherited-parent and actual-child totals, each scaled by two.
-/
private theorem block_comparison_total {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {diameter : Q}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth diameter parents) :
    (Basic.PathModel.mk blocks.comparisonCells).totalWeightedAllowance =
      2 * inheritedBlocks blocks + 2 * (Basic.PathModel.mk blocks.models).totalWeightedAllowance := by
  induction blocks with
  | nil =>
      simp only [SynchronizedDirectBlockRefinement.comparisonCells,
        SynchronizedDirectBlockRefinement.models, inheritedBlocks,
        Basic.PathModel.totalWeightedAllowance, List.foldr_nil]
      ring1
  | @cons parent rest block depthEq diameterEq tail ih =>
      simp only [SynchronizedDirectBlockRefinement.comparisonCells,
        SynchronizedDirectBlockRefinement.models, inheritedBlocks, weighted_append]
      rw [← Map.map_map, comparison_total, ih]
      ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The dyadic count times inherited child contributions is bounded by the original parents' weighted total. -/
private theorem inherited_scaled {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {diameter : Q}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth diameter parents) :
    ((2 ^ depth : Nat) : Q) * inheritedBlocks blocks ≤
      (Basic.PathModel.mk (parents.map model)).totalWeightedAllowance := by
  induction blocks with
  | nil =>
      simp only [inheritedBlocks, List.map_nil, Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, mul_zero]
      exact le_rfl
  | @cons parent rest block depthEq diameterEq tail ih =>
      have movement : ∀ child ∈ block.children, child.edge.pointMovement ≤
          Geometric.Basic.quarterRadius
            (geometricMovement parent.edge.segment parent.edge.left.parameter
              parent.edge.request.endpoint.parameter) block.depth := by
        have bounded := block.movements
        generalize childrenEq : block.children = children at bounded ⊢
        clear childrenEq
        induction bounded with
        | nil => intro c h; exact (List.not_mem_nil h).elim
        | @cons child children head bounded ih =>
            intro c h
            rcases Membership.mem_cons.mp h with same | member
            · subst c; exact head
            · exact ih c member
      have bound := inherited_le parent.model _ block.children movement
      rw [block.childCount, depthEq] at bound
      have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        bound (cast_nonneg (2 ^ depth))
      have parentEq : parent.model.weightedAllowance =
          geometricMovement parent.edge.segment parent.edge.left.parameter
            parent.edge.request.endpoint.parameter * parent.model.localAllowance := by
        unfold Basic.CellModel.weightedAllowance geometricMovement
        rw [PreparedSubdivisionModelCore.CenteredEdge.model_displacement]
        rw [Norm.Basic.normSq_eq_canonical]
      have headBound : ((2 ^ depth : Nat) : Q) *
          inherited parent.model (block.children.map model) ≤ parent.model.weightedAllowance := by
        rw [parentEq]
        apply scaled.trans_eq
        calc
          ((2 ^ depth : Nat) : Q) * (((2 ^ depth : Nat) : Q) *
              (Geometric.Basic.quarterRadius
                (geometricMovement parent.edge.segment parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) depth * parent.model.localAllowance)) =
            (((2 ^ depth : Nat) : Q) * (((2 ^ depth : Nat) : Q) *
              Geometric.Basic.quarterRadius
                (geometricMovement parent.edge.segment parent.edge.left.parameter
                  parent.edge.request.endpoint.parameter) depth)) * parent.model.localAllowance := by ring1
          _ = _ := by rw [count_square]
      simp only [inheritedBlocks, List.map_cons, Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons, mul_add]
      exact add_le_add headBound ih

end ActualChildAllowance

open ActualChildAllowance in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The aggregate comparison allowance is bounded by twice the original parent allowance plus twice the actual child
allowance.

This estimate retains the actual synchronized child models and their allowances instead of replacing them by a
requested-error estimate. -/
theorem SynchronizedDirectBlockRefinement.comparisonAllowance_le_actual {genus : Nat} {curve :
  Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {depth : Nat} {diameter : Q}
    {parents : List (CenteredEdge curve differential)}
    (blocks : SynchronizedDirectBlockRefinement depth diameter parents) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance blocks.toCompatible) ≤
      2 * (Basic.PathModel.mk (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance +
        2 * (Basic.PathModel.mk blocks.models).aggregateAllowance := by
  unfold CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
    Basic.PathModel.aggregateAllowance
  rw [blocks.toCompatible_comparisonCells, blocks.comparisonCells_length,
    blocks.models_length, Map.length_map, Purelib.Algebra.NatCast.mul, block_comparison_total]
  have inheritedBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (inherited_scaled blocks)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Q) ≤ 2)
      (cast_nonneg parents.length))
  calc
    (parents.length : Q) * ((2 ^ depth : Nat) : Q) *
        (2 * inheritedBlocks blocks + 2 * (Basic.PathModel.mk blocks.models).totalWeightedAllowance) =
      (2 * (parents.length : Q)) * (((2 ^ depth : Nat) : Q) * inheritedBlocks blocks) +
        2 * ((parents.length : Q) * ((2 ^ depth : Nat) : Q) *
          (Basic.PathModel.mk blocks.models).totalWeightedAllowance) := by ring1
    _ ≤ (2 * (parents.length : Q)) * (Basic.PathModel.mk (parents.map model)).totalWeightedAllowance +
        2 * ((parents.length : Q) * ((2 ^ depth : Nat) : Q) *
          (Basic.PathModel.mk blocks.models).totalWeightedAllowance) := add_le_add inheritedBound le_rfl
    _ = _ := by ring1

section CheckedAccuracySelection

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {parents : List (CenteredEdge curve
    source)}
  {depth : Nat} {diameter : Purelib.Data.Rat.Fraction.Rational}

set_option genInjectivity false in
/-- Retained aggregate-allowance values and budget checks for each requested differential on the same meshes.

Each value is tied to the original geometry's exact target-differential allowance, and twice that value must fit the
supplied target budget. -/
inductive MeshAllowanceChecks (meshes : CheckedDirectMeshes depth diameter parents)
    (target : Fraction.Rational) : List (Basic.Differential genus) → Type
  /-- The empty target-differential list needs no allowance checks. -/ | nil : MeshAllowanceChecks meshes target []
  /-- Retain the exact current allowance value, its doubled budget inequality and the checked tail. -/ | cons
    {differential : Basic.Differential genus} {remaining : List (Basic.Differential genus)}
      (value : Fraction.Rational) (value_eq : value = meshes.aggregateAllowanceFor differential)
      (twice_le : 2 * value ≤ target)
      (tail : MeshAllowanceChecks meshes target remaining) :
      MeshAllowanceChecks meshes target (differential :: remaining)

constructive_injectivity MeshAllowanceChecks

namespace MeshAllowanceChecks

set_option genInjectivity false in
/-- An excessive doubled-allowance value, retaining every preceding successful target check.

The failing entry stores the exact mesh allowance and proof that its budget inequality fails; later constructors retain
successful values for earlier differentials. -/
inductive Failure (meshes : CheckedDirectMeshes depth diameter parents)
    (target : Fraction.Rational) : List (Basic.Differential genus) → Type
  /-- Retain the exact allowance value and proof that its doubled budget inequality fails. -/ | excessive (differential
    : Basic.Differential genus) (remaining : List (Basic.Differential genus))
      (value : Fraction.Rational) (value_eq : value = meshes.aggregateAllowanceFor differential)
      (violated : ¬ 2 * value ≤ target) : Failure meshes target (differential :: remaining)
  /-- Retain the exact successful current value and locate the excessive value in the original target tail. -/ | later
    (differential : Basic.Differential genus) {remaining : List (Basic.Differential genus)}
      (value : Fraction.Rational) (value_eq : value = meshes.aggregateAllowanceFor differential)
      (enough : 2 * value ≤ target) (failure : Failure meshes target remaining) :
      Failure meshes target (differential :: remaining)

constructive_injectivity Failure

/-- Check each target differential's actual mesh allowance and retain its exact scalar value.

An excessive value records the violated doubled-allowance inequality; earlier successful values remain in the failure
chain or the completed checks. -/
@[expose] public def checkRaw (meshes : CheckedDirectMeshes depth diameter parents) (target : Fraction.Rational) :
    (targets : List (Basic.Differential genus)) →
      Except (Failure meshes target targets) (MeshAllowanceChecks meshes target targets)
  | [] => .ok .nil
  | differential :: remaining =>
      let value := meshes.aggregateAllowanceFor differential
      if enough : 2 * value ≤ target then
        match checkRaw meshes target remaining with
        | .error failure => .error (.later differential value rfl enough failure)
        | .ok tail => .ok (.cons value rfl enough tail)
      else .error (.excessive differential remaining value rfl enough)

set_option genInjectivity false in
/-- The retained geometry and exact request of an unresolved allowance check.

Equalities bind depth, diameter, target and geometry to the original inputs, and the observed equation identifies the
exact excessive-value failure. -/
structure Inconclusive (meshes : CheckedDirectMeshes depth diameter parents)
    (target : Fraction.Rational) (targets : List (Basic.Differential genus)) where
  /-- The original checked meshes retained for reuse after an allowance failure. -/ geometry : CheckedDirectMeshes depth
    diameter parents
  /-- The retained geometry equals the exact meshes that were checked. -/ geometry_eq : geometry = meshes
  /-- The dyadic depth used by this actual attempt. -/ attemptedDepth : Nat
  /-- The recorded attempted depth is the original requested depth. -/ attemptedDepth_eq : attemptedDepth = depth
  /-- The root diameter used by this actual attempt. -/ requestedDiameter : Fraction.Rational
  /-- The recorded diameter is the original requested diameter. -/ requestedDiameter_eq : requestedDiameter = diameter
  /-- The allowance budget used by this actual attempt. -/ requestedTarget : Fraction.Rational
  /-- The recorded allowance budget equals the original requested target. -/ requestedTarget_eq : requestedTarget =
    target
  /-- The excessive-value report for the exact retained geometry and target family. -/ failure : Failure geometry
    requestedTarget targets
  /-- The exact raw allowance check returned this retained failure. -/ observed : checkRaw geometry
    requestedTarget targets = .error failure

constructive_injectivity Inconclusive

/-- Return all retained allowance checks or the original geometry with its exact excessive-value report.

The observed raw-check equation binds the report to the actual target-family check; the retained geometry can be reused.
-/
@[expose] def attempt (meshes : CheckedDirectMeshes depth diameter parents) (target : Fraction.Rational)
    (targets : List (Basic.Differential genus)) :
    Except (Inconclusive meshes target targets) (MeshAllowanceChecks meshes target targets) :=
  match observed : checkRaw meshes target targets with
  | .ok checks => .ok checks
  | .error failure => .error
      { geometry := meshes, geometry_eq := rfl
        attemptedDepth := depth, attemptedDepth_eq := rfl
        requestedDiameter := diameter, requestedDiameter_eq := rfl
        requestedTarget := target, requestedTarget_eq := rfl
        failure := failure, observed := observed }

/-- An inconclusive allowance report reproduces the exact allowance-attempt error result. -/
theorem Inconclusive.attempt_error
    {meshes : CheckedDirectMeshes depth diameter parents} {target : Fraction.Rational}
    {targets : List (Basic.Differential genus)} (report : Inconclusive meshes target targets) :
    attempt meshes target targets = .error report := by
  cases report with
  | mk geometry geometryEq attemptedDepth depthEq requestedDiameter diameterEq
      requestedTarget targetEq failure observed =>
      cases geometryEq
      cases depthEq
      cases diameterEq
      cases targetEq
      unfold attempt
      split
      · rename_i checks found
        have impossible := found.symm.trans observed
        cases impossible
      · rename_i other found
        have equal : other = failure := Except.error.inj (found.symm.trans observed)
        cases equal
        rfl

/-- Build retained allowance checks from supplied bounds for every listed differential. -/
@[expose] def ofBounds (meshes : CheckedDirectMeshes depth diameter parents) (target : Fraction.Rational) :
    (targets : List (Basic.Differential genus)) →
    (∀ differential ∈ targets, 2 * meshes.aggregateAllowanceFor differential ≤ target) →
    MeshAllowanceChecks meshes target targets
  | [], _ => .nil
  | differential :: remaining, bound =>
      .cons (meshes.aggregateAllowanceFor differential) rfl
        (bound differential (List.mem_cons_self))
        (ofBounds meshes target remaining
          (fun differential member => bound differential (List.mem_cons_of_mem _ member)))

/-- Read the doubled aggregate-allowance budget bound for a differential in the checked list. -/
theorem bound {meshes : CheckedDirectMeshes depth diameter parents} {target : Fraction.Rational}
    {targets : List (Basic.Differential genus)} (checks : MeshAllowanceChecks meshes target targets)
    (differential : Basic.Differential genus) (member : differential ∈ targets) :
    2 * meshes.aggregateAllowanceFor differential ≤ target := by
  induction checks with
  | nil => exact False.elim (List.not_mem_nil member)
  | @cons head remaining value valueEq twice tail ih =>
      rcases Membership.mem_cons.mp member with equal | later
      · subst differential
        rw [← valueEq]
        exact twice
      · exact ih later

end MeshAllowanceChecks

namespace MeshAllowanceChecks

/-- Read a cached allowance by differential index, computing the original mesh allowance if the list has no matching
entry. -/
@[expose] def amount {meshes : CheckedDirectMeshes depth diameter parents} {target : Fraction.Rational}
    (differential : Basic.Differential genus) :
    {targets : List (Basic.Differential genus)} → MeshAllowanceChecks meshes target targets → Fraction.Rational
  | [], .nil => meshes.aggregateAllowanceFor differential
  | head :: _, .cons value _ _ tail =>
      if differential.index = head.index then value else tail.amount differential

/-- Reading a cached allowance always returns the exact aggregate allowance of the original meshes for that
differential. -/
theorem amount_eq {meshes : CheckedDirectMeshes depth diameter parents} {target : Fraction.Rational}
    {targets : List (Basic.Differential genus)} (checks : MeshAllowanceChecks meshes target targets)
    (differential : Basic.Differential genus) :
    checks.amount differential = meshes.aggregateAllowanceFor differential := by
  induction checks with
  | nil => rfl
  | @cons head remaining value valueEq twice tail ih =>
      simp only [amount]
      split
      · rename_i indexEqual
        have equal : differential = head := by
          cases differential
          cases head
          congr
        subst differential
        exact valueEq
      · exact ih

end MeshAllowanceChecks

set_option genInjectivity false in
/-- A positive diameter and depth with checked original meshes and allowance checks for the target family.

The dependent checks refer to the exact retained meshes and requested budget, so the selected geometry is the geometry
that paid the bounds. -/
structure CheckedSelection (parents : List (CenteredEdge curve source))
    (targets : List (Basic.Differential genus)) (target : Fraction.Rational) where
  /-- The retained requested root diameter indexing the checked construction. -/ rootDiameter : Fraction.Rational
  /-- The retained requested root diameter is strictly positive. -/ positive : 0 < rootDiameter
  /-- The retained common dyadic subdivision depth. -/ depth : Nat
  /-- The original checked meshes indexed by the retained parents, depth and diameter. -/ meshes : CheckedDirectMeshes
    depth rootDiameter parents
  /-- Retained actual-allowance checks on these exact meshes for every requested differential. -/ allowances :
    MeshAllowanceChecks meshes target targets

constructive_injectivity CheckedSelection

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Construct a checked selection using a provably sufficient common geometric and accuracy depth.

The positive accuracy is derived from the target-family coefficient sum; the retained meshes are checked against every
listed differential's doubled aggregate allowance. -/
@[expose] def uniformSelection (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (targets : List (Basic.Differential genus)) (target : Fraction.Rational) (positive : 0 < target) :
    CheckedSelection parents targets target := by
  let accuracy := differentialRefinementAccuracy parents targets target
  have accuracyPositive : 0 < accuracy :=
    differentialRefinementAccuracy_positive parents targets positive
  let depth := max (commonSufficientDepth accuracy parents) (commonAccuracyDepth accuracy parents)
  have clearanceEnough : commonSufficientDepth accuracy parents ≤ depth := Purelib.Data.Nat.Order.le_max_left _ _
  have accuracyEnough : commonAccuracyDepth accuracy parents ≤ depth := Purelib.Data.Nat.Order.le_max_right _ _
  let meshes := CheckedDirectMeshes.uniform depth accuracy accuracyPositive parents proper clearanceEnough
  refine ⟨accuracy, accuracyPositive, depth, meshes,
    MeshAllowanceChecks.ofBounds meshes target targets ?_⟩
  intro differential member
  let blocks := recastSynchronizedDirectBlockRefinementAtDepth differential
    accuracy accuracyPositive depth parents proper clearanceEnough
  have childrenEqual : (meshes.recast differential).toBlocks.children = blocks.children := by
    rw [meshes.recast_children, CheckedDirectMeshes.uniform_toBlocks,
      recastSynchronizedDirectBlockRefinementAtDepth_children]
  have allowanceEqual : meshes.aggregateAllowanceFor differential =
      (Basic.PathModel.mk blocks.models).aggregateAllowance := by
    rw [meshes.aggregateAllowanceFor_eq, (meshes.recast differential).toBlocks.models_eq_children_map,
      childrenEqual, ← blocks.models_eq_children_map]
  rw [allowanceEqual]
  have recastEnough : commonAccuracyDepth accuracy (parents.map (recastCenteredEdge differential)) ≤ depth := by
    simpa only [commonAccuracyDepth_map_recast] using accuracyEnough
  exact blocks.twice_modelAllowance_le_refinementError.trans
    ((blocks.aggregateRefinementError_le_accuracy accuracyPositive recastEnough).trans
      (differentialRefinementAccuracy_mul_coefficient_le parents targets differential member positive))

/-- The retained edge movement times sixty-four times its prepared point and root error coefficients for a target
differential. -/
@[expose] def preparedEdgeForecast (differential : Basic.Differential genus)
    (prepared : PreparedSubdivisionModelCore.PreparedEdge curve source) : Fraction.Rational :=
  let edge := recastPreparedEdge differential prepared
  edge.pointMovement * (64 *
    (edge.preparedPointErrorCoefficient + edge.preparedRootErrorCoefficient))

/-- Sum prepared-edge refinement forecasts over the original parent list for one differential. -/
@[expose] def preparedForecast (differential : Basic.Differential genus) :
    List (CenteredEdge curve source) → Fraction.Rational
  | [] => 0
  | parent :: remaining =>
      preparedEdgeForecast differential parent.edge + preparedForecast differential remaining

/-- Sum the prepared parent forecasts over the requested differential family. -/
@[expose] def familyForecast (parents : List (CenteredEdge curve source)) :
    List (Basic.Differential genus) → Fraction.Rational
  | [] => 0
  | differential :: remaining => preparedForecast differential parents + familyForecast parents remaining

section
open Purelib.Approximation.Rational
/-- Try a finite sequence of direct mesh and actual allowance checks.

A geometry failure increases depth; an allowance failure increases both depth and root precision. Success retains the
exact meshes and allowance checks, while exhausted fuel returns no selection. -/
@[expose] def searchSelection (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (targets : List (Basic.Differential genus)) (target : Fraction.Rational) :
    Nat → Nat → Nat → Option (CheckedSelection parents targets target)
  | 0, _, _ => none
  | fuel + 1, depth, rootBits =>
      let diameter := Geometric.Basic.quarterRadius 1 rootBits
      have positive : 0 < diameter := Geometric.Basic.quarterRadius_pos (by decide) rootBits
      match CheckedDirectMeshes.attempt depth diameter positive parents proper with
      | .error _report => searchSelection parents proper targets target fuel (depth + 1) rootBits
      | .ok meshes =>
          match MeshAllowanceChecks.attempt meshes target targets with
          | .error _report => searchSelection parents proper targets target fuel (depth + 1) (rootBits + 1)
          | .ok allowances => some ⟨diameter, positive, depth, meshes, allowances⟩

/-- Choose the initial quarter-radius index from the forecast budget, reduced by two with natural subtraction. -/
@[expose] def proposedRootBits (parentCount : Nat) (forecast target : Fraction.Rational) : Nat :=
  let coefficient := Fraction.Cast.fromInt (Int.ofNat parentCount) * forecast
  Geometric.Search.firstQuarterBelow 1 0 (target / (coefficient + 1)) - 2

end

/-- The initial root-index heuristic returns three and zero for the two stated exact rational cases. -/
theorem proposedRootBits_regressions :
    proposedRootBits 1 1023 2 = 3 ∧ proposedRootBits 1 0 2 = 0 := by
  decide +kernel

/-- Select checked meshes by an eight-step forecast-guided search, with a proved uniform construction as fallback.

Every returned selection carries the original mesh geometry and exact allowance checks for the requested positive
budget. -/
@[expose] def checkedDirectSelection (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (targets : List (Basic.Differential genus)) (target : Fraction.Rational) (positive : 0 < target) :
    CheckedSelection parents targets target :=
  let rootBits := proposedRootBits parents.length (familyForecast parents targets) target
  match searchSelection parents proper targets target 8 0 rootBits with
  | some selected => selected
  | none => uniformSelection parents proper targets target positive

set_option genInjectivity false in
/-- A checked target-family refinement retaining meshes, allowances and the exact blocks converted from those meshes.

The shared positive diameter and depth index both representations; the block equality prevents replacing the geometry
after the allowance checks. -/
structure DifferentialAccurateDirectRefinement
    (parents : List (CenteredEdge curve source))
    (targets : List (Basic.Differential genus)) (target : Fraction.Rational) where
  /-- The retained requested root diameter indexing the checked construction. -/ rootDiameter : Fraction.Rational
  /-- The retained requested root diameter is strictly positive. -/ rootDiameterPositive : 0 < rootDiameter
  /-- The retained common dyadic subdivision depth. -/ depth : Nat
  /-- The original checked meshes indexed by the retained parents, depth and diameter. -/ meshes : CheckedDirectMeshes
    depth rootDiameter parents
  /-- Retained actual-allowance checks on these exact meshes for every requested differential. -/ allowances :
    MeshAllowanceChecks meshes target targets
  /-- The synchronized direct blocks obtained from the retained checked meshes. -/ blocks :
    SynchronizedDirectBlockRefinement depth rootDiameter parents
  /-- The retained blocks equal conversion of the exact meshes whose allowances were checked. -/ blocks_eq : blocks =
    meshes.toBlocks

constructive_injectivity DifferentialAccurateDirectRefinement

/-- Package the checked selection and its exact converted blocks as a target-family refinement. -/
@[expose] def differentialAccurateDirectRefinement
    (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (targets : List (Basic.Differential genus)) (target : Fraction.Rational) (positive : 0 < target) :
    DifferentialAccurateDirectRefinement parents targets target :=
  let selected := checkedDirectSelection parents proper targets target positive
  { rootDiameter := selected.rootDiameter
    rootDiameterPositive := selected.positive
    depth := selected.depth
    meshes := selected.meshes
    allowances := selected.allowances
    blocks := selected.meshes.toBlocks
    blocks_eq := rfl }

namespace DifferentialAccurateDirectRefinement

variable {targets : List (Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)} {target :
  Purelib.Data.Rat.Fraction.Rational}

/-- Recast the retained checked meshes to a differential and convert those same meshes into synchronized blocks. -/
@[expose] def recastBlocks (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) :
    SynchronizedDirectBlockRefinement result.depth result.rootDiameter
      (parents.map (recastCenteredEdge differential)) :=
  (result.meshes.recast differential).toBlocks

/-- The recast blocks contain exactly the original result's children recast to the target differential. -/
@[simp] theorem recastBlocks_children
    (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) :
    (result.recastBlocks differential).children =
      result.blocks.children.map (recastCenteredEdge differential) := by
  rw [result.blocks_eq]
  exact result.meshes.recast_children differential

/-- Read the checked result's cached aggregate allowance for a differential. -/
@[expose] def allowanceFor (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) : Fraction.Rational :=
  result.allowances.amount differential

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The cached allowance equals the aggregate allowance of the result's exact recast child models. -/
theorem allowanceFor_eq (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) :
    result.allowanceFor differential =
      (Basic.PathModel.mk
        ((result.blocks.children.map (recastCenteredEdge differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance := by
  rw [allowanceFor, result.allowances.amount_eq, result.meshes.aggregateAllowanceFor_eq]
  exact congrArg (fun models =>
    (Basic.PathModel.mk models).aggregateAllowance)
    ((result.recastBlocks differential).models_eq_children_map.trans
      (congrArg (List.map PreparedSubdivisionModelCore.CenteredEdge.model)
        (result.recastBlocks_children differential)))

/-- For a listed target differential, twice the result's cached allowance fits the requested budget. -/
theorem twice_allowanceFor_le
    (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) (member : differential ∈ targets) :
    2 * result.allowanceFor differential ≤ target := by
  rw [allowanceFor, result.allowances.amount_eq]
  exact result.allowances.bound differential member

/-- Read a compatible constant-path refinement between the original recast parent models and exact recast child models.

The conversion transports only the proved child-list equality, preserving the retained mesh geometry and root
comparisons. -/
@[expose] def compatible (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) :
    CompatibleConstantPathRefinement
      ((parents.map (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)
      ((result.blocks.children.map (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model) :=
  castCompatibleChildren (result.recastBlocks differential).toCompatibleChildren
    (congrArg (List.map PreparedSubdivisionModelCore.CenteredEdge.model)
      (result.recastBlocks_children differential))

open Purelib.Integration.Polynomial.Gaussian.Path
/-- The checked child models' aggregate allowance fits the requested target budget. -/
theorem modelAllowance_le
    (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) (member : differential ∈ targets) :
    (Basic.PathModel.mk
      ((result.blocks.children.map (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance ≤ target := by
  rw [← result.allowanceFor_eq differential]
  have nonnegative : 0 ≤ result.allowanceFor differential := by
    rw [result.allowanceFor_eq]
    exact Basic.PathModel.aggregateAllowance_nonneg _
  have twice : result.allowanceFor differential ≤ 2 * result.allowanceFor differential := by
    calc
      result.allowanceFor differential ≤
          result.allowanceFor differential + result.allowanceFor differential :=
        le_add_of_nonneg_right nonnegative
      _ = _ := by ring1
  exact twice.trans (result.twice_allowanceFor_le differential member)

/-- The refinement comparison allowance is bounded by twice the original parent-model allowance plus the requested
target budget. -/
theorem comparisonAllowance_le
    (result : DifferentialAccurateDirectRefinement parents targets target)
    (differential : Basic.Differential genus) (member : differential ∈ targets) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (result.compatible
      differential)) ≤
      2 * (Basic.PathModel.mk
        ((parents.map (recastCenteredEdge differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance + target := by
  rw [compatible, castCompatibleChildren_comparisonAllowance_eq,
    (result.recastBlocks differential).toCompatibleChildren_comparisonAllowance_eq]
  have bound := (result.recastBlocks differential).comparisonAllowance_le_actual
  have enough : 2 * (Basic.PathModel.mk
      (result.recastBlocks differential).models).aggregateAllowance ≤ target := by
    rw [(result.recastBlocks differential).models_eq_children_map,
      result.recastBlocks_children, ← result.allowanceFor_eq]
    exact result.twice_allowanceFor_le differential member
  exact bound.trans (add_le_add le_rfl enough)

end DifferentialAccurateDirectRefinement

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Recasting centered edges to their own differential preserves their models' total weighted allowance. -/
private theorem recastCenteredEdges_self_totalWeightedAllowance {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} :
    forall parents : List (CenteredEdge curve source),
      (Basic.PathModel.mk
        ((parents.map
          (PreparedEdgeRecasting.recastCenteredEdge
            source)).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance =
        (Basic.PathModel.mk
          (parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance
  | [] => rfl
  | parent :: remaining => by
      have tailEqual :=
        recastCenteredEdges_self_totalWeightedAllowance remaining
      change
        ((remaining.map
          (PreparedEdgeRecasting.recastCenteredEdge
            source)).map
              PreparedSubdivisionModelCore.CenteredEdge.model).foldr
                (fun cell total => cell.weightedAllowance + total) 0 =
          (remaining.map
            PreparedSubdivisionModelCore.CenteredEdge.model).foldr
              (fun cell total => cell.weightedAllowance + total) 0 at tailEqual
      unfold Basic.PathModel.totalWeightedAllowance
      simp only [List.map, List.foldr_cons]
      rw [PreparedEdgeRecasting.recastCenteredEdge_self_weightedAllowance,
        tailEqual]

/-- Recasting centered edges to their own differential preserves their models' aggregate allowance. -/
theorem recastCenteredEdges_self_aggregateAllowance {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source)) :
    (Basic.PathModel.mk
      ((parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          source)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance =
      (Basic.PathModel.mk
        (parents.map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance := by
  unfold Basic.PathModel.aggregateAllowance
  change
    (↑(((parents.map
      (PreparedEdgeRecasting.recastCenteredEdge
        source)).map
          PreparedSubdivisionModelCore.CenteredEdge.model).length) : Fraction.Rational) * _ =
      (↑((parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model).length) : Fraction.Rational) * _
  simp only [Map.length_map]
  rw [recastCenteredEdges_self_totalWeightedAllowance]

end

set_option genInjectivity false in
/-- A checked direct refinement whose target family contains the original differential alone.

The inherited construction retains the exact checked meshes, child blocks and doubled-allowance budget for that
differential. -/
structure AccurateDirectRefinement (parents : List (CenteredEdge curve source)) (target : Fraction.Rational)
    extends DifferentialAccurateDirectRefinement parents [source] target

constructive_injectivity AccurateDirectRefinement

/-- Construct a checked direct refinement for the original differential and a positive target budget. -/
@[expose] def accurateDirectRefinement (parents : List (CenteredEdge curve source))
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (target : Fraction.Rational) (positive : 0 < target) : AccurateDirectRefinement parents target :=
  ⟨differentialAccurateDirectRefinement parents proper [source] target positive⟩

namespace AccurateDirectRefinement

variable {target : Purelib.Data.Rat.Fraction.Rational}

/-- Read the checked result's cached aggregate allowance for a differential. -/
@[expose] def allowanceFor (result : AccurateDirectRefinement parents target)
    (differential : Basic.Differential genus) : Fraction.Rational :=
  result.toDifferentialAccurateDirectRefinement.allowanceFor differential

open Purelib.Integration.Polynomial.Gaussian.Path
/-- The cached allowance equals the aggregate allowance of the result's exact recast child models. -/
theorem allowanceFor_eq (result : AccurateDirectRefinement parents target)
    (differential : Basic.Differential genus) :
    result.allowanceFor differential =
      (Basic.PathModel.mk
        ((result.blocks.children.map (recastCenteredEdge differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance :=
  result.toDifferentialAccurateDirectRefinement.allowanceFor_eq differential

/-- Twice the retained child models' aggregate allowance fits the original differential's target budget. -/
theorem twice_modelAllowance_le (result : AccurateDirectRefinement parents target) :
    2 * (Basic.PathModel.mk result.blocks.models).aggregateAllowance ≤ target := by
  have bound := result.toDifferentialAccurateDirectRefinement.twice_allowanceFor_le
    source (List.mem_cons_self)
  rw [result.toDifferentialAccurateDirectRefinement.allowanceFor_eq,
    recastCenteredEdges_self_aggregateAllowance,
    ← result.blocks.models_eq_children_map] at bound
  exact bound

/-- The checked child models' aggregate allowance fits the requested target budget. -/
theorem modelAllowance_le (result : AccurateDirectRefinement parents target) :
    (Basic.PathModel.mk
      (result.blocks.children.map PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance ≤
      target := by
  have bound := result.toDifferentialAccurateDirectRefinement.modelAllowance_le
    source (List.mem_cons_self)
  rw [recastCenteredEdges_self_aggregateAllowance] at bound
  exact bound

/-- The refinement comparison allowance is bounded by twice the original parent-model allowance plus the requested
target budget. -/
theorem comparisonAllowance_le (result : AccurateDirectRefinement parents target) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance result.blocks.toCompatible) ≤
      2 * (Basic.PathModel.mk
        (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance + target :=
  result.blocks.comparisonAllowance_le_actual.trans
    (add_le_add le_rfl result.twice_modelAllowance_le)

/-- The child-list form of the compatible refinement has comparison allowance at most twice the original parent
allowance plus the target. -/
theorem comparisonAllowanceChildren_le (result : AccurateDirectRefinement parents target) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      result.blocks.toCompatibleChildren) ≤
      2 * (Basic.PathModel.mk
        (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance + target := by
  rw [result.blocks.toCompatibleChildren_comparisonAllowance_eq]
  exact result.comparisonAllowance_le

end AccurateDirectRefinement

end CheckedAccuracySelection

/-! ## Total consecutive direct-refinement programs -/

set_option genInjectivity false in
open Purelib.Geometry.Path.Gaussian in
/-- A proper ordered centered-edge list with its original lifted endpoints and direct path chain.

The chain is indexed by the same parent list, so subsequent refinements retain endpoint and sheet continuity. -/
structure DirectRefinementState {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) where
  /-- The original lifted starting point, including its retained sheet. -/ start : Lifted.Basic.LiftedPoint 2
  /-- The original lifted finishing point, including its retained sheet. -/ finish : Lifted.Basic.LiftedPoint 2
  /-- The original ordered centered-edge list indexing the retained chain. -/ parents : List (CenteredEdge curve
    differential)
  /-- Every retained parent or child interval is strictly increasing, as indexed by this record. -/ proper :
    PreparedDyadicRefinements.AllParentsProper parents
  /-- The chain of this record's exact retained edge list at its original lifted endpoint indices. -/ chain :
    DirectPathChain parents (start := start) (finish := finish)

constructive_injectivity DirectRefinementState

namespace DirectRefinementState

/-- Recast the original state to a target differential while preserving its lifted endpoints and original geometric
chain. -/
@[expose] def recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (state : DirectRefinementState curve source) :
    DirectRefinementState curve target where
  start := state.start
  finish := state.finish
  parents := state.parents.map (recastCenteredEdge target)
  proper := allParentsProper_map_recast state.proper
  chain := state.chain.recast target

/-- Recasting the differential preserves the original lifted starting point. -/
@[simp] theorem recast_start {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (state : DirectRefinementState curve source) :
    (state.recast target).start = state.start := rfl

/-- Recasting the differential preserves the original lifted finishing point. -/
@[simp] theorem recast_finish {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (state : DirectRefinementState curve source) :
    (state.recast target).finish = state.finish := rfl

/-- Replace the state's parents by the checked refinement children at a positive target budget.

The child properness and refined chain retain the original lifted endpoints while using the exact blocks selected by the
checked procedure. -/
@[expose] def refine {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (state : DirectRefinementState curve differential)
    (target : Fraction.Rational) (targetPositive : 0 < target) :
    DirectRefinementState curve differential :=
  let result := accurateDirectRefinement state.parents state.proper target
    targetPositive
  { start := state.start
    finish := state.finish
    parents := result.blocks.children
    proper := result.blocks.childrenProper
    chain := result.blocks.refinedChain state.chain }

open Purelib.Geometry.Path.Gaussian in
/-- Read the lifted path from the original state's retained direct chain. -/
@[expose] def path {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (state : DirectRefinementState curve differential) :
    Lifted.Basic.LiftedPath 2 state.start state.finish :=
  state.chain.path

/-- Recasting the differential preserves the exact original lifted chain path. -/
theorem path_recast {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (target : Basic.Differential genus)
    (state : DirectRefinementState curve source) :
    (state.recast target).path = state.path :=
  DirectPathChain.path_recast target state.chain

/-- Read uniform algebraic certificates for the state's exact original parent models along its retained path. -/
@[expose] def certificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (state : DirectRefinementState curve differential) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      (state.parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model)
      state.path :=
  state.chain.certificates

end DirectRefinementState

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- The initial model aggregate allowance plus one. -/
@[expose] def directScheduleBase {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential) : Fraction.Rational :=
  (Basic.PathModel.mk
      (initial.parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance +
    1

/-- The direct refinement schedule has a strictly positive base.

The retained parent-model allowance is nonnegative. The displayed extra
one makes the same schedule base strictly positive. -/
theorem directScheduleBase_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential) :
    0 < directScheduleBase initial := by
  unfold directScheduleBase
  exact Purelib.Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Basic.PathModel.aggregateAllowance_nonneg _)
    (by decide)

end

section
open Purelib.Approximation.Rational
/-- The next-index quarter-radius target from the original schedule base. -/
@[expose] def directScheduleTarget {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) : Fraction.Rational :=
  Geometric.Basic.quarterRadius (directScheduleBase initial) (index + 1)

/-- Every direct schedule target is strictly positive. -/
theorem directScheduleTarget_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    0 < directScheduleTarget initial index :=
  Geometric.Basic.quarterRadius_pos
    (directScheduleBase_positive initial) (index + 1)

end

/-- Iterate checked direct refinement using the fixed schedule determined by the original state.

Stage zero is the original state; each successor refines the retained preceding stage at its next quarter-radius target.
-/
@[expose] def directRefinementStates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential) :
    Nat -> DirectRefinementState curve differential
  | 0 => initial
  | index + 1 =>
      (directRefinementStates initial index).refine
        (directScheduleTarget initial index)
          (directScheduleTarget_positive initial index)

/-- Every scheduled refinement of an originally closed state remains closed. -/
theorem directRefinementStates_closed {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (closed : initial.finish = initial.start) :
    forall index,
      (directRefinementStates initial index).finish =
        (directRefinementStates initial index).start
  | 0 => closed
  | index + 1 => directRefinementStates_closed initial closed index

open Purelib.Geometry.Path.Gaussian in
/-- Transport a lifted path along the supplied equality of its finish and start indices. -/
@[expose] public def closeLiftedPath
    {start finish : Lifted.Basic.LiftedPoint 2}
    (path : Lifted.Basic.LiftedPath 2 start finish)
    (closed : finish = start) : Lifted.Basic.LiftedPath 2 start start :=
  closed ▸ path

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Transport the original uniform certificates along the supplied path-closing endpoint equality. -/
@[expose] public def closeUniformPathCertificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {cells : List Basic.CellModel}
    {start finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start finish}
    (certificates : Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      cells path)
    (closed : finish = start) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential cells
      (closeLiftedPath path closed) := by
  cases closed
  exact certificates

open Purelib.Geometry.Path.Gaussian in
/-- Read the closed lifted path at a scheduled refinement stage of an originally closed state. -/
@[expose] def directRefinementClosedLift {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (closed : initial.finish = initial.start)
    (index : Nat) : Lifted.Closed.ClosedLiftedPath 2 := by
  let state := directRefinementStates initial index
  have stateClosed : state.finish = state.start :=
    directRefinementStates_closed initial closed index
  exact
    { basepoint := state.start
      path := closeLiftedPath state.path stateClosed }

/-- Retain uniform certificates for the exact scheduled cells on their closed lifted path. -/
@[expose] def directRefinementClosedCertificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (closed : initial.finish = initial.start)
    (index : Nat) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      ((directRefinementStates initial index).parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model)
      (directRefinementClosedLift initial closed index).path := by
  let state := directRefinementStates initial index
  have stateClosed : state.finish = state.start :=
    directRefinementStates_closed initial closed index
  exact closeUniformPathCertificates state.certificates stateClosed

/-- The checked refinement from a scheduled state's parents at the next fixed schedule target. -/
@[expose] def directScheduledRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    AccurateDirectRefinement
      (directRefinementStates initial index).parents
        (directScheduleTarget initial index) :=
  accurateDirectRefinement
    (directRefinementStates initial index).parents
    (directRefinementStates initial index).proper
    (directScheduleTarget initial index)
    (directScheduleTarget_positive initial index)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The path model of the exact parents retained at the requested direct-refinement stage. -/
@[expose] def directRefinementModel {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) : Basic.PathModel :=
  Basic.PathModel.mk
    ((directRefinementStates initial index).parents.map
      PreparedSubdivisionModelCore.CenteredEdge.model)

/-- The compatible constant-path refinement between consecutive scheduled models. -/
@[expose] def directRefinementStep {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    CompatibleConstantPathRefinement
      (directRefinementModel initial index).cells
      (directRefinementModel initial (index + 1)).cells := by
  change CompatibleConstantPathRefinement
    ((directRefinementStates initial index).parents.map
      PreparedSubdivisionModelCore.CenteredEdge.model)
    ((directScheduledRefinement initial index).blocks.children.map
      PreparedSubdivisionModelCore.CenteredEdge.model)
  exact (directScheduledRefinement initial index).blocks.toCompatibleChildren

section
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Every scheduled model allowance is bounded by the quarter-radius of the original schedule base at that stage. -/
theorem directRefinementModel_allowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential) :
    forall (index : Nat),
      (directRefinementModel initial index).aggregateAllowance <=
        Geometric.Basic.quarterRadius
          (directScheduleBase initial) index
  | 0 => by
      unfold directRefinementModel directRefinementStates directScheduleBase
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Fraction.Field.mul_one_direct]
      exact le_add_of_nonneg_right (by decide)
  | index + 1 => by
      change
        (Basic.PathModel.mk
          ((directScheduledRefinement initial index).blocks.children.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
          directScheduleTarget initial index
      exact (directScheduledRefinement initial index).modelAllowance_le

/-- Every scheduled comparison allowance is bounded by the quarter-radius of three times the original schedule base. -/
theorem directRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential)
    (index : Nat) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (directRefinementStep initial
      index)) <=
      Geometric.Basic.quarterRadius
        (3 * directScheduleBase initial) index := by
  have comparisonBound :=
    (directScheduledRefinement initial index).comparisonAllowanceChildren_le
  have parentBound := directRefinementModel_allowance_le initial index
  have doubledParent :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Fraction.Rational) <= 2 by decide)
  have targetLeParent : directScheduleTarget initial index <=
      Geometric.Basic.quarterRadius (directScheduleBase initial) index :=
    quarterRadius_antitone
      (directScheduleBase_positive initial).le (Nat.le_succ index)
  change
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (directScheduledRefinement
      initial index).blocks.toCompatibleChildren) <=
      Geometric.Basic.quarterRadius
        (3 * directScheduleBase initial) index
  calc
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (directScheduledRefinement
      initial index).blocks.toCompatibleChildren) <=
        2 * (directRefinementModel initial index).aggregateAllowance +
          directScheduleTarget initial index := comparisonBound
    _ <= 2 * Geometric.Basic.quarterRadius
            (directScheduleBase initial) index +
          Geometric.Basic.quarterRadius
            (directScheduleBase initial) index :=
      add_le_add doubledParent targetLeParent
    _ = Geometric.Basic.quarterRadius
        (3 * directScheduleBase initial) index := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

end

open Purelib.Approximation.Rational in
open Purelib.Integration.Program in
/-- Package the direct scheduled models and their exact compatible steps as a sequential refinement program.

The program uses three times the positive schedule base as its step scale, with the retained initial and comparison
allowance bounds. -/
@[expose] def directSequentialProgram {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (initial : DirectRefinementState curve differential) :
    Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram where
  model := directRefinementModel initial
  steps := directRefinementStep initial
  stepScale := 3 * directScheduleBase initial
  stepScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (directScheduleBase_positive initial).le
  initialAllowance_le := by
    have initialBound := directRefinementModel_allowance_le initial 0
    have baseNonnegative := (directScheduleBase_positive initial).le
    calc
      (directRefinementModel initial 0).aggregateAllowance <=
          directScheduleBase initial := by
        simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct] using initialBound
      _ = 1 * directScheduleBase initial := by ring1
      _ <= 12 * directScheduleBase initial :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Fraction.Rational) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * directScheduleBase initial) := by ring1
  comparisonAllowance_le := directRefinementStep_comparisonAllowance_le initial

/-! ## Common-geometry finite-differential programs -/

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Sum aggregate model allowances after recasting the original parent list to each target differential. -/
@[expose] def differentialModelAllowanceSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source)) :
    List (Basic.Differential genus) -> Fraction.Rational
  | [] => 0
  | differential :: remaining =>
      (Basic.PathModel.mk
        ((parents.map (recastCenteredEdge differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance +
        differentialModelAllowanceSum parents remaining

/-- The sum of recast target-model aggregate allowances is nonnegative. -/
theorem differentialModelAllowanceSum_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source)) :
    forall (targets : List (Basic.Differential genus)),
      0 <= differentialModelAllowanceSum parents targets
  | [] => le_rfl
  | differential :: remaining =>
      add_nonneg
        (Basic.PathModel.aggregateAllowance_nonneg
          (Basic.PathModel.mk
            ((parents.map (recastCenteredEdge differential)).map
              PreparedSubdivisionModelCore.CenteredEdge.model)))
        (differentialModelAllowanceSum_nonnegative parents remaining)

/-- A listed target differential's model allowance is bounded by the full target-family sum. -/
theorem memberModelAllowance_leDifferentialSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (parents : List (CenteredEdge curve source))
    (differential : Basic.Differential genus) :
    forall (targets : List (Basic.Differential genus)), differential ∈ targets ->
      (Basic.PathModel.mk
        ((parents.map (recastCenteredEdge differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
        differentialModelAllowanceSum parents targets
  | [], member => by cases member
  | head :: remaining, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · subst head
        exact le_add_of_nonneg_right
          (differentialModelAllowanceSum_nonnegative parents remaining)
      · exact
          (memberModelAllowance_leDifferentialSum parents differential
            remaining member).trans
              (le_add_of_nonneg_left
                (Basic.PathModel.aggregateAllowance_nonneg
                  (Basic.PathModel.mk
                    ((parents.map (recastCenteredEdge head)).map
                      PreparedSubdivisionModelCore.CenteredEdge.model))))

end

/-- One plus the initial parent model allowance summed over all target differentials. -/
@[expose] def differentialScheduleBase {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) : Fraction.Rational :=
  differentialModelAllowanceSum initial.parents targets + 1

/-- The common target-family schedule base is strictly positive.

The original target-family allowance sum is nonnegative. The displayed
extra one makes the common schedule base strictly positive. -/
theorem differentialScheduleBase_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) :
    0 < differentialScheduleBase initial targets := by
  unfold differentialScheduleBase
  exact Purelib.Data.Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (differentialModelAllowanceSum_nonnegative initial.parents targets)
    (by decide)

section
open Purelib.Approximation.Rational
/-- The next-index quarter-radius budget from the original target-family schedule base. -/
@[expose] def differentialScheduleTarget {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) (index : Nat) : Fraction.Rational :=
  Geometric.Basic.quarterRadius
    (differentialScheduleBase initial targets) (index + 1)

/-- Every common target-family schedule budget is strictly positive. -/
theorem differentialScheduleTarget_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) (index : Nat) :
    0 < differentialScheduleTarget initial targets index :=
  Geometric.Basic.quarterRadius_pos
    (differentialScheduleBase_positive initial targets) (index + 1)

end

/-- Iterate checked refinements on common geometry for the fixed target differential family.

Each successor uses the exact selected child blocks and preserves the preceding state's lifted endpoints and chain. -/
@[expose] def differentialRefinementStates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) :
    Nat -> DirectRefinementState curve source
  | 0 => initial
  | index + 1 =>
      let current := differentialRefinementStates initial targets index
      let result := differentialAccurateDirectRefinement current.parents
        current.proper targets
          (differentialScheduleTarget initial targets index)
          (differentialScheduleTarget_positive initial targets index)
      { start := current.start
        finish := current.finish
        parents := result.blocks.children
        proper := result.blocks.childrenProper
        chain := result.blocks.refinedChain current.chain }

/-- The checked target-family refinement at one stage of the fixed common schedule. -/
@[expose] def differentialScheduledRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) (index : Nat) :
    DifferentialAccurateDirectRefinement
      (differentialRefinementStates initial targets index).parents targets
        (differentialScheduleTarget initial targets index) :=
  differentialAccurateDirectRefinement
    (differentialRefinementStates initial targets index).parents
    (differentialRefinementStates initial targets index).proper targets
    (differentialScheduleTarget initial targets index)
    (differentialScheduleTarget_positive initial targets index)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read one differential's model on the exact geometry retained by a common scheduled stage. -/
@[expose] def differentialRefinementModel {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (index : Nat) :
    Basic.PathModel :=
  Basic.PathModel.mk
    (((differentialRefinementStates initial targets index).parents.map
      (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)

/-- Read the compatible refinement between consecutive common-stage models for a differential. -/
@[expose] def differentialRefinementStep {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (index : Nat) :
    CompatibleConstantPathRefinement
      (differentialRefinementModel initial targets differential index).cells
      (differentialRefinementModel initial targets differential
        (index + 1)).cells := by
  change CompatibleConstantPathRefinement
    ((((differentialRefinementStates initial targets index).parents.map
      (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model))
    (((differentialScheduledRefinement initial targets index).blocks.children.map
      (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)
  exact (differentialScheduledRefinement initial targets index).compatible
    differential

/-- A listed target differential's initial model allowance is bounded by the common schedule base. -/
theorem differentialInitialModelAllowance_le_base {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (member : differential ∈ targets) :
    (differentialRefinementModel initial targets differential 0).aggregateAllowance <=
      differentialScheduleBase initial targets := by
  unfold differentialRefinementModel differentialRefinementStates
    differentialScheduleBase
  exact
    (memberModelAllowance_leDifferentialSum initial.parents differential
      targets member).trans (le_add_of_nonneg_right (by decide))

section
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Each listed differential's scheduled model allowance satisfies the common quarter-radius budget. -/
theorem differentialRefinementModel_allowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (member : differential ∈ targets) :
    forall (index : Nat),
      (differentialRefinementModel initial targets differential index).aggregateAllowance <=
        Geometric.Basic.quarterRadius
          (differentialScheduleBase initial targets) index
  | 0 => by
      simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Fraction.Field.mul_one_direct] using
          differentialInitialModelAllowance_le_base initial targets
            differential member
  | index + 1 => by
      change
        (Basic.PathModel.mk
          (((differentialScheduledRefinement initial targets index).blocks.children.map
            (recastCenteredEdge differential)).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
          differentialScheduleTarget initial targets index
      exact (differentialScheduledRefinement initial targets index).modelAllowance_le
        differential member

/-- Each listed differential's step comparison allowance is bounded by the quarter-radius of three times the common
base. -/
theorem differentialRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (member : differential ∈ targets)
    (index : Nat) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (differentialRefinementStep
      initial targets differential index)) <=
      Geometric.Basic.quarterRadius
        (3 * differentialScheduleBase initial targets) index := by
  let result := differentialScheduledRefinement initial targets index
  have comparisonBound := result.comparisonAllowance_le differential member
  have parentBound := differentialRefinementModel_allowance_le initial
    targets differential member index
  have doubledParent :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Fraction.Rational) <= 2 by decide)
  have targetLeParent :
      differentialScheduleTarget initial targets index <=
        Geometric.Basic.quarterRadius
          (differentialScheduleBase initial targets) index :=
    quarterRadius_antitone
      (differentialScheduleBase_positive initial targets).le
      (Nat.le_succ index)
  change
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (result.compatible
      differential)) <=
      Geometric.Basic.quarterRadius
        (3 * differentialScheduleBase initial targets) index
  calc
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (result.compatible
      differential)) <=
        2 * (differentialRefinementModel initial targets differential
          index).aggregateAllowance +
            differentialScheduleTarget initial targets index :=
      comparisonBound
    _ <= 2 * Geometric.Basic.quarterRadius
            (differentialScheduleBase initial targets) index +
          Geometric.Basic.quarterRadius
            (differentialScheduleBase initial targets) index :=
      add_le_add doubledParent targetLeParent
    _ = Geometric.Basic.quarterRadius
        (3 * differentialScheduleBase initial targets) index := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

end

open Purelib.Integration.Program in
/-- Package one listed differential's common-geometry schedule as a sequential compatible refinement program.

The models share the original family's selected geometry, while their comparison certificates retain the specified
differential and common step scale. -/
@[expose] def differentialSequentialProgram {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (member : differential ∈ targets) :
    Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram
    where
  model := differentialRefinementModel initial targets differential
  steps := differentialRefinementStep initial targets differential
  stepScale := 3 * differentialScheduleBase initial targets
  stepScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (differentialScheduleBase_positive initial targets).le
  initialAllowance_le := by
    have initialBound :=
      differentialInitialModelAllowance_le_base initial targets
        differential member
    have baseNonnegative :=
      (differentialScheduleBase_positive initial targets).le
    calc
      (differentialRefinementModel initial targets differential 0).aggregateAllowance <=
        differentialScheduleBase initial targets := initialBound
      _ = 1 * differentialScheduleBase initial targets := by ring1
      _ <= 12 * differentialScheduleBase initial targets :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Fraction.Rational) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * differentialScheduleBase initial targets) := by ring1
  comparisonAllowance_le :=
    differentialRefinementStep_comparisonAllowance_le initial targets
      differential member

/-- Every common scheduled state retains the original lifted starting point. -/
theorem differentialRefinementStates_start {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) :
    forall index,
      (differentialRefinementStates initial targets index).start =
        initial.start
  | 0 => rfl
  | index + 1 => differentialRefinementStates_start initial targets index

/-- Every common scheduled state retains the original lifted finishing point. -/
theorem differentialRefinementStates_finish {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) :
    forall index,
      (differentialRefinementStates initial targets index).finish =
        initial.finish
  | 0 => rfl
  | index + 1 => differentialRefinementStates_finish initial targets index

/-- An initially closed common refinement schedule remains closed at every stage. -/
theorem differentialRefinementStates_closed {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (closed : initial.finish = initial.start) :
    forall index,
      (differentialRefinementStates initial targets index).finish =
        (differentialRefinementStates initial targets index).start
  | index => by
      rw [differentialRefinementStates_finish initial targets index,
        differentialRefinementStates_start initial targets index]
      exact closed

section
open Purelib.Geometry.Path.Gaussian
/-- Read the common scheduled lifted path with its endpoint indices transported to the original endpoints. -/
@[expose] def differentialRefinementPath {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus)) (index : Nat) :
    Lifted.Basic.LiftedPath 2 initial.start initial.finish :=
  let state := differentialRefinementStates initial targets index
  (state.path.castStart
    (differentialRefinementStates_start initial targets index)).castFinish
      (differentialRefinementStates_finish initial targets index)

/-- Read the closed lifted path at a common scheduled stage when the original state is closed. -/
@[expose] def differentialRefinementClosedLift {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (closed : initial.finish = initial.start)
    (index : Nat) : Lifted.Closed.ClosedLiftedPath 2 := by
  let state := differentialRefinementStates initial targets index
  have stateClosed : state.finish = state.start :=
    differentialRefinementStates_closed initial targets closed index
  exact
    { basepoint := state.start
      path := closeLiftedPath state.path stateClosed }

end

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Transport the original uniform certificates along an equality of lifted paths with the same endpoints. -/
@[expose] public def castUniformPathCertificatesPath {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {cells : List Basic.CellModel}
    {start finish : Lifted.Basic.LiftedPoint 2}
    {left right : Lifted.Basic.LiftedPath 2 start finish}
    (equal : left = right)
    (certificates : Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      cells left) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential cells right :=
  equal ▸ certificates

/-- Retain one differential's exact scheduled model certificates on the common path with original endpoint indices. -/
@[expose] def differentialRefinementPathCertificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus) (index : Nat) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      (differentialRefinementModel initial targets differential index).cells
      (differentialRefinementPath initial targets index) := by
  let state := differentialRefinementStates initial targets index
  have onStatePath : Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      ((state.parents.map (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)
      state.path :=
    castUniformPathCertificatesPath (state.path_recast differential)
      (state.recast differential).certificates
  exact Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates.castFinish
    (differentialRefinementStates_finish initial targets index)
      (Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates.castStart
        (differentialRefinementStates_start initial targets index)
          onStatePath)

/-- Retain one differential's exact scheduled model certificates on the common closed lifted path. -/
@[expose] def differentialRefinementClosedCertificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    (initial : DirectRefinementState curve source)
    (targets : List (Basic.Differential genus))
    (differential : Basic.Differential genus)
    (closed : initial.finish = initial.start)
    (index : Nat) :
    Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      (differentialRefinementModel initial targets differential index).cells
      (differentialRefinementClosedLift initial targets closed index).path := by
  let state := differentialRefinementStates initial targets index
  have stateClosed : state.finish = state.start :=
    differentialRefinementStates_closed initial targets closed index
  have onCommonPath : Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
      ((state.parents.map (recastCenteredEdge differential)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)
      state.path :=
    castUniformPathCertificatesPath (state.path_recast differential)
      (state.recast differential).certificates
  exact closeUniformPathCertificates onCommonPath stateClosed

/-! ## Certified centered paths -/

set_option linter.unusedVariables false in
set_option genInjectivity false in
open Purelib.Geometry.Path.Gaussian in
/-- An ordered centered-edge chain indexed by its original lifted starting and finishing points.

Each constructor joins the next edge at the exact requested endpoint and sheet of the preceding edge. -/
inductive CenteredPathChain {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    (parents : List (CenteredEdge curve differential)) ->
      {start finish : Lifted.Basic.LiftedPoint 2} -> Type 2
  /-- The empty centered chain at the original lifted point. -/ | nil (point : Lifted.Basic.LiftedPoint 2) :
    CenteredPathChain [] (start := point)
      (finish := point)
  /-- Join the original centered head to the retained tail at its exact requested lifted endpoint. -/ | cons (parent :
    CenteredEdge curve differential)
      {remaining : List (CenteredEdge curve differential)}
      {finish : Lifted.Basic.LiftedPoint 2}
      (tail : CenteredPathChain remaining
        (start :=
          { coordinate := parent.edge.segment.pointAt
              parent.edge.request.endpoint.parameter
            sheet := parent.edge.sheet })
        (finish := finish)) :
      CenteredPathChain (parent :: remaining)
        (start :=
          { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
            sheet := parent.edge.sheet })
        (finish := finish)

constructive_injectivity CenteredPathChain

namespace CenteredPathChain

section
open Purelib.Geometry.Path.Gaussian
/-- Append original direct path chains at their identical retained lifted endpoint. -/
@[expose] def append {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : Lifted.Basic.LiftedPoint 2},
      CenteredPathChain first (start := start) (finish := middle) ->
      CenteredPathChain second (start := middle) (finish := finish) ->
        CenteredPathChain (first ++ second) (start := start) (finish := finish)
  | [], _, _, _, _, .nil _, second => second
  | _ :: _, _, _, _, _, .cons parent tail, second =>
      .cons parent (append tail second)

/-- Transport a centered path chain along equality of its lifted starting point. -/
@[expose] def castStart {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {left right finish : Lifted.Basic.LiftedPoint 2} (equal : left = right)
    (chain : CenteredPathChain parents (start := left) (finish := finish)) :
    CenteredPathChain parents (start := right) (finish := finish) := by
  subst right
  exact chain

/-- Transport a centered path chain along equality of its lifted finishing point. -/
@[expose] def castFinish {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {start left right : Lifted.Basic.LiftedPoint 2} (equal : left = right)
    (chain : CenteredPathChain parents (start := start) (finish := left)) :
    CenteredPathChain parents (start := start) (finish := right) := by
  subst right
  exact chain

end

/-- The centered model starts at its original segment's left request parameter. -/
public theorem model_start {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.start =
      parent.edge.segment.pointAt parent.edge.left.parameter := by
  change parent.edge.point 0 = _
  change
    (PreparedModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 0 = _
  unfold PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_zero] using
    (PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 0).symm

/-- The centered model finishes at its original segment's request endpoint parameter. -/
public theorem model_finish {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.finish =
      parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter := by
  change parent.edge.point 1 = _
  change
    (PreparedModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 1 = _
  unfold PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_one] using
    (PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 1).symm

section
open Purelib.Geometry.Path.Gaussian
/-- Read the lifted path by concatenating the original centered parent segments on their retained sheets. -/
@[expose] def path {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      CenteredPathChain parents (start := start) (finish := finish) ->
        Lifted.Basic.LiftedPath 2 start finish
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons
        (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet
          parent.edge.localSegment)
        tail.path

/-- Read uniform certificates for the original centered parent models along their retained chain. -/
@[expose] def certificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : CenteredPathChain parents (start := start) (finish := finish)),
      Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
        (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
        chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons (model_start parent) (model_finish parent)
        (parent.edge.centeredValidCertificate curve differential parent.center)
        tail.certificates

/-- Convert the original centered path chain to a direct chain with the same parents and endpoint indices. -/
@[expose] def toDirectPathChain {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      CenteredPathChain parents (start := start) (finish := finish) ->
        DirectPathChain parents (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .cons parent tail.toDirectPathChain

/-- Package the centered chain with supplied properness of its original parents as a direct refinement state. -/
@[expose] def toDirectRefinementState {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    (proper : PreparedDyadicRefinements.AllParentsProper parents) :
    DirectRefinementState curve differential where
  start := start
  finish := finish
  parents := parents
  proper := proper
  chain := chain.toDirectPathChain

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Read the centered chain from the original prepared subdivision and supplied center states.

Every edge retains its source owner, request, cache, order and clearance proof on the fixed segment and sheet. -/
@[expose] def ofCenteredSubdivision {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision :
      PreparedSubdivisionModelCore.PreparedSubdivision segment within
        left owner) ->
    (centers : PreparedSubdivisionModelCore.CenterStates curve
      differential sheet subdivision) ->
    CenteredPathChain
      (PreparedSubdivisionModelCore.centeredEdges curve differential
        sheet subdivision centers)
      (start :=
        { coordinate := segment.pointAt left.parameter, sheet := sheet })
      (finish :=
        { coordinate := segment.pointAt subdivision.endpoint.parameter,
          sheet := sheet })
  | .stop endpoint owner, _centers => .nil _
  | .next current owner request cached ordered small remaining, centers =>
      .cons
        { edge :=
            { ambient := ambient
              start := start
              finish := finish
              segment := segment
              within := within
              left := current
              owner := owner
              request := request
              cached := cached
              ordered := ordered
              small := small
              sheet := sheet }
          center := centers.1 }
        (ofCenteredSubdivision curve differential sheet remaining centers.2)

set_option genInjectivity false in
open Purelib.Data.Gaussian in
/-- The original centered parent list and chain of a prepared segment on a fixed sheet.

The original prepared segment determines the retained centered parent list
and its lifted chain at the displayed curve, differential and sheet. -/
structure PreparedSegmentCenteredData {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) (sheet : Fin 2)
    (start finish : Basic.Canonical) where
  /-- The original ordered centered-edge list indexing the retained chain. -/ parents : List (CenteredEdge curve
    differential)
  /-- The chain of this record's exact retained edge list at its original lifted endpoint indices. -/ chain :
    CenteredPathChain parents
    (start := { coordinate := start, sheet := sheet })
    (finish := { coordinate := finish, sheet := sheet })

constructive_injectivity PreparedSegmentCenteredData

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- Construct canonical centered edges and their dependent chain together from the retained subdivision.

Each step reuses its original owner, request and cache and computes its canonical center once before retaining the edge
in both the list and chain. -/
@[expose] public def dataOfCanonicalSubdivisionStored {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision : PreparedSubdivisionModelCore.PreparedSubdivision segment within left owner) :
    PreparedSegmentCenteredData curve differential sheet (segment.pointAt left.parameter)
      (segment.pointAt subdivision.endpoint.parameter) :=
  PreparedSheetContinuation.Subdivision.casesOn
    (motive := fun left _ spine => PreparedSegmentCenteredData curve differential sheet
      (segment.pointAt left.parameter) (segment.pointAt spine.endpoint.parameter)) subdivision
    (fun _ _ => { parents := [], chain := .nil _ })
    (fun current owner request cached ordered small remaining =>
      let edge := PreparedSubdivisionModelCore.edgeOfStep curve differential
        segment within current owner request cached ordered small sheet
      let centered : CenteredEdge curve differential :=
        { edge := edge
          center := PreparedConstantModels.PreparedEdge.CenterState.canonical edge }
      let tail := dataOfCanonicalSubdivisionStored curve differential segment within sheet remaining
      { parents := centered :: tail.parents, chain := .cons centered tail.chain })
termination_by structural subdivision

/-- Read the jointly constructed canonical centered list and chain of the original subdivision. -/
@[inline, expose] def dataOfCanonicalSubdivision {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2)
    (subdivision :
      PreparedSubdivisionModelCore.PreparedSubdivision segment within
        left owner) :
    PreparedSegmentCenteredData curve differential sheet
      (segment.pointAt left.parameter)
      (segment.pointAt subdivision.endpoint.parameter) :=
  dataOfCanonicalSubdivisionStored curve differential segment within sheet subdivision

end

section CanonicalSubdivisionDataEquations

variable {genus : Nat} (curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
  (differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus) {ambient :
    Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  (segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
  (within : segment.WithinAmbient) (left : Endpoint)
  (owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))) (sheet : Fin 2)

/-- A stopped subdivision yields an empty centered list and the constant chain. -/
@[simp] theorem dataOfCanonicalSubdivision_stop :
    dataOfCanonicalSubdivision curve differential segment within sheet
        (.stop left owner) =
      { parents := [], chain := .nil _ } := rfl

/-- The next subdivision step retains its original edge with its canonical center before the recursively retained tail.
-/
@[simp] theorem dataOfCanonicalSubdivision_next
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left owner request)
    (ordered : left.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner request).track.initial.clearance.bound)
    (remaining : PreparedSheetContinuation.Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within left owner request small)) :
    dataOfCanonicalSubdivision curve differential segment within sheet
        (.next left owner request cached ordered small remaining) =
      let edge := PreparedSubdivisionModelCore.edgeOfStep curve differential
        segment within left owner request cached ordered small sheet
      let centered : CenteredEdge curve differential :=
        { edge := edge
          center := PreparedConstantModels.PreparedEdge.CenterState.canonical edge }
      let tail := dataOfCanonicalSubdivision curve differential segment within sheet remaining
      { parents := centered :: tail.parents, chain := .cons centered tail.chain } := rfl

end CanonicalSubdivisionDataEquations

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The jointly constructed parent list equals the original subdivision's centered edges with canonical center states.
-/
theorem dataOfCanonicalSubdivision_parents {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision :
      PreparedSubdivisionModelCore.PreparedSubdivision segment within
        left owner),
      (dataOfCanonicalSubdivision curve differential segment within sheet
        subdivision).parents =
        PreparedSubdivisionModelCore.centeredEdges curve differential
          sheet subdivision
            (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
              differential sheet subdivision)
  | .stop _endpoint _owner => rfl
  | .next current owner request cached ordered small remaining => by
      simp only [dataOfCanonicalSubdivision_next,
        PreparedSubdivisionModelCore.centeredEdges,
        PreparedSubdivisionAutomaticModels.canonicalCenterStates]
      rw [dataOfCanonicalSubdivision_parents curve differential segment within
        sheet remaining]

open Purelib.Data.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Construct the canonical centered list and chain of the complete segment, transporting its endpoints to the original
start and finish. -/
@[expose] def dataOfCompleteSegment {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      PreparedClearPathModels.CompleteSegment segment within owner) :
    PreparedSegmentCenteredData curve differential sheet start finish := by
  let data := dataOfCanonicalSubdivision curve differential segment within
    sheet prepared.subdivision
  let startEqual := congrArg
    (fun coordinate : Basic.Canonical =>
      ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
    prepared.start_eq
  let finishEqual := congrArg
    (fun coordinate : Basic.Canonical =>
      ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
    prepared.finish_eq
  exact
    { parents := data.parents
      chain := (data.chain.castStart startEqual).castFinish finishEqual }

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- The retained complete-segment parent list is exactly its canonical centered-edge list. -/
@[simp] theorem dataOfCompleteSegment_parents {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      PreparedClearPathModels.CompleteSegment segment within owner) :
    (dataOfCompleteSegment curve differential sheet prepared).parents =
      prepared.centeredEdges curve differential sheet := by
  exact dataOfCanonicalSubdivision_parents curve differential segment within
    sheet prepared.subdivision

/-- The complete-segment centered parent list has exactly the retained subdivision step count. -/
@[simp] theorem dataOfCompleteSegment_parents_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      PreparedClearPathModels.CompleteSegment segment within owner) :
    (dataOfCompleteSegment curve differential sheet prepared).parents.length =
      prepared.subdivision.stepCount := by
  rw [dataOfCompleteSegment_parents]
  exact PreparedSubdivisionModelCore.centeredEdges_length
    curve differential sheet prepared.subdivision _

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Read the canonical centered chain of the original complete prepared segment on the supplied sheet. -/
@[expose] def ofCompleteSegment {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      PreparedClearPathModels.CompleteSegment segment within owner) :
    CenteredPathChain
      (prepared.centeredEdges curve differential sheet)
      (start := { coordinate := start, sheet := sheet })
      (finish := { coordinate := finish, sheet := sheet }) := by
  let centers :=
    PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential sheet prepared.subdivision
  let chain := ofCenteredSubdivision curve differential sheet
    prepared.subdivision centers
  let startEqual := congrArg
    (fun coordinate : Basic.Canonical =>
      ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
    prepared.start_eq
  let finishEqual := congrArg
    (fun coordinate : Basic.Canonical =>
      ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
    prepared.finish_eq
  exact (chain.castStart startEqual).castFinish finishEqual

/-- Every retained parameter edge has a strictly increasing endpoint interval. -/
private def AllParameterEdgesProper :
    List ClearSheetContinuation.Subdivision.ParameterEdge -> Prop
  | [] => True
  | edge :: remaining =>
      edge.left.parameter < edge.right.parameter /\
        AllParameterEdgesProper remaining

/-- Strict endpoint ordering is preserved when concatenating parameter-edge lists. -/
private theorem allParameterEdgesProper_append : forall
    (first second :
      List ClearSheetContinuation.Subdivision.ParameterEdge),
    AllParameterEdgesProper first -> AllParameterEdgesProper second ->
      AllParameterEdgesProper (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _ :: _, _second, firstProper, secondProper =>
      ⟨firstProper.1,
        allParameterEdgesProper_append _ _ firstProper.2 secondProper⟩

open Purelib.Riemann.Paths in
/-- The retained strict-parameter-edge predicate supplies strict ordering of every listed interval. -/
private theorem allParameterEdgesProper_of_strictParameterEdges : forall
    (edges :
      List ClearSheetContinuation.Subdivision.ParameterEdge),
    PreparedClearPathModels.PreparedPath.StrictParameterEdges
        edges ->
      AllParameterEdgesProper edges
  | [], _proper => trivial
  | _edge :: remaining, proper =>
      ⟨proper.1,
        allParameterEdgesProper_of_strictParameterEdges remaining proper.2⟩

/-- Every dyadic child interval of a strictly increasing original interval is strictly increasing. -/
private theorem dyadicEdges_allParameterEdgesProper : forall
    (depth : Nat) (left right : Endpoint),
    left.parameter < right.parameter ->
      AllParameterEdgesProper
        (ClearSheetContinuation.Subdivision.dyadicEdges depth
          left right)
  | 0, _left, _right, proper => ⟨proper, trivial⟩
  | depth + 1, left, right, proper => by
      let middle : Endpoint :=
        ⟨ClearSheetContinuation.midpoint left.parameter
            right.parameter,
          ClearSheetContinuation.midpoint_inside
            left.inside right.inside⟩
      apply allParameterEdgesProper_append
      · exact dyadicEdges_allParameterEdgesProper depth left middle
          (left_lt_midpoint proper)
      · exact dyadicEdges_allParameterEdgesProper depth middle right
          (midpoint_lt_right proper)

/-- Strict ordering of the projected parameter edges gives properness of the original centered parent list. -/
private theorem allParentsProper_of_parameterEdgesProper {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall (parents : List (CenteredEdge curve differential)),
      AllParameterEdgesProper
        (parents.map
          PreparedSubdivisionModelCore.CenteredEdge.parameterEdge) ->
      PreparedDyadicRefinements.AllParentsProper parents
  | [], _proper => trivial
  | _ :: remaining, proper =>
      ⟨proper.1,
        allParentsProper_of_parameterEdgesProper remaining proper.2⟩

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A complete segment built from dyadic mesh-safety evidence has proper centered parents. -/
theorem ofSafeDyadic_allParentsProper {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment
        PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive) :
    PreparedDyadicRefinements.AllParentsProper
      ((PreparedClearPathModels.CompleteSegment.ofSafeDyadic
        segment within owner depth rootDiameter rootDiameterPositive safe).centeredEdges
          curve differential sheet) := by
  apply allParentsProper_of_parameterEdgesProper
  rw [PreparedClearPathModels.CompleteSegment.ofSafeDyadic_centeredEdges_parameterEdges]
  exact dyadicEdges_allParameterEdgesProper depth
    PreparedClearPathModels.zeroEndpoint
    PreparedClearPathModels.oneEndpoint (by decide)

/-- A successful complete-segment dyadic preparation has proper centered parents. -/
theorem ofTryDyadic_allParentsProper {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision :
      PreparedSubdivisionModelCore.PreparedSubdivision segment within
        PreparedClearPathModels.zeroEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner)}
    (success :
      PreparedSheetContinuation.Subdivision.tryDyadic segment
        within PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint
        (PreparedClearPathModels.ownerAtStart segment owner) depth
        rootDiameter rootDiameterPositive = some subdivision) :
    PreparedDyadicRefinements.AllParentsProper
      ((PreparedClearPathModels.CompleteSegment.ofTryDyadic
        segment within owner depth rootDiameter rootDiameterPositive
          success).centeredEdges curve differential sheet) := by
  apply allParentsProper_of_parameterEdgesProper
  rw [PreparedClearPathModels.CompleteSegment.ofTryDyadic_centeredEdges_parameterEdges
    curve differential segment within owner sheet depth rootDiameter
      rootDiameterPositive success]
  exact dyadicEdges_allParameterEdgesProper depth
    PreparedClearPathModels.zeroEndpoint
    PreparedClearPathModels.oneEndpoint (by decide)

end

set_option genInjectivity false in
open Purelib.Data.Gaussian in
/-- The retained centered parent list and chain of a checked dyadic path, with strict interval ordering.

Strict parameter ordering certifies the exact retained parents. The indexed
chain connects their original lifted endpoints on the displayed sheet. -/
structure CheckedDyadicCenteredState {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) (sheet : Fin 2)
    (start finish : Basic.Canonical) where
  /-- The original ordered centered-edge list indexing the retained chain. -/ parents : List (CenteredEdge curve
    differential)
  /-- Every retained parent or child interval is strictly increasing, as indexed by this record. -/ proper :
    PreparedDyadicRefinements.AllParentsProper parents
  /-- The chain of this record's exact retained edge list at its original lifted endpoint indices. -/ chain :
    CenteredPathChain parents
    (start := { coordinate := start, sheet := sheet })
    (finish := { coordinate := finish, sheet := sheet })

constructive_injectivity CheckedDyadicCenteredState

set_option genInjectivity false in
open Purelib.Data.Gaussian in
/-- The retained centered parent list and chain of a prepared path on the fixed original sheet.

The chain follows the retained parent list in order and preserves the
original path endpoints on the displayed sheet. -/
structure PreparedPathCenteredData {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) (sheet : Fin 2)
    (start finish : Basic.Canonical) where
  /-- The original ordered centered-edge list indexing the retained chain. -/ parents : List (CenteredEdge curve
    differential)
  /-- The chain of this record's exact retained edge list at its original lifted endpoint indices. -/ chain :
    CenteredPathChain parents
    (start := { coordinate := start, sheet := sheet })
    (finish := { coordinate := finish, sheet := sheet })

constructive_injectivity PreparedPathCenteredData

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Concatenate canonical centered data from the original complete prepared segments.

The resulting chain preserves the original path endpoints, ordered segment occurrences and sheet, using each segment's
retained subdivision. -/
@[expose] def ofPreparedPath {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {ambient : Box} :
    forall {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)},
      PreparedClearPathModels.PreparedPath path owner ->
        PreparedPathCenteredData curve differential sheet start finish
  | _, _, .nil point, _, .nil _ _owner =>
      { parents := []
        chain := .nil _ }
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail =>
      let headData :=
        dataOfCompleteSegment curve differential sheet preparedHead
      let tailData := ofPreparedPath curve differential sheet preparedTail
      { parents :=
          headData.parents ++ tailData.parents
        chain :=
          headData.chain.append tailData.chain }
termination_by structural _ _ path _ _ => path

/-- The original prepared path's real integral lower reading equals that of its retained centered parent list. -/
theorem ofPreparedPath_integralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {ambient : Box} :
    forall {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      prepared.integralRealLower curve differential sheet =
        PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower
          (ofPreparedPath curve differential sheet prepared).parents
  | _, _, .nil _point, _, .nil _ _owner => rfl
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail => by
      simp only [PreparedClearPathModels.PreparedPath.integralRealLower,
        ofPreparedPath,
        PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower_append,
        dataOfCompleteSegment_parents]
      have headEqual :
          preparedHead.integralRealLower curve differential sheet =
            PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower
              (preparedHead.centeredEdges curve differential sheet) := by
        unfold PreparedClearPathModels.CompleteSegment.integralRealLower
          PreparedClearPathModels.CompleteSegment.centeredEdges
        exact
          PreparedSubdivisionModelCore.preparedSubdivisionIntegralRealLower_eq_centeredEdges
            curve differential sheet preparedHead.subdivision
              (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
                differential sheet preparedHead.subdivision)
      rw [headEqual,
        ofPreparedPath_integralRealLower curve differential sheet preparedTail]

/-- The original prepared path's directional integral lower reading equals that of its retained centered parent list. -/
theorem ofPreparedPath_directionalIntegralLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (direction : Basic.Canonical)
    {ambient : Box} :
    forall {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      prepared.directionalIntegralLower curve differential sheet direction =
        PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower
          direction (ofPreparedPath curve differential sheet prepared).parents
  | _, _, .nil _point, _, .nil _ _owner => rfl
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail => by
      simp only [
        PreparedClearPathModels.PreparedPath.directionalIntegralLower,
        ofPreparedPath,
        PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower_append,
        dataOfCompleteSegment_parents]
      have headEqual :
          preparedHead.directionalIntegralLower curve differential sheet
              direction =
            PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower
              direction
                (preparedHead.centeredEdges curve differential sheet) := by
        unfold
          PreparedClearPathModels.CompleteSegment.directionalIntegralLower
          PreparedClearPathModels.CompleteSegment.centeredEdges
        exact
          PreparedSubdivisionModelCore.preparedSubdivisionDirectionalIntegralLower_eq_centeredEdges
            curve differential sheet direction preparedHead.subdivision
              (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
                differential sheet preparedHead.subdivision)
      rw [headEqual,
        ofPreparedPath_directionalIntegralLower curve differential sheet
          direction preparedTail]

/-- The centered parent list of a prepared path has exactly its retained total step count. -/
@[simp] theorem ofPreparedPath_parents_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {ambient : Box} :
    forall {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      (ofPreparedPath curve differential sheet prepared).parents.length =
        prepared.stepCount
  | _, _, .nil point, _, .nil _ _owner => rfl
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail => by
      rewrite [ofPreparedPath, PreparedClearPathModels.PreparedPath.stepCount,
        Append.length_append, dataOfCompleteSegment_parents_length,
        ofPreparedPath_parents_length curve differential sheet preparedTail]
      exact Eq.refl _

/-- Strict parameter-edge ordering in the original prepared path gives properness of its centered parents. -/
theorem ofPreparedPath_allParentsProper_of_allEdgesProper {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {ambient : Box} :
    forall {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      PreparedClearPathModels.PreparedPath.AllEdgesProper
          prepared ->
        PreparedDyadicRefinements.AllParentsProper
          ((ofPreparedPath curve differential sheet prepared).parents)
  | _, _, .nil _point, _, .nil _ _owner, _proper => trivial
  | _, _, .cons _head _tail, _,
      .cons _ _ _owner _headWithin preparedHead preparedTail, proper => by
      apply allParentsProper_append
      · apply allParentsProper_of_parameterEdgesProper
        rw [dataOfCompleteSegment_parents,
          PreparedClearPathModels.CompleteSegment.centeredEdges_parameterEdges]
        exact allParameterEdgesProper_of_strictParameterEdges _ proper.1
      · exact ofPreparedPath_allParentsProper_of_allEdgesProper curve
          differential sheet preparedTail proper.2

/-- A successful dyadic preparation of the original clear path has proper centered parents. -/
theorem ofPreparedPath_allParentsProper_of_tryDyadic {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      (prepared :
        PreparedClearPathModels.PreparedPath path owner),
      PreparedClearPathModels.PreparedPath.tryDyadic path within
          owner depth rootDiameter rootDiameterPositive = some prepared ->
        PreparedDyadicRefinements.AllParentsProper
          ((ofPreparedPath curve differential sheet prepared).parents) := by
  intro ambient start finish path
  induction path with
  | nil point =>
      intro _within _owner _prepared success
      simp only
        [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      cases success
      simpa only [ofPreparedPath] using
        (show PreparedDyadicRefinements.AllParentsProper [] from
          trivial)
  | cons head tail inductionHypothesis =>
      intro within owner _prepared success
      rw [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          cases success
          let preparedHead :=
            PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          simpa only [ofPreparedPath, dataOfCompleteSegment_parents] using
            allParentsProper_append
              (ofTryDyadic_allParentsProper curve differential head
                within.head owner sheet depth rootDiameter
                  rootDiameterPositive headSuccess)
              (inductionHypothesis within.tail preparedHead.finishOwner
                preparedTail tailSuccess)

/-- A checked dyadic path's retained preparation has proper centered parents. -/
theorem ofCheckedDyadic_prepared_allParentsProper {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    PreparedDyadicRefinements.AllParentsProper
      ((ofPreparedPath curve differential sheet checked.prepared).parents) := by
  induction checked with
  | nil =>
      simp only [PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath]
      trivial
  | cons head tail owner headWithin headSafe remaining inductionHypothesis =>
      simp only [PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath]
      simpa only [dataOfCompleteSegment_parents] using
        (allParentsProper_append
          (ofSafeDyadic_allParentsProper curve differential head headWithin
            owner sheet depth rootDiameter rootDiameterPositive headSafe)
          inductionHypothesis)

/-- Package the original checked dyadic path's centered data with its proved properness. -/
@[expose] def ofCheckedDyadic {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    CheckedDyadicCenteredState curve differential sheet start finish :=
  let data := ofPreparedPath curve differential sheet checked.prepared
  { parents := data.parents
    proper := ofCheckedDyadic_prepared_allParentsProper curve differential
      sheet checked
    chain := data.chain }

/-- The checked centered state's parent count equals its original prepared path's step count. -/
@[simp] theorem ofCheckedDyadic_parents_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    (ofCheckedDyadic curve differential sheet checked).parents.length =
      checked.prepared.stepCount := by
  unfold ofCheckedDyadic
  exact ofPreparedPath_parents_length curve differential sheet checked.prepared

/-- A complete segment built from executed dyadic mesh safety has proper centered parents. -/
theorem ofExecutedDyadic_allParentsProper {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.ExecutedDyadicMeshSafe
        segment within PreparedClearPathModels.zeroEndpoint
          PreparedClearPathModels.oneEndpoint
            (PreparedClearPathModels.ownerAtStart segment owner)
              depth rootDiameter rootDiameterPositive) :
    PreparedDyadicRefinements.AllParentsProper
      ((PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
        segment within owner depth rootDiameter rootDiameterPositive
          safe).centeredEdges curve differential sheet) := by
  apply allParentsProper_of_parameterEdgesProper
  rw [PreparedClearPathModels.CompleteSegment.centeredEdges_parameterEdges,
    PreparedClearPathModels.CompleteSegment.ofExecutedDyadic_parameterEdges]
  exact dyadicEdges_allParameterEdgesProper depth
    PreparedClearPathModels.zeroEndpoint
    PreparedClearPathModels.oneEndpoint (by decide)

/-- Construct a proper centered chain directly from the original executed checked dyadic path.

The head uses its retained executed subdivision and joins the recursively retained tail without replacing the original
root owners. -/
@[expose] def ofExecutedCheckedDyadic {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
        depth rootDiameter rootDiameterPositive path owner) :
    CheckedDyadicCenteredState curve differential sheet start finish :=
  match checked with
  | .nil point _owner =>
      { parents := []
        proper := trivial
        chain := .nil _ }
  | .cons head _tail owner headWithin headSafe remaining =>
      let preparedHead :=
        PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      { parents :=
          preparedHead.centeredEdges curve differential sheet ++
            tailState.parents
        proper :=
          allParentsProper_append
            (ofExecutedDyadic_allParentsProper curve differential head
              headWithin owner sheet depth rootDiameter rootDiameterPositive
                headSafe)
            tailState.proper
        chain :=
          (ofCompleteSegment curve differential sheet preparedHead).append
            tailState.chain }
  termination_by structural checked

/-- The directly constructed executed centered state has exactly the parent list read from its retained prepared path.
-/
theorem ofExecutedCheckedDyadic_parents_eq_ofPreparedPath {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      (ofExecutedCheckedDyadic curve differential sheet checked).parents =
        (ofPreparedPath curve differential sheet checked.prepared).parents := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner => rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      simp only [ofExecutedCheckedDyadic,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        ofPreparedPath]
      rw [dataOfCompleteSegment_parents,
        ih]

/-- The complete segment has one canonical centered edge per retained subdivision step. -/
theorem completeSegment_centeredEdges_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      PreparedClearPathModels.CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).length =
      prepared.subdivision.stepCount := by
  unfold PreparedClearPathModels.CompleteSegment.centeredEdges
  exact centeredEdges_length_eq_stepCount curve differential sheet
    prepared.subdivision _

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Recasting canonical subdivision centers to their own differential preserves the exact centered-edge list. -/
private theorem canonicalCenteredEdges_recast_self {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    forall (subdivision :
      PreparedSheetContinuation.Subdivision segment within left
        owner),
      (PreparedSubdivisionModelCore.centeredEdges curve differential
          sheet subdivision
            (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
              differential sheet subdivision)).map
          (recastCenteredEdge differential) =
        PreparedSubdivisionModelCore.centeredEdges curve differential
          sheet subdivision
            (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
              differential sheet subdivision)
  | .stop _ _ => rfl
  | .next _ _ _ _ _ _ remaining => by
      simp only [PreparedSubdivisionModelCore.centeredEdges,
        PreparedSubdivisionAutomaticModels.canonicalCenterStates,
        List.map_cons, recastCenteredEdge]
      rw [recastPreparedEdge_self]
      rw [canonicalCenteredEdges_recast_self curve differential sheet
        remaining]

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Recasting a complete segment's canonical centers to their own differential preserves its centered-edge list. -/
theorem completeSegment_centeredEdges_recast_self {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2)
    (prepared :
      PreparedClearPathModels.CompleteSegment segment within owner) :
    (prepared.centeredEdges curve differential sheet).map
        (recastCenteredEdge differential) =
      prepared.centeredEdges curve differential sheet := by
  unfold PreparedClearPathModels.CompleteSegment.centeredEdges
  exact canonicalCenteredEdges_recast_self curve differential sheet
    prepared.subdivision

/-- Recasting the canonical centered parents of a prepared path to their own differential preserves the exact list. -/
theorem ofPreparedPath_recast_self {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      (ofPreparedPath curve differential sheet prepared).parents.map
          (recastCenteredEdge differential) =
        (ofPreparedPath curve differential sheet prepared).parents := by
  intro ambient start finish path owner prepared
  induction prepared with
  | nil point owner =>
      exact Eq.refl _
  | cons head tail owner headWithin preparedHead preparedTail ih =>
      simp only [ofPreparedPath, Map.map_append]
      rw [dataOfCompleteSegment_parents,
        completeSegment_centeredEdges_recast_self curve differential sheet
          preparedHead,
        ih]

/-- The successful dyadic preparation equation supplies properness of its exact centered parent list. -/
theorem ofPreparedPath_allParentsProper_ofTryDyadic {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : PreparedClearPathModels.PreparedPath path owner},
      PreparedClearPathModels.PreparedPath.tryDyadic path within
          owner depth rootDiameter rootDiameterPositive = some prepared ->
        PreparedDyadicRefinements.AllParentsProper
          (ofPreparedPath curve differential sheet prepared).parents := by
  intro ambient start finish path within owner prepared success
  exact ofPreparedPath_allParentsProper_of_tryDyadic curve differential sheet
    depth rootDiameter rootDiameterPositive path within owner prepared success

/-- Package a successful dyadic path preparation as its proper centered parent list and chain. -/
@[expose] def ofTryDyadic {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter)
    {ambient : Box} {start finish : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Owner (curve.polynomial.eval start))
    {prepared : PreparedClearPathModels.PreparedPath path owner}
    (success : PreparedClearPathModels.PreparedPath.tryDyadic path
      within owner depth rootDiameter rootDiameterPositive = some prepared) :
    CheckedDyadicCenteredState curve differential sheet start finish :=
  let centered := ofPreparedPath curve differential sheet prepared
  { parents := centered.parents
    proper := ofPreparedPath_allParentsProper_ofTryDyadic curve differential
      sheet depth rootDiameter rootDiameterPositive path within owner success
    chain := centered.chain }

end

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
/-- Sum the requested-diameter complete-segment weighted bounds along the original clear path. -/
@[expose] def dyadicPathTotalWeightedBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    (rootDiameter : Fraction.Rational) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish) : Fraction.Rational :=
  match path with
  | .nil _point => 0
  | .cons head tail =>
      completeDyadicTotalWeightedBound differential head rootDiameter depth +
        dyadicPathTotalWeightedBound differential rootDiameter depth tail
  termination_by structural path

/-- Sum the upward dyadic rounded requested-diameter weighted bounds over the original path segments. -/
@[expose] def dyadicPathTotalWeightedDyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    (rootDiameter : Fraction.Rational) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish) : Fraction.Rational :=
  match path with
  | .nil _point => 0
  | .cons head tail =>
      completeDyadicTotalWeightedDyadicBound differential head rootDiameter
          depth +
        dyadicPathTotalWeightedDyadicBound differential rootDiameter depth tail
  termination_by structural path

/-- For a nonnegative requested diameter, the summed dyadic rounded estimates dominate the path's weighted bound. -/
theorem dyadicPathTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {rootDiameter : Fraction.Rational} (rootDiameterNonnegative : 0 <= rootDiameter)
    (depth : Nat) {ambient : Box} {start finish : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish) :
    dyadicPathTotalWeightedBound differential rootDiameter depth path <=
      dyadicPathTotalWeightedDyadicBound differential rootDiameter depth
        path := by
  induction path with
  | nil point => exact le_rfl
  | cons head tail inductionHypothesis =>
      unfold dyadicPathTotalWeightedBound
        dyadicPathTotalWeightedDyadicBound
      exact add_le_add
        (completeDyadicTotalWeightedBound_le_dyadicBound differential head
          rootDiameterNonnegative depth)
        inductionHypothesis

/-- Sum the natural-ceiling requested-diameter squared-integral estimates over the original path segments. -/
@[expose] def dyadicPathIntegralNormSqCeilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    (rootDiameter : Fraction.Rational) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish) : Fraction.Rational :=
  match path with
  | .nil _point => 0
  | .cons head tail =>
      completeDyadicIntegralNormSqCeilBound differential head rootDiameter
          depth +
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth tail
  termination_by structural path

end

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Sum complete-segment weighted bounds using each segment's actual retained root-diameter maximum. -/
@[expose] def preparedPathTotalWeightedBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    Fraction.Rational :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicTotalWeightedBound differential head headWithin
          owner preparedHead depth +
        preparedPathTotalWeightedBound differential depth preparedTail

/-- Sum upward dyadic rounded weighted bounds from the original segments' actual retained root diameters. -/
@[expose] def preparedPathTotalWeightedDyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    Fraction.Rational :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicTotalWeightedDyadicBound differential head
          headWithin owner preparedHead depth +
        preparedPathTotalWeightedDyadicBound differential depth preparedTail

/-- The sum of upward rounded actual-cache estimates dominates the prepared path's weighted bound. -/
theorem preparedPathTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    preparedPathTotalWeightedBound differential depth prepared <=
      preparedPathTotalWeightedDyadicBound differential depth prepared := by
  induction prepared with
  | nil point owner => exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathTotalWeightedBound
        preparedPathTotalWeightedDyadicBound
      exact add_le_add
        (completePreparedDyadicTotalWeightedBound_le_dyadicBound differential
          head headWithin owner preparedHead depth)
        inductionHypothesis

/-- Sum squared-integral estimates using each original prepared segment's actual cached root diameters. -/
@[expose] def preparedPathIntegralNormSqSumBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    Fraction.Rational :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicIntegralNormSqSumBound differential head headWithin
          owner preparedHead depth +
        preparedPathIntegralNormSqSumBound differential depth preparedTail

/-- Sum natural-ceiling squared-integral residual estimates from the actual cached segment diameters. -/
@[expose] def preparedPathIntegralNormSqCeilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    Fraction.Rational :=
  match prepared with
  | .nil _point _owner => 0
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      completePreparedDyadicIntegralNormSqCeilBound differential head
          headWithin owner preparedHead depth +
        preparedPathIntegralNormSqCeilBound differential depth preparedTail

/-- The summed natural-ceiling estimates dominate the prepared path's squared-integral sum bound. -/
theorem preparedPathIntegralNormSqSumBound_le_ceilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    preparedPathIntegralNormSqSumBound differential depth prepared <=
      preparedPathIntegralNormSqCeilBound differential depth prepared := by
  induction prepared with
  | nil point owner => exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathIntegralNormSqSumBound
        preparedPathIntegralNormSqCeilBound
      exact add_le_add
        (completePreparedDyadicIntegralNormSqSumBound_le_ceilBound differential
          head headWithin owner preparedHead depth)
        inductionHypothesis

end

set_option genInjectivity false in
/-- The two scalar preflight estimates aggregated over an original prepared path.

The record stores weighted-allowance and squared-integral estimates; the shared computation and projection laws identify
their exact segment sums. -/
structure PreparedPathPreflightBounds where
  /-- The upward rounded estimate of the retained total weighted allowance. -/ totalWeighted : Fraction.Rational
  /-- The natural-ceiling estimate for the retained sum of squared integral samples. -/ integralNormSqSum :
    Fraction.Rational

constructive_injectivity PreparedPathPreflightBounds

open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Compute both path preflight estimates together from the original retained segment preparations.

Each head shares its local-error calculation between both estimates, and the retained tail contributes its corresponding
pair of sums. -/
@[expose] def preparedPathPreflightBounds {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    PreparedPathPreflightBounds :=
  match prepared with
  | .nil _point _owner =>
      { totalWeighted := 0
        integralNormSqSum := 0 }
  | .cons head _tail owner headWithin preparedHead preparedTail =>
      let headBounds := completePreparedDyadicPreflightBounds differential head
        headWithin owner preparedHead depth
      let tailBounds := preparedPathPreflightBounds differential depth
        preparedTail
      { totalWeighted :=
          headBounds.totalWeighted + tailBounds.totalWeighted
        integralNormSqSum :=
          headBounds.integralNormSqSum + tailBounds.integralNormSqSum }

/-- The shared path preflight computation returns exactly the summed upward dyadic weighted estimate. -/
@[simp] theorem preparedPathPreflightBounds_totalWeighted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    (preparedPathPreflightBounds differential depth prepared).totalWeighted =
      preparedPathTotalWeightedDyadicBound differential depth prepared := by
  induction prepared with
  | nil point owner => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathPreflightBounds preparedPathTotalWeightedDyadicBound
      change
        (completePreparedDyadicPreflightBounds differential head headWithin
            owner preparedHead depth).totalWeighted +
          (preparedPathPreflightBounds differential depth
            preparedTail).totalWeighted = _
      rw [completePreparedDyadicPreflightBounds_totalWeighted,
        inductionHypothesis]

/-- The shared path preflight computation returns exactly the summed natural-ceiling squared-integral estimate. -/
@[simp] theorem preparedPathPreflightBounds_integralNormSqSum {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (prepared : PreparedClearPathModels.PreparedPath path owner) :
    (preparedPathPreflightBounds differential depth prepared).integralNormSqSum =
      preparedPathIntegralNormSqCeilBound differential depth prepared := by
  induction prepared with
  | nil point owner => rfl
  | cons head tail owner headWithin preparedHead preparedTail
      inductionHypothesis =>
      unfold preparedPathPreflightBounds preparedPathIntegralNormSqCeilBound
      change
        (completePreparedDyadicPreflightBounds differential head headWithin
            owner preparedHead depth).integralNormSqSum +
          (preparedPathPreflightBounds differential depth
            preparedTail).integralNormSqSum = _
      rw [completePreparedDyadicPreflightBounds_integralNormSqSum,
        inductionHypothesis]

end CenteredPathChain

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
