module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Coarse/fine root agreement at arbitrary child queries

The coarse edge supplies a fixed positive root-box budget.  Root agreement at
a child's start then propagates to any rational query through a finite
comparison subdivision. Both prepared boxes supply uniform positive budgets;
the comparison depth does not constrain the integration mesh.  All owners below are the actual prepared/query owners,
reindexed
only by explicit equalities of displayed coordinates.
-/

namespace Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge RootChildAt)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

open Purelib.Data.Rat in
/-- The exact rational carrier for retained prepared-edge parameters. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for original point and root readings. -/
abbrev Gaussian := Basic.Canonical
/-- The original winding-one quadratic root owner indexed by its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original operational equivalence certificate between retained Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
open Purelib.Curves.Hyperelliptic in
/-- The original prepared edge for the retained curve and differential. -/
abbrev PreparedEdge {genus : Nat} (curve : Basic.HyperellipticCurve genus) (differential :
  Differentials.Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge curve differential

open Purelib.RootIsolation in
/-- Transporting an original root owner along an exact parameter equality preserves its root name. -/
private theorem castOwner_name {source target : Gaussian} (equal : source = target)
    (owner : Owner source) :
    ownerRootName (SquareRoot.Owner.Transport.castOwnerParameter equal owner).parameterNonzero
      (SquareRoot.Owner.Transport.castOwnerParameter equal owner) = ownerRootName owner.parameterNonzero owner := by
  cases equal
  rfl

open Purelib.Approximation.Gaussian in
/-- Transport a retained operational name equivalence along exact equalities of its two original names. -/
public def rename {first second left right : Name.Basic.Named}
    (firstEq : first = left) (secondEq : second = right)
    (equivalent : NamedEquivalent first second) : NamedEquivalent left right := by
  cases firstEq
  cases secondEq
  exact equivalent

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- The original prepared edge's fixed root-box budget with its exact polynomial variation allowance.

The budget retains the cached prepared owner, and its movement equation identifies the original segment and exact left
and requested endpoint parameters. -/
structure ParentBudget (parent : PreparedEdge curve differential) where
  /-- The fixed-box budget of the original edge's cached prepared owner. -/ data : FixedRootBoxBudget.Budget
    parent.cached.preparedOwner
  /-- The budget movement equals the exact original segment variation between the retained edge endpoint parameters. -/
    movement_eq : data.movement = ClearSheetContinuation.variationBound parent.segment
    parent.left.parameter parent.request.endpoint.parameter

constructive_injectivity ParentBudget

namespace ParentBudget

open Purelib.Riemann.Branches in
/-- Cache the original prepared edge's fixed-box budget using its exact segment variation bound and retained smallness
certificate. -/
def acquire (parent : PreparedEdge curve differential) : ParentBudget parent :=
  let movement := ClearSheetContinuation.variationBound parent.segment parent.left.parameter
    parent.request.endpoint.parameter
  let data := FixedRootBoxBudget.Budget.acquire parent.cached.preparedOwner movement
    (ClearSheetContinuation.variationBound_nonneg parent.segment _ _)
    (by rw [parent.cached.preparedOwner_eq]; exact parent.small)
  ⟨data, rfl⟩

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- Every retained point of the original prepared edge satisfies its cached parent movement budget. -/
theorem pointMovement {parent : PreparedEdge curve differential} (budget : ParentBudget parent)
    (fraction : Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point : Gaussian}
    (pointEq : parent.point fraction = point) :
    normSq (curve.polynomial.eval (parent.segment.pointAt parent.left.parameter) - curve.polynomial.eval point) ≤
      budget.data.movement := by
  have coordinateEq : parent.point fraction = parent.segment.pointAt (parameterAt parent.left parent.request fraction)
    :=
    (pointAt_parameterAt parent.segment parent.within parent.left parent.request fraction).symm
  rw [budget.movement_eq, ← pointEq, coordinateEq]
  rw [← Norm.Basic.normSq_eq_canonical]
  exact (ClearSheetContinuation.evaluation_variation_le parent.segment parent.within
    parent.left.parameter (parameterAt parent.left parent.request fraction) parent.left.inside
    (parameterAt_inside parent.left parent.request parent.ordered fraction inside)).trans
      (ClearSheetContinuation.variationBound_le_of_between parent.segment
        (parameterAt_between parent.left parent.request parent.ordered fraction inside).1
        (parameterAt_between parent.left parent.request parent.ordered fraction inside).2)

end ParentBudget

set_option genInjectivity false in
/-- A retained original prepared-edge root query represented by its exact point owner and source-box refinement.

The owner is indexed by the polynomial at the specified point. Its name equals the original edge query at the retained
fraction and inside proof. -/
structure QueryAt (edge : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (point : Gaussian) where
  /-- The retained root owner at the original polynomial evaluated at this exact query point. -/ owner : Owner
    (curve.polynomial.eval point)
  /-- This owner's original root name equals the retained edge query at its exact fraction and inside proof. -/ name_eq
    : ownerRootName owner.parameterNonzero owner = edge.rootName fraction inside
  /-- The retained query owner's initial box refines the original edge's cached prepared-owner box. -/ refines :
    owner.track.initial.box.Refines edge.cached.preparedOwner.track.initial.box

constructive_injectivity QueryAt

/-- Transport the retained query certificate along an exact equality of its point index. -/
def QueryAt.castPoint {edge : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : 0 ≤ fraction ∧ fraction ≤ 1} {first second : Gaussian}
    (equal : first = second) (query : QueryAt edge fraction inside first) : QueryAt edge fraction inside second :=
  equal ▸ query

open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Retain the original prepared edge's direct query owner at the exact reparameterized segment point.

The certificate preserves the original root-name equation and reserved transport refinement to the cached prepared-owner
box. -/
def directQuery (edge : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    QueryAt edge fraction inside (edge.segment.pointAt (parameterAt edge.left edge.request fraction)) where
  owner := edge.directQueryOwner fraction inside
  name_eq := (edge.rootName_eq_directQueryOwnerRootName fraction inside).symm
  refines := ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines edge.cached.preparedOwner
    (edge.segment.pointAt_eval_ne_zero _ (parameterAt_inside edge.left edge.request edge.ordered fraction inside))
    (by
      rw [edge.cached.preparedOwner_eq]
      exact pointNormSmall edge.segment edge.within edge.left edge.owner
        edge.request edge.ordered edge.small fraction inside)
    (transportReserve edge.segment edge.left edge.request)

/-- Retain the original direct edge query at a point identified by an explicit edge-point equality. -/
@[irreducible] def queryAt (edge : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point : Gaussian} (pointEq : edge.point fraction = point) :
    QueryAt edge fraction inside point :=
  (directQuery edge fraction inside).castPoint
    ((pointAt_parameterAt edge.segment edge.within edge.left edge.request fraction).trans pointEq)

/-- Compare two retained original parent queries at the same exact point using the cached movement budget.

Both original query owners refine the retained prepared-owner box; their name equations transport the common fixed-box
comparison to the original edge readings. -/
def compareQueries {parent : PreparedEdge curve differential} (budget : ParentBudget parent)
    {first second : Coordinate} {firstInside : 0 ≤ first ∧ first ≤ 1}
    {secondInside : 0 ≤ second ∧ second ≤ 1} {point : Gaussian}
    (firstQuery : QueryAt parent first firstInside point)
    (secondQuery : QueryAt parent second secondInside point)
    (movement : normSq (curve.polynomial.eval (parent.segment.pointAt parent.left.parameter) -
      curve.polynomial.eval point) ≤ budget.data.movement) :
    NamedEquivalent (parent.rootName first firstInside) (parent.rootName second secondInside) :=
  rename firstQuery.name_eq secondQuery.name_eq
    ((budget.data.retainedEquivalent firstQuery.owner.parameterNonzero movement
      firstQuery.owner firstQuery.refines).symm.trans
      (budget.data.retainedEquivalent secondQuery.owner.parameterNonzero movement
        secondQuery.owner secondQuery.refines))

/-- Two original parent queries at equal geometric points are operationally equivalent under the retained parent budget.
-/
def samePointEquivalent {parent : PreparedEdge curve differential} (budget : ParentBudget parent)
    (first second : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1)
    (secondInside : 0 ≤ second ∧ second ≤ 1) (equal : parent.point first = parent.point second) :
    NamedEquivalent (parent.rootName first firstInside) (parent.rootName second secondInside) :=
  compareQueries budget (queryAt parent first firstInside equal)
    (queryAt parent second secondInside rfl) (budget.pointMovement second secondInside rfl)

open FixedRootBoxPath (Inside PathData)

section
open Purelib.Data.Rat
/-- The product of two retained unit-interval parameters remains in the unit interval. -/
public theorem multiply_inside {first second : Coordinate}
    (firstInside : Inside first) (secondInside : Inside second) : Inside (first * second) :=
  ⟨Fraction.Order.Arithmetic.mul_nonneg_direct firstInside.1 secondInside.1,
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct secondInside.2 firstInside.1).trans
      (by simpa only [Fraction.Field.mul_one_direct] using firstInside.2)⟩

/-- A unit-interval interpolation of two retained unit-interval parameters remains in that interval. -/
public theorem interpolate_inside {first last fraction : Coordinate}
    (firstInside : Inside first) (lastInside : Inside last) (inside : Inside fraction) :
    Inside ((1 - fraction) * first + fraction * last) := by
  have complementary := Fraction.Order.Arithmetic.sub_nonneg_direct inside.2
  have nonnegative := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct complementary firstInside.1)
    (Fraction.Order.Arithmetic.mul_nonneg_direct inside.1 lastInside.1)
  refine ⟨by simpa only [Fraction.Field.zero_add] using nonnegative, ?_⟩
  calc
    _ ≤ (1 - fraction) * 1 + fraction * 1 := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.2 complementary)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside.2 inside.1)
    _ = 1 := by ring1

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- The original prepared-edge point map preserves the exact affine interpolation formula. -/
private theorem point_interpolate (edge : PreparedEdge curve differential) (first last fraction : Coordinate) :
    edge.point ((1 - fraction) * first + fraction * last) =
      edge.point first + Scale.scale fraction (edge.point last - edge.point first) := by
  apply Basic.ext <;>
    simp only [PreparedConstantModels.PreparedEdge.point, Geometry.ClearPath.ClearSegment.pointAt,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re, Scale.scale_im] <;> ring1

/-- The parent interpolation from a retained child start to an identified child point equals the original scaled child
parameterization. -/
public theorem point_agreement {parent child : CenteredEdge curve differential}
    (start : RootChildAt parent child) (childFraction finishFraction t : Coordinate)
    (finishEq : parent.edge.point finishFraction = child.edge.point childFraction) :
    parent.edge.point ((1 - t) * start.fraction + t * finishFraction) = child.edge.point (childFraction * t) := by
  rw [point_interpolate, start.point_eq, finishEq]
  have childAffine := point_interpolate child.edge 0 childFraction t
  rw [show (1 - t) * 0 + t * childFraction = childFraction * t by ring1] at childAffine
  exact childAffine.symm

/-- A retained unit-interval prepared-edge point lies in its original ambient box. -/
private theorem point_inside (edge : PreparedEdge curve differential) (t : Coordinate) (inside : Inside t) :
    edge.ambient.Contains (edge.point t) :=
  edge.point_contains t inside

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
/-- Bound polynomial movement along a retained fraction of the original prepared edge by its dense Lipschitz majorant
and exact squared parameter displacement. -/
public theorem variation (edge : PreparedEdge curve differential)
    (fraction : Coordinate) (inside : Inside fraction) (left right : Coordinate)
    (leftInside : Inside left) (rightInside : Inside right) :
    normSq (curve.polynomial.eval (edge.point (fraction * left)) - curve.polynomial.eval (edge.point (fraction *
      right))) ≤
      (Bounds.Box.denseLipschitzBound curve.polynomial edge.ambient *
        normSq (edge.localSegment.pointAt 1 - edge.localSegment.pointAt 0) * fraction ^ 2) * (right - left) ^ 2 := by
  have bound := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound curve.polynomial
    (point_inside edge (fraction * left) (multiply_inside inside leftInside))
    (point_inside edge (fraction * right) (multiply_inside inside rightInside))
  have equal : normSq (edge.point (fraction * left) - edge.point (fraction * right)) =
      normSq (edge.localSegment.pointAt 1 - edge.localSegment.pointAt 0) * fraction ^ 2 * (right - left) ^ 2 := by
    change normSq (edge.localSegment.pointAt (fraction * left) - edge.localSegment.pointAt (fraction * right)) = _
    rw [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical]
    rw [edge.localSegment.normSq_pointAt_sub_pointAt, edge.localSegment.normSq_pointAt_sub_pointAt]
    ring1
  rw [Norm.Basic.normSq_eq_canonical
      (curve.polynomial.eval (edge.point (fraction * left)) - curve.polynomial.eval (edge.point (fraction * right))),
    Norm.Basic.normSq_eq_canonical
      (edge.point (fraction * left) - edge.point (fraction * right))] at bound
  rw [equal] at bound
  exact bound.trans_eq (by ring1)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- Construct common fixed-box path data for the original parent and child between their retained corresponding points.

The original child-fraction path is also the retained parent interpolation. Separate parent and child budgets certify
movement, and the exact dense Lipschitz scale controls variation. -/
public def pathData {parent child : CenteredEdge curve differential}
    (budget : ParentBudget parent.edge) (childBudget : ParentBudget child.edge)
    (start : RootChildAt parent child)
    (childFraction : Coordinate) (childInside : Inside childFraction)
    (finishFraction : Coordinate) (finishInside : Inside finishFraction)
    (finishEq : parent.edge.point finishFraction = child.edge.point childFraction) :
    PathData budget.data childBudget.data where
  point := fun t => curve.polynomial.eval (child.edge.point (childFraction * t))
  nonzero := fun t inside => by
    exact (QueryAt.owner (queryAt child.edge (childFraction * t) (multiply_inside childInside inside)
      rfl)).parameterNonzero
  firstMovement := fun t inside => budget.pointMovement
    ((1 - t) * start.fraction + t * finishFraction) (interpolate_inside start.inside finishInside inside)
    (point_agreement start childFraction finishFraction t finishEq)
  secondMovement := fun t inside => childBudget.pointMovement (childFraction * t) (multiply_inside childInside inside)
    rfl
  scale := Bounds.Box.denseLipschitzBound curve.polynomial child.edge.ambient *
    normSq (child.edge.localSegment.pointAt 1 - child.edge.localSegment.pointAt 0) * childFraction ^ 2
  scale_nonnegative := by
    have distanceNonnegative : 0 ≤ normSq (child.edge.localSegment.pointAt 1 - child.edge.localSegment.pointAt 0) := by
      rw [← Norm.Basic.normSq_eq_canonical]
      exact Norm.Basic.normSq_nonneg _
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Bounds.Box.denseLipschitzBound_pos _ _).le distanceNonnegative)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  variation := variation child.edge childFraction childInside

open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Compare the original parent and child root queries at retained corresponding points along the child edge.

The retained start sheet equivalence and exact finish-point equality define a common finite path. Its separate fixed-box
budgets transport the two original owner names to the requested query fractions. -/
def queryEquivalent {parent child : CenteredEdge curve differential}
    (budget : ParentBudget parent.edge) (start : RootChildAt parent child)
    (childFraction : Coordinate) (childInside : Inside childFraction)
    (finishFraction : Coordinate) (finishInside : Inside finishFraction)
    (finishEq : parent.edge.point finishFraction = child.edge.point childFraction) :
    NamedEquivalent (parent.edge.rootName finishFraction finishInside)
      (child.edge.rootName childFraction childInside) where
  compare := fun leftIndex rightIndex target positive =>
    let childBudget := ParentBudget.acquire child.edge
    let path := PreparedRefinementRootEndpoints.pathData budget childBudget start childFraction childInside
      finishFraction finishInside finishEq
    have zeroPoint : child.edge.point 0 = child.edge.point (childFraction * 0) := by rw [Fraction.Field.mul_zero_direct]
    have onePoint : child.edge.point childFraction = child.edge.point (childFraction * 1) := by rw
      [Fraction.Field.mul_one_direct]
    let firstStart := queryAt parent.edge start.fraction start.inside (start.point_eq.trans zeroPoint)
    let secondStart := queryAt child.edge 0 child.edge.baseInside zeroPoint
    let firstFinish := queryAt parent.edge finishFraction finishInside (finishEq.trans onePoint)
    let secondFinish := queryAt child.edge childFraction childInside onePoint
    let startAgreement : NamedEquivalent
        (SquareRootTrackEquivalence.ownerRootName (QueryAt.owner firstStart).parameterNonzero (QueryAt.owner
          firstStart))
        (SquareRootTrackEquivalence.ownerRootName (QueryAt.owner secondStart).parameterNonzero (QueryAt.owner
          secondStart)) := by
      rw [(QueryAt.name_eq firstStart), (QueryAt.name_eq secondStart)]
      exact start.rootEquivalent
    let result := path.retainedEquivalent (QueryAt.owner firstStart) (QueryAt.owner secondStart)
      (QueryAt.refines firstStart) (QueryAt.refines secondStart) startAgreement (QueryAt.owner firstFinish)
        (QueryAt.owner secondFinish)
      (QueryAt.refines firstFinish) (QueryAt.refines secondFinish)
    let renamed := rename (QueryAt.name_eq firstFinish) (QueryAt.name_eq secondFinish) result
    renamed.compare leftIndex rightIndex target positive

end Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints
