module

public import Purelib.Riemann.Paths.OwnerTracePath.Box
public import Purelib.Riemann.Paths.OwnerTracePath.Box.Reverse
public import Purelib.Riemann.Paths.OwnerTracePath.Pullback
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Dyadic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Cast
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTraceReadings.Trace
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Trace
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Riemann.Paths.OwnerTracePath.Between
import Purelib.Riemann.Paths.OwnerTracePath.Reverse
import Purelib.Riemann.Paths.OwnerTraceReadings.Reverse

/-! # Actual paid dyadic root paths from a retained source Owner

One extra finite search pays the trace residual/movement request before
interior Owners or readings are constructed. Interior Owners are actual
advances of the SAME coarse source; each midpoint Owner and residual
request is stored once and shared by the two recursive subpaths. The
given endpoint Owners and tails are never reconstructed.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Dyadic

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.ClearSheetContinuation
  (midpoint midpoint_inside left_le_midpoint midpoint_le_right)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootProvenance
open Purelib.Riemann.RootContinuation.SquareRootTrace
open Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy (parameterInterval)

/-- The original unit interval's initial Endpoint. -/
@[expose] def first : Endpoint := ⟨0, Order.Basic.le_refl _, by decide +kernel⟩

/-- The original unit interval's terminal Endpoint. -/
@[expose] def last : Endpoint := ⟨1, by decide +kernel, Order.Basic.le_refl _⟩

/-- The retained whole unit interval has its original left-to-right orientation. -/
theorem first_le_last : first.parameter ≤ last.parameter := by decide +kernel

/-- Retain the actual polynomial radicand at the original endpoint's real Gaussian parameter. -/
@[expose] def value (polynomial : CoefficientPolynomial) (endpoint : Endpoint) : Canonical :=
  polynomial.eval (Cast.Path.ofCoordinate endpoint.parameter)

/-- The original Gaussian chord between two real parameters is their exact retained rational interpolation. -/
private theorem chord (left right : Endpoint) (time : Rational) :
    Affine.line (Cast.Path.ofCoordinate left.parameter)
      (Cast.Path.ofCoordinate right.parameter - Cast.Path.ofCoordinate left.parameter) time =
        Cast.Path.ofCoordinate (left.parameter + time * (right.parameter - left.parameter)) := by
  apply Basic.ext <;>
    simp only [Affine.line, Cast.Path.ofCoordinate, Basic.add_re, Basic.add_im,
      Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1

variable {referencePolynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood referencePolynomial count) (polynomial : CoefficientPolynomial)
    (source : Owner (value polynomial first))
    (sourceRefines : source.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (nonzero : ∀ endpoint : Endpoint, value polynomial endpoint ≠ 0)
    (scale : Rational) (scaleNonnegative : 0 ≤ scale)
    (variation : ∀ left right : Endpoint,
      Norm.Basic.normSq (value polynomial left - value polynomial right) ≤
        scale * (right.parameter - left.parameter) ^ 2)
    (wholeSmall : scale < source.track.initial.clearance.bound)

include scaleNonnegative variation wholeSmall in
/-- The whole actual variation pays each source-to-interior continuation before its Owner is built. -/
theorem advance_small (endpoint : Endpoint) :
    Norm.Basic.normSq (value polynomial first - value polynomial endpoint) <
      source.track.initial.clearance.bound := by
  have width := endpoint_width_le_one first endpoint endpoint.inside.1
  exact ((variation first endpoint).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width scaleNonnegative).trans_eq
      (Field.mul_one_direct scale))).trans_lt wholeSmall

/-- The actual original-source advance at one requested interior endpoint. -/
def advanceAt (endpoint : Endpoint) : Owner (value polynomial endpoint) :=
  source.advance (nonzero endpoint)
    (advance_small polynomial source scale scaleNonnegative variation wholeSmall endpoint)

include sourceRefines in
/-- The whole retained advance factory derives its refinement to the SAME original signed seed box. -/
theorem advance_refines (endpoint : Endpoint) (owner : Owner (value polynomial endpoint))
    (factory : owner = advanceAt polynomial source nonzero scale scaleNonnegative variation wholeSmall endpoint) :
    owner.track.initial.box.Refines patch.base.seed.owner.track.initial.box := by
  have retained := source.advance_initial_box_refines (nonzero endpoint)
    (advance_small polynomial source scale scaleNonnegative variation wholeSmall endpoint)
  exact (Eq.mpr (congrArg (fun result : Owner (value polynomial endpoint) =>
    result.track.initial.box.Refines source.track.initial.box) factory) retained).trans sourceRefines

/-- The original executable search pays trace movement at an additional depth before any interior work. -/
def selection : Geometric.Search.Selection scale 0 (traceAllowance patch.rootLower) :=
  Geometric.Search.Selection.build scale scaleNonnegative 0 (traceAllowance patch.rootLower)
    (traceAllowance_positive patch.rootLower_positive)

include scaleNonnegative in
/-- Every original leaf edge of the selected dyadic word pays the trace movement request. -/
theorem selection_paid (selected : Geometric.Search.Selection scale 0 (traceAllowance patch.rootLower))
    (edge : ParameterEdge) (member : edge ∈ dyadicEdges selected.stage first last) :
    scale * (edge.right.parameter - edge.left.parameter) ^ 2 ≤ traceAllowance patch.rootLower := by
  have width := dyadicEdges_width_le selected.stage selected.stage (Nat.le_refl _) first last
    first_le_last edge member
  have scaleEq : scale * Geometric.Basic.quarterRadius 1 selected.stage =
      Geometric.Basic.quarterRadius scale selected.stage := by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  exact ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width scaleNonnegative).trans_eq scaleEq).trans
    (selected.later_accurate (Nat.le_refl selected.stage)).le

include scaleNonnegative variation in
/-- A paid ordered leaf bounds actual polynomial movement on its entire chord. -/
theorem movement (left right : Endpoint) (ordered : left.parameter ≤ right.parameter)
    (paid : scale * (right.parameter - left.parameter) ^ 2 ≤ traceAllowance patch.rootLower)
    (time : Rational) (inside : parameterInterval.Contains time) :
    Norm.Basic.normSq (polynomial.eval (Affine.line (Cast.Path.ofCoordinate left.parameter)
        (Cast.Path.ofCoordinate right.parameter - Cast.Path.ofCoordinate left.parameter) time) -
      polynomial.eval (Cast.Path.ofCoordinate left.parameter)) ≤ traceAllowance patch.rootLower := by
  let middle : Endpoint := ⟨left.parameter + time * (right.parameter - left.parameter),
    Box.coordinate_between left.inside right.inside inside⟩
  have between := Box.coordinate_between
    (⟨Order.Basic.le_refl _, ordered⟩ : left.parameter ≤ left.parameter ∧ left.parameter ≤ right.parameter)
    (⟨ordered, Order.Basic.le_refl _⟩ : left.parameter ≤ right.parameter ∧ right.parameter ≤ right.parameter) inside
  have width := Order.Arithmetic.pow_le_pow_direct
    (Order.Arithmetic.sub_nonneg_direct between.1)
    (Order.Arithmetic.sub_le_sub_right_direct between.2 left.parameter) 2
  rewrite [chord]
  exact (Norm.Bounds.normSq_sub_symm (value polynomial middle) (value polynomial left)).trans_le
    ((variation left middle).trans
      ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width scaleNonnegative).trans paid))

include scaleNonnegative variation in
/-- The SAME original leaf payment bounds movement on the full oppositely oriented chord.

The reversed coordinate remains between the same original endpoints.
Only the exact polynomial radicand variation is used; roots are not
interpolated and the forward edge's Small data is not used as a bound.
-/
theorem reverse_movement (left right : Endpoint) (ordered : left.parameter ≤ right.parameter)
    (paid : scale * (right.parameter - left.parameter) ^ 2 ≤ traceAllowance patch.rootLower)
    (time : Rational) (inside : parameterInterval.Contains time) :
    Norm.Basic.normSq (polynomial.eval (Affine.line (Cast.Path.ofCoordinate right.parameter)
        (Cast.Path.ofCoordinate left.parameter - Cast.Path.ofCoordinate right.parameter) time) -
      polynomial.eval (Cast.Path.ofCoordinate right.parameter)) ≤ traceAllowance patch.rootLower := by
  let middle : Endpoint := ⟨right.parameter + time * (left.parameter - right.parameter),
    Box.coordinate_between right.inside left.inside inside⟩
  have between := Box.coordinate_between
    (⟨ordered, Order.Basic.le_refl _⟩ : left.parameter ≤ right.parameter ∧ right.parameter ≤ right.parameter)
    (⟨Order.Basic.le_refl _, ordered⟩ : left.parameter ≤ left.parameter ∧ left.parameter ≤ right.parameter) inside
  have width := Order.Arithmetic.pow_le_pow_direct
    (Order.Arithmetic.sub_nonneg_direct between.2)
    (Order.Arithmetic.sub_le_sub_left_direct between.1 right.parameter) 2
  have square : (middle.parameter - right.parameter) ^ 2 = (right.parameter - middle.parameter) ^ 2 := by
    ring1
  rewrite [chord]
  exact (Norm.Bounds.normSq_sub_symm (value polynomial middle) (value polynomial right)).trans_le
    ((variation right middle).trans
      ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (square.trans_le width) scaleNonnegative).trans paid))

/-- An exact finite leaf-payment predicate on the original ordered dyadic edge occurrences. -/
@[expose] def Paid (depth : Nat) (left right : Endpoint) : Prop :=
  ∀ edge : ParameterEdge, edge ∈ dyadicEdges depth left right →
    scale * (edge.right.parameter - edge.left.parameter) ^ 2 ≤ traceAllowance patch.rootLower

/-- The left recursive word retains its actual original leaf payments. -/
theorem left_paid (depth : Nat) (left right : Endpoint) (paid : Paid patch scale (depth + 1) left right) :
    Paid patch scale depth left
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩ := by
  intro edge member
  exact paid edge (Membership.mem_append.mpr (Or.inl member))

/-- The right recursive word retains its actual original leaf payments. -/
theorem right_paid (depth : Nat) (left right : Endpoint) (paid : Paid patch scale (depth + 1) left right) :
    Paid patch scale depth
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩ right := by
  intro edge member
  exact paid edge (Membership.mem_append.mpr (Or.inr member))

/-- All actual dyadic midpoint Owners, residual requests and leaf links, with their complete original factories.

The recursive product stores each midpoint once. Both child caches receive
that SAME Owner and request. Empty or stationary physical radicand movement
does not erase any original ordered parameter occurrence.
-/
@[expose] def Cache : (depth : Nat) → (left right : Endpoint) → (ordered : left.parameter ≤ right.parameter) →
    (paid : Paid patch scale depth left right) →
    (leftOwner : Owner (value polynomial left)) → (rightOwner : Owner (value polynomial right)) →
    (leftRefines : leftOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (rightRefines : rightOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (leftRequest : OwnerTail.TraceRequest leftOwner patch.rootLower patch.rootLower_positive) →
    (rightRequest : OwnerTail.TraceRequest rightOwner patch.rootLower patch.rootLower_positive) → Type
  | 0, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines, leftRequest, rightRequest =>
      { link : OwnerLink polynomial (Cast.Path.ofCoordinate left.parameter) (Cast.Path.ofCoordinate right.parameter)
          leftOwner rightOwner //
        link = OwnerLink.inBox patch _ _ leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest
          (movement patch polynomial scale scaleNonnegative variation left right ordered
            (paid ⟨left, right⟩ (Membership.mem_singleton.mpr rfl))) }
  | depth + 1, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines,
      leftRequest, rightRequest =>
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      (owner : { result : Owner (value polynomial middle) //
        result = advanceAt polynomial source nonzero scale scaleNonnegative variation wholeSmall middle }) ×
      (request : { result : OwnerTail.TraceRequest owner.val patch.rootLower patch.rootLower_positive //
        result = OwnerTail.requestTrace owner.val patch.rootLower patch.rootLower_positive }) ×
      Cache depth left middle (left_le_midpoint ordered) (left_paid patch scale depth left right paid)
        leftOwner owner.val leftRefines
        (advance_refines patch polynomial source sourceRefines nonzero scale scaleNonnegative variation
          wholeSmall middle owner.val owner.property) leftRequest request.val ×
      Cache depth middle right (midpoint_le_right ordered) (right_paid patch scale depth left right paid)
        owner.val rightOwner
        (advance_refines patch polynomial source sourceRefines nonzero scale scaleNonnegative variation
          wholeSmall middle owner.val owner.property) rightRefines request.val rightRequest

/-- Construct the actual midpoint tree and leaf links once, before requesting trace readings. -/
def build : (depth : Nat) → (left right : Endpoint) → (ordered : left.parameter ≤ right.parameter) →
    (paid : Paid patch scale depth left right) →
    (leftOwner : Owner (value polynomial left)) → (rightOwner : Owner (value polynomial right)) →
    (leftRefines : leftOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (rightRefines : rightOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (leftRequest : OwnerTail.TraceRequest leftOwner patch.rootLower patch.rootLower_positive) →
    (rightRequest : OwnerTail.TraceRequest rightOwner patch.rootLower patch.rootLower_positive) →
      Cache patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
        depth left right ordered paid leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest
  | 0, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines, leftRequest, rightRequest =>
      let link := OwnerLink.inBox patch _ _ leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest
        (movement patch polynomial scale scaleNonnegative variation left right ordered
          (paid ⟨left, right⟩ (Membership.mem_singleton.mpr rfl)))
      ⟨link, rfl⟩
  | depth + 1, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines,
      leftRequest, rightRequest =>
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      let owner : {result : Owner (value polynomial middle) //
          result = advanceAt polynomial source nonzero scale scaleNonnegative variation wholeSmall middle} :=
        ⟨advanceAt polynomial source nonzero scale scaleNonnegative variation wholeSmall middle, rfl⟩
      let request : {result : OwnerTail.TraceRequest owner.val patch.rootLower patch.rootLower_positive //
          result = OwnerTail.requestTrace owner.val patch.rootLower patch.rootLower_positive} :=
        ⟨OwnerTail.requestTrace owner.val patch.rootLower patch.rootLower_positive, rfl⟩
      let refines := advance_refines patch polynomial source sourceRefines nonzero scale scaleNonnegative variation
        wholeSmall middle owner.val owner.property
      let front := build depth left middle (left_le_midpoint ordered) (left_paid patch scale depth left right paid)
        leftOwner owner.val leftRefines refines leftRequest request.val
      let back := build depth middle right (midpoint_le_right ordered) (right_paid patch scale depth left right paid)
        owner.val rightOwner refines rightRefines request.val rightRequest
      ⟨owner, request, front, back⟩

/-- Read the exact ordered owner path from its SAME stored midpoint tree and leaf links. -/
@[expose] def path : (depth : Nat) → (left right : Endpoint) → (ordered : left.parameter ≤ right.parameter) →
    (paid : Paid patch scale depth left right) →
    (leftOwner : Owner (value polynomial left)) → (rightOwner : Owner (value polynomial right)) →
    (leftRefines : leftOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (rightRefines : rightOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (leftRequest : OwnerTail.TraceRequest leftOwner patch.rootLower patch.rootLower_positive) →
    (rightRequest : OwnerTail.TraceRequest rightOwner patch.rootLower patch.rootLower_positive) →
    Cache patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      depth left right ordered paid leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest →
    OwnerPath polynomial (Cast.Path.ofCoordinate left.parameter) leftOwner
      (Cast.Path.ofCoordinate right.parameter) rightOwner
  | 0, _, right, _, _, _, rightOwner, _, _, _, _, cached =>
      .cons cached.val (.nil (Cast.Path.ofCoordinate right.parameter) rightOwner)
  | depth + 1, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines,
      leftRequest, rightRequest, cached =>
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      let refines := advance_refines patch polynomial source sourceRefines nonzero scale scaleNonnegative variation
        wholeSmall middle cached.1.val cached.1.property
      (path depth left middle (left_le_midpoint ordered) (left_paid patch scale depth left right paid)
        leftOwner cached.1.val leftRefines refines leftRequest cached.2.1.val cached.2.2.1).append
      (path depth middle right (midpoint_le_right ordered) (right_paid patch scale depth left right paid)
        cached.1.val rightOwner refines rightRefines cached.2.1.val rightRequest cached.2.2.2)

/-- The actual midpoint tree preserves the full original ordered dyadic target word. -/
theorem path_vertices : (depth : Nat) → (left right : Endpoint) → (ordered : left.parameter ≤ right.parameter) →
    (paid : Paid patch scale depth left right) →
    (leftOwner : Owner (value polynomial left)) → (rightOwner : Owner (value polynomial right)) →
    (leftRefines : leftOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (rightRefines : rightOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (leftRequest : OwnerTail.TraceRequest leftOwner patch.rootLower patch.rootLower_positive) →
    (rightRequest : OwnerTail.TraceRequest rightOwner patch.rootLower patch.rootLower_positive) →
    (cached : Cache patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      depth left right ordered paid leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest) →
    (path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      depth left right ordered paid leftOwner rightOwner leftRefines rightRefines
        leftRequest rightRequest cached).vertices =
      (dyadicTargets depth left right).map (fun endpoint => Cast.Path.ofCoordinate endpoint.parameter)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | depth + 1, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines,
      leftRequest, rightRequest, cached => by
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      let refines := advance_refines patch polynomial source sourceRefines nonzero scale scaleNonnegative variation
        wholeSmall middle cached.1.val cached.1.property
      let frontPath := path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
        depth left middle (left_le_midpoint ordered) (left_paid patch scale depth left right paid)
        leftOwner cached.1.val leftRefines refines leftRequest cached.2.1.val cached.2.2.1
      let backPath := path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
        depth middle right (midpoint_le_right ordered) (right_paid patch scale depth left right paid)
        cached.1.val rightOwner refines rightRefines cached.2.1.val rightRequest cached.2.2.2
      change (frontPath.append backPath).vertices =
        ((dyadicTargets depth left middle) ++ dyadicTargets depth middle right).map _
      rewrite [OwnerPath.append_vertices]
      have front := path_vertices depth left middle (left_le_midpoint ordered)
        (left_paid patch scale depth left right paid) leftOwner cached.1.val leftRefines refines
        leftRequest cached.2.1.val cached.2.2.1
      have back := path_vertices depth middle right (midpoint_le_right ordered)
        (right_paid patch scale depth left right paid) cached.1.val rightOwner refines rightRefines
        cached.2.1.val rightRequest cached.2.2.2
      exact (congrArg₂ List.append front back).trans (Map.map_append _ _ _).symm

/-- Derive reverse operations from the SAME original midpoint/request tree and every genuine leaf payment.

This is a projection/fold of retained caches. No midpoint advance, residual
request, comparison selection or native reading is executed again.
-/
def reversals : (depth : Nat) → (left right : Endpoint) → (ordered : left.parameter ≤ right.parameter) →
    (paid : Paid patch scale depth left right) →
    (leftOwner : Owner (value polynomial left)) → (rightOwner : Owner (value polynomial right)) →
    (leftRefines : leftOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (rightRefines : rightOwner.track.initial.box.Refines patch.base.seed.owner.track.initial.box) →
    (leftRequest : OwnerTail.TraceRequest leftOwner patch.rootLower patch.rootLower_positive) →
    (rightRequest : OwnerTail.TraceRequest rightOwner patch.rootLower patch.rootLower_positive) →
    (cached : Cache patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      depth left right ordered paid leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest) →
    OwnerPath.Reversals (path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      depth left right ordered paid leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest cached)
  | 0, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines,
      leftRequest, rightRequest, cached =>
      let leafPaid := paid ⟨left, right⟩ (Membership.mem_singleton.mpr rfl)
      ⟨Eq.mpr (congrArg OwnerLink.ReverseData cached.property)
        (OwnerLink.reverseInBox patch _ _ leftOwner rightOwner leftRefines rightRefines leftRequest rightRequest
          (movement patch polynomial scale scaleNonnegative variation left right ordered leafPaid)
          (reverse_movement patch polynomial scale scaleNonnegative variation left right ordered leafPaid)), PUnit.unit⟩
  | depth + 1, left, right, ordered, paid, leftOwner, rightOwner, leftRefines, rightRefines,
      leftRequest, rightRequest, cached =>
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      let refines := advance_refines patch polynomial source sourceRefines nonzero scale scaleNonnegative variation
        wholeSmall middle cached.1.val cached.1.property
      let frontPath := path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
        depth left middle (left_le_midpoint ordered) (left_paid patch scale depth left right paid)
        leftOwner cached.1.val leftRefines refines leftRequest cached.2.1.val cached.2.2.1
      let backPath := path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
        depth middle right (midpoint_le_right ordered) (right_paid patch scale depth left right paid)
        cached.1.val rightOwner refines rightRefines cached.2.1.val rightRequest cached.2.2.2
      let front := reversals depth left middle (left_le_midpoint ordered) (left_paid patch scale depth left right paid)
        leftOwner cached.1.val leftRefines refines leftRequest cached.2.1.val cached.2.2.1
      let back := reversals depth middle right (midpoint_le_right ordered)
        (right_paid patch scale depth left right paid)
        cached.1.val rightOwner refines rightRefines cached.2.1.val rightRequest cached.2.2.2
      OwnerPath.Reversals.append frontPath backPath front back

variable (moved target : Owner (value polynomial last))
    (endpointSmall : Norm.Basic.normSq (value polynomial first - value polynomial last) <
      source.track.initial.clearance.bound)
    (movedFactory : moved = source.advance (nonzero last) endpointSmall)
    (equivalent : Approximation.Gaussian.Equivalence.NamedEquivalent (ownerName moved) (ownerName target))

include sourceRefines movedFactory in
/-- The GIVEN endpoint advance retains refinement to the SAME signed source box without advancing it again. -/
theorem moved_refines : moved.track.initial.box.Refines patch.base.seed.owner.track.initial.box := by
  have original := source.advance_initial_box_refines (nonzero last) endpointSmall
  exact (Eq.mpr (congrArg (fun value : Owner (value polynomial last) =>
    value.track.initial.box.Refines source.track.initial.box) movedFactory) original).trans sourceRefines

universe u

/-- The original whole link preparation with one dependent result on its SAME retained final path.

Every original request, midpoint cache, link and final handoff stays in the
same ordered product. Only the final result slot varies; it cannot rebuild
or replace the prefix caches.
-/
@[expose] def PreparationWith
    (Result : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
      (Cast.Path.ofCoordinate last.parameter) target → Type u) :=
  (_inputs : { values : Owner (value polynomial first) × Owner (value polynomial last) ×
      Owner (value polynomial last) // values = (source, moved, target) }) ×
  (selected : { result : Geometric.Search.Selection scale 0 (traceAllowance patch.rootLower) //
    result = selection patch scale scaleNonnegative }) ×
  (firstRequest : { result : OwnerTail.TraceRequest source patch.rootLower patch.rootLower_positive //
    result = OwnerTail.requestTrace source patch.rootLower patch.rootLower_positive }) ×
  (lastRequest : { result : OwnerTail.TraceRequest moved patch.rootLower patch.rootLower_positive //
    result = OwnerTail.requestTrace moved patch.rootLower patch.rootLower_positive }) ×
  (targetRequest : { result : OwnerTail.TraceRequest target patch.rootLower patch.rootLower_positive //
    result = OwnerTail.requestTrace target patch.rootLower patch.rootLower_positive }) ×
  (cached : { result : Cache patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      selected.val.stage first last first_le_last
      (selection_paid patch scale scaleNonnegative selected.val) source moved sourceRefines
      (moved_refines patch polynomial source sourceRefines nonzero moved endpointSmall movedFactory)
      firstRequest.val lastRequest.val //
    result = build patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      selected.val.stage first last first_le_last
      (selection_paid patch scale scaleNonnegative selected.val) source moved sourceRefines
      (moved_refines patch polynomial source sourceRefines nonzero moved endpointSmall movedFactory)
      firstRequest.val lastRequest.val }) ×
  (front : { result : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
      (Cast.Path.ofCoordinate last.parameter) moved //
    result = path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      selected.val.stage first last first_le_last
      (selection_paid patch scale scaleNonnegative selected.val) source moved sourceRefines
      (moved_refines patch polynomial source sourceRefines nonzero moved endpointSmall movedFactory)
      firstRequest.val lastRequest.val cached.val }) ×
  (join : { result : OwnerJoin moved target //
    result = OwnerJoin.ofTails lastRequest.val.tail targetRequest.val.tail equivalent }) ×
  (whole : { result : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
      (Cast.Path.ofCoordinate last.parameter) target //
    result = front.val.append (.cons (OwnerLink.stationary polynomial
      (Cast.Path.ofCoordinate last.parameter) join.val) (.nil (Cast.Path.ofCoordinate last.parameter) target)) }) ×
    Result whole.val

/-- The whole fine owner tree, actual stationary handoff and one realized trace of the original coarse edge.

All three input Owners remain retained data. One strict search precedes
three original endpoint tail requests and all interior construction. The
GIVEN endpoint advance is reused by its whole factory; the final handoff
uses the SAME supplied name comparison and has its own retained join.
-/
@[expose] def Preparation :=
  PreparationWith patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent
    (fun whole => { realized : OwnerPath.Realization whole 0 0 // realized = whole.realize 0 0 })

/-- Construct the original complete link prefix once, then consume that SAME whole final path once.

The dependent result runs only after the original selection, requests,
interior Owners, leaf links and stationary join have been bound. It receives
no reconstruction callback for those caches.
-/
def prepareWith
    (Result : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
      (Cast.Path.ofCoordinate last.parameter) target → Type u)
    (consume : ∀ whole, Result whole) :
    PreparationWith patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      moved target endpointSmall movedFactory equivalent Result :=
  let selected := selection patch scale scaleNonnegative
  let firstRequest := OwnerTail.requestTrace source patch.rootLower patch.rootLower_positive
  let lastRequest := OwnerTail.requestTrace moved patch.rootLower patch.rootLower_positive
  let targetRequest := OwnerTail.requestTrace target patch.rootLower patch.rootLower_positive
  let refines := moved_refines patch polynomial source sourceRefines nonzero moved endpointSmall movedFactory
  let cached := build patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    selected.stage first last first_le_last
    (selection_paid patch scale scaleNonnegative selected) source moved sourceRefines refines firstRequest lastRequest
  let front := path patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    selected.stage first last first_le_last
    (selection_paid patch scale scaleNonnegative selected) source moved sourceRefines refines
    firstRequest lastRequest cached
  let join := OwnerJoin.ofTails lastRequest.tail targetRequest.tail equivalent
  let whole := front.append (.cons (OwnerLink.stationary polynomial (Cast.Path.ofCoordinate last.parameter) join)
    (.nil (Cast.Path.ofCoordinate last.parameter) target))
  let result := consume whole
  ⟨⟨(source, moved, target), rfl⟩, ⟨selected, rfl⟩, ⟨firstRequest, rfl⟩, ⟨lastRequest, rfl⟩,
    ⟨targetRequest, rfl⟩, ⟨cached, rfl⟩, ⟨front, rfl⟩, ⟨join, rfl⟩, ⟨whole, rfl⟩, result⟩

/-- Select the genuine trace depth, build each actual interior Owner once, retain the final join, then realize once.

For depth d this performs 2^d-1 new source advances and 2^d moving-link
constructions. The original endpoint advance is an input. The final
stationary handoff has one new original raw comparison; the single original
path realization samples each ordered path vertex once. Both adjacent cell
consumers can project this SAME stored result without repeating any work.
-/
def prepare : Preparation patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent :=
  prepareWith patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent
    (fun whole => { realized : OwnerPath.Realization whole 0 0 // realized = whole.realize 0 0 })
    (fun whole => let realized := whole.realize 0 0; ⟨realized, rfl⟩)

namespace PreparationWith

variable {patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent}
    {Result : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
      (Cast.Path.ofCoordinate last.parameter) target → Type u}
    (cached : PreparationWith patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      moved target endpointSmall movedFactory equivalent Result)

/-- Read the SAME retained whole path before the dependent final result. -/
@[expose] def whole : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
    (Cast.Path.ofCoordinate last.parameter) target := cached.2.2.2.2.2.2.2.2.1.val

/-- The actual prepared path retains every fine target and its separate final stationary handoff. -/
theorem whole_vertices : cached.whole.vertices =
    (dyadicTargets cached.2.1.val.stage first last).map (fun endpoint => Cast.Path.ofCoordinate endpoint.parameter) ++
      [Cast.Path.ofCoordinate last.parameter] := by
  let refines := moved_refines patch polynomial source sourceRefines nonzero moved endpointSmall movedFactory
  have front := path_vertices patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    cached.2.1.val.stage first last first_le_last
    (selection_paid patch scale scaleNonnegative cached.2.1.val) source moved sourceRefines refines
    cached.2.2.1.val cached.2.2.2.1.val cached.2.2.2.2.2.1.val
  have sameFront := (congrArg OwnerPath.vertices cached.2.2.2.2.2.2.1.property).trans front
  have sameWhole := congrArg OwnerPath.vertices cached.2.2.2.2.2.2.2.2.1.property
  exact sameWhole.trans ((OwnerPath.append_vertices _ _).trans
    (congrArg (fun vertices => vertices ++ [Cast.Path.ofCoordinate last.parameter]) sameFront))

/-- The retained final stationary handoff makes this SAME whole path genuinely nonempty. -/
theorem nonempty : cached.whole.vertices ≠ [] := by
  intro empty
  have lengthEq := congrArg List.length (cached.whole_vertices.symm.trans empty)
  have impossible : Nat.succ
      ((dyadicTargets cached.2.1.val.stage first last).map
        (fun endpoint => Cast.Path.ofCoordinate endpoint.parameter)).length = 0 :=
    (Append.length_append _ _).symm.trans lengthEq
  exact Nat.noConfusion impossible

end PreparationWith

/-- The original whole link preparation without taking any displayed root reading. -/
@[expose] def LinkPreparation : Type :=
  PreparationWith patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent (fun _ => PUnit)

/-- Retain the original complete prefix once and stop before native reading realization. -/
def prepareLinks : LinkPreparation patch polynomial source sourceRefines nonzero scale
    scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent :=
  prepareWith patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent (fun _ => PUnit) (fun _ => PUnit.unit)

namespace LinkPreparation

variable {patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent}
    (cached : LinkPreparation patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      moved target endpointSmall movedFactory equivalent)

/-- Read the SAME entire first residual-request subtype with its original acquisition/selection factory. -/
@[expose] def firstRequest :
    { result : OwnerTail.TraceRequest source patch.rootLower patch.rootLower_positive //
      result = OwnerTail.requestTrace source patch.rootLower patch.rootLower_positive } := cached.2.2.1

/-- Read the SAME entire target residual-request subtype used by the retained final stationary handoff. -/
@[expose] def targetRequest :
    { result : OwnerTail.TraceRequest target patch.rootLower patch.rootLower_positive //
      result = OwnerTail.requestTrace target patch.rootLower patch.rootLower_positive } := cached.2.2.2.2.1

/-- Read the SAME retained path with all actual fine links and its separate final stationary handoff. -/
@[expose] def whole : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
    (Cast.Path.ofCoordinate last.parameter) target := PreparationWith.whole (cached := cached)

/-- The original fine ordered word and final stationary handoff are retained before any displayed reading. -/
theorem whole_vertices : cached.whole.vertices =
    (dyadicTargets cached.2.1.val.stage first last).map (fun endpoint => Cast.Path.ofCoordinate endpoint.parameter) ++
      [Cast.Path.ofCoordinate last.parameter] := PreparationWith.whole_vertices (cached := cached)

/-- The SAME actual link prefix is genuinely nonempty, including stationary physical intervals. -/
theorem nonempty : cached.whole.vertices ≠ [] := PreparationWith.nonempty (cached := cached)

/-- The SAME original stationary handoff cache. -/
@[expose] def join : OwnerJoin moved target := cached.2.2.2.2.2.2.2.1.val

/-- The actual final handoff has equal intrinsic tail lower targets by its two original acquisition factories. -/
theorem join_lower_eq : cached.join.leftTail.lower = cached.join.rightTail.lower := by
  have leftTail : cached.join.leftTail.lower = cached.2.2.2.1.val.tail.lower :=
    congrArg (fun value : OwnerJoin moved target => value.leftTail.lower) cached.2.2.2.2.2.2.2.1.property
  have rightTail : cached.join.rightTail.lower = cached.2.2.2.2.1.val.tail.lower :=
    congrArg (fun value : OwnerJoin moved target => value.rightTail.lower) cached.2.2.2.2.2.2.2.1.property
  have leftOriginal := congrArg (fun tail : OwnerTail moved => tail.lower) cached.2.2.2.1.val.tail_eq
  have rightOriginal := congrArg (fun tail : OwnerTail target => tail.lower) cached.2.2.2.2.1.val.tail_eq
  exact leftTail.trans (leftOriginal.trans
    ((OwnerTail.acquire_lower_eq moved target).trans (rightOriginal.symm.trans rightTail.symm)))

/-- The actual cached reverse handoff beside every reverse operation on the SAME whole path. -/
@[expose] def ReverseLinks :=
  (_swapped : { value : OwnerJoin target moved // value = cached.join.symm cached.join_lower_eq }) ×
    OwnerPath.Reversals cached.whole

/-- Reverse the retained leaf links and handoff without acquiring Owners, requests, comparisons or readings. -/
def reverseLinks : ReverseLinks cached :=
  let swapped := cached.join.symm cached.join_lower_eq
  let refines := moved_refines patch polynomial source sourceRefines nonzero moved endpointSmall movedFactory
  let front := reversals patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    cached.2.1.val.stage first last first_le_last
    (selection_paid patch scale scaleNonnegative cached.2.1.val) source moved sourceRefines refines
    cached.2.2.1.val cached.2.2.2.1.val cached.2.2.2.2.2.1.val
  let retainedFront : OwnerPath.Reversals cached.2.2.2.2.2.2.1.val :=
    Eq.mpr (congrArg OwnerPath.Reversals cached.2.2.2.2.2.2.1.property) front
  let stationary := OwnerLink.stationaryReverseData (polynomial := polynomial)
    (Cast.Path.ofCoordinate last.parameter) cached.join cached.join_lower_eq ⟨swapped, rfl⟩
  let whole := OwnerPath.Reversals.append cached.2.2.2.2.2.2.1.val
    (.cons (OwnerLink.stationary polynomial (Cast.Path.ofCoordinate last.parameter) cached.join)
      (.nil (Cast.Path.ofCoordinate last.parameter) target)) retainedFront ⟨stationary, PUnit.unit⟩
  let retainedWhole : OwnerPath.Reversals cached.whole :=
    Eq.mpr (congrArg OwnerPath.Reversals cached.2.2.2.2.2.2.2.2.1.property) whole
  ⟨⟨swapped, rfl⟩, retainedWhole⟩


variable (incoming : OwnerReading source) (outgoing : OwnerReading target)
    (firstLater : cached.whole.sourceMinimum ≤ incoming.index)
    (lastLater : cached.whole.targetMinimum ≤ outgoing.index)
    (forward : OwnerPath.Between cached.whole incoming outgoing)

/-- The retained reverse-link cache and reverse trace of one given native realization, with both whole factories. -/
@[expose] def ReverseTrace :=
  (links : { value : ReverseLinks cached // value = cached.reverseLinks }) ×
    { result : OwnerPath.ReverseResult cached.whole links.val.2 incoming outgoing forward.realization.roots //
      result = OwnerPath.reverseBetween cached.whole cached.nonempty links.val.2
        incoming outgoing firstLater lastLater forward }

/-- Reverse the given checked trace once through its retained dyadic links and complete native reading spine.

The symmetric handoff and leaf operations are bound before the reverse
trace consumes them. Both complete result factories remain coupled; no
Owner, request, comparison selector or reading is acquired.
-/
def reverseTrace : ReverseTrace cached incoming outgoing firstLater lastLater forward :=
  let links : { value : ReverseLinks cached // value = cached.reverseLinks } := ⟨cached.reverseLinks, rfl⟩
  let result := OwnerPath.reverseBetween cached.whole cached.nonempty links.val.2
    incoming outgoing firstLater lastLater forward
  ⟨links, ⟨result, rfl⟩⟩


namespace ReverseTrace

variable {incoming outgoing firstLater lastLater forward}
    (trace : ReverseTrace cached incoming outgoing firstLater lastLater forward)
    (imagePolynomial : CoefficientPolynomial) (origin direction : Canonical)
    (factory : polynomial = Substitution.Affine.composeLine imagePolynomial origin direction)

/-- The exact affine-image realization family of the given reverse cache and polynomial factory. -/
@[expose] def AffineRealization : Type :=
    OwnerPath.Realization
      ((OwnerPath.reversePath cached.whole trace.1.val.2).affineImage
        (polynomial := imagePolynomial) (pullback := polynomial) origin direction factory)
      outgoing.index incoming.index

/-- Map the given retained reverse trace through its exact affine polynomial factory.

The original checked reverse realization supplies every root and endpoint
reading. Only its base-coordinate image is constructed; the forward trace,
reverse operations and native readings are not executed again.
-/
def affineImage : AffineRealization cached trace imagePolynomial origin direction factory :=
  OwnerPath.Realization.affineImage (polynomial := imagePolynomial) (pullback := polynomial)
    (origin := origin) (direction := direction) (factory := factory) (original := trace.2.val.realization)

end ReverseTrace

end LinkPreparation

namespace Preparation

variable {patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
    moved target endpointSmall movedFactory equivalent}
    (cached : Preparation patch polynomial source sourceRefines nonzero scale scaleNonnegative variation wholeSmall
      moved target endpointSmall movedFactory equivalent)

/-- Read the SAME actual ordered path, retaining the final stationary target-owner handoff. -/
@[expose] def whole : OwnerPath polynomial (Cast.Path.ofCoordinate first.parameter) source
    (Cast.Path.ofCoordinate last.parameter) target := cached.2.2.2.2.2.2.2.2.1.val

/-- Read the SAME original path realization, with all checked edge data and ordered root values. -/
@[expose] def realized : OwnerPath.Realization cached.whole 0 0 := cached.2.2.2.2.2.2.2.2.2.val

/-- The retained whole realization has exactly one original realize call as its factory. -/
theorem realized_eq : cached.realized = cached.whole.realize 0 0 := cached.2.2.2.2.2.2.2.2.2.property

/-- The actual realized path retains every original fine target and its separate final stationary handoff. -/
theorem whole_vertices : cached.whole.vertices =
    (dyadicTargets cached.2.1.val.stage first last).map (fun endpoint => Cast.Path.ofCoordinate endpoint.parameter) ++
      [Cast.Path.ofCoordinate last.parameter] := by
  exact PreparationWith.whole_vertices (cached := cached)

end Preparation

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Dyadic

end
