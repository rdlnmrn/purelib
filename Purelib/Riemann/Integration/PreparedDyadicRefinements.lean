module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Integration.PreparedSubdivisionParentModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Riemann.Integration.PreparedSubdivisionModels
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Checked dyadic refinements of prepared edge lists

This module lifts the constructive one-parent dyadic congruence checker to a
finite list of centered prepared edges.  Every child block retains its exact
dependent owner walk, canonical parent positions, and computed seven-way root
congruence chain.
-/

namespace Purelib.Riemann.Integration.PreparedDyadicRefinements

open Purelib.Riemann.Curves.AlgebraicDifferentials

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
/-- The original square-root continuation owner at its retained radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A retained subdivision parameter with unit-interval bounds. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The original prepared continuation request. -/
abbrev StepRequest := Purelib.Riemann.Branches.PreparedSheetContinuation.StepRequest
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A prepared edge with its exact retained center state. -/
abbrev CenteredEdge {genus : Nat} (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential
/-- A compatible refinement of the original ordered constant path models. -/
abbrev CompatibleConstantPathRefinement :=
  Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel.CompatibleConstantPathRefinement

section
open Purelib
section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.RootContinuation
/-- The minimum of the seven retained clearance bounds required for one direct step comparison.

The bounds come from the parent's direct owner and the step's prepared owner, their fresh owners and bridge tails, and
the first owner's fresh common refinement. -/
def directStepClearanceFloor {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (current : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition parent
      current)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
    (request : StepRequest) : Coordinate :=
  let source := PreparedSheetContinuation.prepared parent.segment
    parent.left parent.owner parent.request
  let first :=
    PreparedSheetContinuation.Subdivision.directOwnerAt
      parent.left source current position.directMoveSmall
  let second := PreparedSheetContinuation.prepared parent.segment
    current owner request
  let nonzero := parent.segment.pointAt_eval_ne_zero current.parameter
    current.inside
  min first.track.initial.clearance.bound
    (min second.track.initial.clearance.bound
      (min (SquareRootTrackEquivalence.freshSourceClearance
          nonzero first)
        (min (SquareRootTrackEquivalence.freshSourceClearance
            nonzero second)
          (min (SquareRootTrackEquivalence.bridgeTailClearance
              nonzero first)
            (min (SquareRootTrackEquivalence.bridgeTailClearance
                nonzero second)
              (SquareRootTrackEquivalence.freshCommonClearance
                nonzero first))))))

/-- The minimum of the seven actual direct-step clearance bounds is positive. -/
theorem directStepClearanceFloor_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (current : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition parent
      current)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
    (request : StepRequest) :
    0 < directStepClearanceFloor parent current position owner request := by
  let source := PreparedSheetContinuation.prepared parent.segment
    parent.left parent.owner parent.request
  let first :=
    PreparedSheetContinuation.Subdivision.directOwnerAt
      parent.left source current position.directMoveSmall
  let second := PreparedSheetContinuation.prepared parent.segment
    current owner request
  let nonzero := parent.segment.pointAt_eval_ne_zero current.parameter
    current.inside
  change 0 < min first.track.initial.clearance.bound
    (min second.track.initial.clearance.bound
      (min (SquareRootTrackEquivalence.freshSourceClearance
          nonzero first)
        (min (SquareRootTrackEquivalence.freshSourceClearance
            nonzero second)
          (min (SquareRootTrackEquivalence.bridgeTailClearance
              nonzero first)
            (min (SquareRootTrackEquivalence.bridgeTailClearance
                nonzero second)
              (SquareRootTrackEquivalence.freshCommonClearance
                nonzero first))))))
  apply Purelib.Data.Rat.Fraction.Order.Basic.lt_min
  · exact first.track.initial.clearance.positive
  · apply Purelib.Data.Rat.Fraction.Order.Basic.lt_min
    · exact second.track.initial.clearance.positive
    · apply Purelib.Data.Rat.Fraction.Order.Basic.lt_min
      · exact (SquareRootReconditioning.freshOwner nonzero
          first).track.initial.clearance.positive
      · apply Purelib.Data.Rat.Fraction.Order.Basic.lt_min
        · exact (SquareRootReconditioning.freshOwner nonzero
            second).track.initial.clearance.positive
        · apply Purelib.Data.Rat.Fraction.Order.Basic.lt_min
          · exact (SquareRootTrackEquivalence.commonTailOfBridge
              (SquareRootReconditioning.bridge nonzero first)).initial
                |>.clearance.positive
          · apply Purelib.Data.Rat.Fraction.Order.Basic.lt_min
            · exact (SquareRootTrackEquivalence.commonTailOfBridge
                (SquareRootReconditioning.bridge nonzero second)).initial
                  |>.clearance.positive
            · exact ((SquareRootReconditioning.freshOwner
                nonzero first).refineAt 1).track.initial.clearance.positive

end

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- Variation below the retained minimum supplies every direct-step clearance inequality.

The original segment evaluation bound pays the radicand movement, then each component of the seven-way minimum supplies
its corresponding owner or bridge condition. -/
theorem directStepSmall_of_variation_lt_floor {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (current : Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition parent
      current)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
    (request : StepRequest)
    (below : ClearSheetContinuation.variationBound parent.segment
      current.parameter request.endpoint.parameter <
        directStepClearanceFloor parent current position owner request) :
    PreparedSheetContinuation.Subdivision.DirectStepSmall
      parent.segment parent.left
        (PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request)
        current position.directMoveSmall owner request := by
  let source := PreparedSheetContinuation.prepared parent.segment
    parent.left parent.owner parent.request
  let first :=
    PreparedSheetContinuation.Subdivision.directOwnerAt
      parent.left source current position.directMoveSmall
  let second := PreparedSheetContinuation.prepared parent.segment
    current owner request
  let nonzero := parent.segment.pointAt_eval_ne_zero current.parameter
    current.inside
  let firstFresh :=
    SquareRootTrackEquivalence.freshSourceClearance nonzero first
  let secondFresh :=
    SquareRootTrackEquivalence.freshSourceClearance nonzero second
  let firstBridge :=
    SquareRootTrackEquivalence.bridgeTailClearance nonzero first
  let secondBridge :=
    SquareRootTrackEquivalence.bridgeTailClearance nonzero second
  let freshCommon :=
    SquareRootTrackEquivalence.freshCommonClearance nonzero first
  let sixth := min secondBridge freshCommon
  let fifth := min firstBridge sixth
  let fourth := min secondFresh fifth
  let third := min firstFresh fourth
  let secondTail := min second.track.initial.clearance.bound third
  let floor := min first.track.initial.clearance.bound secondTail
  have floor_eq : directStepClearanceFloor parent current position owner
      request = floor := rfl
  have distance : Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval (parent.segment.pointAt current.parameter) -
        curve.polynomial.eval
          (parent.segment.pointAt request.endpoint.parameter)) < floor := by
    rw [← floor_eq]
    exact (ClearSheetContinuation.evaluation_variation_le
      parent.segment parent.within current.parameter
        request.endpoint.parameter current.inside
          request.endpoint.inside).trans_lt below
  have firstLe : floor <= first.track.initial.clearance.bound :=
    Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have secondLe : floor <= second.track.initial.clearance.bound :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _
      _)
  have firstFreshLe : floor <= firstFresh :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right
      _ _).trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _))
  have secondFreshLe : floor <= secondFresh :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right
      _ _).trans
      ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left
        _ _)))
  have firstBridgeLe : floor <= firstBridge :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right
      _ _).trans
      ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
        (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _))))
  have secondBridgeLe : floor <= secondBridge :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right
      _ _).trans
      ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
          (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _)))))
  have freshCommonLe : floor <= freshCommon :=
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right
      _ _).trans
      ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
          (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _)))))
  exact
    ⟨{ firstSmall := by simpa only [Norm.Basic.normSq_eq_canonical] using distance.trans_le firstLe
       secondSmall := by simpa only [Norm.Basic.normSq_eq_canonical] using distance.trans_le secondLe
       firstFresh := by simpa only [Norm.Basic.normSq_eq_canonical] using distance.trans_le firstFreshLe
       secondFresh := by simpa only [Norm.Basic.normSq_eq_canonical] using distance.trans_le secondFreshLe
       firstBridge := by simpa only [Norm.Basic.normSq_eq_canonical] using distance.trans_le firstBridgeLe
       secondBridge := by simpa only [Norm.Basic.normSq_eq_canonical] using distance.trans_le secondBridgeLe
       freshCommon := by simpa only [Norm.Basic.normSq_eq_canonical] using distance.trans_le freshCommonLe }⟩

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
/-- Every original subdivision step varies by less than its retained direct-step clearance floor.

The dependent safety proposition follows the exact parent positions, original owners, requests and caches. -/
inductive ParentCongruenceSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivisionModelCore.PreparedSubdivision
      parent.segment parent.within current owner) ->
    PreparedSubdivisionParentModels.ParentPositions parent subdivision ->
      Prop
  /-- The terminal subdivision has no remaining step condition. -/ | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (position : PreparedSubdivisionModelCore.ParentPosition parent
        current) :
      ParentCongruenceSafe parent current owner (.stop current owner)
        (.stop current owner position)
  /-- Retain the variation bound below the exact direct-step floor at this original parent position and the safe tail.
  -/
  | next
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (request : StepRequest)
      (cached : PreparedSheetContinuation.CachedSource
        parent.segment current owner request)
      (ordered : current.parameter <= request.endpoint.parameter)
      (small : ClearSheetContinuation.variationBound
        parent.segment current.parameter request.endpoint.parameter <
          (PreparedSheetContinuation.prepared parent.segment
            current owner request).track.initial.clearance.bound)
      (remaining : PreparedSubdivisionModelCore.PreparedSubdivision
        parent.segment parent.within request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (position : PreparedSubdivisionModelCore.ParentPosition parent
        current)
      (remainingPositions :
        PreparedSubdivisionParentModels.ParentPositions parent remaining)
      (below : ClearSheetContinuation.variationBound parent.segment
        current.parameter request.endpoint.parameter <
          directStepClearanceFloor parent current position owner request)
      (tail : ParentCongruenceSafe parent request.endpoint
        (PreparedSheetContinuation.advance parent.segment
          parent.within current owner request small)
        remaining remainingPositions) :
      ParentCongruenceSafe parent current owner
        (.next current owner request cached ordered small remaining)
        (.next current owner request cached ordered small remaining position
          remainingPositions)

/-- The finite minimum of the original steps' direct-comparison clearance floors, with terminal value one. -/
def parentCongruenceFloor {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivisionModelCore.PreparedSubdivision
      parent.segment parent.within current owner) ->
    PreparedSubdivisionParentModels.ParentPositions parent subdivision ->
      Coordinate
  | _current, _owner, .stop _ _, .stop _ _ _position => 1
  | current, owner, .next _ _ request _cached _ordered _small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions =>
      min (directStepClearanceFloor parent current position owner request)
        (parentCongruenceFloor parent request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request _small)
          remaining remainingPositions)

/-- The retained subdivision's finite congruence clearance floor is positive. -/
theorem parentCongruenceFloor_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) :
    forall (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (subdivision : PreparedSubdivisionModelCore.PreparedSubdivision
        parent.segment parent.within current owner)
      (positions : PreparedSubdivisionParentModels.ParentPositions parent
        subdivision),
      0 < parentCongruenceFloor parent current owner subdivision positions
  | _current, _owner, .stop _ _, .stop _ _ _position => by
      change (0 : Coordinate) < 1
      decide
  | current, owner, .next _ _ request _cached _ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions =>
      Purelib.Data.Rat.Fraction.Order.Basic.lt_min (directStepClearanceFloor_positive parent current position owner
        request)
        (parentCongruenceFloor_positive parent request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small)
          remaining remainingPositions)

/-- One bound on the variation of every original subdivision step.

The dependent proposition retains the original ordered requests and owners; the terminal subdivision contributes no
variation condition. -/
inductive ParentSubdivisionVariationBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) (bound : Coordinate) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    PreparedSubdivisionModelCore.PreparedSubdivision parent.segment
      parent.within current owner -> Prop
  /-- The terminal subdivision has no remaining step condition. -/ | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter))) :
      ParentSubdivisionVariationBound parent bound current owner
        (.stop current owner)
  /-- Retain the current original step's variation bound and the same bound for the remaining subdivision. -/ | next
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (request : StepRequest)
      (cached : PreparedSheetContinuation.CachedSource
        parent.segment current owner request)
      (ordered : current.parameter <= request.endpoint.parameter)
      (small : ClearSheetContinuation.variationBound
        parent.segment current.parameter request.endpoint.parameter <
          (PreparedSheetContinuation.prepared parent.segment
            current owner request).track.initial.clearance.bound)
      (remaining : PreparedSubdivisionModelCore.PreparedSubdivision
        parent.segment parent.within request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (head : ClearSheetContinuation.variationBound parent.segment
        current.parameter request.endpoint.parameter <= bound)
      (tail : ParentSubdivisionVariationBound parent bound request.endpoint
        (PreparedSheetContinuation.advance parent.segment
          parent.within current owner request small) remaining) :
      ParentSubdivisionVariationBound parent bound current owner
        (.next current owner request cached ordered small remaining)

/-- A uniform step-variation bound below the retained finite floor certifies every direct comparison. -/
theorem parentCongruenceSafe_of_bound_lt_floor {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) (bound : Coordinate) :
    forall (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (subdivision : PreparedSubdivisionModelCore.PreparedSubdivision
        parent.segment parent.within current owner)
      (positions : PreparedSubdivisionParentModels.ParentPositions parent
        subdivision),
      ParentSubdivisionVariationBound parent bound current owner subdivision ->
      bound < parentCongruenceFloor parent current owner subdivision positions ->
        ParentCongruenceSafe parent current owner subdivision positions
  | current, owner, .stop _ _, .stop _ _ position, .stop _ _, _below =>
      .stop current owner position
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions,
      .next _ _ _ _ _ _ _ head tail, below => by
      apply ParentCongruenceSafe.next current owner request cached ordered small
        remaining position remainingPositions
      · exact head.trans_lt (below.trans_le (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _))
      · exact parentCongruenceSafe_of_bound_lt_floor parent bound
          request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small)
          remaining remainingPositions tail
            (below.trans_le (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _))

/-- Transfer the original request-edge variation bounds to the subdivision constructed from fresh-mesh safety.

The result retains the exact requested endpoint list and the canonical caches produced by the original builder. -/
theorem parentSubdivisionVariationBound_ofFreshMeshSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) (bound : Coordinate) :
    forall (current : Endpoint)
      (prior : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (requests : List StepRequest)
      (safe : PreparedSheetContinuation.FreshMeshSafe
        parent.segment current requests),
      ClearSheetContinuation.Subdivision.EdgeVariationBound
        parent.segment bound current
          (PreparedSheetContinuation.Subdivision.requestEndpoints
            requests) ->
      ParentSubdivisionVariationBound parent bound current
        prior
        (PreparedSheetContinuation.Subdivision.ofFreshMeshSafe
          parent.segment parent.within current prior requests safe)
  | current, prior, [], _safe, _edges => .stop current prior
  | current, prior, request :: remaining, safe, edges => by
      let small : ClearSheetContinuation.variationBound
          parent.segment current.parameter request.endpoint.parameter <
          (PreparedSheetContinuation.prepared parent.segment
            current prior request).track.initial.clearance.bound :=
        safe.2.1.trans_le
          (PreparedSheetContinuation.canonicalPredictedClearanceFloor_le_prepared
            parent.segment current prior request)
      apply ParentSubdivisionVariationBound.next current prior request
        (PreparedSheetContinuation.CachedSource.canonical
          parent.segment current prior request) safe.1 small
      · exact edges.2.1
      · exact parentSubdivisionVariationBound_ofFreshMeshSafe parent bound
          request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current prior request small)
          remaining safe.2.2 edges.2.2

/-- Transfer the original request-edge variation bounds to the subdivision constructed from mesh safety. -/
theorem parentSubdivisionVariationBound_ofMeshSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) (bound : Coordinate)
    (current : Endpoint)
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) :
    forall (requests : List StepRequest)
      (safe : PreparedSheetContinuation.MeshSafe parent.segment
        current owner requests),
      ClearSheetContinuation.Subdivision.EdgeVariationBound
        parent.segment bound current
          (PreparedSheetContinuation.Subdivision.requestEndpoints
            requests) ->
      ParentSubdivisionVariationBound parent bound current owner
        (PreparedSheetContinuation.Subdivision.ofMeshSafe
          parent.segment parent.within current owner requests safe)
  | [], _safe, _edges => .stop current owner
  | request :: remaining, safe, edges => by
      apply ParentSubdivisionVariationBound.next current owner request
        (PreparedSheetContinuation.CachedSource.canonical
          parent.segment current owner request) safe.1 safe.2.1
      · exact edges.2.1
      · exact parentSubdivisionVariationBound_ofFreshMeshSafe parent bound
          request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request safe.2.1)
          remaining safe.2.2 edges.2.2

end

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- The parent segment's variation bound scaled by the geometric quarter-radius at the requested dyadic depth. -/
def parentDyadicVariationBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) (depth : Nat) : Coordinate :=
  Geometric.Basic.quarterRadius
    (ClearSheetContinuation.variationBound parent.segment
      parent.left.parameter parent.request.endpoint.parameter) depth

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
/-- The retained finite direct-comparison floor of the exact safe parent dyadic subdivision. -/
def parentDyadicCongruenceFloor {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) : Coordinate :=
  parentCongruenceFloor parent parent.left parent.owner
    (PreparedSubdivisionParentModels.parentDyadicSubdivision parent depth
      rootDiameter rootDiameterPositive safe)
    (PreparedSubdivisionParentModels.parentDyadicPositions parent proper
      depth rootDiameter rootDiameterPositive safe)

/-- The direct-comparison floor of the retained safe dyadic subdivision is positive. -/
theorem parentDyadicCongruenceFloor_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) :
    0 < parentDyadicCongruenceFloor parent proper depth rootDiameter
      rootDiameterPositive safe :=
  parentCongruenceFloor_positive parent parent.left parent.owner
    (PreparedSubdivisionParentModels.parentDyadicSubdivision parent depth
      rootDiameter rootDiameterPositive safe)
    (PreparedSubdivisionParentModels.parentDyadicPositions parent proper
      depth rootDiameter rootDiameterPositive safe)

/-- Every actual dyadic step meets the parent's geometric quarter-radius variation bound. -/
theorem parentDyadicSubdivisionVariationBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) :
    ParentSubdivisionVariationBound parent
      (parentDyadicVariationBound parent depth) parent.left parent.owner
      (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe) := by
  apply parentSubdivisionVariationBound_ofMeshSafe parent
    (parentDyadicVariationBound parent depth) parent.left parent.owner
    (PreparedSheetContinuation.Subdivision.dyadicRequests depth
      parent.left parent.request.endpoint rootDiameter rootDiameterPositive)
    safe
  simpa only [
    PreparedSheetContinuation.Subdivision.requestEndpoints_dyadicRequests,
    parentDyadicVariationBound]
    using
      (ClearSheetContinuation.Subdivision.dyadicTargets_edgeVariationBound
        parent.segment depth parent.left parent.request.endpoint parent.ordered)

/-- The safe dyadic subdivision is comparison-safe when its variation bound lies below its retained floor. -/
theorem parentDyadicCongruenceSafe_of_bound_lt_floor {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (below : parentDyadicVariationBound parent depth <
      parentDyadicCongruenceFloor parent proper depth rootDiameter
        rootDiameterPositive safe) :
    ParentCongruenceSafe parent parent.left parent.owner
      (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (PreparedSubdivisionParentModels.parentDyadicPositions parent proper
        depth rootDiameter rootDiameterPositive safe) :=
  parentCongruenceSafe_of_bound_lt_floor parent
    (parentDyadicVariationBound parent depth) parent.left parent.owner
      (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (PreparedSubdivisionParentModels.parentDyadicPositions parent proper
        depth rootDiameter rootDiameterPositive safe)
      (parentDyadicSubdivisionVariationBound parent depth rootDiameter
        rootDiameterPositive safe) below

/-- Decide whether the dyadic variation bound is below the exact retained comparison floor. -/
def parentDyadicCongruenceBoundAccepted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive) : Bool :=
  decide (parentDyadicVariationBound parent depth <
    parentDyadicCongruenceFloor parent proper depth rootDiameter
      rootDiameterPositive safe)

/-- Acceptance of the exact scalar comparison supplies safety for every original dyadic step. -/
theorem parentDyadicCongruenceSafe_of_accepted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (accepted : parentDyadicCongruenceBoundAccepted parent proper depth
      rootDiameter rootDiameterPositive safe = true) :
    ParentCongruenceSafe parent parent.left parent.owner
      (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (PreparedSubdivisionParentModels.parentDyadicPositions parent proper
        depth rootDiameter rootDiameterPositive safe) :=
  parentDyadicCongruenceSafe_of_bound_lt_floor parent proper depth rootDiameter
    rootDiameterPositive safe (of_decide_eq_true accepted)

/-- Add the requested offset to the parent's sufficient dyadic depth for the given root-diameter target. -/
def parentCandidateDepth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) (rootDiameter : Coordinate) (offset : Nat) : Nat :=
  PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
    parent.segment parent.left parent.request.endpoint rootDiameter + offset

/-- Every nonnegative offset from the sufficient depth retains mesh safety for the positive diameter target. -/
theorem parentCandidateMeshSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (offset : Nat) :
    PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner
        (parentCandidateDepth parent rootDiameter offset) rootDiameter
          rootDiameterPositive :=
  PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le
    parent.segment parent.left parent.request.endpoint parent.owner
      (parentCandidateDepth parent rootDiameter offset) rootDiameter
        rootDiameterPositive parent.ordered
          (Nat.le_add_right _ offset)

end

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Test the retained comparison bound at the exact offset candidate depth. -/
def parentCandidateAccepted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (offset : Nat) : Bool :=
  parentDyadicCongruenceBoundAccepted parent proper
    (parentCandidateDepth parent rootDiameter offset) rootDiameter
      rootDiameterPositive
        (parentCandidateMeshSafe parent rootDiameter rootDiameterPositive
          offset)

open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
/-- Comparison safety guarantees success of the original dependent direct-step checker.

Each retained variation inequality supplies the exact direct-step predicate tested by the checker, and the recursive
safety witness supplies success of the original tail. -/
theorem tryParentStepSmalls_isSome_of_congruenceSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential) :
    forall (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (subdivision : PreparedSubdivisionModelCore.PreparedSubdivision
        parent.segment parent.within current owner)
      (positions : PreparedSubdivisionParentModels.ParentPositions parent
        subdivision),
      ParentCongruenceSafe parent current owner subdivision positions ->
        (PreparedSubdivisionParentModels.tryParentStepSmalls parent
          current owner subdivision positions).isSome = true
  | current, owner, .stop _ _, .stop _ _ position, .stop _ _ _ => rfl
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions,
      .next _ _ _ _ _ _ _ _ _ below tail => by
      let stepSmall := directStepSmall_of_variation_lt_floor parent current
        position owner request below
      have tailAccepted := tryParentStepSmalls_isSome_of_congruenceSafe parent
        request.endpoint
        (PreparedSheetContinuation.advance parent.segment
          parent.within current owner request small)
        remaining remainingPositions tail
      cases checkedTail :
          PreparedSubdivisionParentModels.tryParentStepSmalls parent
            request.endpoint
            (PreparedSheetContinuation.advance parent.segment
              parent.within current owner request small)
            remaining remainingPositions with
      | none =>
          simp only [checkedTail, Option.isSome, -eq_self, -iff_self] at tailAccepted
          cases tailAccepted
      | some checked =>
          simp only [PreparedSubdivisionParentModels.tryParentStepSmalls,
            dif_pos stepSmall, checkedTail, Option.isSome, -eq_self, -iff_self]
          rfl

/-- Comparison safety guarantees that the original dyadic checker returns its certificate. -/
theorem tryCheckedParentDyadic_isSome_of_congruenceSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (congruenceSafe : ParentCongruenceSafe parent parent.left parent.owner
      (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (PreparedSubdivisionParentModels.parentDyadicPositions parent
        proper depth rootDiameter rootDiameterPositive safe)) :
    (PreparedSubdivisionParentModels.tryCheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe).isSome = true := by
  have accepted := tryParentStepSmalls_isSome_of_congruenceSafe parent
    parent.left parent.owner
    (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
      depth rootDiameter rootDiameterPositive safe)
    (PreparedSubdivisionParentModels.parentDyadicPositions parent
      proper depth rootDiameter rootDiameterPositive safe) congruenceSafe
  cases checkedSteps :
      PreparedSubdivisionParentModels.tryParentStepSmalls parent
        parent.left parent.owner
        (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
          depth rootDiameter rootDiameterPositive safe)
        (PreparedSubdivisionParentModels.parentDyadicPositions parent
          proper depth rootDiameter rootDiameterPositive safe) with
  | none =>
      simp only [checkedSteps, Option.isSome, -eq_self, -iff_self] at accepted
      cases accepted
  | some stepSmalls =>
      simp only [PreparedSubdivisionParentModels.tryCheckedParentDyadic,
        checkedSteps, Option.isSome, -eq_self, -iff_self]
      rfl

/-- Extract the original dyadic checker's certificate using the proof that it succeeds.

The construction reads the actual checked result and preserves its exact depth, diameter, mesh safety and
parent-position indices. -/
def checkedParentDyadicOfCongruenceSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (congruenceSafe : ParentCongruenceSafe parent parent.left parent.owner
      (PreparedSubdivisionParentModels.parentDyadicSubdivision parent
        depth rootDiameter rootDiameterPositive safe)
      (PreparedSubdivisionParentModels.parentDyadicPositions parent
        proper depth rootDiameter rootDiameterPositive safe)) :
    PreparedSubdivisionParentModels.CheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe :=
  let checked :=
    PreparedSubdivisionParentModels.tryCheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe
  checked.get (tryCheckedParentDyadic_isSome_of_congruenceSafe parent proper
    depth rootDiameter rootDiameterPositive safe congruenceSafe)

/-- Extract the original dyadic certificate from acceptance of its exact variation-versus-floor test. -/
def checkedParentDyadicOfBoundAccepted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.segment parent.left parent.request.endpoint parent.owner depth
          rootDiameter rootDiameterPositive)
    (accepted : parentDyadicCongruenceBoundAccepted parent proper depth
      rootDiameter rootDiameterPositive safe = true) :
    PreparedSubdivisionParentModels.CheckedParentDyadic parent proper
      depth rootDiameter rootDiameterPositive safe :=
  checkedParentDyadicOfCongruenceSafe parent proper depth rootDiameter
    rootDiameterPositive safe
      (parentDyadicCongruenceSafe_of_accepted parent proper depth rootDiameter
        rootDiameterPositive safe accepted)

end

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- An actual offset candidate together with acceptance of its retained dyadic comparison test.

The parent, strict endpoint ordering and positive root-diameter target remain indices of the certificate. -/
structure CheckedParentCandidate {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) where
  /-- The actual offset beyond the parent's sufficient dyadic depth. -/ offset : Nat
  /-- The exact candidate comparison test returns true at the retained offset. -/ accepted : parentCandidateAccepted
    parent proper rootDiameter
    rootDiameterPositive offset = true

constructive_injectivity CheckedParentCandidate

namespace CheckedParentCandidate

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- The actual sufficient depth plus the retained candidate offset. -/
def depth {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {rootDiameter : Coordinate} {rootDiameterPositive : 0 < rootDiameter}
    (candidate : CheckedParentCandidate parent proper rootDiameter
      rootDiameterPositive) : Nat :=
  parentCandidateDepth parent rootDiameter candidate.offset

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- The retained candidate depth satisfies the original dyadic mesh-safety predicate. -/
theorem meshSafe {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {rootDiameter : Coordinate} {rootDiameterPositive : 0 < rootDiameter}
    (candidate : CheckedParentCandidate parent proper rootDiameter
      rootDiameterPositive) :
    PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner
        candidate.depth rootDiameter rootDiameterPositive :=
  parentCandidateMeshSafe parent rootDiameter rootDiameterPositive
    candidate.offset

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Recover the original dyadic step certificate at the candidate's retained depth and mesh-safety proof. -/
def toCheckedParentDyadic {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {rootDiameter : Coordinate} {rootDiameterPositive : 0 < rootDiameter}
    (candidate : CheckedParentCandidate parent proper rootDiameter
      rootDiameterPositive) :
    PreparedSubdivisionParentModels.CheckedParentDyadic parent proper
      candidate.depth rootDiameter rootDiameterPositive candidate.meshSafe :=
  checkedParentDyadicOfBoundAccepted parent proper candidate.depth rootDiameter
    rootDiameterPositive candidate.meshSafe candidate.accepted

end CheckedParentCandidate

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Integration
/-- Search candidate offsets from zero through the supplied fuel, retaining the first accepted result.

Each candidate uses the same original parent and positive diameter target. `none` means this finite offset search
returned no certificate. -/
def tryCheckedParentCandidateUpTo {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (fuel : Nat) -> Option
      (CheckedParentCandidate parent proper rootDiameter rootDiameterPositive)
  | 0 =>
      if accepted : parentCandidateAccepted parent proper rootDiameter
          rootDiameterPositive 0 = true then
        some ⟨0, accepted⟩
      else none
  | fuel + 1 =>
      match tryCheckedParentCandidateUpTo parent proper rootDiameter
          rootDiameterPositive fuel with
      | some candidate => some candidate
      | none =>
          if accepted : parentCandidateAccepted parent proper rootDiameter
              rootDiameterPositive (fuel + 1) = true then
            some ⟨fuel + 1, accepted⟩
          else none

/-- The finite candidate search succeeds whenever its final permitted offset is accepted. -/
theorem tryCheckedParentCandidateUpTo_isSome_of_lastAccepted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedSubdivisionModelCore.PreparedEdge curve
      differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    forall fuel : Nat,
      parentCandidateAccepted parent proper rootDiameter rootDiameterPositive
          fuel = true ->
        (tryCheckedParentCandidateUpTo parent proper rootDiameter
          rootDiameterPositive fuel).isSome = true
  | 0, accepted => by
      simp only [tryCheckedParentCandidateUpTo, dif_pos accepted,
        Option.isSome, -eq_self, -iff_self]
      rfl
  | fuel + 1, accepted => by
      cases earlier : tryCheckedParentCandidateUpTo parent proper rootDiameter
          rootDiameterPositive fuel with
      | none =>
          simp only [tryCheckedParentCandidateUpTo, earlier,
            dif_pos accepted, Option.isSome, -eq_self, -iff_self]
          rfl
      | some candidate =>
          simp only [tryCheckedParentCandidateUpTo, earlier, Option.isSome, -eq_self, -iff_self]
          rfl

end

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Read the exact centered children of the retained safe parent dyadic subdivision.

The supplied center family is indexed by that original subdivision and remains attached to its actual cached steps. -/
def childEdges {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe :
      PreparedSheetContinuation.Subdivision.DyadicMeshSafe
        parent.edge.segment parent.edge.left parent.edge.request.endpoint
          parent.edge.owner depth rootDiameter rootDiameterPositive)
    (centers : PreparedSubdivisionModelCore.CenterStates curve
      differential parent.edge.sheet
      (PreparedSubdivisionParentModels.parentDyadicSubdivision
        parent.edge depth rootDiameter rootDiameterPositive safe)) :
    List (CenteredEdge curve differential) :=
  PreparedSubdivisionModelCore.centeredEdges curve differential
    parent.edge.sheet
      (PreparedSubdivisionParentModels.parentDyadicSubdivision
        parent.edge depth rootDiameter rootDiameterPositive safe) centers

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- A list refinement retaining each parent's checked dyadic subdivision and exact child centers.

Each constructor records the parent, depth, diameter, safety and direct-step certificate before appending its actual
child edges to the remaining refinement. -/
inductive CheckedRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    List (CenteredEdge curve differential) ->
      List (CenteredEdge curve differential) -> Type
  /-- The empty checked refinement between empty edge lists. -/ | nil : CheckedRefinement [] []
  /-- Retain the original parent, checked depth and diameter, actual child centers and remaining refinement. -/ | cons
      (parent : CenteredEdge curve differential)
      (proper : parent.edge.left.parameter <
        parent.edge.request.endpoint.parameter)
      (depth : Nat) (rootDiameter : Coordinate)
      (rootDiameterPositive : 0 < rootDiameter)
      (safe :
        PreparedSheetContinuation.Subdivision.DyadicMeshSafe
          parent.edge.segment parent.edge.left parent.edge.request.endpoint
            parent.edge.owner depth rootDiameter rootDiameterPositive)
      (checked : PreparedSubdivisionParentModels.CheckedParentDyadic
        parent.edge proper depth rootDiameter rootDiameterPositive safe)
      (centers : PreparedSubdivisionModelCore.CenterStates curve
        differential parent.edge.sheet
        (PreparedSubdivisionParentModels.parentDyadicSubdivision
          parent.edge depth rootDiameter rootDiameterPositive safe))
      {parents children : List (CenteredEdge curve differential)}
      (remaining : CheckedRefinement parents children) :
      CheckedRefinement (parent :: parents)
        (childEdges parent depth rootDiameter rootDiameterPositive safe centers ++
          children)

constructive_injectivity CheckedRefinement

namespace CheckedRefinement

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
set_option backward.match.sparseCases false in
/-- Transfer checked dyadic blocks to root-comparison refinements with their exact displacement equations. -/
def toCenteredEdgeRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents children : List (CenteredEdge curve differential)},
      CheckedRefinement parents children ->
        PreparedSubdivisionModelCore.CenteredEdgeRefinement
          parents children
  | _, _, .nil => .nil
  | _, _, .cons parent proper depth rootDiameter rootDiameterPositive safe
      checked centers remaining =>
      .cons parent
        (PreparedSubdivisionParentModels.rootChildBlockOfParentStepSmalls
          parent
          (PreparedSubdivisionParentModels.parentDyadicSubdivision
            parent.edge depth rootDiameter rootDiameterPositive safe)
          (PreparedSubdivisionParentModels.parentDyadicPositions
            parent.edge proper depth rootDiameter rootDiameterPositive safe)
          checked.stepSmalls centers)
        (PreparedSubdivisionModelCore.centeredEdges_displacement_eq_parent
          parent
          (PreparedSubdivisionParentModels.parentDyadicSubdivision
            parent.edge depth rootDiameter rootDiameterPositive safe)
          centers
          (PreparedSubdivisionParentModels.parentDyadicSubdivision_endpoint_eq
            parent.edge depth rootDiameter rootDiameterPositive safe))
        (toCenteredEdgeRefinement remaining)

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Transfer the retained checked refinement to compatible constant models of the same ordered edges. -/
def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parents children : List (CenteredEdge curve differential)}
    (refinement : CheckedRefinement parents children) :
    CompatibleConstantPathRefinement
      (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
      (children.map PreparedSubdivisionModelCore.CenteredEdge.model) :=
  refinement.toCenteredEdgeRefinement.toCompatible

end CheckedRefinement

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Every original centered parent has strictly ordered endpoint parameters. -/
def AllParentsProper {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    List (CenteredEdge curve differential) -> Prop
  | [] => True
  | parent :: remaining =>
      parent.edge.left.parameter < parent.edge.request.endpoint.parameter /\
        AllParentsProper remaining

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Read the accepted candidate's exact dyadic child edges with their canonical center family. -/
def candidateChildEdges {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (candidate : CheckedParentCandidate parent.edge proper rootDiameter
      rootDiameterPositive) : List (CenteredEdge curve differential) :=
  childEdges parent candidate.depth rootDiameter rootDiameterPositive
    candidate.meshSafe
    (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve
      differential parent.edge.sheet
      (PreparedSubdivisionParentModels.parentDyadicSubdivision
        parent.edge candidate.depth rootDiameter rootDiameterPositive
          candidate.meshSafe))

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Actual child edges with a checked dyadic refinement from the original parent list.

The result retains the ordered children and the certificate relating those exact children to the input parents. -/
structure CheckedRefinementResult {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parents : List (CenteredEdge curve differential)) where
  /-- The actual ordered child edges returned by the finite refinement construction. -/ children : List (CenteredEdge
    curve differential)
  /-- The checked dyadic refinement from the original parents to these exact child edges. -/ refinement :
    CheckedRefinement parents children

constructive_injectivity CheckedRefinementResult

namespace CheckedRefinementResult

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Transfer the retained checked refinement to compatible constant models of the same ordered edges. -/
def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    (result : CheckedRefinementResult parents) :
    CompatibleConstantPathRefinement
      (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
      (result.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model) :=
  result.refinement.toCompatible

end CheckedRefinementResult

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Attempt checked dyadic refinement of every original parent within the supplied offset-search fuel.

Success retains each accepted depth and its canonical child centers, concatenated in parent order. `none` is the
unsuccessful result of one of these finite checks. -/
def tryCheckedRefinementUpTo {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (fuel : Nat) :
    (parents : List (CenteredEdge curve differential)) ->
    AllParentsProper parents -> Option (CheckedRefinementResult parents)
  | [], _proper => some ⟨[], .nil⟩
  | parent :: remaining, proper =>
      match tryCheckedParentCandidateUpTo parent.edge proper.1 rootDiameter
          rootDiameterPositive fuel with
      | none => none
      | some candidate =>
          match tryCheckedRefinementUpTo rootDiameter rootDiameterPositive fuel
              remaining proper.2 with
          | none => none
          | some tail =>
              let centers :=
                PreparedSubdivisionAutomaticModels.canonicalCenterStates
                  curve differential parent.edge.sheet
                  (PreparedSubdivisionParentModels.parentDyadicSubdivision
                    parent.edge candidate.depth rootDiameter
                      rootDiameterPositive candidate.meshSafe)
              some
                { children := candidateChildEdges parent proper.1 rootDiameter
                    rootDiameterPositive candidate ++ tail.children
                  refinement :=
                    .cons parent proper.1 candidate.depth rootDiameter
                      rootDiameterPositive candidate.meshSafe
                      candidate.toCheckedParentDyadic centers tail.refinement }

end Purelib.Riemann.Integration.PreparedDyadicRefinements
