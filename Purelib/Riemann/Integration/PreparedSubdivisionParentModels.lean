module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.List.Append
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.RootIsolation.Track.Basic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Parent-refinement models for prepared subdivisions

Finite position, smallness, and direct-coherence certificates for refining one
prepared parent edge.  This layer is independent of automatic centre and
boundary-witness synthesis, allowing the two elaboration-heavy developments to
compile in parallel.
-/

namespace Purelib.Riemann.Integration.PreparedSubdivisionParentModels

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
/-- Parent-edge query positions for every source and terminal endpoint of the original subdivision.

Each retained fraction has unit-interval bounds and its exact affine parameter equation. The dependent constructors
preserve the actual requests, caches and successive owners. -/
inductive ParentPositions {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential) :
    {current : Endpoint} ->
      {owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter))} ->
      PreparedSubdivision parent.segment parent.within current owner -> Type
  /-- Retain the terminal endpoint, original owner and exact parent query position. -/ | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (position : ParentPosition parent current) :
      ParentPositions parent (.stop current owner)
  /-- Retain the current step's original request, cache, order and clearance evidence with its position and certified
    tail. -/ | next
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
      (remaining : PreparedSubdivision parent.segment parent.within
        request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (head : ParentPosition parent current)
      (tail : ParentPositions parent remaining) :
      ParentPositions parent
        (.next current owner request cached ordered small remaining)

constructive_injectivity ParentPositions

namespace ParentPositions

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Read the retained parent position of the subdivision's current endpoint. -/
def currentPosition {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {current : Endpoint}
    {owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))}
    {subdivision : PreparedSubdivision parent.segment parent.within current
      owner} (positions : ParentPositions parent subdivision) :
    ParentPosition parent current :=
  match positions with
  | .stop _ _ position => position
  | .next _ _ _ _ _ _ _ head _ => head

end ParentPositions

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original subdivision's ordered steps place its terminal parameter after its starting parameter. -/
theorem subdivision_start_le_endpoint
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : PreparedSubdivisionModelCore.Box}
    {start finish : PreparedSubdivisionModelCore.Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))} :
    forall (subdivision : PreparedSubdivision segment within current owner),
      current.parameter <= subdivision.endpoint.parameter
  | .stop _ _ => le_refl _
  | .next _current _owner _request _cached ordered _small remaining =>
      ordered.trans (subdivision_start_le_endpoint remaining)

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
/-- Construct parent query positions for a subdivision contained between a strictly ordered parent's endpoints.

The supplied starting lower bound and terminal upper bound propagate through the original ordered requests. Every
fraction is computed from that endpoint's actual offset and the parent width. -/
def parentPositionsOfBounds {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) ->
    parent.left.parameter <= current.parameter ->
    subdivision.endpoint.parameter <= parent.request.endpoint.parameter ->
      ParentPositions parent subdivision
  | current, owner, .stop _ _, lower, upper =>
      .stop current owner (ParentPosition.ofBetween proper ⟨lower, upper⟩)
  | current, owner, .next _ _ request cached ordered small remaining, lower,
      upper =>
      let currentUpper :=
        (ordered.trans (subdivision_start_le_endpoint remaining)).trans upper
      .next current owner request cached ordered small remaining
        (ParentPosition.ofBetween proper ⟨lower, currentUpper⟩)
        (parentPositionsOfBounds parent proper request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small)
          remaining (lower.trans ordered) upper)

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Construct all parent positions when the subdivision has the same starting owner and terminal parameter as the
parent. -/
def parentPositionsOfEndpointEq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (subdivision : PreparedSubdivision parent.segment parent.within
      parent.left parent.owner)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.request.endpoint.parameter) : ParentPositions parent subdivision :=
  parentPositionsOfBounds parent proper parent.left parent.owner subdivision
    (le_refl _) (by rw [endpoint_eq])

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
/-- Direct-step clearance certificates at the exact retained parent positions.

The dependent list preserves each original request, cache and owner, together with the direct-move evidence of its
associated position. -/
inductive ParentStepSmalls {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential) :
    {current : Endpoint} ->
      {owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter))} ->
      {subdivision : PreparedSubdivision parent.segment parent.within current
        owner} -> ParentPositions parent subdivision -> Type
  /-- The terminal parent position requires no further direct-step certificate. -/ | stop
      (current : Endpoint)
      (owner : Owner
        (curve.polynomial.eval (parent.segment.pointAt current.parameter)))
      (position : ParentPosition parent current) :
      ParentStepSmalls parent (.stop current owner position)
  /-- Retain the direct-step certificate at the exact current parent position, together with the original step data and
    certified tail. -/ | next
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
      (remaining : PreparedSubdivision parent.segment parent.within
        request.endpoint
          (PreparedSheetContinuation.advance parent.segment
            parent.within current owner request small))
      (position : ParentPosition parent current)
      (remainingPositions : ParentPositions parent remaining)
      (stepSmall :
        PreparedSheetContinuation.Subdivision.DirectStepSmall
          parent.segment parent.left
            (PreparedSheetContinuation.prepared parent.segment
              parent.left parent.owner parent.request)
            current position.directMoveSmall owner request)
      (tail : ParentStepSmalls parent remainingPositions) :
      ParentStepSmalls parent
        (.next current owner request cached ordered small remaining position
          remainingPositions)

constructive_injectivity ParentStepSmalls

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Branches in
/-- Check the direct-step clearance conditions of the original subdivision at its retained parent positions.

Success returns the dependent certificates for those exact steps. `none` records that this finite check did not return
the full certificate family. -/
def tryParentStepSmalls {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) ->
    (positions : ParentPositions parent subdivision) ->
      Option (ParentStepSmalls parent positions)
  | current, owner, .stop _ _, .stop _ _ position =>
      some (.stop current owner position)
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions =>
      if stepSmall :
          PreparedSheetContinuation.Subdivision.DirectStepSmall
            parent.segment parent.left
              (PreparedSheetContinuation.prepared parent.segment
                parent.left parent.owner parent.request)
              current position.directMoveSmall owner request then
        match tryParentStepSmalls parent request.endpoint
            (PreparedSheetContinuation.advance parent.segment
              parent.within current owner request small)
            remaining remainingPositions with
        | none => none
        | some tail =>
            some (.next current owner request cached ordered small remaining
              position remainingPositions stepSmall tail)
      else none

/-- Report whether the finite parent-step check returned its complete certificate family. -/
def parentStepSmallsAccepted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    {current : Endpoint}
    {owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))}
  (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) (positions : ParentPositions parent subdivision) : Bool :=
  (tryParentStepSmalls parent current owner subdivision positions).isSome

open Purelib.Riemann.Branches
/-- Construct the safe dyadic subdivision of the parent's original segment and endpoint interval.

The supplied depth, positive root-diameter target and mesh-safety certificate determine the original checked
subdivision, starting from the parent's retained owner. -/
def parentDyadicSubdivision {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (depth : Nat) (rootDiameter : PreparedSubdivisionModelCore.Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    PreparedSubdivision parent.segment parent.within parent.left parent.owner :=
  PreparedSheetContinuation.Subdivision.checkedDyadic
    parent.segment parent.within parent.left parent.request.endpoint
      parent.owner depth rootDiameter rootDiameterPositive safe

/-- The checked dyadic subdivision ends at the parent's exact request parameter. -/
theorem parentDyadicSubdivision_endpoint_eq {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (depth : Nat) (rootDiameter : PreparedSubdivisionModelCore.Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
      safe).endpoint.parameter = parent.request.endpoint.parameter := by
  apply congrArg (fun endpoint : Endpoint => endpoint.parameter)
  exact PreparedSheetContinuation.Subdivision.tryDyadic_endpoint
    parent.segment parent.within parent.left parent.request.endpoint
      parent.owner depth rootDiameter rootDiameterPositive
        (PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic
          parent.segment parent.within parent.left parent.request.endpoint
            parent.owner depth rootDiameter rootDiameterPositive safe)

/-- Construct exact parent query positions for every endpoint of the safe dyadic subdivision.

Strict parent endpoint order and the checked subdivision's terminal equation supply all affine fractions and
unit-interval bounds. -/
def parentDyadicPositions {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : PreparedSubdivisionModelCore.Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    ParentPositions parent
      (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
        safe) :=
  parentPositionsOfEndpointEq parent proper
    (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
      safe)
    (parentDyadicSubdivision_endpoint_eq parent depth rootDiameter
      rootDiameterPositive safe)

end

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
/-- Direct-step certificates for the exact safe dyadic subdivision of the retained parent.

The certificate is indexed by the parent, depth, positive diameter target and original mesh-safety evidence, preserving
the actual subdivision and position family. -/
structure CheckedParentDyadic {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : PreparedSubdivisionModelCore.Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) where
  /-- Direct-step clearance certificates for the exact parent dyadic positions retained by this certificate. -/
    stepSmalls : ParentStepSmalls parent
    (parentDyadicPositions parent proper depth rootDiameter
      rootDiameterPositive safe)

constructive_injectivity CheckedParentDyadic

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Branches in
/-- Check direct-step clearance for the exact safe parent dyadic subdivision.

Success packages the returned certificate family with its original depth, diameter and safety indices. Failure is the
unsuccessful result of this finite certificate check. -/
def tryCheckedParentDyadic {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (depth : Nat) (rootDiameter : PreparedSubdivisionModelCore.Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive) :
    Option (CheckedParentDyadic parent proper depth rootDiameter
      rootDiameterPositive safe) :=
  match tryParentStepSmalls parent parent.left parent.owner
      (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
        safe)
      (parentDyadicPositions parent proper depth rootDiameter
        rootDiameterPositive safe) with
  | none => none
  | some stepSmalls => some ⟨stepSmalls⟩

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Relate the parent's direct owner at its source to the original source owner.

The comparison reverses same-radicand advancement and the prepared-source root equivalence, retaining the exact source
coordinate and both owner names. -/
def parentInitialRootEquivalent {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (sourceSmall :
      PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.segment parent.left
          (PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request) parent.left) :
    PreparedSheetContinuation.Subdivision.RootEquivalentAt
      parent.segment parent.left
        (PreparedSheetContinuation.Subdivision.directOwnerAt
          parent.left
          (PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request)
          parent.left sourceSmall)
        parent.owner :=
  { firstName := SquareRootTrackEquivalence.ownerRootName
      (parent.segment.pointAt_eval_ne_zero parent.left.parameter
        parent.left.inside)
      (PreparedSheetContinuation.Subdivision.directOwnerAt
        parent.left
        (PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request)
        parent.left sourceSmall)
    secondName := SquareRootTrackEquivalence.ownerRootName
      (parent.segment.pointAt_eval_ne_zero parent.left.parameter
        parent.left.inside) parent.owner
    equivalent := Equivalence.NamedEquivalent.trans
      (SquareRootTrackEquivalence.rootEquivalent_advance_same
        (parent.segment.pointAt_eval_ne_zero parent.left.parameter
          parent.left.inside)
        (PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request) (by
              simpa only [Norm.Basic.normSq_eq_canonical]
                using sourceSmall.proof)).symm
      (PreparedSheetContinuation.sourceRootEquivalent
        parent.segment parent.left parent.owner parent.request).symm
    first_eq := rfl
    second_eq := rfl }

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Riemann.Branches
/-- Propagate a retained direct-owner equivalence through the certified parent steps.

At each original request, direct-step and direct-move clearance produce the next root equivalence; the dependent result
retains the exact subdivision and its original owner sequence. -/
def directlyCoherentOfParentStepSmalls {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential) :
    (current : Endpoint) ->
    (owner : Owner
      (curve.polynomial.eval (parent.segment.pointAt current.parameter))) ->
    (subdivision : PreparedSubdivision parent.segment parent.within current
      owner) ->
    (positions : ParentPositions parent subdivision) ->
    (currentEquivalent :
      PreparedSheetContinuation.Subdivision.RootEquivalentAt
        parent.segment current
          (PreparedSheetContinuation.Subdivision.directOwnerAt
            parent.left
            (PreparedSheetContinuation.prepared parent.segment
              parent.left parent.owner parent.request)
            current positions.currentPosition.directMoveSmall)
          owner) ->
    (stepSmalls : ParentStepSmalls parent positions) ->
      PreparedSheetContinuation.Subdivision.DirectlyCoherent
        parent.segment parent.within parent.left
          (PreparedSheetContinuation.prepared parent.segment
            parent.left parent.owner parent.request)
          positions.currentPosition.directMoveSmall owner currentEquivalent
            subdivision
  | current, owner, .stop _ _, .stop _ _ position, currentEquivalent,
      .stop _ _ _ =>
      .stop current position.directMoveSmall owner currentEquivalent
  | current, owner, .next _ _ request cached ordered small remaining,
      .next _ _ _ _ _ _ _ position remainingPositions, currentEquivalent,
      .next _ _ _ _ _ _ _ _ _ stepSmall tail =>
      let sourceNextSmall :=
        remainingPositions.currentPosition.directMoveSmall
      let nextEquivalent :=
        PreparedSheetContinuation.Subdivision.directNextRootEquivalent
          parent.segment parent.within parent.left
            (PreparedSheetContinuation.prepared parent.segment
              parent.left parent.owner parent.request)
            current position.directMoveSmall owner currentEquivalent request
              small sourceNextSmall stepSmall
      .next current position.directMoveSmall owner currentEquivalent request
        cached ordered small remaining sourceNextSmall stepSmall
          (directlyCoherentOfParentStepSmalls parent request.endpoint
            (PreparedSheetContinuation.advance parent.segment
              parent.within current owner request small)
            remaining remainingPositions nextEquivalent tail)

/-- Construct direct coherence for the whole parent subdivision from its retained positions and step certificates.

The initial comparison uses the parent's original owner, and every subsequent comparison follows the original cached
subdivision. -/
def directlyCoherentParentBlock {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (subdivision : PreparedSubdivision parent.segment parent.within
      parent.left parent.owner)
    (positions : ParentPositions parent subdivision)
    (stepSmalls : ParentStepSmalls parent positions) :
    PreparedSheetContinuation.Subdivision.DirectlyCoherent
      parent.segment parent.within parent.left
        (PreparedSheetContinuation.prepared parent.segment
          parent.left parent.owner parent.request)
        positions.currentPosition.directMoveSmall parent.owner
          (parentInitialRootEquivalent parent
            positions.currentPosition.directMoveSmall)
          subdivision :=
  directlyCoherentOfParentStepSmalls parent parent.left parent.owner
    subdivision positions
    (parentInitialRootEquivalent parent
      positions.currentPosition.directMoveSmall) stepSmalls

/-- Build child root comparisons from the subdivision's direct coherence and supplied center family.

Each child retains its actual cached edge and center. The parent positions identify its query coordinates, while the
original coherence supplies the root-name comparison. -/
def rootChildBlockOfDirectlyCoherent {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    {current : Endpoint}
    (sourceCurrentSmall :
      PreparedSheetContinuation.Subdivision.DirectMoveSmall
        parent.edge.segment parent.edge.left
          (PreparedSheetContinuation.prepared parent.edge.segment
            parent.edge.left parent.edge.owner parent.edge.request) current)
    (owner : Owner
      (curve.polynomial.eval (parent.edge.segment.pointAt current.parameter)))
    (currentEquivalent :
      PreparedSheetContinuation.Subdivision.RootEquivalentAt
        parent.edge.segment current
          (PreparedSheetContinuation.Subdivision.directOwnerAt
            parent.edge.left
            (PreparedSheetContinuation.prepared parent.edge.segment
              parent.edge.left parent.edge.owner parent.edge.request)
            current sourceCurrentSmall)
          owner)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      current owner)
    (coherent :
      PreparedSheetContinuation.Subdivision.DirectlyCoherent
        parent.edge.segment parent.edge.within parent.edge.left
          (PreparedSheetContinuation.prepared parent.edge.segment
            parent.edge.left parent.edge.owner parent.edge.request)
          sourceCurrentSmall owner currentEquivalent subdivision)
    (positions : ParentPositions parent.edge subdivision)
    (centers : CenterStates curve differential parent.edge.sheet subdivision) :
    RootChildBlock parent
      (centeredEdges curve differential parent.edge.sheet subdivision centers) :=
  match coherent, positions, centers with
  | .stop _ _ _ _, .stop _ _ _, _ => .nil
  | .next current sourceSmall owner equivalent request cached ordered
        childSmall remaining sourceNextSmall stepSmall tail,
      .next _ _ _ _ _ _ _ position remainingPositions, centers =>
      .cons
        (rootChildAtOfDirectStep parent current owner request cached ordered
          childSmall centers.1 sourceSmall equivalent position)
        (rootChildBlockOfDirectlyCoherent parent sourceNextSmall
          (PreparedSheetContinuation.advance parent.edge.segment
            parent.edge.within current owner request childSmall)
          (PreparedSheetContinuation.Subdivision.directNextRootEquivalent
            parent.edge.segment parent.edge.within parent.edge.left
              (PreparedSheetContinuation.prepared
                parent.edge.segment parent.edge.left parent.edge.owner
                  parent.edge.request)
              current sourceSmall owner equivalent request childSmall
                sourceNextSmall stepSmall)
          remaining tail remainingPositions centers.2)

end

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Construct a root comparison block from the exact parent-step certificates and retained centers.

Direct coherence is derived from the original parent owner and subdivision before transferring it to the centered child
edges. -/
def rootChildBlockOfParentStepSmalls {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (positions : ParentPositions parent.edge subdivision)
    (stepSmalls : ParentStepSmalls parent.edge positions)
    (centers : CenterStates curve differential parent.edge.sheet subdivision) :
    RootChildBlock parent
      (centeredEdges curve differential parent.edge.sheet subdivision centers) :=
  rootChildBlockOfDirectlyCoherent parent
    positions.currentPosition.directMoveSmall parent.edge.owner
      (parentInitialRootEquivalent parent.edge
        positions.currentPosition.directMoveSmall)
      subdivision
      (directlyCoherentParentBlock parent.edge subdivision positions stepSmalls)
      positions centers

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.List in
/-- Refine one retained centered parent by its original certified child subdivision.

The root comparison block preserves both centers and caches. The supplied terminal parameter equation gives the exact
total displacement required by the refinement. -/
def singleParentRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (positions : ParentPositions parent.edge subdivision)
    (stepSmalls : ParentStepSmalls parent.edge positions)
    (centers : CenterStates curve differential parent.edge.sheet subdivision)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.edge.request.endpoint.parameter) :
    CenteredEdgeRefinement [parent]
      (centeredEdges curve differential parent.edge.sheet subdivision centers) := by
  let block := rootChildBlockOfParentStepSmalls parent subdivision positions
    stepSmalls centers
  have displacement := centeredEdges_displacement_eq_parent parent subdivision
    centers endpoint_eq
  simpa only [Append.append_nil] using
    CenteredEdgeRefinement.cons parent block displacement
      (CenteredEdgeRefinement.nil (curve := curve)
        (differential := differential))

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Transfer the retained one-parent root refinement to a compatible constant path refinement.

The child list is the exact ordered centered subdivision, and the parent model remains the supplied original centered
model. -/
def compatibleSingleParentRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : CenteredEdge curve differential)
    (subdivision : PreparedSubdivision parent.edge.segment parent.edge.within
      parent.edge.left parent.edge.owner)
    (positions : ParentPositions parent.edge subdivision)
    (stepSmalls : ParentStepSmalls parent.edge positions)
    (centers : CenterStates curve differential parent.edge.sheet subdivision)
    (endpoint_eq : subdivision.endpoint.parameter =
      parent.edge.request.endpoint.parameter) :
    Basic.PathModel.CompatibleConstantPathRefinement
      [parent.model]
      ((centeredEdges curve differential parent.edge.sheet subdivision
        centers).map CenteredEdge.model) := by
  simpa only [List.map_cons, List.map_nil] using
    (singleParentRefinement parent subdivision positions stepSmalls centers
      endpoint_eq).toCompatible

namespace CheckedParentDyadic

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Read a compatible refinement from the checked dyadic parent certificate and supplied center states.

The retained safety and step certificates determine the exact dyadic child subdivision; the original parent center and
each supplied child center are preserved. -/
def compatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {proper : parent.left.parameter < parent.request.endpoint.parameter}
    {depth : Nat} {rootDiameter : PreparedSubdivisionModelCore.Coordinate}
    {rootDiameterPositive : 0 < rootDiameter}
    {safe : PreparedSheetContinuation.Subdivision.DyadicMeshSafe
      parent.segment parent.left parent.request.endpoint parent.owner depth
        rootDiameter rootDiameterPositive}
    (checked : CheckedParentDyadic parent proper depth rootDiameter
      rootDiameterPositive safe)
    (parentCenter :
      PreparedConstantModels.PreparedEdge.CenterState parent)
    (centers : CenterStates curve differential parent.sheet
      (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
        safe)) :
    Basic.PathModel.CompatibleConstantPathRefinement
      [CenteredEdge.model { edge := parent, center := parentCenter }]
      ((centeredEdges curve differential parent.sheet
        (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive
          safe) centers).map CenteredEdge.model) :=
  compatibleSingleParentRefinement
    { edge := parent, center := parentCenter }
    (parentDyadicSubdivision parent depth rootDiameter rootDiameterPositive safe)
    (parentDyadicPositions parent proper depth rootDiameter
      rootDiameterPositive safe)
    checked.stepSmalls centers
    (parentDyadicSubdivision_endpoint_eq parent depth rootDiameter
      rootDiameterPositive safe)

end CheckedParentDyadic

end Purelib.Riemann.Integration.PreparedSubdivisionParentModels
