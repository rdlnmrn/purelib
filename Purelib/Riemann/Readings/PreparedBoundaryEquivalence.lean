module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot

public section

/-!
# Operational coefficient transport across prepared cell boundaries

Prepared integration cells query their sheet root through a pointwise
continuation, while the recursive continuation checker resets each accepted
endpoint to a fresh global owner.  This module proves, using only the stored
finite winding-one bridges, that the coefficient at the right end of one cell
is operationally equal to the coefficient at the left end of its successor.
-/

namespace Purelib.Riemann.Readings.PreparedBoundaryEquivalence

open Purelib.Riemann.Curves.AlgebraicDifferentials

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational box type. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The retained square-root continuation owner at its original radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A subdivision parameter carrying its original unit-interval bounds. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The original prepared continuation request, including its endpoint and root-diameter target. -/
abbrev StepRequest := Purelib.Riemann.Branches.PreparedSheetContinuation.StepRequest
/-- Operational equivalence between the two original Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
/-- A Gaussian process together with its retained starting state. -/
abbrev Named := Purelib.Approximation.Gaussian.Name.Basic.Named
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A prepared differential edge retaining the original segment, root owner, request and cached source. -/
abbrev PreparedEdge {genus : Nat} (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge curve differential

/-- The rational parameter zero belongs to the closed unit interval.

Direct computation certifies the two retained weak bounds of this endpoint
in the original constructive rational carrier. -/
theorem zeroInside :
    (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1 := by decide

/-- The rational parameter one belongs to the closed unit interval.

Direct computation certifies the two retained weak bounds of this endpoint
in the original constructive rational carrier. -/
theorem oneInside :
    (0 : Coordinate) <= 1 ∧ (1 : Coordinate) <= 1 := by decide

set_option genInjectivity false in
/-- Two original Gaussian names with their operational equivalence certificate.

The bridge retains both endpoints of the equivalence rather than replacing either name with a chosen common
representative. -/
structure NamedBridge where
  /-- The original source Gaussian name. -/ first : Named
  /-- The original target Gaussian name. -/ second : Named
  /-- Operational equivalence of the two retained names, with their original processes and starting states. -/
    equivalent : NamedEquivalent first second

constructive_injectivity NamedBridge

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Relate the prepared edge's endpoint query to its retained transported root name.

The cached endpoint-name equation identifies the exact query produced at parameter one; reflexive equivalence then
retains the transported name unchanged. -/
@[expose] def endpointQueryEquivalentToTransported {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edge : PreparedEdge curve differential) : NamedBridge where
  first := edge.rootName 1 oneInside
  second := edge.transportedRootName
  equivalent := by
    unfold PreparedConstantModels.PreparedEdge.rootName
      PreparedConstantModels.PreparedEdge.transportedRootName
    rw [PreparedModels.rootAtCached_one_name_eq_transportedRootName]
    exact Equivalence.NamedEquivalent.refl _

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- Relate the prepared owner root to the edge's cached base query.

The comparison composes same-radicand owner advancement with the reserved transport comparison, then uses the cached
zero-query equation. -/
@[expose] def preparedEquivalentToBaseQuery {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (edge : PreparedEdge curve differential) : NamedBridge where
  first := edge.preparedRootName
  second := edge.rootName 0 zeroInside
  equivalent := by
    let prepared := PreparedSheetContinuation.prepared edge.segment
      edge.left edge.owner edge.request
    have sameSmall :
        Data.Gaussian.Norm.Basic.normSq
            (curve.polynomial.eval (edge.segment.pointAt edge.left.parameter) -
              curve.polynomial.eval
                (edge.segment.pointAt edge.left.parameter)) <
          prepared.track.initial.clearance.bound := by
      rw [Basic.sub_self,
        Norm.Basic.normSq_zero]
      exact prepared.track.initial.clearance.positive
    have preparedToGeneric :=
      SquareRootTrackEquivalence.rootEquivalent_advance_same
        (edge.segment.pointAt_eval_ne_zero edge.left.parameter edge.left.inside)
          prepared (by simpa only [Norm.Basic.normSq_eq_canonical] using sameSmall)
    have genericToDirect :=
      PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
        prepared
          (edge.segment.pointAt_eval_ne_zero edge.left.parameter
            edge.left.inside)
          sameSmall
        (PreparedSheetContinuation.transportReserve edge.segment
          edge.left edge.request)
    have equivalent := Equivalence.NamedEquivalent.trans
      preparedToGeneric genericToDirect
    unfold PreparedConstantModels.PreparedEdge.preparedRootName
      PreparedConstantModels.PreparedEdge.rootName
    rw [PreparedModels.rootAtCached_zero_name_eq_zeroMoveRootName]
    unfold PreparedSheetContinuation.preparedRootName
      PreparedSheetContinuation.zeroMoveRootName
    exact equivalent

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- Adjacent prepared steps on the same sheet have equivalent coefficient names at their shared endpoint.

The second step uses the first step's actual advanced owner. The comparison retains both caches, composes transport,
reserve reset and preparation equivalences, and uses the common endpoint coordinate to transfer root equivalence to the
differential coefficient. -/
@[expose] def adjacentCoefficientEquivalent {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (curve.polynomial.eval
      (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left
      owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment left owner
          request).track.initial.clearance.bound)
    (nextRequest : StepRequest)
    (nextCached : PreparedSheetContinuation.CachedSource segment
      request.endpoint
        (PreparedSheetContinuation.advance segment within left
          owner request small) nextRequest)
    (nextOrdered : request.endpoint.parameter <=
      nextRequest.endpoint.parameter)
    (nextSmall : ClearSheetContinuation.variationBound segment
      request.endpoint.parameter nextRequest.endpoint.parameter <
        (PreparedSheetContinuation.prepared
          segment request.endpoint
          (PreparedSheetContinuation.advance segment within left
            owner request small) nextRequest).track.initial.clearance.bound)
    (sheet : Fin 2) :
    NamedEquivalent
      (PreparedModels.coefficientAtCached curve
        differential segment within left owner request cached ordered small
          sheet 1 oneInside).name
      (PreparedModels.coefficientAtCached curve differential
        segment within request.endpoint
          (PreparedSheetContinuation.advance segment within left
            owner request small)
          nextRequest nextCached nextOrdered nextSmall sheet 0 zeroInside).name := by
  let endpointNonzero : curve.polynomial.eval
      (segment.pointAt request.endpoint.parameter) ≠ 0 :=
    segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside
  let transported := PreparedSheetContinuation.transported segment
    within left owner request small
  let nextOwner := PreparedSheetContinuation.advance segment within
    left owner request small
  have resetEquivalent : NamedEquivalent
      (transported.certificate endpointNonzero).value.name
      (nextOwner.certificate endpointNonzero).value.name := by
    simpa only [nextOwner, PreparedSheetContinuation.advance,
      SquareRootTrackEquivalence.ownerRootName] using
      (PreparedSheetContinuation.retainedAtReserveRootEquivalent
        transported
        (PreparedSheetContinuation.preparedClearanceLower
          segment left request))
  have preparationEquivalent :=
    PreparedSheetContinuation.sourceRootEquivalent segment
      request.endpoint nextOwner nextRequest
  let parent : PreparedEdge curve differential :=
    { ambient := ambient
      start := start
      finish := finish
      segment := segment
      within := within
      left := left
      owner := owner
      request := request
      cached := cached
      ordered := ordered
      small := small
      sheet := sheet }
  let child : PreparedEdge curve differential :=
    { ambient := ambient
      start := start
      finish := finish
      segment := segment
      within := within
      left := request.endpoint
      owner := nextOwner
      request := nextRequest
      cached := nextCached
      ordered := nextOrdered
      small := nextSmall
      sheet := sheet }
  have endpointEquivalent :=
    (endpointQueryEquivalentToTransported parent).equivalent
  change NamedEquivalent (parent.rootName 1 oneInside)
    parent.transportedRootName at endpointEquivalent
  have baseEquivalent := (preparedEquivalentToBaseQuery child).equivalent
  change NamedEquivalent child.preparedRootName
    (child.rootName 0 zeroInside) at baseEquivalent
  let nextOwnerRoot := (nextOwner.certificate endpointNonzero).value.name
  have resetWrapped : NamedEquivalent parent.transportedRootName
      nextOwnerRoot := by
    simpa only [parent,
      PreparedConstantModels.PreparedEdge.transportedRootName,
      PreparedSheetContinuation.transportedRootName,
      PreparedSheetContinuation.advance,
      transported, nextOwner, nextOwnerRoot] using resetEquivalent
  have preparationWrapped : NamedEquivalent nextOwnerRoot
      child.preparedRootName := by
    simpa only [child,
      PreparedConstantModels.PreparedEdge.preparedRootName,
      PreparedSheetContinuation.preparedRootName,
      nextOwnerRoot, nextOwner] using preparationEquivalent
  have edgeRootEquivalent :=
    Equivalence.NamedEquivalent.trans endpointEquivalent
      (Equivalence.NamedEquivalent.trans resetWrapped
        (Equivalence.NamedEquivalent.trans preparationWrapped
          baseEquivalent))
  have point_eq : parent.point 1 = child.point 0 := by
    dsimp only [parent, child, PreparedConstantModels.PreparedEdge.point,
      PreparedConstantModels.PreparedEdge.localSegment, PreparedModels.edge]
    rw [Geometry.ClearPath.ClearSegment.pointAt_one,
      Geometry.ClearPath.ClearSegment.pointAt_zero]
  exact
    PreparedConstantModels.PreparedEdge.coefficientEquivalent_of_rootEquivalent
      parent child 1 oneInside point_eq edgeRootEquivalent

end Purelib.Riemann.Readings.PreparedBoundaryEquivalence
