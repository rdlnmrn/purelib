module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Riemann.RootContinuation.RootContinuationCongruence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

@[expose] public section

/-!
# Actual prepared endpoint congruence from ordinary acceptance

Repreparation, same-box transport, and reserve retention may change the owner
presentation.  They preserve the endpoint root whenever the two ordinary
prepared moves are accepted.  No fresh-owner or bridge-movement test is added.
This compares moves over the same displayed request; the coarse/fine
comparison for independently anchored dyadic children remains separate work.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.Congruence

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-- The canonical Gaussian rational coordinate type. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- Finite dense Gaussian rational polynomials. -/
abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The retained rational box type. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original indexed square-root continuation owner. -/
abbrev Owner := Riemann.Topology.SquareRootContinuationChain.Owner
/-- Operational equivalence of the original named Gaussian approximation processes. -/
abbrev NamedEquivalent := Equivalence.NamedEquivalent

open Purelib.RootIsolation
/-- The two accepted prepared moves retain equivalent endpoint owners.
This is the ordinary-bound replacement for
`PreparedSheetContinuation.advanceRootEquivalent_of_rootEquivalent`. -/
def advanceEquivalent {polynomial : SquareRoot.Preparation.Congruence.Polynomial} {ambient :
  SquareRoot.Preparation.Congruence.Box} {start finish : SquareRoot.Preparation.Congruence.Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Riemann.Branches.PreparedSheetContinuation.Endpoint)
    (first second : SquareRoot.Preparation.Congruence.Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (equivalent : SquareRoot.Preparation.Congruence.NamedEquivalent
      (Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName first.parameterNonzero first)
      (Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName second.parameterNonzero second))
    (firstSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (Riemann.Branches.PreparedSheetContinuation.prepared segment left first request).track.initial.clearance.bound)
    (secondSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (Riemann.Branches.PreparedSheetContinuation.prepared segment left second request).track.initial.clearance.bound) :
    SquareRoot.Preparation.Congruence.NamedEquivalent
      (Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName (segment.pointAt_eval_ne_zero
        request.endpoint.parameter request.endpoint.inside)
        (Riemann.Branches.PreparedSheetContinuation.advance segment within left first request firstSmall))
      (Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName (segment.pointAt_eval_ne_zero
        request.endpoint.parameter request.endpoint.inside)
        (Riemann.Branches.PreparedSheetContinuation.advance segment within left second request secondSmall)) := by
  have preparedEquivalent := (Riemann.Branches.PreparedSheetContinuation.sourceRootEquivalent segment left first
    request).symm.trans
    (equivalent.trans (Riemann.Branches.PreparedSheetContinuation.sourceRootEquivalent segment left second request))
  have variation := Riemann.Branches.ClearSheetContinuation.evaluation_variation_le segment within
    left.parameter request.endpoint.parameter left.inside request.endpoint.inside
  have generic := Riemann.RootContinuation.RootContinuationCongruence.continuedEquivalent
    (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside)
    (Riemann.Branches.PreparedSheetContinuation.prepared segment left first request)
      (Riemann.Branches.PreparedSheetContinuation.prepared segment left second request)
    preparedEquivalent (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (variation.trans_lt firstSmall))
      (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (variation.trans_lt secondSmall))
  have transportedEquivalent :=
    (Riemann.Branches.PreparedSheetContinuation.continuedRootNameEquivalentTransportedRootName segment within left first
      request firstSmall).symm.trans
      (generic.trans (Riemann.Branches.PreparedSheetContinuation.continuedRootNameEquivalentTransportedRootName segment
        within left second request secondSmall))
  have retained :=
    (Riemann.Branches.PreparedSheetContinuation.retainedAtReserveRootEquivalent
      (Riemann.Branches.PreparedSheetContinuation.transported segment within left first request firstSmall)
      (Riemann.Branches.PreparedSheetContinuation.preparedClearanceLower segment left request)).symm.trans
    (transportedEquivalent.trans
      (Riemann.Branches.PreparedSheetContinuation.retainedAtReserveRootEquivalent
        (Riemann.Branches.PreparedSheetContinuation.transported segment within left second request secondSmall)
        (Riemann.Branches.PreparedSheetContinuation.preparedClearanceLower segment left request)))
  simpa only [Riemann.Branches.PreparedSheetContinuation.advance,
    Riemann.Branches.PreparedSheetContinuation.transportedRootName,
    Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName] using retained

/-- Compact cached-name form for dependent bank recursion. -/
def advanceAtEquivalent {polynomial : SquareRoot.Preparation.Congruence.Polynomial} {ambient :
  SquareRoot.Preparation.Congruence.Box} {start finish : SquareRoot.Preparation.Congruence.Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Riemann.Branches.PreparedSheetContinuation.Endpoint)
    (first second : SquareRoot.Preparation.Congruence.Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (equivalent : Riemann.Branches.PreparedSheetContinuation.Subdivision.RootEquivalentAt segment left first second)
    (firstSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (Riemann.Branches.PreparedSheetContinuation.prepared segment left first request).track.initial.clearance.bound)
    (secondSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (Riemann.Branches.PreparedSheetContinuation.prepared segment left second request).track.initial.clearance.bound) :
    Riemann.Branches.PreparedSheetContinuation.Subdivision.RootEquivalentAt segment request.endpoint
      (Riemann.Branches.PreparedSheetContinuation.advance segment within left first request firstSmall)
      (Riemann.Branches.PreparedSheetContinuation.advance segment within left second request secondSmall) where
  firstName := Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName (segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside)
    (Riemann.Branches.PreparedSheetContinuation.advance segment within left first request firstSmall)
  secondName := Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName (segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside)
    (Riemann.Branches.PreparedSheetContinuation.advance segment within left second request secondSmall)
  first_eq := rfl
  second_eq := rfl
  equivalent := SquareRoot.Preparation.Congruence.advanceEquivalent segment within left first second request
    equivalent.toNamedEquivalent firstSmall secondSmall

end Purelib.RootIsolation.SquareRoot.Preparation.Congruence
