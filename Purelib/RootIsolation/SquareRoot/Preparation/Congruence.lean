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
abbrev Polynomial := Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The retained rational box type. -/
abbrev Box := Geometry.Rational.Box
/-- The original indexed square-root continuation owner. -/
abbrev Owner := Riemann.Topology.SquareRootContinuationChain.Owner
/-- Operational equivalence of the original named Gaussian approximation processes. -/
abbrev NamedEquivalent := Equivalence.NamedEquivalent

open Purelib.RootIsolation
/-- The two accepted prepared moves retain equivalent endpoint owners.
This is the ordinary-bound replacement for
`PreparedSheetContinuation.advanceRootEquivalent_of_rootEquivalent`. -/
def advanceEquivalent {polynomial : Polynomial} {ambient :
  Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (equivalent : NamedEquivalent
      (ownerRootName first.parameterNonzero first)
      (ownerRootName second.parameterNonzero second))
    (firstSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (prepared segment left first request).track.initial.clearance.bound)
    (secondSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (prepared segment left second request).track.initial.clearance.bound) :
    NamedEquivalent
      (ownerRootName (segment.pointAt_eval_ne_zero
        request.endpoint.parameter request.endpoint.inside)
        (advance segment within left first request firstSmall))
      (ownerRootName (segment.pointAt_eval_ne_zero
        request.endpoint.parameter request.endpoint.inside)
        (advance segment within left second request secondSmall)) := by
  have preparedEquivalent := (sourceRootEquivalent segment left first
    request).symm.trans
    (equivalent.trans (sourceRootEquivalent segment left second request))
  have variation := Riemann.Branches.ClearSheetContinuation.evaluation_variation_le segment within
    left.parameter request.endpoint.parameter left.inside request.endpoint.inside
  have generic := Riemann.RootContinuation.RootContinuationCongruence.continuedEquivalent
    (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside)
    (prepared segment left first request)
      (prepared segment left second request)
    preparedEquivalent (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (variation.trans_lt firstSmall))
      (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (variation.trans_lt secondSmall))
  have transportedEquivalent :=
    (continuedRootNameEquivalentTransportedRootName segment within left first
      request firstSmall).symm.trans
      (generic.trans (continuedRootNameEquivalentTransportedRootName segment
        within left second request secondSmall))
  have retained :=
    (retainedAtReserveRootEquivalent
      (transported segment within left first request firstSmall)
      (preparedClearanceLower segment left request)).symm.trans
    (transportedEquivalent.trans
      (retainedAtReserveRootEquivalent
        (transported segment within left second request secondSmall)
        (preparedClearanceLower segment left request)))
  simpa only [advance,
    transportedRootName,
    ownerRootName] using retained

/-- Compact cached-name form for dependent bank recursion. -/
def advanceAtEquivalent {polynomial : Polynomial} {ambient :
  Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (equivalent : Subdivision.RootEquivalentAt segment left first second)
    (firstSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (prepared segment left first request).track.initial.clearance.bound)
    (secondSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
      request.endpoint.parameter <
      (prepared segment left second request).track.initial.clearance.bound) :
    Subdivision.RootEquivalentAt segment request.endpoint
      (advance segment within left first request firstSmall)
      (advance segment within left second request secondSmall) where
  firstName := ownerRootName (segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside)
    (advance segment within left first request firstSmall)
  secondName := ownerRootName (segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside)
    (advance segment within left second request secondSmall)
  first_eq := rfl
  second_eq := rfl
  equivalent := advanceEquivalent segment within left first second request
    equivalent.toNamedEquivalent firstSmall secondSmall

end Purelib.RootIsolation.SquareRoot.Preparation.Congruence
