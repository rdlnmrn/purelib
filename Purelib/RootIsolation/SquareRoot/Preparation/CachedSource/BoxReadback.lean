module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Generated sample certificates for the quartic A-backward connector

This module identifies the 64 canonical centred edges of the explicit
A-backward horizontal path with the independently generated rational root
and sample data.  The reversed stationary prefix is handled separately as a
zero-displacement path.
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticABackwardSampleCertificates

/-- A ready canonical cached source has the same box as its selected strengthened owner.

The supplied carrying and box equalities identify the actual prepared source selected by the original constructor. -/
private theorem canonicalCachedSource_box_eq
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (left : Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint)
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (box : Box)
    (ready : Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared
      segment left owner request)
    (strengthenedCarries :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound)
    (boxEq : owner.track.initial.box = box) :
    (Riemann.Branches.PreparedSheetContinuation.CachedSource.canonical
      segment left owner request).preparedOwner.track.initial.box = box := by
  exact
    (Riemann.Branches.PreparedSheetContinuation.prepared_initial_box_eq_of_ready_of_strengthenedCarries
      segment left owner request ready strengthenedCarries).trans boxEq
end Purelib.Examples.Riemann.ExplicitQuarticABackwardSampleCertificates

end

section
@[expose] public section

/-!
# Generated sample certificates for the horizontal quartic connector

This module connects the untrusted generated rational root data to the exact
prepared edges cached by the A-forward construction.  The common helpers keep
the proof cost linear in the 64 nonstationary horizontal edges.
-/

namespace Purelib.Examples.Riemann.ExplicitQuarticHorizontalSampleCertificates

/-- A ready canonical cached source has the same box as its selected strengthened owner.

The supplied carrying and box equalities identify the actual prepared source selected by the original constructor. -/
private theorem canonicalCachedSource_box_eq
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (left : Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint)
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (box : Box)
    (ready : Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared
      segment left owner request)
    (strengthenedCarries :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound)
    (boxEq : owner.track.initial.box = box) :
    (Riemann.Branches.PreparedSheetContinuation.CachedSource.canonical
      segment left owner request).preparedOwner.track.initial.box = box := by
  exact
    (Riemann.Branches.PreparedSheetContinuation.prepared_initial_box_eq_of_ready_of_strengthenedCarries
      segment left owner request ready strengthenedCarries).trans boxEq
end Purelib.Examples.Riemann.ExplicitQuarticHorizontalSampleCertificates

end

section
@[expose] public section

namespace Purelib.RootIsolation.SquareRoot.Preparation.CachedSource.BoxReadback

/-- A canonical cached source retains the prepared owner's original box.

Readiness and the strengthened variation bound identify the cached owner; the
input equality then transports that box to the requested retained box. -/
theorem canonicalCachedSource_box_eq
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (left : Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint)
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (box : Box)
    (ready : Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared
      segment left owner request)
    (strengthenedCarries :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound)
    (boxEq : owner.track.initial.box = box) :
    (Riemann.Branches.PreparedSheetContinuation.CachedSource.canonical
      segment left owner request).preparedOwner.track.initial.box = box :=
  (Riemann.Branches.PreparedSheetContinuation.prepared_initial_box_eq_of_ready_of_strengthenedCarries
    segment left owner request ready strengthenedCarries).trans boxEq

end Purelib.RootIsolation.SquareRoot.Preparation.CachedSource.BoxReadback

end
