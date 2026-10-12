module

meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Integration.Algebraic.SquareFactor.PathObservation

import Purelib.Elab.Deriving.Repr
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Polynomial.Geometry.PolynomialPathDiagnostics
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic

public section

/-!
# Coefficient-first input for original-differential observations

All algebra, path margins and the inherited coherent program are generated
from finite coefficients, the differential request, the retained oriented
segment and its initial sheet.  No success, coherence or transport witness
is a public input.  The initial program is lazy and shared across policies.

The original-coordinate mode checks that `s` is nonzero throughout the path.
The separately selected cancelled-expression mode permits an extension of
the reduced quotient.  It never calls that extension a value of `0/0`.
A failed coarse margin is inconclusive, not evidence of divergence.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.ObservationInput

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput

/-- Select the original-coordinate domain or the square-factor-cancelled expression domain. -/
inductive Domain where
  /-- Require the original coordinate expression's certified nonzero square-factor domain. -/ | originalCoordinate
  /-- Use the square-factor-cancelled expression domain. -/ | cancelledExpression
deriving DecidableEq
derive_exposed_repr Purelib.Integration.Algebraic.SquareFactor.ObservationInput.Domain

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The original-coordinate domain requires a positive retained square-factor margin; the cancelled domain adds no such
requirement. -/
@[expose] def Domain.Evidence {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
    {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
    (domain : ObservationInput.Domain) (data : PathInput.Data prepared segment) : Prop :=
  match domain with
  | .originalCoordinate => 0 < data.squareFactor.lowerBound
  | .cancelledExpression => True

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- The exact polynomial preparation and safe segment data with domain evidence and a retained lazy source cache.

All indices retain the original polynomial, differential request, segment, sheet and selected domain; the source
equation binds the cache to those owners. -/
structure PreparedEntry (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request)
    (segment : PathInput.Segment) (sheet : Fin 2) (domain : ObservationInput.Domain) where
  /-- The exact retained square-factor preparation for the original polynomial and differential request. -/ prepared :
    SquareFactor.Prepared polynomial request
  /-- The retained original segment bounds indexed by that exact preparation. -/ data : PathInput.Data prepared segment
  /-- The retained positive denominator and radicand margins. -/ safe : data.Safe
  /-- The exact additional evidence required by the originally requested domain. -/ domainEvidence : domain.Evidence
    data
  /-- The retained lazy source indexed by the original path data and sheet. -/ sourceCache : Thunk
    (PathObservation.Source data sheet)
  /-- Forcing the source cache gives the exact canonical original safe-path source. -/ source_eq : sourceCache.get =
    PathObservation.Source.canonical safe sheet

constructive_injectivity PreparedEntry

namespace PreparedEntry

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request} {segment :
  Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {sheet : Fin 2} {domain : Purelib.Integration.Algebraic.SquareFactor.ObservationInput.Domain}

open Purelib.Integration.Algebraic.SquareFactor in
/-- Force the original retained source cache without replacing its path data or sheet. -/
@[expose] def source (entry : ObservationInput.PreparedEntry polynomial request segment sheet domain) :
    PathObservation.Source entry.data sheet := entry.sourceCache.get

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Retain the supplied preparation, safe path data and domain evidence with the exact lazy canonical source. -/
@[expose] def ofData (prepared : SquareFactor.Prepared polynomial request) (data : PathInput.Data prepared segment)
    (safe : data.Safe) (sheet : Fin 2) (domain : ObservationInput.Domain) (evidence : domain.Evidence data) :
    ObservationInput.PreparedEntry polynomial request segment sheet domain :=
  { prepared := prepared
    data := data
    safe := safe
    domainEvidence := evidence
    sourceCache := ⟨fun _ => PathObservation.Source.canonical safe sheet⟩
    source_eq := rfl }

open Purelib.Integration.Algebraic.SquareFactor
/-- The retained source carries the exact original entry safety certificate. -/
theorem source_safe (entry : ObservationInput.PreparedEntry polynomial request segment sheet domain) :
    entry.source.safe = entry.safe := by
  rw [ObservationInput.PreparedEntry.source, entry.source_eq]
  rfl

/-- Original-coordinate domain evidence excludes a square-factor zero at every in-range original segment point. -/
theorem squareFactor_nonzero
    (entry : ObservationInput.PreparedEntry polynomial request segment sheet .originalCoordinate)
    {parameter : PathInput.Coordinate} (inside : PathInput.unitInterval.Contains parameter) :
    entry.prepared.reduction.squareFactor.eval (segment.point parameter) ≠ 0 :=
  entry.data.squareFactor.eval_nonzero entry.domainEvidence inside

end PreparedEntry

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- A retained zero-polynomial certificate, endpoint obstruction or inconclusive original path/domain check.

Inconclusive outcomes retain the exact preparation and bounds; they do not establish a global obstruction. -/
inductive Failure (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request) (segment :
  PathInput.Segment) where
  /-- The original polynomial has a certified zero test result. -/ | zero (certificate : polynomial.isZero = true)
  /-- The retained original preparation and path data identify a certified endpoint pole or branch obstruction. -/ |
    endpointObstruction (prepared : SquareFactor.Prepared polynomial request) (data : PathInput.Data prepared segment)
      (endpoint : PathInput.Data.Endpoint) (obstruction : data.EndpointObstruction endpoint)
  /-- The exact retained original path margin check is inconclusive. -/ | inconclusive (prepared : SquareFactor.Prepared
    polynomial request) (data : PathInput.Data prepared segment)
      (failure : data.MarginFailure)
  /-- The retained original endpoint has a certified square-factor zero. -/ | originalCoordinateObstruction (prepared :
    SquareFactor.Prepared polynomial request) (data : PathInput.Data prepared segment)
      (endpoint : PathInput.Data.Endpoint)
      (zero : prepared.reduction.squareFactor.eval (segment.point endpoint.parameter) = 0)
  /-- The retained square-factor bound fails to certify the original-coordinate domain. -/ |
    originalCoordinateUncertified (prepared : SquareFactor.Prepared polynomial request) (data : PathInput.Data prepared
    segment)
      (certificate : data.squareFactor.Inconclusive)

constructive_injectivity Failure

open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Integration.Algebraic.SquareFactor
/-- Check original segment endpoints for a certified square-factor zero, preferring the starting endpoint.

The start endpoint is checked before the finish endpoint. A detected zero
retains its original endpoint and polynomial evaluation certificate. -/
@[expose] def originalCoordinateObstruction? {polynomial : SquareFactor.GaussianPolynomial} {request :
  SquareFactor.Request} {segment : PathInput.Segment}
    (prepared : SquareFactor.Prepared polynomial request) (data : PathInput.Data prepared segment) :
    Option (ObservationInput.Failure polynomial request segment) :=
  if startZero : data.squareFactor.value 0 = 0 then
    some (.originalCoordinateObstruction prepared data .start
      ((data.squareFactor.value_eq 0).symm.trans startZero))
  else if finishZero : data.squareFactor.value 1 = 0 then
    some (.originalCoordinateObstruction prepared data .finish
      ((data.squareFactor.value_eq 1).symm.trans finishZero))
  else none

/-- Check the retained path margins and requested domain before constructing the original cached entry.

Endpoint obstructions remain explicit; missing original-coordinate margin is distinguished from a certified endpoint
zero and from an inconclusive path-safety check. -/
@[expose] def prepareChecked {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request} {segment :
  PathInput.Segment}
    (prepared : SquareFactor.Prepared polynomial request) (data : PathInput.Data prepared segment)
    (sheet : Fin 2) (domain : ObservationInput.Domain) :
    Except (ObservationInput.Failure polynomial request segment) (ObservationInput.PreparedEntry polynomial request
      segment sheet domain) :=
  match data.check with
  | .endpointObstruction endpoint obstruction => .error (.endpointObstruction prepared data endpoint obstruction)
  | .inconclusive failure =>
      match domain with
      | .cancelledExpression => .error (.inconclusive prepared data failure)
      | .originalCoordinate =>
          match ObservationInput.originalCoordinateObstruction? prepared data with
          | some obstruction => .error obstruction
          | none => .error (.inconclusive prepared data failure)
  | .accepted safe =>
      match domain with
      | .originalCoordinate =>
          if positive : 0 < data.squareFactor.lowerBound then
            .ok (ObservationInput.PreparedEntry.ofData prepared data safe sheet .originalCoordinate positive)
          else
            match ObservationInput.originalCoordinateObstruction? prepared data with
            | some obstruction => .error obstruction
            | none => .error (.originalCoordinateUncertified prepared data
                (data.squareFactor.inconclusiveCertificate (le_of_not_gt positive)))
      | .cancelledExpression =>
          .ok (ObservationInput.PreparedEntry.ofData prepared data safe sheet .cancelledExpression True.intro)

/-- Prepare the original polynomial and segment bounds, then check the requested sheet and domain entry. -/
@[expose] def prepare (polynomial : SquareFactor.GaussianPolynomial) (request : SquareFactor.Request) (segment :
  PathInput.Segment)
    (sheet : Fin 2) (domain : ObservationInput.Domain) :
    Except (ObservationInput.Failure polynomial request segment) (ObservationInput.PreparedEntry polynomial request
      segment sheet domain) :=
  match SquareFactor.prepare polynomial request with
  | .error zero => .error (.zero zero.down)
  | .ok prepared =>
      let requireOriginal := match domain with | .originalCoordinate => true | .cancelledExpression => false
      ObservationInput.prepareChecked prepared (PathInput.prepareData prepared segment requireOriginal) sheet domain

/-- The supplied exact path safety and domain evidence force successful preparation of the retained original entry. -/
theorem prepareChecked_complete {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request} {segment
  : PathInput.Segment}
    (prepared : SquareFactor.Prepared polynomial request) (data : PathInput.Data prepared segment)
    (safe : data.Safe) (sheet : Fin 2) (domain : ObservationInput.Domain) (evidence : domain.Evidence data) :
    ObservationInput.prepareChecked prepared data sheet domain =
      .ok (ObservationInput.PreparedEntry.ofData prepared data safe sheet domain evidence) := by
  rw [ObservationInput.prepareChecked, data.check_complete safe]
  cases domain with
  | originalCoordinate => exact dif_pos evidence
  | cancelledExpression => rfl

end Purelib.Integration.Algebraic.SquareFactor.ObservationInput
