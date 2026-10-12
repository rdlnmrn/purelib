module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Winding.Polygon.Stationary

public import Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Trace
public import Purelib.Riemann.Paths.PreparedTraceEdges
public import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Data.Nat.Basic

@[expose] public section

/-!
# Root traces on the retained prepared subdivision

Every accepted step contributes its actual source-preparation handoff, its
moving edge, and its actual endpoint-retention handoff.  Adjacent pieces use
the same cached residual tails.  The owner path is indexed by the original
subdivision's terminal owner, not by a newly selected sheet label.
-/

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace

open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerTail)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)

/-- The original rational Gaussian box carrier. -/
abbrev Box := Purelib.Geometry.Rational.Box

namespace PreparedTraceBudget

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment polynomial ambient start finish} {left right : Endpoint}

open Purelib.Riemann.Branches in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Construct the original owner path through a retained prepared subdivision whose requests fit the trace budget.

Each step keeps the cached source and target joins, one moving link and two stationary handoff links. Recursion follows
the exact original subdivision and terminal owner. -/
def ownerPath (budget : PreparedTraceBudget segment left right)
    {within : segment.WithinAmbient} :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner),
      budget.RequestsFit current subdivision.requests →
        OwnerPath polynomial (segment.pointAt current.parameter) owner
          (segment.pointAt subdivision.endpoint.parameter) subdivision.terminalOwner
  | current, owner, .stop _ _, _ => .nil (segment.pointAt current.parameter) owner
  | current, owner, .next _ _ request cached ordered safe remaining, fits =>
      let sourceJoin :=
        SquareRoot.Preparation.Handoff.Trace.CachedSource.traceJoin cached
      let targetJoin := SquareRoot.Preparation.Handoff.Trace.advanceTraceJoin
        segment within current owner request safe
      let moving : OwnerLink polynomial (segment.pointAt current.parameter)
          (segment.pointAt request.endpoint.parameter) cached.preparedOwner
          (PreparedSheetContinuation.transported segment within current owner request safe) :=
        { leftTail := sourceJoin.rightTail
          rightTail := targetJoin.leftTail
          leftIndex := sourceJoin.rightTail.first
          rightIndex := targetJoin.leftTail.first
          left_ge := le_rfl
          right_ge := le_rfl
          realize := fun first second _ _ =>
            PreparedTraceEdges.PreparedTraceBudget.edge
              budget within current owner request cached ordered safe fits.1 fits.2.1 first second }
      .cons (OwnerLink.stationary polynomial (segment.pointAt current.parameter) sourceJoin)
        (.cons moving
          (.cons (OwnerLink.stationary polynomial (segment.pointAt request.endpoint.parameter) targetJoin)
            (ownerPath budget remaining fits.2.2)))

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The exact original base vertices of the retained subdivision trace, including source and target handoff repetitions.
-/
def traceVertices (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    Endpoint → List PreparedSheetContinuation.StepRequest → List Basic.Canonical
  | _, [] => []
  | current, request :: remaining =>
      segment.pointAt current.parameter :: segment.pointAt request.endpoint.parameter ::
        segment.pointAt request.endpoint.parameter :: traceVertices segment request.endpoint remaining

/-- The retained subdivision owner path has exactly the original request-derived trace vertex list. -/
theorem ownerPath_vertices (budget : PreparedTraceBudget segment left right)
    {within : segment.WithinAmbient} :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (fits : budget.RequestsFit current subdivision.requests),
      (ownerPath budget subdivision fits).vertices = traceVertices segment current subdivision.requests
  | _, _, .stop _ _, _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining, fits => by
      change _ :: _ :: _ :: (ownerPath budget remaining fits.2.2).vertices =
        _ :: _ :: _ :: traceVertices segment _ remaining.requests
      rw [ownerPath_vertices budget remaining fits.2.2]

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The retained trace vertex list and the original moving-request endpoint list have equal raw polynomial winding.

The exact repeated source and target vertices contribute stationary segments, while the original moving endpoints and
ordering remain unchanged. -/
theorem traceVertices_chainRaw (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    ∀ (current : Endpoint) (requests : List PreparedSheetContinuation.StepRequest),
      Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt current.parameter)
          (traceVertices segment current requests) =
        Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt current.parameter)
          (requests.map fun request => segment.pointAt request.endpoint.parameter)
  | _, [] => rfl
  | current, request :: remaining => by
      rw [traceVertices, Winding.Polygon.Stationary.chainRaw_cons_self polynomial _
        (segment.pointAt_eval_ne_zero current.parameter current.inside)]
      change _ + Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt request.endpoint.parameter)
        (segment.pointAt request.endpoint.parameter :: traceVertices segment request.endpoint remaining) =
          _ + Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt request.endpoint.parameter)
            (remaining.map fun next => segment.pointAt next.endpoint.parameter)
      rw [Winding.Polygon.Stationary.chainRaw_cons_self polynomial _
        (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside),
        traceVertices_chainRaw segment request.endpoint remaining]

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The retained trace vertices terminate at the same original point as the moving-request endpoint list. -/
theorem traceVertices_terminal (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    ∀ (current : Endpoint) (requests : List PreparedSheetContinuation.StepRequest),
      Polygon.Chain.terminal (segment.pointAt current.parameter)
          (traceVertices segment current requests) =
        Polygon.Chain.terminal (segment.pointAt current.parameter)
          (requests.map fun request => segment.pointAt request.endpoint.parameter)
  | _, [] => rfl
  | _, request :: remaining => traceVertices_terminal segment request.endpoint remaining

open Purelib.Polynomial in
/-- The original owner path and retained moving-request endpoint list have equal raw polynomial winding. -/
theorem ownerPath_chainRaw (budget : PreparedTraceBudget segment left right)
    {within : segment.WithinAmbient} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (fits : budget.RequestsFit current subdivision.requests) :
    Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt current.parameter)
        (ownerPath budget subdivision fits).vertices =
      Winding.Polygon.Basic.chainRaw polynomial (segment.pointAt current.parameter)
        (subdivision.requests.map fun request => segment.pointAt request.endpoint.parameter) := by
  rw [ownerPath_vertices budget subdivision fits, traceVertices_chainRaw]

set_option genInjectivity false in
/-- A retained budgeted subdivision together with its original owner path and exact trace-vertex equation.

The original starting owner, terminal owner and request list remain those of the stored subdivision, with each request's
budget certificate retained. -/
structure TracedSubdivision (budget : PreparedTraceBudget segment left right)
    (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) where
  /-- The original prepared subdivision from the retained start owner and endpoint. -/ subdivision : Subdivision segment
    within left owner
  /-- Every original stored subdivision request satisfies the retained trace budget. -/ fits : budget.RequestsFit left
    subdivision.requests
  /-- The original owner path to the exact stored subdivision endpoint and terminal owner. -/ path : OwnerPath
    polynomial (segment.pointAt left.parameter) owner
    (segment.pointAt subdivision.endpoint.parameter) subdivision.terminalOwner
  /-- The path vertices equal the exact trace list derived from the original subdivision requests. -/ vertices_eq :
    path.vertices = traceVertices segment left subdivision.requests

constructive_injectivity TracedSubdivision

/-- Build the original checked subdivision and retain its request-fit certificate, owner path and exact vertex equation.
-/
def traced (budget : PreparedTraceBudget segment left right) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (ordered : left.parameter ≤ right.parameter) : TracedSubdivision budget within owner :=
  let subdivision := budget.prepare within owner ordered
  let fits := budget.prepare_fit within owner ordered
  { subdivision := subdivision
    fits := fits
    path := ownerPath budget subdivision fits
    vertices_eq := ownerPath_vertices budget subdivision fits }

end PreparedTraceBudget

end Purelib.Riemann.Paths.PreparedSubdivisionTrace
