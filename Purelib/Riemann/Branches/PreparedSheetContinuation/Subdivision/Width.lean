module

public import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Width payment on the retained original prepared requests

Width certificates refer to the exact supplied prepared request spine. The
original uniform-mesh width theorem pays its dyadic targets, and successful
acquisition identifies that same list with its original depth-indexed
factory. No prepared source, advance, request or terminal Owner is replaced.
-/

public section

namespace Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge parameterEdgesFrom)

/-- Each actual supplied prepared request has squared parameter width at most the same scalar allowance. -/
@[expose] def WidthsFit (bound : Coordinate) : Endpoint → List StepRequest → Prop
  | _current, [] => True
  | current, request :: remaining =>
      (current.parameter - request.endpoint.parameter) ^ 2 ≤ bound ∧ WidthsFit bound request.endpoint remaining

namespace WidthsFit

/-- An increased scalar width allowance preserves the identical original request spine. -/
theorem mono {first last : Coordinate} (increase : first ≤ last) :
    ∀ (current : Endpoint) (requests : List StepRequest),
      WidthsFit first current requests → WidthsFit last current requests
  | _current, [], _paid => trivial
  | _current, request :: remaining, paid =>
      ⟨paid.1.trans increase, mono increase request.endpoint remaining paid.2⟩

/-- The head request's actual original parameter displacement is paid by its retained width certificate. -/
theorem head {bound : Coordinate} {current : Endpoint} {request : StepRequest}
    {remaining : List StepRequest} (paid : WidthsFit bound current (request :: remaining)) :
    (current.parameter - request.endpoint.parameter) ^ 2 ≤ bound := paid.1

/-- The same remaining original requests stay width-paid starting at the identical head endpoint. -/
theorem tail {bound : Coordinate} {current : Endpoint} {request : StepRequest}
    {remaining : List StepRequest} (paid : WidthsFit bound current (request :: remaining)) :
    WidthsFit bound request.endpoint remaining := paid.2

/-- Paid original consecutive parameter edges give the same certificate on the unchanged prepared request spine. -/
theorem of_edges (bound : Coordinate) :
    ∀ (current : Endpoint) (requests : List StepRequest),
      (∀ edge : ParameterEdge, edge ∈ parameterEdgesFrom current (requestEndpoints requests) →
        (edge.left.parameter - edge.right.parameter) ^ 2 ≤ bound) → WidthsFit bound current requests
  | _current, [], _paid => trivial
  | current, request :: remaining, paid =>
      ⟨paid { left := current, right := request.endpoint } (List.Mem.head _),
        of_edges bound request.endpoint remaining (fun edge member => by
          apply paid edge
          change edge ∈ (⟨current, request.endpoint⟩ : ParameterEdge) ::
            parameterEdgesFrom request.endpoint (requestEndpoints remaining)
          exact List.Mem.tail (⟨current, request.endpoint⟩ : ParameterEdge) member)⟩

end WidthsFit

/-- The original dyadic requests inherit their retained mesh edges' exact depth-dependent squared width.

The proof uses the existing original uniform-mesh width theorem. Membership
and original request-endpoint equations retain the same ordered occurrences;
no duplicate midpoint-width construction is introduced.
-/
theorem dyadicRequests_widthsFit (depth : Nat) (left right : Endpoint) (diameter : Coordinate)
    (positive : 0 < diameter) :
    WidthsFit (Geometric.Basic.quarterRadius ((left.parameter - right.parameter) ^ 2) depth) left
      (dyadicRequests depth left right diameter positive) := by
  apply WidthsFit.of_edges
  intro edge member
  rewrite [requestEndpoints_dyadicRequests, ClearSheetContinuation.Subdivision.parameterEdgesFrom_dyadicTargets]
    at member
  have width := UniformPrimitiveMesh.dyadicEdges_width depth left right edge member
  exact (show (edge.left.parameter - edge.right.parameter) ^ 2 =
      (edge.right.parameter - edge.left.parameter) ^ 2 by ring1).trans_le
    (width.le.trans_eq (congrArg (fun scale => Geometric.Basic.quarterRadius scale depth)
      (show (right.parameter - left.parameter) ^ 2 = (left.parameter - right.parameter) ^ 2 by ring1)))

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
variable {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
variable {left right : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}

/-- A successful original dyadic acquisition pays widths on its actual retained subdivision requests.

Its original success equation identifies the exact list and retained depth.
The subdivision, CachedSources, advances and terminal Owner are unchanged.
-/
theorem tryDyadic_widthsFit (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth diameter positive = some subdivision) :
    WidthsFit (Geometric.Basic.quarterRadius ((left.parameter - right.parameter) ^ 2) depth)
      left subdivision.requests := by
  rewrite [tryDyadic_requests segment within left right owner depth diameter positive success]
  exact dyadicRequests_widthsFit depth left right diameter positive

end Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision
