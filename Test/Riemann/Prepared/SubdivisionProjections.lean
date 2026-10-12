module
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Riemann.Branches.PreparedSheetContinuation
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches

@[expose] public section

/-!
Focused compiler inspection for projections from an already prepared spine.
Build this module's C output without generated certificates or root isolation.
These consumers use only the public API.  Their compiled calls must select
the direct stored-data traversals, not replay `advance` to read a field.
-/

namespace SubdivisionProjectionHarness

open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within :
    segment.WithinAmbient}
  {left : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}

/-- Read the stored step count of the prepared subdivision. -/
@[noinline] def stepCount (subdivision : Subdivision segment within left owner) : Nat :=
  subdivision.stepCount

/-- Read the stored terminal endpoint of the prepared subdivision. -/
@[noinline] def endpoint (subdivision : Subdivision segment within left owner) : Endpoint :=
  subdivision.endpoint

/-- Read the terminal owner indexed by the subdivision's exact endpoint value. -/
@[noinline] def terminalOwner (subdivision : Subdivision segment within left owner) :
    Owner (polynomial.eval (segment.pointAt subdivision.endpoint.parameter)) := subdivision.terminalOwner

/-- Read the prepared subdivision's stored parameter-edge list. -/
@[noinline] def parameterEdges (subdivision : Subdivision segment within left owner) :
    List ClearSheetContinuation.Subdivision.ParameterEdge := subdivision.parameterEdges

/-- Read the prepared subdivision's stored box list. -/
@[noinline] def preparedBoxes (subdivision : Subdivision segment within left owner) : List Box :=
  subdivision.preparedBoxes

/-- Read the prepared subdivision's stored step requests. -/
@[noinline] def requests (subdivision : Subdivision segment within left owner) : List StepRequest :=
  subdivision.requests

/-- Read the clear path from the original segment point to the retained terminal endpoint. -/
@[noinline] def toClearPath (subdivision : Subdivision segment within left owner) :
    Purelib.Polynomial.Geometry.ClearPath polynomial ambient (segment.pointAt left.parameter)
      (segment.pointAt subdivision.endpoint.parameter) := subdivision.toClearPath

/-- The projection wrapper preserves the stored subdivision step count. -/
theorem stepCount_eq (subdivision : Subdivision segment within left owner) :
    stepCount subdivision = subdivision.stepCount := rfl

/-- The projection wrapper preserves the stored terminal endpoint. -/
theorem endpoint_eq (subdivision : Subdivision segment within left owner) :
    endpoint subdivision = subdivision.endpoint := rfl

/-- The projection wrapper preserves the exact terminal owner. -/
theorem terminalOwner_eq (subdivision : Subdivision segment within left owner) :
    terminalOwner subdivision = subdivision.terminalOwner := rfl

end SubdivisionProjectionHarness
