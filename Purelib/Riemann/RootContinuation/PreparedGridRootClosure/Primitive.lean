module

public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Approximation.Gaussian.Equivalence

/-! # Closing given primitive observations on an actual root-closed grid walk

The original retained return comparison supplies one actual final-to-initial
OwnerJoin. Its complete final Owner is the cached original trace endpoint;
the original whole finishOwner equality transports that same join to the
prepared-path index. The existing primitive closing constructor consumes
the given old Spine. No path, root Owner or old observation is acquired.
-/

public section

namespace Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)

variable {polynomial : Coefficients} {ambient : Box} {grid : ClearGrid polynomial ambient}
    {base : Canonical} {owner : Owner (polynomial.eval base)}

/-- Close the SAME given old Spine using the original return certificate and both retained endpoint Owners.

The cached final Owner supplies the only OwnerJoin acquisition. Whole
Owner equality changes its nominal prepared-path endpoint index; the same
join and old observations then feed one existing closing comparison.
Both original join factories and the complete comparison factory remain
available to the continuation. No identity of old readings is asserted.
-/
def withClosing (closed : RootClosedWalk grid base owner)
    {expression : Expression polynomial} {accuracy : AccuracyRequest}
    (materialized : OwnerPath polynomial base owner base (PreparedPathGluing.finishOwner closed.traced.prepared))
    (observed : Primitive.Spine expression accuracy materialized) {Result : Type u}
    (consume :
      (retainedJoin : OwnerJoin closed.traced.finishOwner owner) →
      retainedJoin = OwnerJoin.acquire closed.traced.finishOwner owner closed.rootReturn →
      (join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner) →
      join = Eq.mp (congrArg (fun terminal : Owner (polynomial.eval base) => OwnerJoin terminal owner)
        closed.traced.finishOwner_eq) retainedJoin →
      (compared : Primitive.Closing.Comparison observed join) →
      compared = Primitive.Closing.Comparison.build observed join → Result) : Result :=
  let retainedJoin := OwnerJoin.acquire closed.traced.finishOwner owner closed.rootReturn
  let join := Eq.mp (congrArg (fun terminal : Owner (polynomial.eval base) => OwnerJoin terminal owner)
    closed.traced.finishOwner_eq) retainedJoin
  let compared := Primitive.Closing.Comparison.build observed join
  consume retainedJoin rfl join rfl compared rfl

end Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

end
