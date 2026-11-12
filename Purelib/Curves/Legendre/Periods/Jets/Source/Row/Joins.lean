module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Row
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Joins.Handoffs
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Joins.Payment
public import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Requested handoff observations on two actual retained Legendre rows

Both actual TransportRows and their four existing endpoint joins are
inputs. The original source-row expression is defined at every retained
Owner. One request is allocated before its new coefficient observations;
three external Vertices share their literal middle cache. The complete
stationary sum uses the actual two trace counts plus four endpoint joins.
No row, Point,
selector, numerical primitive or source crop is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Row

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

universe u

variable {parameter : Canonical} (row : Row)
    {firstPoint middlePoint lastPoint : Canonical} {firstAmbient lastAmbient : Box}
    {firstPath : ClearPath (Paths.polynomial parameter) firstAmbient firstPoint middlePoint}
    {lastPath : ClearPath (Paths.polynomial parameter) lastAmbient middlePoint lastPoint}
    {firstFrame : OwnerFrame ((Paths.polynomial parameter).eval firstPoint)}
    {middleFrame : OwnerFrame ((Paths.polynomial parameter).eval middlePoint)}
    {lastFrame : OwnerFrame ((Paths.polynomial parameter).eval lastPoint)}
    {firstIndex lastIndex : Fin 2}
    (before : TransportRow firstPath firstFrame middleFrame firstIndex)
    (after : TransportRow lastPath middleFrame lastFrame lastIndex)
    {outerFirst : Owner ((Paths.polynomial parameter).eval firstPoint)}
    {outerMiddle : Owner ((Paths.polynomial parameter).eval middlePoint)}
    {outerLast : Owner ((Paths.polynomial parameter).eval lastPoint)}
    (beforeSource : OwnerJoin outerFirst (firstFrame.owners firstIndex))
    (beforeTarget : OwnerJoin before.traced.finishOwner outerMiddle)
    (afterSource : OwnerJoin outerMiddle (middleFrame.owners lastIndex))
    (afterTarget : OwnerJoin after.traced.finishOwner outerLast)

/-- Pay the four endpoint handoffs of the same two retained rows using the original Legendre row expression.

Each original Owner supplies its genuine denominator guard. The existing
path guard theorem supplies the two moving Spines' domains. The original
row traces and all four joins are consumed as cached data, with neither
TransportRow.build nor OwnerJoin.acquire run again. The returned payment
concerns only the separate four endpoint changes; internal row handoffs,
independently normalized numerical primitives and total integral accuracy
remain distinct.
-/
def withEndpointPayment (request : AccuracyRequest) {Result : Type u}
    (consume :
      (beforePath : OwnerPath (Paths.polynomial parameter) firstPoint (firstFrame.owners firstIndex)
        middlePoint before.traced.finishOwner) → beforePath = before.traced.trace.get →
      (afterPath : OwnerPath (Paths.polynomial parameter) middlePoint (middleFrame.owners lastIndex)
        lastPoint after.traced.finishOwner) → afterPath = after.traced.trace.get →
      (beforeDefined : Primitive.Defined (row.expression parameter) beforePath) →
      (afterDefined : Primitive.Defined (row.expression parameter) afterPath) →
      Primitive.Spine.EndpointConsumer (polynomial := Paths.polynomial parameter)
        (expression := row.expression parameter)
        beforePath afterPath beforeSource beforeTarget afterSource afterTarget
        (Row.defined parameter firstPoint row outerFirst) (Row.defined parameter middlePoint row outerMiddle)
        (Row.defined parameter lastPoint row outerLast) beforeDefined afterDefined request Result) : Result :=
  let beforePath := before.traced.trace.get
  let afterPath := after.traced.trace.get
  let beforeDefined := Trace.defined (parameter := parameter) row beforePath
  let afterDefined := Trace.defined (parameter := parameter) row afterPath
  Primitive.Spine.withEndpointJoins (polynomial := Paths.polynomial parameter)
    (expression := row.expression parameter)
    (before := beforePath) (after := afterPath)
    (beforeSource := beforeSource) (beforeTarget := beforeTarget)
    (afterSource := afterSource) (afterTarget := afterTarget)
    (firstDefined := Row.defined parameter firstPoint row outerFirst)
    (middleDefined := Row.defined parameter middlePoint row outerMiddle)
    (lastDefined := Row.defined parameter lastPoint row outerLast)
    (beforeDefined := beforeDefined) (afterDefined := afterDefined) request
    (consume beforePath rfl afterPath rfl beforeDefined afterDefined)

/-- Pay all stationary handoffs on the same two retained rows, including their four actual endpoint joins.

The original row traces determine the exact count before any coefficient
observation. One preselected minimum request drives the endpoint producer.
The existing callback receives its same caches, while the returned Between
completion retains their actual combined Spine and requested payment. The
moving integral and independent numerical primitive constants are not
identified by this operation.
-/
def withHandoffPayment (endpointTarget handoffTarget : AccuracyRequest) {Result : Type u}
    (consume :
      (beforePath : OwnerPath (Paths.polynomial parameter) firstPoint (firstFrame.owners firstIndex)
        middlePoint before.traced.finishOwner) → beforePath = before.traced.trace.get →
      (afterPath : OwnerPath (Paths.polynomial parameter) middlePoint (middleFrame.owners lastIndex)
        lastPoint after.traced.finishOwner) → afterPath = after.traced.trace.get →
      (beforeDefined : Primitive.Defined (row.expression parameter) beforePath) →
      (afterDefined : Primitive.Defined (row.expression parameter) afterPath) →
      Primitive.Spine.EndpointConsumer (polynomial := Paths.polynomial parameter)
        (expression := row.expression parameter)
        beforePath afterPath beforeSource beforeTarget afterSource afterTarget
        (Row.defined parameter firstPoint row outerFirst) (Row.defined parameter middlePoint row outerMiddle)
        (Row.defined parameter lastPoint row outerLast) beforeDefined afterDefined
        (Primitive.Spine.handoffRequest beforePath afterPath endpointTarget handoffTarget) Result) :
    Primitive.Spine.HandoffCompletion (polynomial := Paths.polynomial parameter)
      (expression := row.expression parameter) before.traced.trace.get after.traced.trace.get
      beforeSource beforeTarget afterSource afterTarget endpointTarget handoffTarget × Result :=
  let beforePath := before.traced.trace.get
  let afterPath := after.traced.trace.get
  let beforeDefined := Trace.defined (parameter := parameter) row beforePath
  let afterDefined := Trace.defined (parameter := parameter) row afterPath
  Primitive.Spine.withHandoffPayment (polynomial := Paths.polynomial parameter)
    (expression := row.expression parameter) (before := beforePath) (after := afterPath)
    (beforeSource := beforeSource) (beforeTarget := beforeTarget)
    (afterSource := afterSource) (afterTarget := afterTarget)
    (firstDefined := Row.defined parameter firstPoint row outerFirst)
    (middleDefined := Row.defined parameter middlePoint row outerMiddle)
    (lastDefined := Row.defined parameter lastPoint row outerLast)
    (beforeDefined := beforeDefined) (afterDefined := afterDefined) endpointTarget handoffTarget
    (consume beforePath rfl afterPath rfl beforeDefined afterDefined)

end Purelib.Curves.Legendre.Periods.Jets.Source.Row

end
