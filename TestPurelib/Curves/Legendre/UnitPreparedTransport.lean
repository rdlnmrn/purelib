module

import Purelib.Curves.Legendre.Degeneration.UnitRoot.PreparedTransport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Paths.OwnerTracePath

/-! # Complete original cofactor continuation with retained prepared handoffs -/

namespace TestPurelib.Curves.Legendre.UnitPreparedTransport

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Degeneration.UnitRoot.PreparedTransport
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedSegment TracedPath)
open Purelib.Riemann.Paths
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Every complete prepared result derives comparison with the independent patch reading internally. -/
example {site : Fin 2} {start finish : Canonical} (segment : Segment site start finish)
    (within : segment.WithinAmbient)
    (traced : TracedSegment segment within
      (Degeneration.UnitRoot.owner site start (start_inside segment within))) :
    NamedEquivalent (ownerRootName traced.finishOwner.parameterNonzero traced.finishOwner)
      (ownerRootName (Degeneration.UnitRoot.owner site finish (finish_inside segment within)).parameterNonzero
        (Degeneration.UnitRoot.owner site finish (finish_inside segment within))) :=
  build_agrees segment within traced

/-- Independent accepted preparations preserve their actual endpoint owners and compute operational agreement. -/
example {site : Fin 2} {start finish : Canonical} (segment : Segment site start finish)
    (within : segment.WithinAmbient)
    (first second : TracedSegment segment within
      (Degeneration.UnitRoot.owner site start (start_inside segment within))) :
    NamedEquivalent (ownerRootName first.finishOwner.parameterNonzero first.finishOwner)
      (ownerRootName second.finishOwner.parameterNonzero second.finishOwner) :=
  builds_agree segment within first second

/-- Intrinsic endpoint admission constructs and completely prepares an actual two-piece path with finish agreement. -/
example (site : Fin 2) (first last : Canonical)
    (firstInside : (Degeneration.spatialBox site).Contains first)
    (lastInside : (Degeneration.spatialBox site).Contains last) :
    let path := axisPath site first last firstInside lastInside
    let within := axisPath_within site first last firstInside lastInside
    let actual := buildPath path within firstInside
    ReadingAgreement site last (path_finish_inside path within firstInside) actual.finishOwner := by
  exact buildPath_agrees (axisPath site first last firstInside lastInside)
    (axisPath_within site first last firstInside lastInside) firstInside
    (buildPath (axisPath site first last firstInside lastInside)
      (axisPath_within site first last firstInside lastInside) firstInside)

/-- Independent complete path preparations preserve both original finish owners when computing their comparison. -/
example {site : Fin 2} {start finish : Canonical} (first second : Path site start finish)
    (firstWithin : first.WithinAmbient) (secondWithin : second.WithinAmbient)
    (inside : (Degeneration.spatialBox site).Contains start)
    (left : TracedPath first (Degeneration.UnitRoot.owner site start inside))
    (right : TracedPath second (Degeneration.UnitRoot.owner site start inside)) :
    NamedEquivalent (ownerRootName left.finishOwner.parameterNonzero left.finishOwner)
      (ownerRootName right.finishOwner.parameterNonzero right.finishOwner) :=
  buildPaths_agree first second firstWithin secondWithin inside left right

/-- A returning actual path constructs a closed geometric trace without a supplied terminal root join. -/
example {site : Fin 2} {base : Canonical} (path : Path site base base)
    (within : path.WithinAmbient) (inside : (Degeneration.spatialBox site).Contains base)
    (actual : TracedPath path (Degeneration.UnitRoot.owner site base inside)) :
    OwnerTracePath.OwnerPath.ClosedRealization actual.trace.get :=
  closePath path within inside actual

end TestPurelib.Curves.Legendre.UnitPreparedTransport
