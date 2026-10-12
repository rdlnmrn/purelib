module
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.PreparedSubdivisionTrace
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.RootIsolation.State.Raw

import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSideRoots
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Branches.ClearSheetContinuation

@[expose] public section

/-! Owner traces retain the exact subdivision used by paired Newton sides. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide.PairedBoundarySide
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide (PairedBoundarySide)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}

variable {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
  {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)} {sheet : Fin 2}

open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Owner path following the actual retained paired-side subdivision.

Uses the stored trace budget and fit certificate, transporting only the segment endpoint coordinates and original
root-owner identities. -/
def ownerPath (side :
  PairedBoundarySide request other segment within owner sheet) :
    OwnerTracePath.OwnerPath curve.polynomial start owner finish side.finishOwner :=
  (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath side.traceBudget side.covered.subdivision
    side.traceFits).castEndpoints
    segment.pointAt_zero
    (by rw [side.covered.endpoint_eq]; exact segment.pointAt_one)
    (by unfold PreparedClearPathModels.ownerAtStart; exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _)
    (UniformPreparedBoundarySegments.CoveredSegment.finishOwner_heq_terminalOwner side.covered).symm

open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- The retained owner path has the subdivision's exact trace vertices.

Endpoint transport preserves the original cached request sequence and vertex readback. -/
theorem ownerPath_vertices (side :
  PairedBoundarySide request other segment within owner sheet) :
    side.ownerPath.vertices = PreparedSubdivisionTrace.PreparedTraceBudget.traceVertices segment firstEndpoint
      side.covered.subdivision.requests := by
  rw [PreparedNewtonPairedSide.PairedBoundarySide.ownerPath, OwnerTracePath.OwnerPath.castEndpoints_vertices]
  exact PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath_vertices side.traceBudget side.covered.subdivision
    side.traceFits

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- The owner path winding equals that of the retained request endpoints.

Uses the exact subdivision trace-vertex identity with the original segment start point. -/
theorem ownerPath_winding (side :
  PairedBoundarySide request other segment within owner sheet) :
    Winding.Polygon.Basic.chainRaw curve.polynomial start side.ownerPath.vertices =
      Winding.Polygon.Basic.chainRaw curve.polynomial start
        (side.covered.subdivision.requests.map fun entry => segment.pointAt entry.endpoint.parameter) := by
  rw [side.ownerPath_vertices]
  have equal := PreparedSubdivisionTrace.PreparedTraceBudget.traceVertices_chainRaw segment firstEndpoint
    side.covered.subdivision.requests
  simpa only [firstEndpoint, Geometry.ClearPath.ClearSegment.pointAt_zero] using equal

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- The retained side owner path has the original clear segment's raw winding.

Combines the stored subdivision endpoint and request-winding identities without replacing its actual owner path. -/
theorem ownerPath_winding_original
  (side : PairedBoundarySide request other segment within owner sheet) :
    Winding.Polygon.Basic.chainRaw curve.polynomial start side.ownerPath.vertices =
      PreparedPathWinding.ClearSegment.rawWinding segment := by
  rw [side.ownerPath_winding]
  have equality := PreparedPathWinding.Subdivision.requests_winding side.covered.subdivision
  rw [side.covered.endpoint_eq] at equality
  simpa only [firstEndpoint, lastEndpoint, Geometry.ClearPath.ClearSegment.pointAt_zero,
    PreparedPathWinding.ClearSegment.rawWinding, Path.Segment.segment] using equality

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide.PairedBoundarySide
