module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Faces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Realization
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.GridLiftedTriangleStars
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Polygon.Stokes

/-! # Actual signed face-word coordinates on its retained cut boundary

The same stored WordRoute supplies the path and signed face correction.
The existing coordinate and integral-spanning factories consume that path
and the supplied retained cut geometry and normal form; every physical
coordinate survives.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Riemann.Meshes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)
open Purelib.LinearAlgebra.Alternating

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}
variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {frame : Paths.Frame parameter} {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {meshBase : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}

namespace Execution.Cache.Lines.DetourCache.Signed.Faces

variable {lines : Lines execution elimination clearances}
variable {numericBase : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}
variable {cached : DetourCache lines numericBase}
variable {reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
  WindingOneLoop (Paths.polynomial parameter) point}
variable {prepared : Signed cached reference} {lifted : LiftedPuncturedGrid meshBase}
variable {sameGrid : cached.val.1 = meshBase.bank.grid}
variable (retained : Faces cached reference prepared lifted sameGrid)
variable (routed : SewingRetraction.WordRoute lifted.mesh.triangulation.faces
  lifted.cutPolygon.patch.boundary retained.word)

/-- Compute and retain the original integer cut coordinates of this actual signed word's supplied boundary route.

The original WordCoordinates builder consumes the cached alphabet and the
route's same ordered path. Its signed letters, complete physical generator totals and exact
projection certificate remain in that same existing carrier.
-/
def coordinates (geometry : LiftedPuncturedGrid.Cut lifted) :
    WordCoordinates lifted.cutBoundaryWord.alphabet routed.path :=
  geometry.coordinates routed.path routed.supported

/-- The original coordinate factory uses the same retained boundary path and support certificate. -/
theorem coordinates_eq (geometry : LiftedPuncturedGrid.Cut lifted) : retained.coordinates routed geometry =
    WordCoordinates.build lifted.cutBoundaryWord.alphabet routed.path (by
      rewrite [lifted.cutPolygon.patch.cut.boundary_eq]
      exact routed.supported) :=
  geometry.coordinates_eq routed.path routed.supported

variable (rows : WordCoordinates lifted.cutBoundaryWord.alphabet routed.path)

/-- Produce the original integral-spanning certificate on the actual cached integer row and supplied normal form.

The same lifted mesh supplies its orientation, nonloop and vertex-star
certificates. Closure comes from the original signed word through this
same retained route. The original producer retains both the paired
coefficients and all physical-boundary coordinates.
-/
def spanning (geometry : LiftedPuncturedGrid.Cut lifted)
    (integral : Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : NormalForm integral.paired raw) : SpanningCoordinates integral rows.totals :=
  geometry.spanning routed.path rows integral normal (routed.endpoints retained.closed) routed.supported

/-- Evaluate this actual signed word through its retained integer boundary row with the complete signed face term. -/
theorem coordinates_value (value : OrientedEdge lifted.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value retained.word =
      WordCoordinates.combine rows.totals (fun index => value (VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index))) +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value routed.correction := by
  rewrite [routed.value_eq value anti, rows.value_eq value anti]
  rfl

/-- Evaluate the same actual signed word through its original spanning certificate without discarding physical terms.

Both the integral-pairing combination and the remaining physical-boundary
row use the supplied certificate of these exact cached coordinates. The
same route contributes its entire signed face correction.
-/
theorem spanning_value {integral : Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (span : SpanningCoordinates integral rows.totals)
    (value : OrientedEdge lifted.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value retained.word =
      WordCoordinates.combine span.coefficients (fun index =>
        WordCoordinates.combine (integral.paired index) (fun column => value (VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      WordCoordinates.combine span.physical (fun column => value (VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value routed.correction := by
  rewrite [retained.coordinates_value routed rows value anti, SpanningCoordinates.value_eq span]
  rfl

end Execution.Cache.Lines.DetourCache.Signed.Faces

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
