module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.Physical
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Data.Int.Arithmetic
import Purelib.Polynomial.Winding.Polygon.Stationary
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Tactic.QuotientFreeOmega

/-! # Signed regular-face incidence of the SAME Point-owned physical crop

The original cleared segment is restricted to the retained fragment.
The stored source, moving and target path keeps both actual stationary
joins. Clear-face winding derives its Entry incidence, without another
classification, Query, Point or physical preparation. This is not an
indexed mesh deformation, primitive normalization or homology certificate.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

namespace PrimitiveFragmentCell.RegularRequest.UpperEndpoint.SampleCrop

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Polynomial.Winding.Polygon.Stationary (chainRaw_cons_self)
open Purelib.Riemann.Branches.PreparedSheetContinuation (parameterAt parameterAt_inside pointAt_parameterAt)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (segment_winding windingPotential)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearSegment (rawWinding)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace (CropComparisons)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {requestTarget : Rational}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval} {domains : FaceDomainBank frames faces.regulars}
variable {request : LocalRequest parent count requestTarget}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {retained : RegularRequest domains request fragment location} {upper : retained.UpperEndpoint}
variable {physical : CropComparisons parent interval.lower interval.upper fragment.lower_inside fragment.upper_inside}
variable {query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside}
variable (cropped : upper.SampleCrop physical query)

/-- The literal stored stationary/moving/stationary path has its actual open clear-face winding.

The moving edge is the original segment restricted at the actual lower
and upper fractions. Both stationary joins remain in the path; only their
zero winding is removed using the nonzero actual endpoint parameters.
No path or Owner identity is inferred from coincident coordinates.
-/
theorem winding
    (vertices : (physical.2 query upper.query).vertices = [parent.edge.point interval.upper]) :
    chainRaw curve.polynomial fragment.first cropped.path.vertices =
      windingPotential curve.polynomial location.face.cell.box fragment.last -
        windingPotential curve.polynomial location.face.cell.box fragment.first := by
  let lower := parameterAt parent.edge.left parent.edge.request interval.lower
  let lastParameter := parameterAt parent.edge.left parent.edge.request interval.upper
  have lowerInside := parameterAt_inside parent.edge.left parent.edge.request parent.edge.ordered
    interval.lower fragment.lower_inside
  have upperInside := parameterAt_inside parent.edge.left parent.edge.request parent.edge.ordered
    interval.upper fragment.upper_inside
  have firstEq : parent.edge.segment.pointAt lower = fragment.first :=
    (pointAt_parameterAt parent.edge.segment parent.edge.within parent.edge.left parent.edge.request
      interval.lower).trans fragment.first_eq.symm
  have lastEq : parent.edge.segment.pointAt lastParameter = fragment.last :=
    (pointAt_parameterAt parent.edge.segment parent.edge.within parent.edge.left parent.edge.request
      interval.upper).trans fragment.last_eq.symm
  let restricted := parent.edge.segment.restrict parent.edge.within lower lastParameter lowerInside upperInside
  let segment : ClearSegment curve.polynomial parent.edge.ambient fragment.first fragment.last :=
    (restricted.castStart firstEq).castFinish lastEq
  have moving : chainRaw curve.polynomial fragment.first [fragment.last] =
      windingPotential curve.polynomial location.face.cell.box fragment.last -
        windingPotential curve.polynomial location.face.cell.box fragment.first := by
    change rawWinding segment + 0 = _
    rewrite [Int.add_zero]
    exact segment_winding location.face.clearance (BranchIsolation.degreePositive curve) segment
      (fragment.regular_endpoints location).1 (fragment.regular_endpoints location).2
  have actualVertices : cropped.path.vertices = [fragment.first, fragment.last, fragment.last] := by
    let terminal := OwnerPath.cons
      (OwnerTracePath.OwnerLink.stationary curve.polynomial fragment.last cropped.target)
      (OwnerPath.nil fragment.last upper.sample.owner)
    have projected := congrArg
      (fun path : OwnerPath curve.polynomial fragment.first retained.sample.owner
        fragment.last upper.sample.owner => path.vertices) cropped.path_eq
    change cropped.path.vertices = fragment.first :: (cropped.queryPath.append terminal).vertices at projected
    have tail := OwnerPath.append_vertices cropped.queryPath terminal
    have replaced : cropped.queryPath.vertices ++ terminal.vertices = [fragment.last, fragment.last] := by
      rewrite [cropped.queryPath_vertices vertices]
      rfl
    exact projected.trans (congrArg (fun points : List Canonical => fragment.first :: points)
      (tail.trans replaced))
  rewrite [actualVertices, chainRaw_cons_self curve.polynomial fragment.first retained.sample.owner.parameterNonzero]
  change (Polynomial.Dense.Gaussian.Path.Segment.segment curve.polynomial fragment.first
    fragment.last).doubledWinding + chainRaw curve.polynomial fragment.last [fragment.last] = _
  rewrite [chainRaw_cons_self curve.polynomial fragment.last upper.sample.owner.parameterNonzero]
  exact moving

/-- The SAME physical crop and retained through-anchor path have their actual common open winding.

Both route windings are the face-potential differences of their actual
endpoints. This compares their winding integers only: no indexed mesh
support, oriented deformation, homology or primitive equality follows.
-/
theorem winding_eq_throughAnchor
    (vertices : (physical.2 query upper.query).vertices = [parent.edge.point interval.upper]) :
    chainRaw curve.polynomial fragment.first cropped.path.vertices =
      chainRaw curve.polynomial fragment.first upper.throughAnchor.vertices := by
  have backward := ClearBoxPathWinding.Route.winding location.face.clearance (BranchIsolation.degreePositive curve)
    retained.compared.acquired.inward (fragment.regular_endpoints location).1
  have forward := ClearBoxPathWinding.Route.winding location.face.clearance (BranchIsolation.degreePositive curve)
    upper.acquired.outward location.face.cell.box.contains_anchor
  have replacement : chainRaw curve.polynomial fragment.first upper.throughAnchor.vertices =
      windingPotential curve.polynomial location.face.cell.box fragment.last -
        windingPotential curve.polynomial location.face.cell.box fragment.first := by
    rewrite [upper.throughAnchor_winding, backward, forward]
    omega0
  exact (cropped.winding vertices).trans replacement.symm

/-- Propagate the original lower Entry to the actual upper Point along the SAME stored crop path.

Only the erased reachability proof is extended. The retained sheet and
both supplied Point Owners stay unchanged; no return route, selection,
entry acquisition, Query or Point producer is executed by this operation.
-/
def entry (vertices : (physical.2 query upper.query).vertices = [parent.edge.point interval.upper]) :
    Entry retained.compared.shared.models fragment.last upper.sample.owner :=
  ⟨retained.compared.acquired.entry.sheet,
    retained.compared.acquired.entry.reached.append ⟨cropped.path, cropped.winding vertices⟩⟩

/-- The propagated Entry retains the exact lower selected sheet, independently of repeated endpoints. -/
theorem entry_sheet (vertices : (physical.2 query upper.query).vertices = [parent.edge.point interval.upper]) :
    (cropped.entry vertices).sheet = retained.compared.acquired.entry.sheet := by
  rfl

include cropped in
/-- The actual cropped path and the existing upper acquisition reach the same original face sheet.

Uniqueness is applied to two Entries of the literal SAME upper Point
Owner in the retained regular face. It does not identify arbitrary Owners,
primitive constants, a mesh walk or a canonical cycle.
-/
theorem upper_sheet (vertices : (physical.2 query upper.query).vertices = [parent.edge.point interval.upper]) :
    retained.compared.acquired.entry.sheet = upper.acquired.entry.sheet :=
  (entry_sheet (cropped := cropped) vertices).symm.trans
    ((cropped.entry vertices).sheet_unique upper.acquired.entry (fragment.regular_endpoints location).2)

end PrimitiveFragmentCell.RegularRequest.UpperEndpoint.SampleCrop

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
