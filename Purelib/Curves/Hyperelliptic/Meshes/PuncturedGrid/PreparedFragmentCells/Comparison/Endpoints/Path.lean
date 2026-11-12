module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Original lower-to-upper OwnerPath through one retained regular-face anchor

The lower return connector and upper forward connector keep their actual
transport rows and supplied Point Owners. The derived sheet equality only
reindexes their common anchor Owner. This new path is not identified with
an arbitrary-fraction subpath of the original paid physical Trace.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

namespace PrimitiveFragmentCell.RegularRequest.UpperEndpoint

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open Purelib.Riemann.RootContinuation.RootPathTransport
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {target : Rational}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {domains : FaceDomainBank frames faces.regulars}
variable {request : LocalRequest parent count target}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {retained : RegularRequest domains request fragment location}
variable (upper : retained.UpperEndpoint)

/-- Connect the two SAME acquired Point Owners through their common retained regular-face anchor.

The lower return and upper forward paths retain their original order.
Only upper.sheet_eq transports the upper path's starting frame Owner to
the identical lower frame occurrence. No Point, Query, route, frame or
entry acquisition is executed here; the original connector joins are new.
-/
def throughAnchor : OwnerPath curve.polynomial fragment.first retained.sample.owner
    fragment.last upper.sample.owner :=
  let outward := upper.acquired.anchorToOwner
  let same := congrArg (fun sheet => retained.compared.shared.models.frame.owners sheet) upper.sheet_eq.symm
  retained.sampleToAnchor.append (outward.reindexOwners same rfl)

/-- The entire leaf path is its literal lower-return/upper-forward connector composition. -/
theorem throughAnchor_eq : upper.throughAnchor =
    retained.sampleToAnchor.append (upper.acquired.anchorToOwner.reindexOwners
      (congrArg (fun sheet => retained.compared.shared.models.frame.owners sheet) upper.sheet_eq.symm) rfl) := by
  rfl

/-- The new path retains both complete ordered connector vertex lists, including repeated stationary vertices. -/
theorem throughAnchor_vertices : upper.throughAnchor.vertices =
    retained.sampleToAnchor.vertices ++ upper.acquired.anchorToOwner.vertices := by
  let outward := upper.acquired.anchorToOwner
  let same := congrArg (fun sheet => retained.compared.shared.models.frame.owners sheet) upper.sheet_eq.symm
  have appended := OwnerPath.append_vertices retained.sampleToAnchor (outward.reindexOwners same rfl)
  have preserved := OwnerPath.reindexOwners_vertices same rfl outward
  have complete := appended.trans (congrArg
    (fun vertices : List Canonical => retained.sampleToAnchor.vertices ++ vertices) preserved)
  exact complete

/-- The leaf path retains the sum of the two actual open route windings. -/
theorem throughAnchor_winding :
    chainRaw curve.polynomial fragment.first upper.throughAnchor.vertices =
      rawWinding retained.compared.acquired.inward.path + rawWinding upper.acquired.outward.path := by
  let outward := upper.acquired.anchorToOwner
  let same := congrArg (fun sheet => retained.compared.shared.models.frame.owners sheet) upper.sheet_eq.symm
  have vertices := OwnerPath.reindexOwners_vertices same rfl outward
  have upperWinding := (congrArg (chainRaw curve.polynomial location.face.cell.box.anchor) vertices).trans
    upper.acquired.anchorToOwner_winding
  have appended := OwnerPath.append_winding retained.sampleToAnchor (outward.reindexOwners same rfl)
  have firstWinding := congrArg (fun value : Int => value +
    chainRaw curve.polynomial location.face.cell.box.anchor (outward.reindexOwners same rfl).vertices)
    retained.sampleToAnchor_winding
  have lastWinding := congrArg
    (fun value : Int => rawWinding retained.compared.acquired.inward.path + value) upperWinding
  have complete := appended.trans (firstWinding.trans lastWinding)
  exact complete

/-- Compare actual lower and upper Queries to their respective SAME retained Point Owners.

The lower Query is supplied as its original cache because the lower
RegularRequest does not store one. The upper Query is already retained.
Both endpoint equations and both actual request refinements are consumed;
neither Query nor Point is built, identified or replaced by this operation.
-/
def queryComparisons (firstQuery : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside) :
    NamedEquivalent (ownerName firstQuery.owner) retained.sample.certificate.value.name ×
      NamedEquivalent (ownerName upper.query.owner) upper.sample.certificate.value.name :=
  let first := NamedEquivalent.transport firstQuery.name_eq rfl
    (request.retainedQueryEquivalent interval.lower fragment.lower_inside firstQuery
      fragment.first_eq.symm (fragment.request_endpoints request).1 retained.sample)
  ⟨first, upper.queryEquivalent⟩

end PrimitiveFragmentCell.RegularRequest.UpperEndpoint

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
