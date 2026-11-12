module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.Path
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # An actual contained query crop on the two retained regular-fragment Point Owners

The lower query is supplied and the upper query is already retained.
Two new original stationary joins attach their certified contained moving
crop to the unchanged lower and upper Points. No primitive normalization,
path homotopy or canonical comparison is asserted by endpoint agreement.
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
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace (CropComparisons)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName_castOwnerParameter)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)

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
variable {retained : RegularRequest domains request fragment location}
variable (upper : retained.UpperEndpoint)

/-- Reindex the SAME lower query Owner to the literal lower fragment endpoint. -/
def sourceOwner (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside) :
    Owner (curve.polynomial.eval fragment.first) :=
  castOwnerParameter (congrArg curve.polynomial.eval fragment.first_eq.symm) query.owner

/-- Reindex the SAME retained upper query Owner to the literal upper fragment endpoint. -/
def targetOwner : Owner (curve.polynomial.eval fragment.last) :=
  castOwnerParameter (congrArg curve.polynomial.eval fragment.last_eq.symm) upper.query.owner

/-- Exact endpoint reindexing preserves the lower Query Owner's original root name. -/
private theorem sourceOwner_name
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside) :
    ownerName (sourceOwner (fragment := fragment) query) = ownerName query.owner := by
  unfold sourceOwner
  exact ownerRootName_castOwnerParameter
    (congrArg curve.polynomial.eval fragment.first_eq.symm) query.owner

/-- Exact endpoint reindexing preserves the retained upper Query Owner's original root name. -/
private theorem targetOwner_name : ownerName upper.targetOwner = ownerName upper.query.owner := by
  unfold targetOwner
  exact ownerRootName_castOwnerParameter
    (congrArg curve.polynomial.eval fragment.last_eq.symm) upper.query.owner

/-- Reindex and reverse the supplied lower comparison to the same retained Point and Query Owners. -/
def sourceEquivalent
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside)
    (compared : NamedEquivalent (ownerName query.owner) retained.sample.certificate.value.name) :
    NamedEquivalent (ownerName retained.sample.owner) (ownerName (sourceOwner (fragment := fragment) query)) := by
  let shifted : NamedEquivalent (ownerName (sourceOwner (fragment := fragment) query))
      retained.sample.certificate.value.name :=
    NamedEquivalent.transport (sourceOwner_name query).symm rfl compared
  change NamedEquivalent retained.sample.certificate.value.name
    (ownerName (sourceOwner (fragment := fragment) query))
  exact shifted.symm

/-- Reindex the supplied upper comparison to the same retained Query and Point Owners. -/
def targetEquivalent
    (compared : NamedEquivalent (ownerName upper.query.owner) upper.sample.certificate.value.name) :
    NamedEquivalent (ownerName upper.targetOwner) (ownerName upper.sample.owner) := by
  change NamedEquivalent (ownerName upper.targetOwner) upper.sample.certificate.value.name
  exact NamedEquivalent.transport upper.targetOwner_name.symm rfl compared

/-- Consume the original crop once and change only its exact endpoint and whole Owner indices. -/
def queryCrop
    (physical : CropComparisons parent interval.lower interval.upper fragment.lower_inside fragment.upper_inside)
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside) :
    OwnerPath curve.polynomial fragment.first (sourceOwner (fragment := fragment) query)
      fragment.last upper.targetOwner :=
  let actual := physical.2 query upper.query
  actual.castEndpoints fragment.first_eq.symm fragment.last_eq.symm
    (castOwnerParameter_heq (congrArg curve.polynomial.eval fragment.first_eq.symm) query.owner).symm
    (castOwnerParameter_heq (congrArg curve.polynomial.eval fragment.last_eq.symm) upper.query.owner).symm

/-- Exact endpoint/Owner transports preserve the supplied moving crop's one terminal occurrence. -/
theorem queryCrop_vertices
    {physical : CropComparisons parent interval.lower interval.upper fragment.lower_inside fragment.upper_inside}
    {query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside}
    (vertices : (physical.2 query upper.query).vertices = [parent.edge.point interval.upper]) :
    (upper.queryCrop physical query).vertices = [fragment.last] := by
  unfold queryCrop
  rewrite [OwnerPath.castEndpoints_vertices]
  exact vertices.trans (congrArg (fun point : Canonical => [point]) fragment.last_eq.symm)

/-- Five complete retained results and their exact original factories on the supplied physical crop and Queries.

The carriers are independent: one comparison pair, one query-owned crop,
two genuine new stationary joins and the final Point-owned composition.
One subtype of products retains all five values and their defining laws.
The old Point/Entry/domain/split and both original Queries are unchanged.
-/
@[expose] def SampleCrop
    (physical : CropComparisons parent interval.lower interval.upper fragment.lower_inside fragment.upper_inside)
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside) :=
  { values :
      (NamedEquivalent (ownerName query.owner) retained.sample.certificate.value.name ×
        NamedEquivalent (ownerName upper.query.owner) upper.sample.certificate.value.name) ×
      OwnerPath curve.polynomial fragment.first (sourceOwner (fragment := fragment) query)
        fragment.last upper.targetOwner ×
      OwnerJoin retained.sample.owner (sourceOwner (fragment := fragment) query) ×
      OwnerJoin upper.targetOwner upper.sample.owner ×
      OwnerPath curve.polynomial fragment.first retained.sample.owner fragment.last upper.sample.owner //
    values.1 = upper.queryComparisons query ∧
    values.2.1 = upper.queryCrop physical query ∧
    values.2.2.1 = OwnerJoin.acquire retained.sample.owner (sourceOwner (fragment := fragment) query)
      (sourceEquivalent query values.1.1) ∧
    values.2.2.2.1 = OwnerJoin.acquire upper.targetOwner upper.sample.owner
      (upper.targetEquivalent values.1.2) ∧
    values.2.2.2.2 = OwnerPath.cons
      (OwnerLink.stationary curve.polynomial fragment.first values.2.2.1)
      (values.2.1.append (OwnerPath.cons
        (OwnerLink.stationary curve.polynomial fragment.last values.2.2.2.1)
        (OwnerPath.nil fragment.last upper.sample.owner))) }

namespace SampleCrop

/-- Compare the retained Queries once, construct their crop once, and acquire both actual endpoint joins once. -/
def build
    (physical : CropComparisons parent interval.lower interval.upper fragment.lower_inside fragment.upper_inside)
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside) : upper.SampleCrop physical query :=
  let compared := upper.queryComparisons query
  let cropped := upper.queryCrop physical query
  let source := OwnerJoin.acquire retained.sample.owner (sourceOwner (fragment := fragment) query)
    (sourceEquivalent query compared.1)
  let target := OwnerJoin.acquire upper.targetOwner upper.sample.owner
    (upper.targetEquivalent compared.2)
  let path := OwnerPath.cons (OwnerLink.stationary curve.polynomial fragment.first source)
    (cropped.append (OwnerPath.cons (OwnerLink.stationary curve.polynomial fragment.last target)
      (OwnerPath.nil fragment.last upper.sample.owner)))
  ⟨⟨compared, cropped, source, target, path⟩, rfl, rfl, rfl, rfl, rfl⟩

variable {upper}
variable {physical : CropComparisons parent interval.lower interval.upper fragment.lower_inside fragment.upper_inside}
variable {query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside}
variable (cropped : upper.SampleCrop physical query)

/-- Read both whole actual endpoint comparisons without another query or Point comparison. -/
def compared :
    NamedEquivalent (ownerName query.owner) retained.sample.certificate.value.name ×
      NamedEquivalent (ownerName upper.query.owner) upper.sample.certificate.value.name := cropped.val.1

/-- Read the whole query-owned physical crop under its exact fragment endpoint transports. -/
def queryPath : OwnerPath curve.polynomial fragment.first (sourceOwner (fragment := fragment) query)
    fragment.last upper.targetOwner := cropped.val.2.1

/-- Read the actual new source join from the retained lower Point to its same queried Owner. -/
def source : OwnerJoin retained.sample.owner (sourceOwner (fragment := fragment) query) := cropped.val.2.2.1

/-- Read the actual new target join from the retained upper Query to the same upper Point. -/
def target : OwnerJoin upper.targetOwner upper.sample.owner := cropped.val.2.2.2.1

/-- Read the complete Point-owned path, preserving the source, moving and target order. -/
def path : OwnerPath curve.polynomial fragment.first retained.sample.owner fragment.last upper.sample.owner :=
  cropped.val.2.2.2.2

/-- The whole retained comparison pair is the original same-query comparison factory. -/
theorem compared_eq : cropped.compared = upper.queryComparisons query := cropped.property.1

/-- The entire retained moving crop is the same actual selected physical operation on both original Queries. -/
theorem queryPath_eq : cropped.queryPath = upper.queryCrop physical query := cropped.property.2.1

/-- The whole source join retains the actual original acquisition and signed comparison from the cached pair. -/
theorem source_eq : cropped.source = OwnerJoin.acquire retained.sample.owner (sourceOwner (fragment := fragment) query)
    (sourceEquivalent query cropped.compared.1) :=
  cropped.property.2.2.1

/-- The whole target join retains its original acquisition and the same cached upper comparison. -/
theorem target_eq : cropped.target = OwnerJoin.acquire upper.targetOwner upper.sample.owner
    (upper.targetEquivalent cropped.compared.2) :=
  cropped.property.2.2.2.1

/-- The full final path is the literal stationary/moving/stationary composition of those same retained results. -/
theorem path_eq : cropped.path = OwnerPath.cons
    (OwnerLink.stationary curve.polynomial fragment.first cropped.source)
    (cropped.queryPath.append (OwnerPath.cons
      (OwnerLink.stationary curve.polynomial fragment.last cropped.target)
      (OwnerPath.nil fragment.last upper.sample.owner))) := cropped.property.2.2.2.2

/-- The stored query-owned path keeps the actual selected crop's literal one-vertex geometry. -/
theorem queryPath_vertices
    (vertices : (physical.2 query upper.query).vertices = [parent.edge.point interval.upper]) :
    cropped.queryPath.vertices = [fragment.last] :=
  (congrArg (fun path : OwnerPath curve.polynomial fragment.first (sourceOwner (fragment := fragment) query)
    fragment.last upper.targetOwner => path.vertices) cropped.queryPath_eq).trans
      (upper.queryCrop_vertices vertices)

end SampleCrop

end PrimitiveFragmentCell.RegularRequest.UpperEndpoint

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
