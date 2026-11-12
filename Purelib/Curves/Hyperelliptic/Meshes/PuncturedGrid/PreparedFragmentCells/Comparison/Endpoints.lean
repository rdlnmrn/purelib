module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison
public import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.UniformPreparedRequests.Face
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Tactic.Ring

/-! # Retained upper Point, Query and entry of one original regular leaf

The existing lower regular request supplies its exact face models and
analytic split. Three new original factories acquire the upper endpoint
once. Finite nearest-sign propagation through the retained split identifies
its original sheet without preparing another runtime domain or primitive.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {target : Rational}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}

namespace PrimitiveFragmentCell

/-- The actual upper leaf endpoint is a bounded fraction of its unchanged original parent. -/
theorem upper_inside (fragment : PrimitiveFragmentCell axes parent partition interval) :
    (0 : Rational) ≤ interval.upper ∧ interval.upper ≤ 1 :=
  let bounds := partition.interval_bounds fragment.member
  ⟨bounds.1.trans interval.ordered.le, bounds.2⟩

namespace RegularRequest

variable {domains : FaceDomainBank frames faces.regulars} {request : LocalRequest parent count target}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}

/-- Three complete upper-endpoint results on the existing lower request and its same selected face models.

The Point belongs to fragment.last; the Query retains interval.upper on
the original parent. The entry acquisition classifies that same Point
Owner. Each subtype keeps its original whole factory equation, while the
lower Point, acquisition, domain and split remain in retained unchanged.
-/
@[expose] def UpperEndpoint (retained : RegularRequest domains request fragment location) :=
  Σ sample : {value : ContinuedNeighborhood.Point request.neighborhood fragment.last //
    value = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.last
      (fragment.request_endpoints request).2},
  {value : PreparedEdge.Query parent.edge interval.upper fragment.upper_inside //
    value = PreparedEdge.Query.build parent.edge interval.upper fragment.upper_inside} ×
  {value : Entry.Acquisition retained.compared.shared.models (fragment.regular_endpoints location).2
      sample.val.owner //
    value = Entry.Acquisition.build retained.compared.shared.models (fragment.regular_endpoints location).2
      sample.val.owner}

namespace UpperEndpoint

/-- Acquire one upper Point, one original upper Query and one same-model entry acquisition, in that order. -/
def build (retained : RegularRequest domains request fragment location) : retained.UpperEndpoint :=
  let sample := ContinuedNeighborhood.Point.acquire request.neighborhood fragment.last
    (fragment.request_endpoints request).2
  let query := PreparedEdge.Query.build parent.edge interval.upper fragment.upper_inside
  let acquired := Entry.Acquisition.build retained.compared.shared.models (fragment.regular_endpoints location).2
    sample.owner
  ⟨⟨sample, rfl⟩, ⟨query, rfl⟩, ⟨acquired, rfl⟩⟩

variable {retained : RegularRequest domains request fragment location}
variable (upper : retained.UpperEndpoint)

/-- Read the whole upper Point acquired at this literal retained fragment endpoint. -/
def sample : ContinuedNeighborhood.Point request.neighborhood fragment.last := upper.1.val

/-- Read the whole original Query at the literal upper fraction of this same parent. -/
def query : PreparedEdge.Query parent.edge interval.upper fragment.upper_inside := upper.2.1.val

/-- Read the complete upper entry acquisition on the SAME face models and SAME upper Point Owner. -/
def acquired : Entry.Acquisition retained.compared.shared.models (fragment.regular_endpoints location).2
    upper.sample.owner := upper.2.2.val

/-- The entire upper Point is the original point-acquisition factory result. -/
theorem sample_eq : upper.sample = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.last
    (fragment.request_endpoints request).2 := by
  exact upper.1.property

/-- The entire upper Query is the original query-construction factory result. -/
theorem query_eq : upper.query = PreparedEdge.Query.build parent.edge interval.upper fragment.upper_inside := by
  exact upper.2.1.property

/-- The entire upper acquisition is the original entry factory on the same models and same Point Owner. -/
theorem acquired_eq : upper.acquired = Entry.Acquisition.build retained.compared.shared.models
    (fragment.regular_endpoints location).2 upper.sample.owner := by
  exact upper.2.2.property

/-- Compare the retained upper Query Owner to the same acquired upper Point through their original request seed.

The endpoint equation reindexes the physical point only. Both original
Owners and refinement witnesses remain distinct; no Query or Point is
built by this comparison. Its symmetric witness gives the reverse relation.
-/
def queryEquivalent : NamedEquivalent (ownerName upper.query.owner) upper.sample.certificate.value.name :=
  NamedEquivalent.transport upper.query.name_eq rfl
    (request.retainedQueryEquivalent interval.upper fragment.upper_inside upper.query
      fragment.last_eq.symm (fragment.request_endpoints request).2 upper.sample)

/-- The upper acquisition selects the lower retained face sheet by finite sign propagation on the same split.

All auxiliary cell/domain reads are erased proof data. The two original
lazy face-domain thunks are not forced into a new runtime cache, and the
old materialized domain and primitive split remain unchanged.
-/
theorem sheet_eq : retained.compared.acquired.entry.sheet = upper.acquired.entry.sheet := by
  let oldDomain := retained.compared.domain
  let oldLocation := EnteredPaths.PeriodDomain.locate oldDomain fragment.last
    (fragment.regular_endpoints location).2
  let newDomain := retained.compared.shared.domain upper.acquired.entry.sheet
  let newLocation := EnteredPaths.PeriodDomain.locate newDomain fragment.last
    (fragment.regular_endpoints location).2
  let oldCell := oldDomain.patch.transported.cell oldLocation.column oldLocation.row
  let newCell := newDomain.patch.transported.cell newLocation.column newLocation.row
  have oldNearest := EndpointSheets.FaceModels.split_finish_nearest oldDomain.patch differential
    retained.compared.split request.neighborhood
    (fragment.request_endpoints request).1 (fragment.request_endpoints request).2
    (fun column row inside => request.face_nearest interval.lower fragment.lower_inside fragment.first_eq.symm
      (fragment.request_endpoints request).1 retained.sample retained.compared.acquired
      (oldDomain.patch.transported.cell column row) inside 0 2)
    oldLocation.column oldLocation.row oldLocation.inside
  have newNearest := EndpointSheets.FaceModels.Entry.point_nearest upper.sample upper.acquired.entry
    newCell differential newLocation.inside (fragment.request_endpoints request).2
  have reverseNearest (first last : Canonical)
      (near : normSq (first - last) ≤ normSq (first + last)) :
      normSq (last - first) ≤ normSq (last + first) := by
    rewrite [Data.Gaussian.Norm.Bounds.normSq_sub_symm last first,
      show last + first = first + last by ring1]
    exact near
  have common := ((Model.overlapRefine oldCell.model) 0).nearest_trans
    ((Model.overlapRefine request.neighborhood.base.model) 0) ((Model.overlapRefine newCell.model) 0)
    oldLocation.inside (request.neighborhood.box_refines.contains (fragment.request_endpoints request).2)
    newLocation.inside oldNearest (reverseNearest _ _ newNearest)
  exact EndpointSheets.FaceModels.sheet_eq_of_nearest oldCell newCell differential
    oldLocation.inside newLocation.inside common

end UpperEndpoint

end RegularRequest

end PrimitiveFragmentCell

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
