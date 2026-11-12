module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Classification
public import Purelib.Riemann.Readings.UniformPreparedRequests.Face.Pieces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Retained regular/hole comparisons on the actual ordered parent leaves

The source requests, partitions, located cells and classifications are
inputs. Regular leaves acquire one new Point only when requested by the
new producer; ofSample reuses an already supplied Point. Hole outcomes
retain the exact original HoleLocation as an unresolved detour case.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation HoleLocation LocatedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit SegmentPiece)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {target : Rational}

section Partitions

variable {cuts : List Rational}
variable {partition : Geometry.Rectangle.AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}

namespace PrimitiveFragmentCell

/-- The literal lower leaf endpoint is an admitted fraction of its original retained parent. -/
theorem lower_inside (fragment : PrimitiveFragmentCell axes parent partition interval) :
    (0 : Rational) ≤ interval.lower ∧ interval.lower ≤ 1 :=
  let bounds := partition.interval_bounds fragment.member
  ⟨bounds.1, interval.ordered.le.trans bounds.2⟩

/-- The same original request neighborhood contains both endpoints of this retained leaf. -/
theorem request_endpoints (fragment : PrimitiveFragmentCell axes parent partition interval)
    (request : LocalRequest parent count target) :
    request.neighborhood.box.Contains fragment.first ∧ request.neighborhood.box.Contains fragment.last := by
  rewrite [fragment.first_eq, fragment.last_eq]
  exact PrimitiveSplits.endpoints_inside partition fragment.member request

/-- The retained regular-cell equality places both actual oriented endpoints in that same face. -/
theorem regular_endpoints (fragment : PrimitiveFragmentCell axes parent partition interval)
    (location : RegularLocation faces.regulars fragment.cell) :
    location.face.cell.box.Contains fragment.first ∧ location.face.cell.box.Contains fragment.last := by
  rewrite [location.cell_eq]
  exact ⟨fragment.first_inside, fragment.last_inside⟩

/-- An actual old point sample, shared face-cache lookup, signed entry acquisition, domain and analytic split.

The same PrimitiveFragmentCell and RegularLocation retain the original
parent, interval, face index and both endpoint orders. No complete indexed
grid edge is fabricated. Existing containers retain every new factory once.
-/
@[expose] def RegularComparison (domains : FaceDomainBank frames faces.regulars)
    (request : LocalRequest parent count target) (fragment : PrimitiveFragmentCell axes parent partition interval)
    (location : RegularLocation faces.regulars fragment.cell)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.first) :=
  Σ shared : {value : FaceDomains frames location.face // value = domains.atLocation location},
  Σ acquired : {value : Entry.Acquisition shared.val.models (fragment.regular_endpoints location).1 sample.owner //
    value = Entry.Acquisition.build shared.val.models (fragment.regular_endpoints location).1 sample.owner},
  Σ domain : {value : PeriodDomain shared.val.models acquired.val.entry.sheet //
    value = shared.val.domain acquired.val.entry.sheet},
  {value : SegmentSplit domain.val.cuts fragment.first fragment.last //
    value = SegmentSplit.build domain.val.cuts fragment.first fragment.last
      (domain.val.covers (fragment.regular_endpoints location).1)
      (domain.val.covers (fragment.regular_endpoints location).2)}

namespace RegularComparison

variable {domains : FaceDomainBank frames faces.regulars} {request : LocalRequest parent count target}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {sample : ContinuedNeighborhood.Point request.neighborhood fragment.first}

/-- Attach the supplied complete old Point without running its producer or the original request again. -/
def ofSample (domains : FaceDomainBank frames faces.regulars) (request : LocalRequest parent count target)
    (fragment : PrimitiveFragmentCell axes parent partition interval)
    (location : RegularLocation faces.regulars fragment.cell)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.first) :
    RegularComparison domains request fragment location sample :=
  let shared := domains.atLocation location
  let acquired := Entry.Acquisition.build shared.models (fragment.regular_endpoints location).1 sample.owner
  let domain := shared.domain acquired.entry.sheet
  let split := SegmentSplit.build domain.cuts fragment.first fragment.last
    (domain.covers (fragment.regular_endpoints location).1) (domain.covers (fragment.regular_endpoints location).2)
  ⟨⟨shared, rfl⟩, ⟨acquired, rfl⟩, ⟨domain, rfl⟩, ⟨split, rfl⟩⟩

variable (compared : RegularComparison domains request fragment location sample)

/-- Read the complete original face-cache lookup result retained on this exact regular location. -/
@[expose] def shared : FaceDomains frames location.face := compared.1.val

/-- Read both complete retained transport banks and the exact original selected sample Owner. -/
@[expose] def acquired :
    Entry.Acquisition compared.shared.models (fragment.regular_endpoints location).1 sample.owner :=
  compared.2.1.val

/-- Read the same shared face domain on the genuinely selected full-sheet occurrence. -/
@[expose] def domain : PeriodDomain compared.shared.models compared.acquired.entry.sheet := compared.2.2.1.val

/-- Read the original analytic segment split of these same oriented leaf endpoints. -/
@[expose] def split : SegmentSplit compared.domain.cuts fragment.first fragment.last := compared.2.2.2.val

/-- The entire cached face entry comes from the original bank at this retained location. -/
theorem shared_eq : compared.shared = domains.atLocation location := compared.1.property

/-- The whole interior-entry acquisition belongs to the actual original point sample and retained face cache. -/
theorem acquired_eq : compared.acquired =
    Entry.Acquisition.build compared.shared.models (fragment.regular_endpoints location).1 sample.owner :=
  compared.2.1.property

/-- The retained domain is the exact shared bank domain on the selected sheet. -/
theorem domain_eq : compared.domain = compared.shared.domain compared.acquired.entry.sheet := compared.2.2.1.property

/-- The complete split is the original factory at the same actual endpoints and selected shared domain. -/
theorem split_eq : compared.split = SegmentSplit.build compared.domain.cuts fragment.first fragment.last
    (compared.domain.covers (fragment.regular_endpoints location).1)
    (compared.domain.covers (fragment.regular_endpoints location).2) := compared.2.2.2.property

/-- Read the same whole existing shared numerical cache, preserving its primitive polynomials, anchors and offsets. -/
def data {index : Nat} (numerics : PrimitiveData.FacePrimitiveBank differential index domains) :
    PrimitiveData.DomainPrimitives compared.domain differential index :=
  ((((numerics.get location.index).castFace location.indexed).castDomains compared.shared_eq.symm).atSheet
    compared.acquired.entry.sheet).castDomain compared.domain_eq.symm

/-- Read the original shared face budget with its exact whole-domain transports. -/
def budget {points : List Data.Gaussian.Basic.Canonical} {tolerance : Rational}
    (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains) :
    CommonMeshes.DomainMeshBudget compared.domain differential points tolerance :=
  ((((budgets.get location.index).castFace location.indexed).castDomains compared.shared_eq.symm).atSheet
    compared.acquired.entry.sheet).castDomain compared.domain_eq.symm

/-- Each actual analytic piece pays its original request discrepancy using the same shared numerical primitive cache. -/
theorem piece_le {index : Nat} {points : List Data.Gaussian.Basic.Canonical} {tolerance : Rational}
    (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains)
    (piece : SegmentPiece compared.domain.geometry fragment.first fragment.last)
    (member : piece ∈ compared.split.pieces) :
    normSq (((compared.data numerics).primitives.value piece.column piece.row piece.lastPoint -
      (compared.data numerics).primitives.value piece.column piece.row piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint)) ≤
    request.facePieceCharge compared.domain (compared.budget budgets).bounds piece index :=
  request.facePiece_increment_le sample compared.acquired.entry compared.domain compared.split interval.lower
    fragment.lower_inside fragment.first_eq.symm (fragment.request_endpoints request).1
    (fragment.request_endpoints request).2 (compared.budget budgets).bounds piece member
    (compared.data numerics).primitives

/-- The actual retained local-cell increment list has a derived finite bound against the same old request increment.

This left side remains a list of original per-cell increments. Shared
primitive normalization and canonical period identification are not asserted.
-/
theorem split_le {index : Nat} {points : List Data.Gaussian.Basic.Canonical} {tolerance : Rational}
    (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (compared.split.pieces.map fun piece =>
      (compared.data numerics).primitives.value piece.column piece.row piece.lastPoint -
        (compared.data numerics).primitives.value piece.column piece.row piece.firstPoint) -
      (request.request.model.primitive.value.eval fragment.last -
        request.request.model.primitive.value.eval fragment.first)) ≤
    (compared.split.pieces.length : Rational) * Algebra.FiniteSum.Rational.Squares.coordinateSum
      (compared.split.pieces.map fun piece =>
        request.facePieceCharge compared.domain (compared.budget budgets).bounds piece index) :=
  request.faceSplit_increment_le sample compared.acquired.entry compared.domain compared.split interval.lower
    fragment.lower_inside fragment.first_eq.symm (fragment.request_endpoints request).1
    (fragment.request_endpoints request).2 (compared.budget budgets).bounds (compared.data numerics).primitives

end RegularComparison

/-- A genuinely new regular-leaf Point and its comparison cache, with both full original factory results retained. -/
@[expose] def RegularRequest (domains : FaceDomainBank frames faces.regulars)
    (request : LocalRequest parent count target) (fragment : PrimitiveFragmentCell axes parent partition interval)
    (location : RegularLocation faces.regulars fragment.cell) :=
  Σ sample : {value : ContinuedNeighborhood.Point request.neighborhood fragment.first //
    value = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.first
      (fragment.request_endpoints request).1},
  {value : RegularComparison domains request fragment location sample.val //
    value = RegularComparison.ofSample domains request fragment location sample.val}

namespace RegularRequest

/-- Acquire one new point for this new leaf request, then retain the comparison built from that identical Point. -/
def build (domains : FaceDomainBank frames faces.regulars) (request : LocalRequest parent count target)
    (fragment : PrimitiveFragmentCell axes parent partition interval)
    (location : RegularLocation faces.regulars fragment.cell) : RegularRequest domains request fragment location :=
  let sample := ContinuedNeighborhood.Point.acquire request.neighborhood fragment.first
    (fragment.request_endpoints request).1
  let compared := RegularComparison.ofSample domains request fragment location sample
  ⟨⟨sample, rfl⟩, ⟨compared, rfl⟩⟩

variable {domains : FaceDomainBank frames faces.regulars} {request : LocalRequest parent count target}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable (retained : RegularRequest domains request fragment location)

/-- Read the complete Point acquired once for this original leaf and request. -/
@[expose] def sample : ContinuedNeighborhood.Point request.neighborhood fragment.first := retained.1.val

/-- Read the complete comparison on that identical retained Point. -/
@[expose] def compared : RegularComparison domains request fragment location retained.sample := retained.2.val

/-- The retained Point is the whole original acquisition at the same leaf endpoint. -/
theorem sample_eq : retained.sample = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.first
    (fragment.request_endpoints request).1 := retained.1.property

/-- The stored comparison is the complete factory on that same retained Point. -/
theorem compared_eq : retained.compared =
    RegularComparison.ofSample domains request fragment location retained.sample := retained.2.property

/-- Connect the retained regular-face sheet anchor to this exact already acquired lower Point owner. -/
def anchorToSample : OwnerPath curve.polynomial location.face.cell.box.anchor
    (retained.compared.shared.models.frame.owners retained.compared.acquired.entry.sheet)
    fragment.first retained.sample.owner :=
  retained.compared.acquired.anchorToOwner

/-- The lower sample connector consumes the identical retained interior-entry acquisition. -/
theorem anchorToSample_eq :
    retained.anchorToSample = retained.compared.acquired.anchorToOwner := by rfl

/-- The lower-sample connector preserves its actual cached outward route winding. -/
theorem anchorToSample_winding :
    chainRaw curve.polynomial location.face.cell.box.anchor retained.anchorToSample.vertices =
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding retained.compared.acquired.outward.path :=
  retained.compared.acquired.anchorToOwner_winding

/-- Return from the same retained lower Point owner to its actual selected regular-face sheet anchor. -/
def sampleToAnchor : OwnerPath curve.polynomial fragment.first retained.sample.owner
    location.face.cell.box.anchor
      (retained.compared.shared.models.frame.owners retained.compared.acquired.entry.sheet) :=
  retained.compared.acquired.ownerToAnchor

/-- The return connector consumes the identical cached Point, selections and reverse transport. -/
theorem sampleToAnchor_eq :
    retained.sampleToAnchor = retained.compared.acquired.ownerToAnchor := by rfl

/-- The lower-sample return connector preserves its actual cached inward route winding. -/
theorem sampleToAnchor_winding :
    chainRaw curve.polynomial fragment.first retained.sampleToAnchor.vertices =
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding retained.compared.acquired.inward.path :=
  retained.compared.acquired.ownerToAnchor_winding

end RegularRequest

end PrimitiveFragmentCell

end Partitions

variable {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}

namespace PrimitiveFragmentCells

/-- Actual regular comparisons or literal unresolved original hole payloads, preserving every retained interval. -/
@[expose] def Comparisons (domains : FaceDomainBank frames faces.regulars)
    (request : LocalRequest parent count target) :
    {intervals : List PreparedAxisPartitions.Interval} → (located : PrimitiveFragmentCells axes parent partition
      intervals) → Classifications faces located → Type
  | _, .nil => fun _ => PUnit
  | _, .cons fragment remaining => fun classified =>
      (match classified.1 with
        | .regular location => PrimitiveFragmentCell.RegularRequest domains request fragment location
        | .hole location => {value : HoleLocation faces.holes fragment.cell // value = location}) ×
      Comparisons domains request remaining classified.2
termination_by structural _ located => located

/-- Consume the ordered classifications, acquiring regular leaves once and retaining exact unresolved hole payloads. -/
def compare (domains : FaceDomainBank frames faces.regulars) (request : LocalRequest parent count target) :
    {intervals : List PreparedAxisPartitions.Interval} → (located : PrimitiveFragmentCells axes parent partition
      intervals) → (classified : Classifications faces located) → Comparisons domains request located classified
  | _, .nil => fun _ => PUnit.unit
  | _, .cons fragment remaining => fun classified =>
      match classified with
      | (head, tail) =>
          match head with
          | .regular location =>
              let first := PrimitiveFragmentCell.RegularRequest.build domains request fragment location
              let following := compare domains request remaining tail
              ⟨first, following⟩
          | .hole location =>
              let following := compare domains request remaining tail
              ⟨⟨location, rfl⟩, following⟩
termination_by structural _ located => located

end PrimitiveFragmentCells

namespace LocatedPrimitiveSplits

/-- The original request bank and located parent/interval spine determine every ordered regular/hole comparison. -/
@[expose] def Comparisons (domains : FaceDomainBank frames faces.regulars) :
    {parents : List (CenteredEdge curve differential)} → {splits : PrimitiveSplits axes parents} →
    (located : LocatedPrimitiveSplits axes splits) → (requests : RequestedParents count target parents) →
    Classifications faces located → Type 2
  | _, _, .nil => fun _ _ => PUnit
  | _, _, .cons first remaining => fun requests classified =>
      match requests with
      | .cons request rest =>
          PrimitiveFragmentCells.Comparisons domains request first classified.1 ×
            Comparisons domains remaining rest classified.2
termination_by structural _ _ located => located

/-- Zip the same whole requests with their literal retained parents and cell classifications, without replay. -/
def compare (domains : FaceDomainBank frames faces.regulars) :
    {parents : List (CenteredEdge curve differential)} → {splits : PrimitiveSplits axes parents} →
    (located : LocatedPrimitiveSplits axes splits) → (requests : RequestedParents count target parents) →
    (classified : Classifications faces located) → Comparisons domains located requests classified
  | _, _, .nil => fun _ _ => PUnit.unit
  | _, _, .cons first remaining => fun requests classified =>
      match requests with
      | .cons request rest =>
          let head := PrimitiveFragmentCells.compare domains request first classified.1
          let tail := compare domains remaining rest classified.2
          ⟨head, tail⟩
termination_by structural _ _ located => located

end LocatedPrimitiveSplits

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
