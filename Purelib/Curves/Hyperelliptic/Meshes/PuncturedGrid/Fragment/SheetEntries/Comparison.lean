module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison
public import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Paths.RectangularSegmentSplitting

/-! # Original SheetEntry from one retained lower regular request

The selected face location, original lower Point/acquisition/domain/split
and one retained lower Query are inputs. Whole face-cache equality reindexes
the existing dependent fields; no Point, Entry, domain or split is rebuilt.
The same retained Query and Point derive the original signed root relation.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  renaming RegularPrimitiveFragment -> RegularFragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularLocation)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {differential : Differential genus}
variable {axes : PrimitiveAxes base.bank.grid} {parent : CenteredEdge curve differential}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval} {target : Rational}

/-- Read the same selected regular payload with only its cell index changed to the literal located fragment. -/
@[expose] def lowerLocation (fragment : RegularFragment axes parent partition interval)
    (sameCell : fragment.face.geometry.cell = fragment.located.cell) :
    RegularLocation base.faces.regulars fragment.located.cell :=
  fragment.face.located.castCell sameCell

/-- The complete existing lower Point/acquisition/domain/split cache on this exact selected face. -/
@[expose] def LowerRequest (fragment : RegularFragment axes parent partition interval)
    (sameCell : fragment.face.geometry.cell = fragment.located.cell)
    (domains : FaceDomainBank frames base.faces.regulars) (request : LocalRequest parent count target) :=
  PrimitiveFragmentCell.RegularRequest domains request fragment.located (lowerLocation fragment sameCell)

/-- The three original dependent SheetEntry fields transported together along a whole face-cache equality. -/
private def Fields (fragment : RegularFragment axes parent partition interval)
    (request : LocalRequest parent count target)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.first)
    (shared : FaceDomains frames fragment.face.located.face) :=
  Σ entry : Entry shared.models fragment.located.first sample.owner,
  Σ domain : {value : PeriodDomain shared.models entry.sheet // value = shared.domain entry.sheet},
  SegmentSplit domain.val.cuts fragment.located.first fragment.located.last

/-- Reindex the original dependent field tuple without evaluating its face-cache factory again. -/
private def castFields {fragment : RegularFragment axes parent partition interval}
    {request : LocalRequest parent count target}
    {sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.first}
    {first last : FaceDomains frames fragment.face.located.face} (equal : first = last)
    (retained : Fields fragment request sample first) : Fields fragment request sample last :=
  Eq.mp (congrArg (Fields fragment request sample) equal) retained

/-- Whole-cache transport retains the original Entry value heterogeneously. -/
private theorem castFields_entry_heq {fragment : RegularFragment axes parent partition interval}
    {request : LocalRequest parent count target}
    {sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.first}
    {first last : FaceDomains frames fragment.face.located.face} (equal : first = last)
    (retained : Fields fragment request sample first) : HEq (castFields equal retained).1 retained.1 := by
  cases equal
  rfl

/-- Whole-cache transport retains the original PeriodDomain value heterogeneously. -/
private theorem castFields_domain_heq {fragment : RegularFragment axes parent partition interval}
    {request : LocalRequest parent count target}
    {sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.first}
    {first last : FaceDomains frames fragment.face.located.face} (equal : first = last)
    (retained : Fields fragment request sample first) :
    HEq (castFields equal retained).2.1.val retained.2.1.val := by
  cases equal
  rfl

/-- Whole-cache transport retains the original ordered SegmentSplit value heterogeneously. -/
private theorem castFields_split_heq {fragment : RegularFragment axes parent partition interval}
    {request : LocalRequest parent count target}
    {sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.first}
    {first last : FaceDomains frames fragment.face.located.face} (equal : first = last)
    (retained : Fields fragment request sample first) : HEq (castFields equal retained).2.2 retained.2.2 := by
  cases equal
  rfl

/-- An original SheetEntry retaining the same lower Point, selected Entry, whole domain and ordered split. -/
@[expose] def FromRegularRequest (fragment : RegularFragment axes parent partition interval)
    (sameCell : fragment.face.geometry.cell = fragment.located.cell)
    (domains : FaceDomainBank frames base.faces.regulars) (request : LocalRequest parent count target)
    (lower : LowerRequest fragment sameCell domains request) :=
  {assigned : SheetEntry fragment domains request //
    assigned.sample = lower.sample ∧
    HEq assigned.entry lower.compared.acquired.entry ∧
    HEq assigned.domain lower.compared.domain ∧
    HEq assigned.split lower.compared.split}

/-- Attach the complete retained lower regular request using one supplied original lower Query.

The signed relation is derived from the Query and Point's common prepared
seed. A cast of the whole dependent field tuple preserves the already
cached Entry, domain and split; no lookup, classification or acquisition
is run by this adapter. The same retained Query/sample comparison is now
kept as actual data, rather than erased by a Nonempty proof wrapper. -/
def ofRegularRequest (fragment : RegularFragment axes parent partition interval)
    (sameCell : fragment.face.geometry.cell = fragment.located.cell)
    (domains : FaceDomainBank frames base.faces.regulars) (request : LocalRequest parent count target)
    (lower : LowerRequest fragment sameCell domains request)
    (query : PreparedEdge.Query parent.edge interval.lower fragment.located.lower_inside) :
    FromRegularRequest fragment sameCell domains request lower := by
  let sample := lower.sample
  let compared := lower.compared
  have sharedEq : compared.shared = domainCache fragment domains := compared.shared_eq
  let retained : Fields fragment request sample compared.shared :=
    ⟨compared.acquired.entry, ⟨compared.domain, compared.domain_eq⟩, compared.split⟩
  let aligned := castFields sharedEq retained
  let original := request.retainedQueryEquivalent interval.lower fragment.located.lower_inside query
    fragment.located.first_eq.symm (fragment.located.request_endpoints request).1 sample
  let assigned : SheetEntry fragment domains request :=
    ⟨sample, aligned.1, fragment.located.lower_inside, original,
      aligned.2.1.val, aligned.2.1.property, aligned.2.2⟩
  exact ⟨assigned, rfl, castFields_entry_heq sharedEq retained,
    castFields_domain_heq sharedEq retained, castFields_split_heq sharedEq retained⟩

/-- Retain the whole lower regular-request factory, one new lower Query and the resulting SheetEntry adapter cache. -/
@[expose] def Acquisition (fragment : RegularFragment axes parent partition interval)
    (sameCell : fragment.face.geometry.cell = fragment.located.cell)
    (domains : FaceDomainBank frames base.faces.regulars) (request : LocalRequest parent count target) :=
  Σ lower : {value : LowerRequest fragment sameCell domains request //
    value = PrimitiveFragmentCell.RegularRequest.build domains request fragment.located
      (lowerLocation fragment sameCell)},
  Σ query : PreparedEdge.Query parent.edge interval.lower fragment.located.lower_inside,
  {assigned : FromRegularRequest fragment sameCell domains request lower.val //
    assigned = ofRegularRequest fragment sameCell domains request lower.val query}

/-- Acquire the original lower regular cache and one lower Query once, then retain the cache-preserving adapter. -/
def acquire (fragment : RegularFragment axes parent partition interval)
    (sameCell : fragment.face.geometry.cell = fragment.located.cell)
    (domains : FaceDomainBank frames base.faces.regulars) (request : LocalRequest parent count target) :
    Acquisition fragment sameCell domains request :=
  let lower := PrimitiveFragmentCell.RegularRequest.build domains request fragment.located
    (lowerLocation fragment sameCell)
  let query := PreparedEdge.Query.build parent.edge interval.lower fragment.located.lower_inside
  let assigned := ofRegularRequest fragment sameCell domains request lower query
  ⟨⟨lower, rfl⟩, query, ⟨assigned, rfl⟩⟩

namespace Acquisition

variable {fragment : RegularFragment axes parent partition interval}
variable {sameCell : fragment.face.geometry.cell = fragment.located.cell}
variable {domains : FaceDomainBank frames base.faces.regulars} {request : LocalRequest parent count target}
variable (retained : Acquisition fragment sameCell domains request)

/-- Read the entire once-built lower Point/acquisition/domain/split result. -/
@[expose] def lower : LowerRequest fragment sameCell domains request := retained.1.val

/-- Read the same original lower Query, with its complete direct Owner factory certificate. -/
@[expose] def query : PreparedEdge.Query parent.edge interval.lower fragment.located.lower_inside := retained.2.1

/-- Read the retained adapter result with all four original-cache readbacks. -/
@[expose] def assigned : FromRegularRequest fragment sameCell domains request retained.lower := retained.2.2.val

/-- Read the original nominal SheetEntry on the same supplied fragment, domains and numerical request. -/
@[expose] def sheetEntry : SheetEntry fragment domains request := retained.assigned.val

/-- The attached SheetEntry retains the exact original lower Point value. -/
theorem sample_eq : retained.sheetEntry.sample = retained.lower.sample := retained.assigned.property.1

/-- The attached SheetEntry retains the complete selected lower Entry under the whole face-cache transport. -/
theorem entry_heq : HEq retained.sheetEntry.entry retained.lower.compared.acquired.entry :=
  retained.assigned.property.2.1

/-- The attached SheetEntry retains the whole original selected PeriodDomain. -/
theorem domain_heq : HEq retained.sheetEntry.domain retained.lower.compared.domain :=
  retained.assigned.property.2.2.1

/-- The attached SheetEntry retains the whole original ordered analytic split. -/
theorem split_heq : HEq retained.sheetEntry.split retained.lower.compared.split := retained.assigned.property.2.2.2

/-- The entire lower cache is exactly the original regular-request factory on these same inputs. -/
theorem lower_eq : retained.lower = PrimitiveFragmentCell.RegularRequest.build domains request fragment.located
    (lowerLocation fragment sameCell) := retained.1.property

/-- The adapter result is its exact factory on the same stored lower cache and same stored Query. -/
theorem assigned_eq : retained.assigned =
    ofRegularRequest fragment sameCell domains request retained.lower retained.query := retained.2.2.property

end Acquisition
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

end
