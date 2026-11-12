module

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Comparison
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Point.Transport
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Readings.UniformPreparedRequests.Query

/-! # Actual final samples and consecutive fragment owner joins

The original assigned face domain and split remain unchanged. A retained
upper Query compares a real finish Point with the parent root; the original
endpoint propagation certifies its assigned face sheet. Consecutive original
partition intervals then give an actual cross-face join to the next stored
incoming Point. Coordinate transport reindexes whole Points and Entries;
the root comparison comes from the two retained signed query relations.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  renaming RegularPrimitiveFragment -> RegularFragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count : Nat} {curve : HyperellipticCurve genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {differential : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve differential} {cuts : List Rational}
variable {partition : AxisPartition 0 1 cuts} {interval : PreparedAxisPartitions.Interval}
variable {fragment : RegularFragment axes parent partition interval}
variable {domains : FaceDomainBank frames base.faces.regulars}
variable {target : Rational} {request : LocalRequest parent count target}

/-- The actual finish Point has the same retained face sheet as the original incoming entry.

Finite sign propagation uses the original analytic split and request
neighborhood. Only the reachability proof is produced; no new face models,
domain, selector or primitive bank is acquired.
-/
def finishEntry (assigned : SheetEntry fragment domains request)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last) :
    Entry (domainCache fragment domains).models fragment.located.last sample.owner :=
  ⟨assigned.entry.sheet, EndpointSheets.SheetEntry.finish_point_reached assigned sample⟩

/-- The finish entry retains exactly the original assigned sheet. -/
theorem finishEntry_sheet (assigned : SheetEntry fragment domains request)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last) :
    (finishEntry assigned sample).sheet = assigned.entry.sheet := by
  unfold finishEntry
  rfl

/-- One whole finish Point and Query, their signed comparison, and its same-sheet Entry.

The Point retains its original acquisition factory. The Query itself owns
its complete direct-query factory. The remaining two subtypes retain the
exact comparison and Entry operations on those same supplied caches.
-/
@[expose] def Finish (assigned : SheetEntry fragment domains request) :=
  Σ sample : {value : ContinuedNeighborhood.Point request.neighborhood fragment.located.last //
    value = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.last
      (fragment.located.request_endpoints request).2},
  Σ query : PreparedEdge.Query parent.edge interval.upper fragment.located.upper_inside,
  {value : NamedEquivalent (parent.edge.rootName interval.upper fragment.located.upper_inside)
      sample.val.certificate.value.name //
    value = request.retainedQueryEquivalent interval.upper fragment.located.upper_inside query
      fragment.located.last_eq.symm (fragment.located.request_endpoints request).2 sample.val} ×
  {value : Entry (domainCache fragment domains).models fragment.located.last sample.val.owner //
    value = finishEntry assigned sample.val}

/-- Retain a given original upper Point and Query and derive their actual comparison and face Entry.

The Point factory identifies this supplied value with its original request
acquisition. Neither Point nor Query is run here. The original parent
comparison and assigned-sheet endpoint certificate operate on those inputs.
-/
def finishFrom (assigned : SheetEntry fragment domains request)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last)
    (sampleFactory : sample = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.last
      (fragment.located.request_endpoints request).2)
    (query : PreparedEdge.Query parent.edge interval.upper fragment.located.upper_inside) : Finish assigned :=
  let equivalent := request.retainedQueryEquivalent interval.upper fragment.located.upper_inside query
    fragment.located.last_eq.symm (fragment.located.request_endpoints request).2 sample
  let entry := finishEntry assigned sample
  ⟨⟨sample, sampleFactory⟩, query, ⟨equivalent, rfl⟩, ⟨entry, rfl⟩⟩

namespace Finish

/-- Acquire a finish Point and upper Query once on the same original request, then retain their endpoint evidence. -/
def build (assigned : SheetEntry fragment domains request) : Finish assigned :=
  let sample := ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.last
    (fragment.located.request_endpoints request).2
  let query := PreparedEdge.Query.build parent.edge interval.upper fragment.located.upper_inside
  finishFrom assigned sample rfl query

variable {assigned : SheetEntry fragment domains request} (retained : Finish assigned)

/-- Read the complete actual finish Point. -/
@[expose] def sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last := retained.1.val

/-- Read the same whole original upper Query. -/
@[expose] def query : PreparedEdge.Query parent.edge interval.upper fragment.located.upper_inside := retained.2.1

/-- Read the actual signed original-parent comparison to this finish Point. -/
@[expose] def original : NamedEquivalent
    (parent.edge.rootName interval.upper fragment.located.upper_inside) retained.sample.certificate.value.name :=
  retained.2.2.1.val

/-- Read the actual finish Point's Entry in the unchanged original face model bank. -/
@[expose] def entry : Entry (domainCache fragment domains).models fragment.located.last retained.sample.owner :=
  retained.2.2.2.val

/-- The complete finish Point is its retained original factory value. -/
theorem sample_eq : retained.sample = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.last
    (fragment.located.request_endpoints request).2 := retained.1.property

/-- The comparison is exactly the original given-Query request comparison on these caches. -/
theorem original_eq : retained.original = request.retainedQueryEquivalent interval.upper fragment.located.upper_inside
    retained.query fragment.located.last_eq.symm (fragment.located.request_endpoints request).2 retained.sample :=
  retained.2.2.1.property

/-- The whole finish Entry is the original same-sheet endpoint operation. -/
theorem entry_eq : retained.entry = finishEntry assigned retained.sample := retained.2.2.2.property

/-- The retained finish Entry selects the unchanged incoming sheet. -/
theorem entry_sheet : retained.entry.sheet = assigned.entry.sheet :=
  (congrArg Entry.sheet retained.entry_eq).trans (finishEntry_sheet assigned retained.sample)

end Finish

/-- The given-finish adapter retains the complete supplied Point value. -/
theorem finishFrom_sample (assigned : SheetEntry fragment domains request)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last)
    (sampleFactory : sample = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.last
      (fragment.located.request_endpoints request).2)
    (query : PreparedEdge.Query parent.edge interval.upper fragment.located.upper_inside) :
    (finishFrom assigned sample sampleFactory query).sample = sample := by
  unfold finishFrom
  rfl

/-- The given-finish adapter retains the complete supplied Query value. -/
theorem finishFrom_query (assigned : SheetEntry fragment domains request)
    (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last)
    (sampleFactory : sample = ContinuedNeighborhood.Point.acquire request.neighborhood fragment.located.last
      (fragment.located.request_endpoints request).2)
    (query : PreparedEdge.Query parent.edge interval.upper fragment.located.upper_inside) :
    (finishFrom assigned sample sampleFactory query).query = query := by
  unfold finishFrom
  rfl

/-- Reuse a complete original regular-request upper cache without another Point, Query or entry acquisition.

The given lower-to-SheetEntry adapter and UpperEndpoint keep all original
lower and upper acquisition data. This operation derives only the signed
comparison and assigned-sheet Entry for the same retained upper Point.
-/
def finishFromUpper {sameCell : fragment.face.geometry.cell = fragment.located.cell}
    {lower : LowerRequest fragment sameCell domains request}
    (assigned : FromRegularRequest fragment sameCell domains request lower) (upper : lower.UpperEndpoint) :
    Finish assigned.val :=
  finishFrom assigned.val upper.sample upper.sample_eq upper.query

section Seams

variable {nextInterval : PreparedAxisPartitions.Interval}
variable {nextFragment : RegularFragment axes parent partition nextInterval}

/-- Equal original upper and lower parameters identify the actual two physical fragment endpoints. -/
theorem endpoint_eq (same : interval.upper = nextInterval.lower) :
    fragment.located.last = nextFragment.located.first :=
  fragment.located.last_eq.trans ((congrArg parent.edge.point same).trans nextFragment.located.first_eq.symm)

/-- Reindex the whole next incoming Point at the identical preceding finish coordinate. -/
def incomingPoint (next : SheetEntry nextFragment domains request)
    (same : interval.upper = nextInterval.lower) :
    ContinuedNeighborhood.Point request.neighborhood fragment.located.last :=
  ContinuedNeighborhood.Point.castPoint (endpoint_eq (fragment := fragment) (nextFragment := nextFragment) same)
    next.sample

/-- The reindexed incoming Point is the complete given next Point, including its original Owner. -/
theorem incomingPoint_heq (next : SheetEntry nextFragment domains request)
    (same : interval.upper = nextInterval.lower) :
    HEq (incomingPoint (fragment := fragment) next same) next.sample := by
  unfold incomingPoint
  exact ContinuedNeighborhood.Point.castPoint_heq (endpoint_eq (fragment := fragment) same) next.sample

/-- The incoming reindexing retains its whole original Owner, with only its dependent parameter changed. -/
theorem incomingPoint_owner_heq (next : SheetEntry nextFragment domains request)
    (same : interval.upper = nextInterval.lower) :
    HEq next.sample.owner (incomingPoint (fragment := fragment) next same).owner := by
  unfold incomingPoint
  have castOwner {first last : Canonical} (equal : first = last)
      (sample : ContinuedNeighborhood.Point request.neighborhood last) :
      HEq sample.owner (ContinuedNeighborhood.Point.castPoint equal sample).owner := by
    cases equal
    rfl
  exact castOwner (endpoint_eq (fragment := fragment) same) next.sample

/-- Transport the same next Entry to the identical coordinate with its complete original Point Owner.

This operation changes dependent point indices only. The original selected
sheet and face reachability witness are transported together. It does not
construct or compare any new root Owner.
-/
def incomingEntry (next : SheetEntry nextFragment domains request)
    (same : interval.upper = nextInterval.lower) :
    Entry (domainCache nextFragment domains).models fragment.located.last
      (incomingPoint (fragment := fragment) next same).owner :=
  next.entry.castPoint (endpoint_eq (fragment := fragment) same).symm
    (incomingPoint_owner_heq (fragment := fragment) next same)

/-- The whole next Entry, including its original reachability certificate, survives the exact point transport. -/
theorem incomingEntry_heq (next : SheetEntry nextFragment domains request)
    (same : interval.upper = nextInterval.lower) :
    HEq (incomingEntry (fragment := fragment) next same) next.entry := by
  unfold incomingEntry
  exact next.entry.castPoint_heq (endpoint_eq (fragment := fragment) same).symm
    (incomingPoint_owner_heq (fragment := fragment) next same)

/-- The whole transported next Entry keeps exactly its original face sheet. -/
theorem incomingEntry_sheet (next : SheetEntry nextFragment domains request)
    (same : interval.upper = nextInterval.lower) :
    (incomingEntry (fragment := fragment) next same).sheet = next.entry.sheet := by
  unfold incomingEntry
  exact next.entry.castPoint_sheet (endpoint_eq (fragment := fragment) same).symm
    (incomingPoint_owner_heq (fragment := fragment) next same)

/-- Compose the actual finish and next incoming comparisons through their original same-parent seam.

The fraction equality transports the original parent root name. The Point
coordinate equality transports only the next whole sample name. Signed
root agreement itself uses the two actual retained query comparisons.
-/
def incomingEquivalent {assigned : SheetEntry fragment domains request} (finish : Finish assigned)
    (next : SheetEntry nextFragment domains request) (same : interval.upper = nextInterval.lower) :
    NamedEquivalent finish.sample.certificate.value.name
      (incomingPoint (fragment := fragment) next same).certificate.value.name := by
  let parentNames := parent.edge.rootName_eq (firstInside := fragment.located.upper_inside)
    (lastInside := next.fractionInside) same
  let nextFromParent := NamedEquivalent.transport parentNames.symm rfl next.original
  let original := finish.original.symm.trans nextFromParent
  unfold incomingPoint
  exact NamedEquivalent.transport rfl
    (ContinuedNeighborhood.Point.castPoint_name (endpoint_eq (fragment := fragment) same) next.sample).symm original

/-- The actual incoming Point, Entry, signed comparison and retained OwnerJoin on a same-parent seam.

Whole-value readbacks retain the original next Point transport and Entry.
The join is built from the same executable comparison. Both domains and
all primitive banks remain in their unchanged input SheetEntries.
-/
@[expose] def AtSeam {assigned : SheetEntry fragment domains request} (finish : Finish assigned)
    (next : SheetEntry nextFragment domains request) (same : interval.upper = nextInterval.lower) :=
  {values : (sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last) ×
      Entry (domainCache nextFragment domains).models fragment.located.last sample.owner ×
      NamedEquivalent finish.sample.certificate.value.name sample.certificate.value.name ×
      OwnerJoin finish.sample.owner sample.owner //
    values.1 = incomingPoint (fragment := fragment) next same ∧
    HEq values.2.1 (incomingEntry (fragment := fragment) next same) ∧
    values.2.1.sheet = next.entry.sheet ∧
    HEq values.2.2.1 (incomingEquivalent finish next same) ∧
    values.2.2.2 = OwnerJoin.acquire finish.sample.owner values.1.owner values.2.2.1}

section

attribute [local irreducible] incomingPoint incomingEntry incomingEquivalent

/-- Construct the actual cross-face endpoint join once using only the retained same-parent fragment caches. -/
def atSeam {assigned : SheetEntry fragment domains request} (finish : Finish assigned)
    (next : SheetEntry nextFragment domains request) (same : interval.upper = nextInterval.lower) :
    AtSeam finish next same :=
  let sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last :=
    incomingPoint (fragment := fragment) next same
  let entry : Entry (domainCache nextFragment domains).models fragment.located.last sample.owner :=
    incomingEntry (fragment := fragment) next same
  let equivalent : NamedEquivalent finish.sample.certificate.value.name sample.certificate.value.name :=
    incomingEquivalent finish next same
  let joined : OwnerJoin finish.sample.owner sample.owner :=
    OwnerJoin.acquire finish.sample.owner sample.owner equivalent
  ⟨⟨sample, entry, equivalent, joined⟩, rfl, HEq.rfl,
    incomingEntry_sheet (fragment := fragment) next same, HEq.rfl, rfl⟩

end

namespace AtSeam

variable {assigned : SheetEntry fragment domains request} {finish : Finish assigned}
variable {next : SheetEntry nextFragment domains request} {same : interval.upper = nextInterval.lower}
variable (retained : AtSeam finish next same)

/-- Read the whole reindexed original next incoming Point. -/
@[expose] def sample : ContinuedNeighborhood.Point request.neighborhood fragment.located.last := retained.val.1

/-- Read its actual original next-face Entry, preserving the genuine reachability proof. -/
@[expose] def entry : Entry (domainCache nextFragment domains).models fragment.located.last retained.sample.owner :=
  retained.val.2.1

/-- Read the signed root comparison used by this actual join. -/
@[expose] def equivalent : NamedEquivalent finish.sample.certificate.value.name
    retained.sample.certificate.value.name :=
  retained.val.2.2.1

/-- Read the actual two-Owner finite-tail join. -/
@[expose] def joined : OwnerJoin finish.sample.owner retained.sample.owner := retained.val.2.2.2

/-- The entire next incoming Point is its original exact-coordinate transport. -/
theorem sample_eq : retained.sample = incomingPoint (fragment := fragment) next same := retained.property.1

/-- The whole next Entry is retained through that same physical-index transport. -/
theorem entry_heq : HEq retained.entry (incomingEntry (fragment := fragment) next same) := retained.property.2.1

/-- The whole original next Entry remains the actual incoming Entry before coordinate reindexing. -/
theorem original_entry_heq : HEq retained.entry next.entry :=
  retained.entry_heq.trans (incomingEntry_heq (fragment := fragment) next same)

/-- The complete given next Point remains the actual incoming Point before coordinate reindexing. -/
theorem original_sample_heq : HEq retained.sample next.sample :=
  (heq_of_eq retained.sample_eq).trans (incomingPoint_heq (fragment := fragment) next same)

/-- The original next face-sheet index is unchanged. -/
theorem entry_sheet : retained.entry.sheet = next.entry.sheet := retained.property.2.2.1

/-- The actual root comparison is the same composition of both original query relations. -/
theorem equivalent_heq : HEq retained.equivalent (incomingEquivalent finish next same) :=
  retained.property.2.2.2.1

/-- The whole retained join uses those two actual Owners and the same signed comparison. -/
theorem joined_eq : retained.joined = OwnerJoin.acquire finish.sample.owner retained.sample.owner retained.equivalent :=
  retained.property.2.2.2.2

end AtSeam

end Seams

section Consecutive

variable (position : Nat) (later : position + 1 < partition.intervals.length)
variable {fragment : RegularFragment axes parent partition
  (partition.intervals[position]'(Nat.lt_trans (Nat.lt_succ_self _) later))}
variable {nextFragment : RegularFragment axes parent partition (partition.intervals[position + 1]'later)}

/-- Join consecutive original partition occurrences using their internally derived exact common endpoint.

The original interval-list indices distinguish repeated and stationary
physical occurrences. The retained partition's own consecutive law provides
the seam; no root comparison or primitive-offset equation is assumed.
-/
def consecutive {assigned : SheetEntry fragment domains request} (finish : Finish assigned)
    (next : SheetEntry nextFragment domains request) :
    AtSeam finish next (partition.consecutive position later) :=
  atSeam finish next (partition.consecutive position later)

/-- The consecutive occurrence producer is its original intrinsic common-endpoint seam construction. -/
theorem consecutive_eq_atSeam {assigned : SheetEntry fragment domains request} (finish : Finish assigned)
    (next : SheetEntry nextFragment domains request) :
    consecutive position later finish next = atSeam finish next (partition.consecutive position later) := by
  unfold consecutive
  rfl

end Consecutive

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

end
