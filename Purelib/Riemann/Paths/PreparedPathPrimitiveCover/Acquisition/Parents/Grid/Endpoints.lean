module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Grid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Occurrence
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Position
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Exact endpoint occurrences in the retained paid grid fragments

Each endpoint reader retains the original partition endpoint and finite
first-occurrence scan, then reads the complete fragment and regular/hole
payload from the same cached spines. No midpoint lookup, classification,
root selection or primitive evaluation is repeated.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents.GridFragments

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (LocatedCell RegularLocation)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable {sheet : Fin 2} {count : Nat}
variable {retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) request}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {axes : PrimitiveAxes base.bank.grid}
variable {parents : Acquisition.Segment.Parents basis sheet count retained}
variable {first : (Cuts.Ambient curve).Contains start} {last : (Cuts.Ambient curve).Contains finish}
variable (cached : GridFragments base axes parents first last) (index : Fin parents.covered.parents.length)

/-- Either literal endpoint parameter belongs to the same retained parent partition. -/
theorem endpoint_member (high : Bool) :
    (if high then (1 : Rational) else 0) ∈ (cached.splits.partitionAt index).coordinates := by
  cases high with
  | false => exact (cached.splits.partitionAt index).lower_mem
  | true => exact (cached.splits.partitionAt index).upper_mem

/-- The original endpoint scan and the same whole located/classified fragment at its bounded occurrence.

The endpoint bit concerns parameter zero or one, even for a physically
stationary parent. The payload subtype retains the original complete cell
and its regular or hole outcome together, with one whole reader equation.
-/
@[expose] def Endpoint (high : Bool) :=
  let partition := cached.splits.partitionAt index
  let fragments := cached.locations.fragmentsAt index
  let classifications := cached.locations.classificationsAt base.faces cached.classifications index
  Σ selected : {value : AxisPartition.Endpoint partition (if high then 1 else 0) //
      value = partition.endpoint (if high then 1 else 0) (cached.endpoint_member index high)},
  Σ found : {value : {position : Fin partition.intervals.length //
      partition.intervals[position.val]'position.isLt = selected.val.interval} //
      value = PreparedAxisPartitions.Interval.position selected.val.interval
        partition.intervals selected.val.member},
    {value : (Σ fragment : PrimitiveFragmentCell axes (parents.covered.parents[index.val]'index.isLt)
        partition (partition.intervals[found.val.val.val]'found.val.val.isLt),
      LocatedCell base.faces.regulars base.faces.holes fragment.cell) //
      value = ⟨fragments.fragmentAt found.val.val,
        fragments.classificationAt base.faces classifications found.val.val⟩}

/-- Select one endpoint occurrence and read its old fragment and outcome once.

Only finite interval metadata is selected here. Both original dependent
spines supply their existing payloads; no grid or face lookup runs.
-/
def endpoint (high : Bool) : cached.Endpoint index high :=
  let partition := cached.splits.partitionAt index
  let selected := partition.endpoint (if high then 1 else 0) (cached.endpoint_member index high)
  let found := PreparedAxisPartitions.Interval.position selected.interval partition.intervals selected.member
  let fragments := cached.locations.fragmentsAt index
  let classifications := cached.locations.classificationsAt base.faces cached.classifications index
  let fragment := fragments.fragmentAt found.val
  let classification := fragments.classificationAt base.faces classifications found.val
  ⟨⟨selected, rfl⟩, ⟨found, rfl⟩, ⟨⟨fragment, classification⟩, rfl⟩⟩

/-- The complete original endpoint factory equation, proved inside its owner module. -/
private theorem packaged_endpoint_eq (high : Bool) : cached.endpoint index high =
    (show cached.Endpoint index high from
      let partition := cached.splits.partitionAt index
      let selected := partition.endpoint (if high then 1 else 0) (cached.endpoint_member index high)
      let found := PreparedAxisPartitions.Interval.position selected.interval partition.intervals selected.member
      let fragments := cached.locations.fragmentsAt index
      let classifications := cached.locations.classificationsAt base.faces cached.classifications index
      let fragment := fragments.fragmentAt found.val
      let classification := fragments.classificationAt base.faces classifications found.val
      ⟨⟨selected, rfl⟩, ⟨found, rfl⟩, ⟨⟨fragment, classification⟩, rfl⟩⟩) := by
  rfl

/-- The complete endpoint factory reads the same cached parent and interval payloads. -/
theorem endpoint_eq (high : Bool) : cached.endpoint index high =
    (show cached.Endpoint index high from
      let partition := cached.splits.partitionAt index
      let selected := partition.endpoint (if high then 1 else 0) (cached.endpoint_member index high)
      let found := PreparedAxisPartitions.Interval.position selected.interval partition.intervals selected.member
      let fragments := cached.locations.fragmentsAt index
      let classifications := cached.locations.classificationsAt base.faces cached.classifications index
      let fragment := fragments.fragmentAt found.val
      let classification := fragments.classificationAt base.faces classifications found.val
      ⟨⟨selected, rfl⟩, ⟨found, rfl⟩, ⟨⟨fragment, classification⟩, rfl⟩⟩) :=
  packaged_endpoint_eq cached index high

namespace Endpoint

variable {cached index} {high : Bool} (located : cached.Endpoint index high)

/-- Read the complete original partition endpoint, including its retained lower/upper role. -/
abbrev selected : AxisPartition.Endpoint (cached.splits.partitionAt index)
    (if high then 1 else 0) := located.1.val

/-- Read the whole original first-occurrence result on the unchanged interval list. -/
abbrev position : {position : Fin (cached.splits.partitionAt index).intervals.length //
    (cached.splits.partitionAt index).intervals[position.val]'position.isLt = located.selected.interval} :=
  located.2.1.val

/-- Read the identical old fragment, retaining its actual cell, endpoints and original interval index. -/
abbrev fragment : PrimitiveFragmentCell axes (parents.covered.parents[index.val]'index.isLt)
    (cached.splits.partitionAt index)
    ((cached.splits.partitionAt index).intervals[located.position.val.val]'located.position.val.isLt) :=
  located.2.2.val.1

/-- Read the identical old regular-face or branch-hole payload for this same fragment. -/
abbrev classification : LocatedCell base.faces.regulars base.faces.holes located.fragment.cell :=
  located.2.2.val.2

/-- The selected endpoint is the original finite neighbor operation on the same partition. -/
theorem selected_eq : located.selected = (cached.splits.partitionAt index).endpoint
    (if high then 1 else 0) (cached.endpoint_member index high) := located.1.property

/-- The bounded interval reader retains the complete original fragment/classification pair. -/
theorem payload_eq : (⟨located.fragment, located.classification⟩ :
    Σ fragment : PrimitiveFragmentCell axes (parents.covered.parents[index.val]'index.isLt)
      (cached.splits.partitionAt index)
      ((cached.splits.partitionAt index).intervals[located.position.val.val]'located.position.val.isLt),
      LocatedCell base.faces.regulars base.faces.holes fragment.cell) =
    ⟨(cached.locations.fragmentsAt index).fragmentAt located.position.val,
      (cached.locations.fragmentsAt index).classificationAt base.faces
        (cached.locations.classificationsAt base.faces cached.classifications index) located.position.val⟩ :=
  located.2.2.property

/-- The retained metadata position is the whole original first-occurrence reader result. -/
theorem position_eq : located.position = PreparedAxisPartitions.Interval.position located.selected.interval
    (cached.splits.partitionAt index).intervals located.selected.member := located.2.1.property

/-- The selected bounded interval is the complete original endpoint interval. -/
theorem interval_eq :
    (cached.splits.partitionAt index).intervals[located.position.val.val]'located.position.val.isLt =
      located.selected.interval := located.position.property

/-- An outer endpoint has its actual lower or upper role in every proper retained partition. -/
theorem role_eq : located.selected.high = high := by
  have bounds := (cached.splits.partitionAt index).interval_bounds located.selected.member
  have endpoint := located.selected.endpoint_eq
  cases high with
  | false =>
      cases same : located.selected.high with
      | false => rfl
      | true =>
          rewrite [same] at endpoint
          have strict : (0 : Rational) < located.selected.interval.upper :=
            bounds.1.trans_lt located.selected.interval.ordered
          exact (strict.ne endpoint.symm).elim
  | true =>
      cases same : located.selected.high with
      | false =>
          rewrite [same] at endpoint
          have strict : located.selected.interval.lower < (1 : Rational) :=
            located.selected.interval.ordered.trans_le bounds.2
          exact (strict.ne endpoint).elim
      | true => rfl

/-- The zero-role occurrence retains an interval whose actual lower fraction is zero.

The equation follows from the original endpoint bit and interval lookup.
It concerns the parameter even when the physical edge is stationary.
-/
theorem lower_eq_zero (located : cached.Endpoint index false) :
    ((cached.splits.partitionAt index).intervals[located.position.val.val]'located.position.val.isLt).lower = 0 := by
  have endpoint := located.selected.endpoint_eq
  rewrite [located.role_eq] at endpoint
  exact (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower)
    located.interval_eq).trans endpoint

/-- The unit-role occurrence retains an interval whose actual upper fraction is one. -/
theorem upper_eq_one (located : cached.Endpoint index true) :
    ((cached.splits.partitionAt index).intervals[located.position.val.val]'located.position.val.isLt).upper = 1 := by
  have endpoint := located.selected.endpoint_eq
  rewrite [located.role_eq] at endpoint
  exact (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper)
    located.interval_eq).trans endpoint

/-- The zero-endpoint fragment starts at the unchanged physical parent point, including stationary parents. -/
theorem first_eq (located : cached.Endpoint index false) :
    located.fragment.first = (parents.covered.parents[index.val]'index.isLt).edge.point 0 := by
  have endpoint := located.selected.endpoint_eq
  rewrite [located.role_eq] at endpoint
  have lower := (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.lower)
    located.interval_eq).trans endpoint
  exact located.fragment.first_eq.trans
    (congrArg (parents.covered.parents[index.val]'index.isLt).edge.point lower)

/-- The unit-endpoint fragment finishes at the independent original parent endpoint. -/
theorem last_eq (located : cached.Endpoint index true) :
    located.fragment.last = (parents.covered.parents[index.val]'index.isLt).edge.point 1 := by
  have endpoint := located.selected.endpoint_eq
  rewrite [located.role_eq] at endpoint
  have upper := (congrArg (fun interval : PreparedAxisPartitions.Interval => interval.upper)
    located.interval_eq).trans endpoint
  exact located.fragment.last_eq.trans
    (congrArg (parents.covered.parents[index.val]'index.isLt).edge.point upper)

end Endpoint

end Acquisition.Segment.Parents.GridFragments

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
