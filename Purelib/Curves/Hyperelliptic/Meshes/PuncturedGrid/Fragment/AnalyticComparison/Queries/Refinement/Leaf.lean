module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.Refinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Queries.Refinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EndpointSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SplitSigns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring

/-! # Actual sample-bearing leaves after a strict retained cut

The new acquisition classifies the SAME direct-query Owner in the SAME
retained face models. The cached query comparison reaches the old Point;
exact endpoint transport preserves that Point and its complete Owner.
The old domain and full lifted side are reindexed only after their actual
sheet equality is derived. No query, Point or old side is acquired again.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry (LiftedSource)
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {mesh : LiftedMesh vertices edges base.faces}
variable {axes : PrimitiveAxes base.bank.grid} {parent : CenteredEdge curve differential}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}
variable {request : LocalRequest parent count target} {assigned : SheetEntry fragment domains request}
variable {index : Nat} {data : DomainPrimitives assigned.domain differential index}
variable {time : Rational} {timeInside : 0 ≤ time ∧ time ≤ 1}
variable {query : PreparedEdge.Query parent.edge time timeInside}
variable {inside : QueryCut.InFragment (interval := interval) (time := time)}
variable {retained : QueryCut.Cache assigned data.primitives query inside}

namespace QueryCut.Cache

/-- The actual query Entry selects the old assigned sheet in these SAME retained face models.

Positive overlap propagates along the selected old analytic piece. The
same retained Point and the actual Entry supply the second comparison;
finite opposite-sheet separation identifies their indices internally.
-/
theorem entry_sheet_eq (retained : QueryCut.Cache assigned data.primitives query inside)
    (entry : QueryEntry (fragment := fragment) (domains := domains) query) :
    assigned.entry.sheet = entry.sheet := by
  let actual := retained.pointEntry (data := data) entry
  let selectedDomain := (domainCache fragment domains).domain actual.sheet
  have pointInside := QueryCut.neighborhood_inside assigned inside
  have faceInside := QueryCut.face_inside (fragment := fragment) inside
  let selectedCell := Face.EnteredPaths.PeriodDomain.locate selectedDomain (parent.edge.point time) faceInside
  let oldCell := assigned.domain.patch.transported.cell retained.location.piece.column retained.location.piece.row
  let newCell := selectedDomain.patch.transported.cell selectedCell.column selectedCell.row
  have oldInside : (assigned.domain.geometry.box retained.location.piece.column retained.location.piece.row).Contains
      (parent.edge.point time) := retained.points_inside (data := data) 1
  have ends := Face.SplitSigns.piece_neighborhood retained.location.piece
    (AnalyticComparison.neighborhood_endpoints assigned).1 (AnalyticComparison.neighborhood_endpoints assigned).2
  have initial := AnalyticComparison.piece_nearest assigned retained.location.piece retained.location.member 0 2
  have oldNearest := Model.nearest_finish (oldCell.model.refine 2) (request.neighborhood.base.refine 2)
    retained.location.piece.first_inside oldInside
    (request.neighborhood.box_refines.contains ends.1) (request.neighborhood.box_refines.contains pointInside) initial
  have newNearest := EndpointSheets.FaceModels.Entry.point_nearest retained.point actual newCell differential
    selectedCell.inside pointInside
  have reverseNearest (first last : Canonical)
      (near : normSq (first - last) ≤ normSq (first + last)) :
      normSq (last - first) ≤ normSq (last + first) := by
    rewrite [Data.Gaussian.Norm.Bounds.normSq_sub_symm last first,
      show last + first = first + last by ring1]
    exact near
  have common := ((Model.overlapRefine oldCell.model) 0).nearest_trans
    ((Model.overlapRefine request.neighborhood.base.model) 0) ((Model.overlapRefine newCell.model) 0)
    oldInside (request.neighborhood.box_refines.contains pointInside) selectedCell.inside oldNearest
    (reverseNearest _ _ newNearest)
  have same := EndpointSheets.FaceModels.sheet_eq_of_nearest oldCell newCell differential
    oldInside selectedCell.inside common
  exact same.trans (retained.pointEntry_sheet (data := data) entry)

end QueryCut.Cache

namespace QueryCut.Cache.Preparation

variable (prepared : retained.Preparation (data := data))
variable (original : LiftedSource assigned mesh)
variable (child : PreparedAxisPartitions.Interval) (member : child ∈ prepared.fine.val.intervals)
variable (subinterval : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper)
variable (starts : child.lower = time)

/-- The complete new face-entry acquisition on the SAME cached query Owner in the original selected face models. -/
@[expose] def QueryAcquisition : Type :=
  Entry.Acquisition (domainCache fragment domains).models
    (QueryCut.face_inside (fragment := fragment) inside) query.owner

/-- Construct one new actual Entry acquisition and one original sample-bearing lifted fragment.

The complete Point is transported by its exact endpoint readback. The
actual old domain and lifted side are transported by a derived sheet
equality. Only the new Entry acquisition, geometric restriction and new
analytic split execute; the query, Point, domain and old side are reused.
-/
def materialize : QueryAcquisition (fragment := fragment) (domains := domains) (query := query)
    (inside := inside) × LiftedFragment axes domains mesh differential count target := by
  let geometry := fragment.restrict prepared.fine.val child member subinterval
  let acquired := Entry.Acquisition.build (domainCache fragment domains).models
    (QueryCut.face_inside (fragment := fragment) inside) query.owner
  have pointEq : geometry.located.first = parent.edge.point time :=
    geometry.located.first_eq.trans (congrArg parent.edge.point starts)
  let sample := ContinuedNeighborhood.Point.castPoint pointEq retained.point
  let incoming := retained.pointEntry (data := data) acquired.entry
  have ownerEq : HEq retained.point.owner sample.owner := by
    have castOwner {first last : Canonical} (same : first = last)
        (point : ContinuedNeighborhood.Point request.neighborhood last) :
        HEq point.owner (ContinuedNeighborhood.Point.castPoint same point).owner := by
      cases same
      rfl
    exact castOwner pointEq retained.point
  let entry : Entry (domainCache geometry domains).models geometry.located.first sample.owner :=
    ⟨incoming.sheet, PreparedFaceTracePrefixes.Reached.castFinish pointEq.symm ownerEq incoming.reached⟩
  have fractionInside : 0 ≤ child.lower ∧ child.lower ≤ 1 := by
    rewrite [starts]
    exact timeInside
  let signed : NamedEquivalent (parent.edge.rootName child.lower fractionInside)
      sample.certificate.value.name := by
    have parentName : parent.edge.rootName child.lower fractionInside = parent.edge.rootName time timeInside := by
      cases starts
      rfl
    exact NamedEquivalent.transport parentName.symm
      (ContinuedNeighborhood.Point.castPoint_name pointEq retained.point).symm
      (retained.originalComparison (data := data))
  have sheetEq : entry.sheet = assigned.entry.sheet :=
    (retained.pointEntry_sheet (data := data) acquired.entry).trans
      (retained.entry_sheet_eq (data := data) acquired.entry).symm
  let domain : PeriodDomain (domainCache geometry domains).models entry.sheet :=
    Eq.mpr (congrArg (fun sheet => PeriodDomain (domainCache fragment domains).models sheet) sheetEq) assigned.domain
  have domainEq : domain = (domainCache geometry domains).domain entry.sheet := by
    have transported {first last : Fin 2} (same : first = last)
        (value : PeriodDomain (domainCache fragment domains).models last)
        (correct : value = (domainCache fragment domains).domain last) :
        Eq.mpr (congrArg (fun sheet => PeriodDomain (domainCache fragment domains).models sheet) same) value =
          (domainCache fragment domains).domain first := by
      cases same
      exact correct
    exact transported sheetEq assigned.domain assigned.domain_eq
  have firstInside : geometry.face.located.face.cell.box.Contains geometry.located.first := by
    rewrite [geometry.face.located.cell_eq]
    exact geometry.first_inside
  have lastInside : geometry.face.located.face.cell.box.Contains geometry.located.last := by
    rewrite [geometry.face.located.cell_eq]
    exact geometry.last_inside
  let split := SegmentSplit.build domain.cuts geometry.located.first geometry.located.last
    (domain.covers firstInside) (domain.covers lastInside)
  let assignment : SheetEntry geometry domains request :=
    ⟨sample, entry, fractionInside, signed, domain, domainEq, split⟩
  let side : LiftedEdges.RegularEdgeCell.LiftedSide geometry.face mesh assignment.entry.sheet :=
    Eq.mpr (congrArg (fun sheet => LiftedEdges.RegularEdgeCell.LiftedSide fragment.face mesh sheet) sheetEq)
      original.side
  let occurrence := LiftedSource.ofSide assignment mesh side
  let piece : LiftedFragment axes domains mesh differential count target :=
    ⟨parent, cuts ++ [time], prepared.fine.val, child, geometry, request, assignment, occurrence⟩
  exact ⟨acquired, piece⟩

/-- The two cached outputs with their complete original constructor identity.

LiftedFragment already retains the geometry, assignment, sample, domain,
split and lifted occurrence. Only the auxiliary Entry acquisition needs a
separate data slot; no parallel fragment or observation bank is introduced.
-/
@[expose] def Leaf : Type 2 :=
  {value : QueryAcquisition (fragment := fragment) (domains := domains) (query := query) (inside := inside) ×
      LiftedFragment axes domains mesh differential count target //
    value = prepared.materialize original child member subinterval starts}

/-- Execute the actual leaf constructor once and retain its whole result. -/
def buildLeaf : prepared.Leaf original child member subinterval starts :=
  let value := prepared.materialize original child member subinterval starts
  ⟨value, rfl⟩

namespace Leaf

variable {prepared original child member subinterval starts}
variable (leaf : prepared.Leaf original child member subinterval starts)

/-- Read the whole new acquisition on the same original query Owner. -/
def acquired : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) := leaf.val.1

/-- Read the actual original lifted fragment containing all retained child owners and caches. -/
def piece : LiftedFragment axes domains mesh differential count target := leaf.val.2

/-- Both retained outputs are the complete constructor result on the supplied cached inputs. -/
theorem factory_eq : leaf.val = prepared.materialize original child member subinterval starts := leaf.property

/-- The complete acquisition is the original new factory on this same retained query Owner. -/
theorem acquired_eq : leaf.acquired = Entry.Acquisition.build (domainCache fragment domains).models
    (QueryCut.face_inside (fragment := fragment) inside) query.owner :=
  congrArg Prod.fst leaf.property

/-- The output keeps the literal original parent. -/
theorem parent_eq : leaf.piece.parent = parent := by
  have same := congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      value.2.parent) leaf.property
  exact same

/-- The output retains the actual extended cut data. -/
theorem cuts_eq : leaf.piece.cuts = cuts ++ [time] := by
  have same := congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      value.2.cuts) leaf.property
  exact same

/-- The literal child interval is retained without coordinate-based occurrence identification. -/
theorem interval_eq : leaf.piece.interval = child := by
  have same := congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      value.2.interval) leaf.property
  exact same

/-- The complete retained fine partition is the output occurrence's partition. -/
theorem partition_heq : HEq leaf.piece.partition prepared.fine.val := by
  rcases leaf with ⟨value, same⟩
  cases same
  rfl

/-- The literal original local request is retained under the output's parent index. -/
theorem request_heq : HEq leaf.piece.request request := by
  rcases leaf with ⟨value, same⟩
  cases same
  rfl

/-- The complete geometric restriction is the actual output fragment. -/
theorem geometry_heq : HEq leaf.piece.fragment (fragment.restrict prepared.fine.val child member subinterval) := by
  rcases leaf with ⟨value, same⟩
  cases same
  rfl

/-- The output sample is the same retained Point under its exact endpoint-index transport. -/
theorem sample_heq : HEq leaf.piece.assigned.sample retained.point := by
  rcases leaf with ⟨value, same⟩
  cases same
  have transported {first last : Canonical} (same : first = last)
      (point : ContinuedNeighborhood.Point request.neighborhood last) :
      HEq (ContinuedNeighborhood.Point.castPoint same point) point := by
    cases same
    rfl
  exact transported
    ((fragment.restrict prepared.fine.val child member subinterval).located.first_eq.trans
      (congrArg parent.edge.point starts)) retained.point

/-- The actual first coordinate is the same cached query point. -/
theorem first_eq : leaf.piece.first = parent.edge.point time := by
  have same := congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      value.2.first) leaf.property
  exact same.trans ((fragment.restrict prepared.fine.val child member subinterval).located.first_eq.trans
    (congrArg parent.edge.point starts))

/-- The actual final coordinate is the original parent point at this selected child's upper endpoint. -/
theorem last_eq : leaf.piece.last = parent.edge.point child.upper := by
  have same := congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      value.2.last) leaf.property
  exact same.trans (fragment.restrict prepared.fine.val child member subinterval).located.last_eq

/-- The actual retained assignment selects the sheet of the new cached query acquisition. -/
theorem entry_sheet : leaf.piece.assigned.entry.sheet = leaf.acquired.entry.sheet := by
  rcases leaf with ⟨value, same⟩
  cases same
  exact retained.pointEntry_sheet (data := data) _

/-- The original selected sheet is preserved by the derived same-face comparison. -/
theorem sheet_eq : leaf.piece.assigned.entry.sheet = assigned.entry.sheet := by
  have originalSheet := retained.entry_sheet_eq (data := data) leaf.acquired.entry
  exact leaf.entry_sheet.trans originalSheet.symm

/-- The whole old domain is reused under its actual sheet transport. -/
theorem domain_heq : HEq leaf.piece.assigned.domain assigned.domain := by
  rcases leaf with ⟨value, same⟩
  cases same
  have transported {first last : Fin 2} (same : first = last)
      (value : PeriodDomain (domainCache fragment domains).models last) :
      HEq (Eq.mpr (congrArg (fun sheet => PeriodDomain (domainCache fragment domains).models sheet) same) value)
        value := by
    cases same
    rfl
  let acquired := Entry.Acquisition.build (domainCache fragment domains).models
    (QueryCut.face_inside (fragment := fragment) inside) query.owner
  have sameSheet := (retained.pointEntry_sheet (data := data) acquired.entry).trans
    (retained.entry_sheet_eq (data := data) acquired.entry).symm
  exact transported sameSheet assigned.domain

/-- The complete old lifted side and its transport caches are retained under the derived sheet index. -/
theorem side_heq : HEq leaf.piece.occurrence.side original.side := by
  rcases leaf with ⟨value, same⟩
  cases same
  dsimp only [piece, materialize]
  rewrite [LiftedSource.ofSide_side]
  have transported {first last : Fin 2} (same : first = last)
      (side : LiftedEdges.RegularEdgeCell.LiftedSide fragment.face mesh last) :
      HEq (Eq.mpr (congrArg (fun sheet => LiftedEdges.RegularEdgeCell.LiftedSide fragment.face mesh sheet) same) side)
        side := by
    cases same
    rfl
  let acquired := Entry.Acquisition.build (domainCache fragment domains).models
    (QueryCut.face_inside (fragment := fragment) inside) query.owner
  have sameSheet := (retained.pointEntry_sheet (data := data) acquired.entry).trans
    (retained.entry_sheet_eq (data := data) acquired.entry).symm
  exact transported sameSheet original.side

/-- The child retains the literal start of the same complete source edge. -/
theorem source_start_eq : leaf.piece.fragment.source.start = fragment.source.start :=
  congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      value.2.fragment.source.start) leaf.property

/-- The child retains the literal finish of the same complete source edge. -/
theorem source_finish_eq : leaf.piece.fragment.source.finish = fragment.source.finish :=
  congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      value.2.fragment.source.finish) leaf.property

/-- The actual restricted child retains the original forward, reverse or stationary edge direction. -/
theorem source_forward_eq :
    decide (leaf.piece.fragment.source.first.parameter ≤ leaf.piece.fragment.source.last.parameter) =
      decide (fragment.source.first.parameter ≤ fragment.source.last.parameter) := by
  have actual := congrArg (fun value : QueryAcquisition (fragment := fragment) (domains := domains)
    (query := query) (inside := inside) × LiftedFragment axes domains mesh differential count target =>
      decide (value.2.fragment.source.first.parameter ≤ value.2.fragment.source.last.parameter)) leaf.property
  exact actual.trans (fragment.restrict_forward prepared.fine.val child member subinterval)

/-- Prepare actual numerical readings and the whole-child comparison on this retained leaf's complete split.

The original Point, Entry, domain and request remain the output piece's
owners. The new mesh uses ALL child split points and the computed matching
primitive stage; no selected-piece three-point mesh pays this full child.
-/
def prepareNumerics (tolerance : Rational) (positive : 0 < tolerance) :
    SharedComparison.Preparation leaf.piece.assigned tolerance positive :=
  SharedComparison.Preparation.build leaf.piece.assigned tolerance positive

end Leaf

section StrictCut

variable {child member subinterval starts}
variable (strict : interval.lower < time ∧ time < interval.upper)

include fragment strict in
/-- A strict cut in this retained fragment lies before the parent finish. -/
theorem before_parent_end : time < 1 :=
  strict.2.trans_le (partition.interval_bounds fragment.located.member).2

include strict in
/-- Select the genuine right neighbor on the same already retained fine partition. -/
def following : AxisNeighbors.AtEndpoint prepared.fine.val.intervals time false :=
  prepared.fine.val.following time (prepared.fine.additional_mem List.mem_cons_self timeInside)
    (before_parent_end (fragment := fragment) strict)

/-- The selected right interval stays inside the old actual fragment. -/
theorem following_inside : interval.lower ≤ (prepared.following strict).interval.lower ∧
    (prepared.following strict).interval.upper ≤ interval.upper := by
  have starts : (prepared.following strict).interval.lower = time := (prepared.following strict).endpoint_eq
  have endpoint := prepared.fine.interval_endpoints fragment.located.member
  have outside := prepared.fine.val.coordinate_outside (prepared.following strict).member endpoint.2
  constructor
  · exact starts.symm ▸ strict.1.1
  · cases outside with
    | inl before =>
        have reverse : interval.upper ≤ time := starts ▸ before
        exact (not_lt_of_ge reverse strict.2).elim
    | inr after => exact after

/-- The genuine right-neighbor selection and its actual sample-bearing leaf, each retained once. -/
@[expose] def After : Type 2 :=
  Σ selected : {value : AxisNeighbors.AtEndpoint prepared.fine.val.intervals time false //
      value = prepared.following strict},
  prepared.Leaf original selected.val.interval selected.val.member
    (selected.property.symm ▸ prepared.following_inside strict) selected.val.endpoint_eq

/-- Select and construct the actual right partial leaf without a supplied Entry or signed relation. -/
def buildAfter : prepared.After original strict :=
  let selected := prepared.following strict
  let leaf := prepared.buildLeaf original selected.interval selected.member
    (prepared.following_inside strict) selected.endpoint_eq
  ⟨⟨selected, rfl⟩, leaf⟩

namespace After

variable {prepared original strict}
variable (following : prepared.After original strict)

/-- Read the literal retained following interval and its original endpoint evidence. -/
def selected : AxisNeighbors.AtEndpoint prepared.fine.val.intervals time false := following.1.val

/-- The whole selected neighbor is the original finite factory result on the same retained partition. -/
theorem selected_eq : following.selected = prepared.following strict := following.1.property

/-- Read the actual cached partial leaf at the literal selected occurrence. -/
def leaf : prepared.Leaf original following.selected.interval following.selected.member
    (following.selected_eq.symm ▸ prepared.following_inside strict) following.selected.endpoint_eq := following.2

/-- The new partial leaf starts at the exact original retained query point. -/
theorem first_eq : following.leaf.piece.first = parent.edge.point time := following.leaf.first_eq

end After
end StrictCut
end QueryCut.Cache.Preparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry

end
