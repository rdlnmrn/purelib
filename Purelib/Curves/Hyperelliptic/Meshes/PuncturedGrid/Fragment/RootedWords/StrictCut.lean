module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Queries.Refinement.Leaf
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.Refinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.List.Append
import Init.Data.List.TakeDrop

/-! # Strict signed cuts in the same retained fragment word

The existing cut query and complete right-leaf acquisition remain inputs.
Only the left selector, geometric restriction and analytic split execute.
The original Point, Entry, domain and complete lifted side are transported
by their actual endpoint laws. Every outside occurrence stays in order.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment
  (SheetEntry domainCache)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry (LiftedSource)
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {mesh : LiftedMesh vertices edges base.faces} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}

namespace StrictCut

variable (focus : LiftedFragment axes domains mesh differential count target)
variable {index : Nat} {data : DomainPrimitives focus.assigned.domain differential index}
variable {time : Rational} {timeInside : 0 ≤ time ∧ time ≤ 1}
variable {query : PreparedEdge.Query focus.parent.edge time timeInside}
variable {inside : QueryCut.InFragment (interval := focus.interval) (time := time)}
variable {retained : QueryCut.Cache focus.assigned data.primitives query inside}
variable (prepared : retained.Preparation (data := data))
variable (strict : focus.interval.lower < time ∧ time < focus.interval.upper)
variable (after : prepared.After focus.occurrence strict)

include strict in
/-- The original fragment start is strictly before the parent finish. -/
theorem lower_lt_one : focus.interval.lower < 1 :=
  strict.1.trans (strict.2.trans_le (focus.partition.interval_bounds focus.fragment.located.member).2)

include strict in
/-- Select the left interval on the same already cached singleton refinement. -/
def selectBefore : AxisNeighbors.AtEndpoint prepared.fine.val.intervals focus.interval.lower false :=
  prepared.fine.val.following focus.interval.lower
    (prepared.fine.interval_endpoints focus.fragment.located.member).1 (lower_lt_one focus strict)

/-- The actual left selection starts at the retained original lower parameter. -/
theorem selectBefore_lower : (selectBefore focus prepared strict).interval.lower = focus.interval.lower :=
  (selectBefore focus prepared strict).endpoint_eq

/-- The inserted coordinate bounds the actual left selection from above. -/
theorem selectBefore_upper_le : (selectBefore focus prepared strict).interval.upper ≤ time := by
  have outside := prepared.fine.val.coordinate_outside (selectBefore focus prepared strict).member
    (prepared.fine.additional_mem List.mem_cons_self timeInside)
  cases outside with
  | inl before =>
      have reverse : time ≤ focus.interval.lower := (selectBefore_lower focus prepared strict) ▸ before
      exact (not_lt_of_ge reverse strict.1).elim
  | inr after => exact after

/-- Singleton refinement makes the selected left finish exactly the inserted cut. -/
theorem selectBefore_upper : (selectBefore focus prepared strict).interval.upper = time := by
  have endpoints := ClearGrid.Interval.endpoints_mem prepared.fine.val.coordinates prepared.fine.val.ordered
    (Eq.mp (congrArg (fun intervals => (selectBefore focus prepared strict).interval ∈ intervals)
      prepared.fine.val.intervals_eq) (selectBefore focus prepared strict).member)
  cases prepared.fine.singleton_coordinate endpoints.2 with
  | inl old =>
      have outside := focus.partition.coordinate_outside focus.fragment.located.member old
      cases outside with
      | inl before =>
          have proper : focus.interval.lower < (selectBefore focus prepared strict).interval.upper :=
            Eq.mp (congrArg (fun lower => lower < (selectBefore focus prepared strict).interval.upper)
              (selectBefore_lower focus prepared strict)) (selectBefore focus prepared strict).interval.ordered
          exact (not_lt_of_ge before proper).elim
      | inr beyond =>
          exact (not_lt_of_ge (beyond.trans (selectBefore_upper_le focus prepared strict)) strict.2).elim
  | inr cut => exact cut

/-- The cached right neighbor ends at the actual original fragment finish. -/
theorem after_upper : after.selected.interval.upper = focus.interval.upper := by
  have endpoints := ClearGrid.Interval.endpoints_mem prepared.fine.val.coordinates prepared.fine.val.ordered
    (Eq.mp (congrArg (fun intervals => after.selected.interval ∈ intervals)
      prepared.fine.val.intervals_eq) after.selected.member)
  have subset : focus.interval.lower ≤ after.selected.interval.lower ∧
      after.selected.interval.upper ≤ focus.interval.upper :=
    after.selected_eq.symm ▸ prepared.following_inside strict
  cases prepared.fine.singleton_coordinate endpoints.2 with
  | inl old =>
      have outside := focus.partition.coordinate_outside focus.fragment.located.member old
      cases outside with
      | inl before =>
          have proper : time < after.selected.interval.upper :=
            Eq.mp (congrArg (fun lower => lower < after.selected.interval.upper)
              (show after.selected.interval.lower = time from after.selected.endpoint_eq))
              after.selected.interval.ordered
          exact (not_lt_of_ge (before.trans strict.1.1) proper).elim
      | inr beyond => exact Data.Rat.Fraction.Order.Basic.le_antisymm _ _ subset.2 beyond
  | inr cut =>
      have proper : time < after.selected.interval.upper :=
        Eq.mp (congrArg (fun lower => lower < after.selected.interval.upper)
              (show after.selected.interval.lower = time from after.selected.endpoint_eq))
              after.selected.interval.ordered
      exact (proper.ne cut.symm).elim

variable {focus prepared strict after}

/-- The actual original left selection with its whole finite-factory identity. -/
@[expose] def BeforeSelection : Type :=
  {value : AxisNeighbors.AtEndpoint prepared.fine.val.intervals focus.interval.lower false //
    value = selectBefore focus prepared strict}

section

variable (selected : BeforeSelection (focus := focus) (prepared := prepared) (strict := strict))

/-- The cached selector retains the original lower parameter. -/
theorem before_lower : selected.val.interval.lower = focus.interval.lower :=
  (congrArg (fun value => value.interval.lower) selected.property).trans
    (selectBefore_lower focus prepared strict)

/-- The cached selector retains the literal inserted upper parameter. -/
theorem before_upper : selected.val.interval.upper = time :=
  (congrArg (fun value => value.interval.upper) selected.property).trans
    (selectBefore_upper focus prepared strict)

/-- The selected left interval is a subinterval of the same original fragment. -/
theorem before_inside : focus.interval.lower ≤ selected.val.interval.lower ∧
    selected.val.interval.upper ≤ focus.interval.upper := by
  constructor
  · rewrite [before_lower selected]
    exact Data.Rat.Fraction.Order.Basic.le_refl _
  · exact (before_upper selected).symm ▸ strict.2.1

/-- Equal actual parents and fractions retain the same original signed query name. -/
private theorem parameterName {firstParent lastParent : CenteredEdge curve differential}
    {first last : Rational} (sameParent : firstParent = lastParent) (same : first = last)
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    firstParent.edge.rootName first firstInside = lastParent.edge.rootName last lastInside := by
  cases sameParent
  cases same
  rfl

/-- Construct a left leaf using the original Point, Entry, domain and complete lifted side.

The Point, Entry and retained signed comparison are transported only along
the actual first-endpoint readback. No Point or query is reacquired to
recover the original comparison. The new analytic split covers the entire selected child; the
old selected-piece three-point mesh is not reused as a whole-child bound.
-/
def materializeBefore : LiftedFragment axes domains mesh differential count target := by
  let geometry := focus.fragment.restrict prepared.fine.val selected.val.interval selected.val.member
    (before_inside selected)
  have pointEq : geometry.located.first = focus.fragment.located.first :=
    geometry.located.first_eq.trans
      ((congrArg focus.parent.edge.point (before_lower selected)).trans focus.fragment.located.first_eq.symm)
  let sample := ContinuedNeighborhood.Point.castPoint pointEq focus.assigned.sample
  have ownerEq : HEq focus.assigned.sample.owner sample.owner := by
    have castOwner {first last : Canonical} (same : first = last)
        (point : ContinuedNeighborhood.Point focus.request.neighborhood last) :
        HEq point.owner (ContinuedNeighborhood.Point.castPoint same point).owner := by
      cases same
      rfl
    exact castOwner pointEq focus.assigned.sample
  let entry : Entry (domainCache geometry domains).models geometry.located.first sample.owner :=
    ⟨focus.assigned.entry.sheet,
      PreparedFaceTracePrefixes.Reached.castFinish pointEq.symm ownerEq focus.assigned.entry.reached⟩
  have fractionInside : 0 ≤ selected.val.interval.lower ∧ selected.val.interval.lower ≤ 1 :=
    (before_lower selected).symm ▸ focus.assigned.fractionInside
  let signed : NamedEquivalent
      (focus.parent.edge.rootName selected.val.interval.lower fractionInside)
      sample.certificate.value.name := by
    have parentName := parameterName (firstParent := focus.parent) (lastParent := focus.parent)
      rfl (before_lower selected) fractionInside focus.assigned.fractionInside
    exact NamedEquivalent.transport parentName.symm
      (ContinuedNeighborhood.Point.castPoint_name pointEq focus.assigned.sample).symm focus.assigned.original
  let domain := focus.assigned.domain
  have firstInside : geometry.face.located.face.cell.box.Contains geometry.located.first := by
    rewrite [geometry.face.located.cell_eq]
    exact geometry.first_inside
  have lastInside : geometry.face.located.face.cell.box.Contains geometry.located.last := by
    rewrite [geometry.face.located.cell_eq]
    exact geometry.last_inside
  let split := SegmentSplit.build domain.cuts geometry.located.first geometry.located.last
    (domain.covers firstInside) (domain.covers lastInside)
  let assigned : SheetEntry geometry domains focus.request :=
    ⟨sample, entry, fractionInside, signed, domain, focus.assigned.domain_eq, split⟩
  let occurrence := LiftedSource.ofSide assigned mesh focus.occurrence.side
  exact ⟨focus.parent, focus.cuts ++ [time], prepared.fine.val, selected.val.interval,
    geometry, focus.request, assigned, occurrence⟩

/-- Retain the left selector and whole actual fragment constructor in the original containers. -/
@[expose] def Before : Type 2 :=
  Σ selected : BeforeSelection (focus := focus) (prepared := prepared) (strict := strict),
  {piece : LiftedFragment axes domains mesh differential count target // piece = materializeBefore selected}

/-- Execute only the left selection, restriction and analytic split once. -/
def buildBefore : Before (focus := focus) (prepared := prepared) (strict := strict) :=
  let selected : BeforeSelection (focus := focus) (prepared := prepared) (strict := strict) :=
    ⟨selectBefore focus prepared strict, rfl⟩
  let piece := materializeBefore selected
  ⟨selected, ⟨piece, rfl⟩⟩

end

namespace Before
variable (before : Before (focus := focus) (prepared := prepared) (strict := strict))

/-- Read the complete retained left selector. -/
def selected : BeforeSelection (focus := focus) (prepared := prepared) (strict := strict) := before.1

/-- Read the complete left sample-bearing lifted fragment. -/
def piece : LiftedFragment axes domains mesh differential count target := before.2.val

/-- The whole retained left fragment is its cached-input factory result. -/
theorem factory_eq : before.piece = materializeBefore before.selected := before.2.property

/-- The left occurrence keeps the original first coordinate. -/
theorem first_eq : before.piece.first = focus.first := by
  have actual := congrArg LiftedFragment.first before.factory_eq
  exact actual.trans ((focus.fragment.restrict prepared.fine.val before.selected.val.interval
    before.selected.val.member (before_inside before.selected)).located.first_eq.trans
      ((congrArg focus.parent.edge.point (before_lower before.selected)).trans focus.fragment.located.first_eq.symm))

/-- The left occurrence ends at the actual retained query point. -/
theorem last_eq : before.piece.last = focus.parent.edge.point time := by
  have actual := congrArg LiftedFragment.last before.factory_eq
  exact actual.trans ((focus.fragment.restrict prepared.fine.val before.selected.val.interval
    before.selected.val.member (before_inside before.selected)).located.last_eq.trans
      (congrArg focus.parent.edge.point (before_upper before.selected)))

/-- The left source channel is the same original parent query channel. -/
theorem firstName_eq : before.piece.firstName = focus.firstName :=
  (congrArg LiftedFragment.firstName before.factory_eq).trans
    (parameterName rfl (before_lower before.selected) _ _)

/-- The left terminal channel is the same already retained direct-query Owner. -/
theorem lastName_eq : before.piece.lastName = ownerName query.owner :=
  (congrArg LiftedFragment.lastName before.factory_eq).trans
    ((parameterName rfl (before_upper before.selected) _ _).trans query.name_eq)

/-- The actual transported left Point is the complete original Point. -/
theorem sample_heq : HEq before.piece.assigned.sample focus.assigned.sample := by
  rcases before with ⟨selected, piece, same⟩
  cases same
  have castSample {first last : Canonical} (equal : first = last)
      (point : ContinuedNeighborhood.Point focus.request.neighborhood last) :
      HEq (ContinuedNeighborhood.Point.castPoint equal point) point := by
    cases equal
    rfl
  exact castSample
    ((focus.fragment.restrict prepared.fine.val selected.val.interval selected.val.member
      (before_inside selected)).located.first_eq.trans
      ((congrArg focus.parent.edge.point (before_lower selected)).trans focus.fragment.located.first_eq.symm))
    focus.assigned.sample

/-- The complete original domain, including anchors and offsets, is retained. -/
theorem domain_heq : HEq before.piece.assigned.domain focus.assigned.domain := by
  rcases before with ⟨selected, piece, same⟩
  cases same
  rfl

/-- The complete original lifted side and its operational route caches are retained. -/
theorem side_heq : HEq before.piece.occurrence.side focus.occurrence.side := by
  rcases before with ⟨selected, piece, same⟩
  cases same
  dsimp only [piece, materializeBefore]
  rewrite [LiftedSource.ofSide_side]
  rfl

/-- The left piece retains the literal original complete-edge start. -/
theorem source_start_eq : before.piece.fragment.source.start = focus.fragment.source.start := by
  have actual := congrArg (fun piece : LiftedFragment axes domains mesh differential count target =>
    piece.fragment.source.start) before.factory_eq
  exact actual.trans rfl

/-- The left piece retains the literal original complete-edge finish. -/
theorem source_finish_eq : before.piece.fragment.source.finish = focus.fragment.source.finish := by
  have actual := congrArg (fun piece : LiftedFragment axes domains mesh differential count target =>
    piece.fragment.source.finish) before.factory_eq
  exact actual.trans rfl

/-- The actual left restriction retains the original forward, reverse or stationary edge direction. -/
theorem source_forward_eq :
    decide (before.piece.fragment.source.first.parameter ≤ before.piece.fragment.source.last.parameter) =
      decide (focus.fragment.source.first.parameter ≤ focus.fragment.source.last.parameter) := by
  have actual := congrArg (fun piece : LiftedFragment axes domains mesh differential count target =>
    decide (piece.fragment.source.first.parameter ≤ piece.fragment.source.last.parameter)) before.factory_eq
  exact actual.trans (focus.fragment.restrict_forward prepared.fine.val before.selected.val.interval
    before.selected.val.member (before_inside before.selected))

/-- The singleton left word has the actual old source and cached-query endpoints. -/
theorem rooted : RootedWord [before.piece] focus.first focus.firstName
    (focus.parent.edge.point time) (ownerName query.owner) := by
  refine .cons before.piece before.first_eq.symm ?_ (.nil before.last_eq ?_)
  · rewrite [before.firstName_eq]
    exact ⟨NamedEquivalent.refl _⟩
  · rewrite [before.lastName_eq]
    exact ⟨NamedEquivalent.refl _⟩

end Before

variable (after)

/-- The supplied right leaf retains the original terminal coordinate. -/
theorem after_last : after.leaf.piece.last = focus.last :=
  after.leaf.last_eq.trans ((congrArg focus.parent.edge.point (after_upper focus prepared strict after)).trans
    focus.fragment.located.last_eq.symm)

/-- The right source name is the actual retained cut-query name. -/
theorem after_firstName : after.leaf.piece.firstName = ownerName query.owner := by
  have parameter : after.leaf.piece.interval.lower = time :=
    (congrArg (fun value : PreparedAxisPartitions.Interval => value.lower) after.leaf.interval_eq).trans
      after.selected.endpoint_eq
  exact (parameterName after.leaf.parent_eq parameter _ _).trans query.name_eq

/-- The right terminal name is the original terminal signed channel. -/
theorem after_lastName : after.leaf.piece.lastName = focus.lastName := by
  have parameter : after.leaf.piece.interval.upper = focus.interval.upper :=
    (congrArg (fun value : PreparedAxisPartitions.Interval => value.upper) after.leaf.interval_eq).trans
      (after_upper focus prepared strict after)
  exact parameterName after.leaf.parent_eq parameter _ _

/-- The supplied right singleton has its genuine cached-query source and old terminal channel. -/
theorem after_rooted : RootedWord [after.leaf.piece] (focus.parent.edge.point time)
    (ownerName query.owner) focus.last focus.lastName := by
  refine .cons after.leaf.piece after.first_eq.symm ?_ (.nil (after_last after) ?_)
  · rewrite [after_firstName after]
    exact ⟨NamedEquivalent.refl _⟩
  · rewrite [after_lastName after]
    exact ⟨NamedEquivalent.refl _⟩

section

variable (before : Before (focus := focus) (prepared := prepared) (strict := strict))

/-- The ordered replacement word retains both outside lists literally. -/
@[expose] def refinedWord (preceding tail : List (LiftedFragment axes domains mesh differential count target)) :
    List (LiftedFragment axes domains mesh differential count target) :=
  (preceding ++ [before.piece]) ++ after.leaf.piece :: tail

/-- The new strict prefix and tail meet at the same actual cached direct-query Owner. -/
theorem halves (preceding tail : List (LiftedFragment axes domains mesh differential count target))
    {first last : Canonical} {firstName lastName : Named}
    (old : RootedWord (preceding ++ focus :: tail) first firstName last lastName) :
    RootedWord (preceding ++ [before.piece]) first firstName (focus.parent.edge.point time) (ownerName query.owner) ∧
      RootedWord (after.leaf.piece :: tail) (focus.parent.edge.point time) (ownerName query.owner) last lastName :=
  RootedWord.splice before.rooted (after_rooted after) preceding old

/-- Replacing the literal occurrence preserves all old signed junctions and both outer endpoints. -/
theorem refinedWord_rooted (preceding tail : List (LiftedFragment axes domains mesh differential count target))
    {first last : Canonical} {firstName lastName : Named}
    (old : RootedWord (preceding ++ focus :: tail) first firstName last lastName) :
    RootedWord (refinedWord after before preceding tail) first firstName last lastName :=
  (halves after before preceding tail old).1.append (halves after before preceding tail old).2

/-- The two same-direction leaves telescope in one actual selected-route shared reading owner.

The exact old parent/query root certificates identify the lifted edge.
The original finite route lookup, direction and shared reading bank then
identify the common cut reading. Assigned-face versus route-face primitive
jumps are separate; no independent primitive owners are equated here.
-/
theorem side_telescope {points : List Canonical} {tolerance : Rational} {numericalIndex : Nat}
    {budgets : FaceMeshBudgets differential points tolerance domains}
    {numerics : FacePrimitiveBank differential numericalIndex domains}
    (shared : FaceSharedMeshes budgets numerics) :
    gaussianSum ([before.piece, after.leaf.piece].map (fun piece =>
      RouteContacts.routeValue piece (RouteWords.canonicalRoute piece) shared)) =
      RouteCancellation.canonicalPoint before.piece shared focus.last -
        RouteCancellation.canonicalPoint before.piece shared focus.first := by
  have actual : RootedWord [before.piece, after.leaf.piece]
      focus.first focus.firstName focus.last focus.lastName :=
    before.rooted.append (after_rooted after)
  refine RouteCancellation.RootedWord.canonical_telescope actual ?_ shared
  intro piece member
  rcases Data.List.Membership.mem_cons.mp member with selected | impossible
  · subst piece
    exact ⟨before.source_start_eq.trans after.leaf.source_start_eq.symm,
      before.source_finish_eq.trans after.leaf.source_finish_eq.symm,
      before.source_forward_eq.trans after.leaf.source_forward_eq.symm⟩
  · exact (List.not_mem_nil impossible).elim

end

/-- Retain the once-built left leaf, the complete supplied right cache and the ordered resulting word. -/
@[expose] def Assembly (preceding tail : List (LiftedFragment axes domains mesh differential count target)) : Type 2 :=
  Σ before : {value : Before (focus := focus) (prepared := prepared) (strict := strict) // value = buildBefore},
  Σ right : {value : prepared.After focus.occurrence strict // value = after},
  {pieces : List (LiftedFragment axes domains mesh differential count target) //
    pieces = refinedWord right.val before.val preceding tail}

/-- Execute the left leaf factory once and retain the supplied entire right cache once. -/
def assemble (preceding tail : List (LiftedFragment axes domains mesh differential count target)) :
    Assembly after preceding tail :=
  let before := buildBefore (focus := focus) (prepared := prepared) (strict := strict)
  let right := after
  let pieces := refinedWord right before preceding tail
  ⟨⟨before, rfl⟩, ⟨right, rfl⟩, ⟨pieces, rfl⟩⟩

namespace Assembly

variable {after} {preceding tail : List (LiftedFragment axes domains mesh differential count target)}
variable (assembled : Assembly after preceding tail)

/-- Read the entire once-built left cache. -/
def before : Before (focus := focus) (prepared := prepared) (strict := strict) := assembled.1.val

/-- Read the same whole supplied right acquisition, Point and leaf. -/
def right : prepared.After focus.occurrence strict := assembled.2.1.val

/-- Read the actual cached ordered replacement word. -/
def pieces : List (LiftedFragment axes domains mesh differential count target) := assembled.2.2.val

/-- The left cache is the exact original factory result on these supplied inputs. -/
theorem before_eq : assembled.before = buildBefore (focus := focus) (prepared := prepared) (strict := strict) :=
  assembled.1.property

/-- The complete right cache is literally the supplied original value. -/
theorem right_eq : assembled.right = after := assembled.2.1.property

/-- The complete word is the actual finite assembly of the retained caches and outside occurrences. -/
theorem pieces_eq : assembled.pieces = refinedWord assembled.right assembled.before preceding tail :=
  assembled.2.2.property

/-- The cached assembly preserves all original signed endpoints and junctions. -/
theorem rooted {first last : Canonical} {firstName lastName : Named}
    (old : RootedWord (preceding ++ focus :: tail) first firstName last lastName) :
    RootedWord assembled.pieces first firstName last lastName :=
  assembled.pieces_eq.symm ▸ refinedWord_rooted assembled.right assembled.before preceding tail old

/-- The two actual cached subwords meet at the same original cut-query channel. -/
theorem halves {first last : Canonical} {firstName lastName : Named}
    (old : RootedWord (preceding ++ focus :: tail) first firstName last lastName) :
    RootedWord (preceding ++ [assembled.before.piece]) first firstName
        (focus.parent.edge.point time) (ownerName query.owner) ∧
      RootedWord (assembled.right.leaf.piece :: tail) (focus.parent.edge.point time)
        (ownerName query.owner) last lastName :=
  StrictCut.halves assembled.right assembled.before preceding tail old

end Assembly
end StrictCut

namespace AtOccurrence

variable (pieces : List (LiftedFragment axes domains mesh differential count target))
variable (position : Fin pieces.length)
variable {index : Nat}
variable {data : DomainPrimitives (pieces[position.val]'position.isLt).assigned.domain differential index}
variable {time : Rational} {timeInside : 0 ≤ time ∧ time ≤ 1}
variable {query : PreparedEdge.Query (pieces[position.val]'position.isLt).parent.edge time timeInside}
variable {inside : QueryCut.InFragment (interval := (pieces[position.val]'position.isLt).interval) (time := time)}
variable {retained : QueryCut.Cache (pieces[position.val]'position.isLt).assigned data.primitives query inside}
variable (prepared : retained.Preparation (data := data))
variable (strict : (pieces[position.val]'position.isLt).interval.lower < time ∧
  time < (pieces[position.val]'position.isLt).interval.upper)
variable (after : prepared.After (pieces[position.val]'position.isLt).occurrence strict)

/-- The exact finite position determines the original prefix, selected occurrence and literal tail. -/
theorem decomposition : pieces = pieces.take position.val ++
    (pieces[position.val]'position.isLt) :: pieces.drop (position.val + 1) :=
  (List.take_append_drop position.val pieces).symm.trans
    (congrArg (List.append (pieces.take position.val)) (List.drop_eq_getElem_cons position.isLt))

/-- Assemble at the actual retained finite occurrence without supplying a prefix/fragment identity. -/
def assemble : StrictCut.Assembly after (pieces.take position.val) (pieces.drop (position.val + 1)) :=
  StrictCut.assemble after (pieces.take position.val) (pieces.drop (position.val + 1))

/-- The finite-position assembly inherits the same original word certificate and signed outer endpoints.

An original cached Rooted.sources word supplies this certificate through
its stored rooted field; the producer does not flatten or acquire it again.
-/
theorem rooted (assembled : StrictCut.Assembly after (pieces.take position.val) (pieces.drop (position.val + 1)))
    {first last : Canonical} {firstName lastName : Named}
    (old : RootedWord pieces first firstName last lastName) :
    RootedWord assembled.pieces first firstName last lastName :=
  StrictCut.Assembly.rooted assembled ((decomposition pieces position) ▸ old)

end AtOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment

end
