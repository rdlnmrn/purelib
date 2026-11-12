module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega

/-! # Requested canonical-cochain payment on the actual odd-degree boundary loops

The exterior keeps its actual two-lap root transport. Each original hole
keeps its doubled inward word. The preparation stores original paired-walk
and cancellation requests before any shared numerical bank is sampled.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopRequests

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
  (IncrementRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    (lifted : LiftedPuncturedGrid base)
    (domains : FaceDomainBank lifted.frames base.faces.regulars) (differential : Differential genus)

/-- One original paired-walk cache and its actual canonical-cochain cancellation request, with both whole factories. -/
@[expose] def WalkRequest {first last : Canonical} (walk : Walk base.bank.grid first last)
    (target : Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) : Type _ :=
  (paired : {value : PairedWalk lifted.mesh walk // value = PairedWalk.build lifted.mesh walk}) ×
  {request : IncrementRequest paired.val domains differential 0 target polynomial //
    request = IncrementRequest.build paired.val domains differential 0 target positive polynomial}

/-- Build the actual paired walk once, then its original transport and two signed chart request families once. -/
def prepareWalk {first last : Canonical} (walk : Walk base.bank.grid first last)
    (target : Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    WalkRequest lifted domains differential walk target positive polynomial :=
  let paired := PairedWalk.build lifted.mesh walk
  let request := IncrementRequest.build paired domains differential 0 target positive polynomial
  ⟨⟨paired, rfl⟩, ⟨request, rfl⟩⟩

namespace WalkRequest

variable {lifted domains differential} {first last : Canonical} {walk : Walk base.bank.grid first last}
    {target : Rational} {positive : 0 < target} {polynomial : Option (Ordinary curve.polynomial)}
    (retained : WalkRequest lifted domains differential walk target positive polynomial)

/-- Read the actual sufficient stage from the same stored original cancellation request. -/
@[expose] def index : Nat := retained.2.val.index

/-- The stored request bounds the sum on the two actual indexed lifts at every sufficient later stage. -/
theorem accurate (retained : WalkRequest lifted domains differential walk target positive)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains}
    (readings : TriangleReadings shared lifted.mesh) (later : retained.index ≤ stage) :
    normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (lifted.edges.indexedEdges lifted.vertices walk 0) +
      wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (lifted.edges.indexedEdges lifted.vertices walk 1)) ≤ target := by
  exact retained.2.val.accurate readings later

/-- The exact common chart-comparison data of the SAME original paired cancellation request. -/
@[expose] def Comparison {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  retained.2.val.Comparison shared

/-- Execute the retained original cancellation request's two signed comparison products once. -/
def compare {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    retained.Comparison shared := retained.2.val.compare shared

/-- The SAME retained polynomial comparisons bound the two actual indexed sheet lifts at every paid stage. -/
theorem comparison_accurate {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared lifted.mesh) (compared : retained.Comparison shared)
    (later : retained.index ≤ stage) :
    normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (lifted.edges.indexedEdges lifted.vertices walk 0) +
      wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (lifted.edges.indexedEdges lifted.vertices walk 1)) ≤ target := by
  exact retained.2.val.comparison_accurate readings compared later

end WalkRequest

/-- One actual exterior request, one original request at each bounded hole occurrence, and their exact common stage.

The hole vector preserves the original finite order and bounds. Its empty
case has maximum zero. No cochain, primitive bank or reading is constructed
by this cache; numerical sampling follows the selected stage.
-/
@[expose] def Preparation (target : Rational) (positive : 0 < target) (minimum : Nat)
    (polynomial : Option (Ordinary curve.polynomial) := none) : Type _ :=
  (exterior : WalkRequest lifted domains differential base.bank.exterior target positive polynomial) ×
  (holes : DependentVector (fun position : Fin base.faces.holes.length =>
    WalkRequest lifted domains differential (base.faces.holes[position.val]'position.isLt).inwardBoundary
      target positive polynomial)) ×
  {index : Nat // index = max minimum
    (max exterior.index (holes.maximum (fun _ request => request.index)))}

/-- Assemble given whole request caches and their exact scalar maximum without unfolding their producers. -/
private def withRequests (target : Rational) (positive : 0 < target) (minimum : Nat)
    {polynomial : Option (Ordinary curve.polynomial)}
    (exterior : WalkRequest lifted domains differential base.bank.exterior target positive polynomial)
    (holes : DependentVector (fun position : Fin base.faces.holes.length =>
      WalkRequest lifted domains differential (base.faces.holes[position.val]'position.isLt).inwardBoundary
        target positive polynomial)) : Preparation lifted domains differential target positive minimum polynomial :=
  let index : {value : Nat // value = max minimum
      (max exterior.index (holes.maximum (fun _ request => request.index)))} :=
    ⟨max minimum (max exterior.index (holes.maximum (fun _ request => request.index))), rfl⟩
  ⟨exterior, holes, index⟩

/-- Prepare the original exterior and hole requests and select their common stage before numerical sampling. -/
def prepare (target : Rational) (positive : 0 < target) (minimum : Nat)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    Preparation lifted domains differential target positive minimum polynomial :=
  let exterior := prepareWalk lifted domains differential base.bank.exterior target positive polynomial
  let holes := DependentVector.ofFn fun position : Fin base.faces.holes.length =>
    prepareWalk lifted domains differential (base.faces.holes[position.val]'position.isLt).inwardBoundary
      target positive polynomial
  withRequests lifted domains differential target positive minimum (polynomial := polynomial) exterior holes

namespace Preparation

variable {lifted domains differential} {target : Rational} {positive : 0 < target} {minimum : Nat}
    {polynomial : Option (Ordinary curve.polynomial)}
    (prepared : Preparation lifted domains differential target positive minimum polynomial)

/-- Read the selected stage of the actual exterior and original bounded hole requests. -/
@[expose] def index : Nat := prepared.2.2.val

/-- The selected stage is exactly the original minimum and retained request maxima. -/
theorem index_eq : prepared.index = max minimum
    (max prepared.1.index (prepared.2.1.maximum (fun _ request => request.index))) := prepared.2.2.property

/-- The actual selected common stage retains the requested minimum. -/
theorem minimum_le : minimum ≤ prepared.index :=
  (Data.Nat.Order.le_max_left _ _).trans_eq prepared.index_eq.symm

/-- The original exterior request needs no later stage than the retained preparation. -/
theorem exterior_le : prepared.1.index ≤ prepared.index :=
  ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans_eq prepared.index_eq.symm

/-- Each actual original hole occurrence's retained request needs no later stage than the retained preparation. -/
theorem hole_le (position : Fin base.faces.holes.length) :
    (prepared.2.1.get position).index ≤ prepared.index :=
  ((DependentVector.get_le_maximum (fun _ request => request.index) prepared.2.1 position).trans
    ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))).trans_eq prepared.index_eq.symm

/-- Every actual bounded hole word meets the prepared target in the same later shared canonical cochain. -/
theorem hole_accurate (prepared : Preparation lifted domains differential target positive minimum)
    (position : Fin base.faces.holes.length)
    {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains} (readings : TriangleReadings shared lifted.mesh)
    (later : prepared.index ≤ stage) :
    normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      ((base.faces.holes[position.val]'position.isLt).liftedBoundary lifted.vertices lifted.edges)) ≤ target := by
  have original := (prepared.2.1.get position).accurate readings ((prepared.hole_le position).trans later)
  rewrite [(base.faces.holes[position.val]'position.isLt).liftedBoundary_eq, wordValue_append]
  exact original

/-- The original bounded hole occurrence estimates cover every actual displayed hole word. -/
private theorem holes_bound (value : OrientedEdge lifted.vertices.count → Canonical)
    (bounded : ∀ position : Fin base.faces.holes.length,
      normSq (wordValue value
        ((base.faces.holes[position.val]'position.isLt).liftedBoundary lifted.vertices lifted.edges)) ≤ target) :
    ∀ hole ∈ base.faces.holes, normSq (wordValue value
      (hole.liftedBoundary lifted.vertices lifted.edges)) ≤ target := by
  have members {Alpha : Type _} (items : List Alpha) (property : Alpha → Prop)
      (atIndex : ∀ position : Fin items.length, property (items[position.val]'position.isLt)) :
      ∀ item ∈ items, property item := by
    induction items with
    | nil => intro item impossible; nomatch impossible
    | cons head tail ih =>
      intro item member
      rcases Membership.mem_cons.mp member with equal | member
      · cases equal; exact atIndex 0
      · exact ih (fun position => atIndex position.succ) item member
  exact members base.faces.holes _ bounded

/-- Every actual displayed hole word retains its own bounded request, including repeated hole occurrences. -/
private theorem holes_accurate (prepared : Preparation lifted domains differential target positive minimum)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains}
    (readings : TriangleReadings shared lifted.mesh) (later : prepared.index ≤ stage) :
    ∀ hole ∈ base.faces.holes, normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (hole.liftedBoundary lifted.vertices lifted.edges)) ≤ target := by
  exact holes_bound (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
    (fun position => prepared.hole_accurate position readings later)

/-- The actual odd-degree exterior's two consecutive laps meet the prepared canonical-cochain target. -/
theorem exterior_accurate (prepared : Preparation lifted domains differential target positive minimum)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains} (readings : TriangleReadings shared lifted.mesh)
    (later : prepared.index ≤ stage) :
    normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (lifted.edges.indexedEdges lifted.vertices (base.bank.exterior.append base.bank.exterior) 0)) ≤ target := by
  have original := prepared.1.accurate readings (prepared.exterior_le.trans later)
  rewrite [lifted.edges.indexedEdges_append, lifted.exterior_swap_odd degree,
    BranchCutLifts.otherSheet_zero, wordValue_append]
  exact original

/-- The retained odd-degree exterior word and original bounded hole words cover the actual physical loop list. -/
private theorem loops_bound (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (value : OrientedEdge lifted.vertices.count → Canonical)
    (exterior : normSq (wordValue value
      (lifted.edges.indexedEdges lifted.vertices (base.bank.exterior.append base.bank.exterior) 0)) ≤ target)
    (holes : ∀ hole ∈ base.faces.holes,
      normSq (wordValue value (hole.liftedBoundary lifted.vertices lifted.edges)) ≤ target) :
    ∀ word ∈ lifted.boundaryLoops, normSq (wordValue value word) ≤ target := by
  intro word member
  change word ∈ lifted.exteriorBoundaries ++ base.faces.holes.map
    (fun hole => hole.liftedBoundary lifted.vertices lifted.edges) at member
  rcases Membership.mem_append.mp member with exteriorMember | holeMember
  · have same := Membership.mem_singleton.mp
      (Eq.mp (congrArg (fun words => word ∈ words) (lifted.exteriorBoundaries_odd degree)) exteriorMember)
    cases same
    exact exterior
  · obtain ⟨hole, holeInList, same⟩ := Map.mem_map.mp holeMember
    cases same
    exact holes hole holeInList

/-- At every sufficient later stage all original odd-degree physical boundary loops satisfy their paid common target.

The retained root-edge bank proves the exterior swap and the actual doubled
hole words. The same supplied primitive bank and triangle readings are used
for every loop; parity and closedness alone supply no numerical cancellation.
-/
theorem accurate (prepared : Preparation lifted domains differential target positive minimum)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains} (readings : TriangleReadings shared lifted.mesh)
    (later : prepared.index ≤ stage) :
    ∀ word ∈ lifted.boundaryLoops,
      normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) word) ≤ target := by
  exact loops_bound degree (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
    (prepared.exterior_accurate degree readings later) (prepared.holes_accurate readings later)

/-- The exact exterior and bounded-hole common comparison caches on the SAME given polynomial primitive bank. -/
@[expose] def Comparison {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  prepared.1.Comparison shared × DependentVector
    (fun position : Fin base.faces.holes.length => (prepared.2.1.get position).Comparison shared)

/-- Execute each original exterior and bounded-hole comparison once, retaining their original occurrence positions. -/
def compare {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    prepared.Comparison shared :=
  let exterior := prepared.1.compare shared
  let holes := DependentVector.ofFn (fun position : Fin base.faces.holes.length =>
    (prepared.2.1.get position).compare shared)
  ⟨exterior, holes⟩

/-- The SAME retained polynomial comparison pays one original doubled-hole word at every sufficient later stage. -/
theorem comparison_hole_accurate (position : Fin base.faces.holes.length) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared lifted.mesh) (compared : prepared.Comparison shared)
    (later : prepared.index ≤ stage) :
    normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      ((base.faces.holes[position.val]'position.isLt).liftedBoundary lifted.vertices lifted.edges)) ≤ target := by
  have original := (prepared.2.1.get position).comparison_accurate readings (compared.2.get position)
    ((prepared.hole_le position).trans later)
  rewrite [(base.faces.holes[position.val]'position.isLt).liftedBoundary_eq, wordValue_append]
  exact original

/-- The retained polynomial comparison pays the actual root-transported two-lap exterior word. -/
theorem comparison_exterior_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared lifted.mesh) (compared : prepared.Comparison shared)
    (later : prepared.index ≤ stage) :
    normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (lifted.edges.indexedEdges lifted.vertices (base.bank.exterior.append base.bank.exterior) 0)) ≤ target := by
  have original := prepared.1.comparison_accurate readings compared.1 (prepared.exterior_le.trans later)
  rewrite [lifted.edges.indexedEdges_append, lifted.exterior_swap_odd degree,
    BranchCutLifts.otherSheet_zero, wordValue_append]
  exact original

/-- Every actual physical boundary word meets its paid target using the SAME retained polynomial comparison caches.

The original root-edge bank supplies the actual exterior sheet swap and doubled-hole incidence. No loop-zero,
root-closure, cap normalization or wanted period equality is an additional premise.
-/
theorem comparison_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared lifted.mesh) (compared : prepared.Comparison shared)
    (later : prepared.index ≤ stage) :
    ∀ word ∈ lifted.boundaryLoops,
      normSq (wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) word) ≤ target := by
  exact loops_bound degree (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
    (prepared.comparison_exterior_accurate degree readings compared later)
    (holes_bound (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (fun position => prepared.comparison_hole_accurate position readings compared later))

end Preparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopRequests
