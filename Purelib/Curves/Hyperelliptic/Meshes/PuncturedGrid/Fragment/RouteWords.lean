module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring
import Purelib.Data.List.OfFn.Basic

public section

/-! Whole-word transport of original partial increments to retained routes. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords

open Purelib.Approximation.Rational
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Differentials.Basic.Differential genus} {axes :
    PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}

/-- Retain the selected occurrence while reversing its orientation. -/
@[expose] def reverseRoute {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge.reverse) :
      MeshPathWalks.EdgeRoute mesh edge :=
  match route with
  | .forward location => .backward location
  | .backward location => .forward location

/-- The finite route lookup depends only on the lifted edge and traversal
orientation. The support certificate contributes no numerical data. -/
@[expose] def directedRoute (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (edge : Topology.Polygon.Stokes.OrientedEdge vertices.count)
    (supported : edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (forward : Bool) : MeshPathWalks.EdgeRoute mesh edge :=
  if forward then MeshPathWalks.EdgeRoute.build mesh edge supported
  else RouteWords.reverseRoute
    (MeshPathWalks.EdgeRoute.build mesh edge.reverse
    (by simpa only [Topology.Polygon.Stokes.OrientedEdge.reverse_reverse] using supported.symm))

/-- The original partial traversal, including a stationary fragment. -/
@[expose] def routeForward (piece : RootedWords.LiftedFragment axes domains
  mesh source count target) : Bool :=
  decide (piece.fragment.source.first.parameter ≤ piece.fragment.source.last.parameter)

/-- Use the same finite lookup as the standard grid-walk assignment in the
original fragment's direction. The returned route is reoriented onto its
containing edge, while its face and sheet remain those of that lookup. -/
@[expose] def canonicalRoute (piece : RootedWords.LiftedFragment axes
  domains mesh source count target) :
    MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge := by
  have supported : piece.occurrence.side.edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces
    ∨
      piece.occurrence.side.edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces :=
        by
    rw [piece.occurrence.side.indexed_eq piece.fragment.source.edge]
    exact SkeletonFaceAssignments.indexedEdge_supported mesh
      piece.fragment.source.edge _
  exact RouteWords.directedRoute mesh piece.occurrence.side.edge supported
    (RouteWords.routeForward piece)

set_option genInjectivity false in
/-- Route requests aligned with an original partial word.

Each spine entry keeps its original occurrence, chosen route and contact
request. The indexed word preserves all repeated and reversed occurrences. -/
inductive RouteRequests (allowance : Fraction.Rational) :
    (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)) →
      (polynomial : optParam (Option (Ordinary curve.polynomial)) none) → Type 2
  /-- The empty original word requires no route contacts. -/ | nil
    {polynomial : Option (Ordinary curve.polynomial)} : RouteRequests allowance [] polynomial
  /-- Retain the actual head fragment's selected route, shared contact and budget together with the original tail
    requests. -/ | cons {piece : RootedWords.LiftedFragment axes domains
    mesh source count target}
      {pieces : List (RootedWords.LiftedFragment axes domains mesh source
        count target)}
      {polynomial : Option (Ordinary curve.polynomial)}
      (location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
      (contact : RouteContacts.RouteContact piece location)
      (budget : RouteContacts.RouteContact.Budget contact allowance polynomial)
      (tail : RouteRequests allowance pieces polynomial) :
        RouteRequests allowance (piece :: pieces) polynomial

constructive_injectivity RouteRequests

namespace RouteRequests

variable {allowance : Fraction.Rational}

/-- Select one actual route per original fragment and retain its shared contact and scalar request in the same word
order. -/
@[expose] def build (allowance : Fraction.Rational) (positive : 0 < allowance)
    (select : (piece : RootedWords.LiftedFragment axes domains mesh source
      count target) → MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge) :
    (pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)) → RouteRequests allowance pieces
  | [] => .nil
  | piece :: pieces =>
      let location := select piece
      let contact := RouteContacts.RouteContact.build piece location
      .cons location contact (RouteContacts.RouteContact.budget contact
        allowance positive) (RouteRequests.build
        allowance positive select pieces)

/-- The maximum sufficient contact-reading index over the original fragment word. -/
@[expose] def index {polynomial : Option (Ordinary curve.polynomial)} :
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} →
      RouteRequests allowance pieces polynomial → Nat
  | _, .nil => 0
  | _, .cons _ _ budget tail => max (RouteContacts.RouteContact.Budget.index budget) tail.index

/-- One actual bounded request occurrence, retaining its complete route, contact and selected numerical budget. -/
@[expose] def Entry (piece : RootedWords.LiftedFragment axes domains mesh source count target)
    (polynomial : Option (Ordinary curve.polynomial) := none) : Type _ :=
  Σ location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge,
    Σ contact : RouteContacts.RouteContact piece location, contact.Budget allowance polynomial

/-- The complete route/contact geometry of one retained occurrence, independent of its numerical specification. -/
@[expose] def Geometry (piece : RootedWords.LiftedFragment axes domains mesh source count target) : Type _ :=
  Σ location : MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge,
    RouteContacts.RouteContact piece location

/-- Read the actual original bounded occurrence without running a route, root, contact, cache or request producer. -/
@[expose] def «at» {polynomial : Option (Ordinary curve.polynomial)} :
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} →
      (requests : RouteRequests allowance pieces polynomial) → (position : Fin pieces.length) →
        Entry (allowance := allowance) (pieces[position.val]'position.isLt) polynomial
  | _, .nil, position => Fin.elim0 position
  | _, .cons location contact budget _remaining, ⟨0, _bound⟩ => ⟨location, contact, budget⟩
  | _, .cons _location _contact _budget remaining, ⟨position + 1, bound⟩ =>
      «at» remaining ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- Read the whole actual route/contact pair once from its original bounded request occurrence. -/
@[expose] def geometryAt {polynomial : Option (Ordinary curve.polynomial)}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (requests : RouteRequests allowance pieces polynomial) (position : Fin pieces.length) :
    Geometry (pieces[position.val]'position.isLt) :=
  let selected := requests.at position
  ⟨selected.1, selected.2.1⟩

/-- Each actual stored numerical request floor is bounded by the same whole request maximum. -/
theorem at_index_le {polynomial : Option (Ordinary curve.polynomial)} :
    ∀ {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      (requests : RouteRequests allowance pieces polynomial) (position : Fin pieces.length),
      RouteContacts.RouteContact.Budget.index (requests.at position).2.2 ≤ requests.index
  | _, .nil, position => Fin.elim0 position
  | _, .cons _location _contact _budget _remaining, ⟨0, _bound⟩ => Nat.Order.le_max_left _ _
  | _, .cons _location _contact _budget remaining, ⟨position + 1, bound⟩ =>
      (at_index_le remaining ⟨position, Nat.lt_of_succ_lt_succ bound⟩).trans (Nat.Order.le_max_right _ _)

/-- Select a new allowance on the SAME literal raw route/contact spine.

Every stored location, root Owner, prepared path, ParentCache and pair of
Entries is forwarded. The numerical legacy budget alone is reselected;
the resulting raw request can then select genuine polynomial budgets.
-/
def retarget {previous : Fraction.Rational} (allowance : Fraction.Rational) (positive : 0 < allowance) :
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} →
      RouteRequests previous pieces → RouteRequests allowance pieces
  | _, .nil => .nil
  | _, .cons location contact _ remaining =>
      let budget := contact.budget allowance positive
      let tail := retarget allowance positive remaining
      .cons location contact budget tail

/-- Retargeting an actually built raw spine preserves its complete original canonical-builder identity.

The equality is proved pointwise in the literal piece list. It does not
execute the builder to recover data; the retarget operation forwards the
given contacts and uses this law only for whole-value proof transport.
-/
theorem retarget_build (previous : Fraction.Rational) (previousPositive : 0 < previous)
    (allowance : Fraction.Rational) (positive : 0 < allowance)
    (select : (piece : RootedWords.LiftedFragment axes domains mesh source count target) →
      MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge) :
    (pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)) →
      (RouteRequests.build previous previousPositive select pieces).retarget allowance positive =
        RouteRequests.build allowance positive select pieces
  | [] => rfl
  | piece :: pieces =>
      congrArg (fun tail => RouteRequests.cons (allowance := allowance) (polynomial := none)
        (select piece) (RouteContacts.RouteContact.build piece (select piece))
        ((RouteContacts.RouteContact.build piece (select piece)).budget allowance positive) tail)
          (retarget_build previous previousPositive allowance positive select pieces)

/-- Prepare true P budgets on the GIVEN exact route/contact spine, without constructing its geometry again.

Each old location, root Owner, prepared path, ParentCache and both Entries
are forwarded as the literal stored contact. Only numerical bounds and
independent source/face floors are selected for the supplied polynomial.
-/
def onNumerator (ordinary : Ordinary curve.polynomial) (positive : 0 < allowance) :
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} →
      RouteRequests allowance pieces → RouteRequests allowance pieces (some ordinary)
  | _, .nil => .nil
  | _, .cons location contact _oldBudget remaining =>
      .cons location contact (contact.prepareBudget allowance positive (some ordinary))
        (onNumerator ordinary positive remaining)

/-- Each rebudgeted occurrence is the actual old route/contact pair with its one new genuine-P budget factory. -/
theorem onNumerator_at (ordinary : Ordinary curve.polynomial) (positive : 0 < allowance) :
    ∀ {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      (requests : RouteRequests allowance pieces) (position : Fin pieces.length),
      (requests.onNumerator ordinary positive).at position =
        (let original := requests.at position
         (⟨original.1, original.2.1, original.2.1.prepareBudget allowance positive (some ordinary)⟩ :
           Entry (allowance := allowance) (pieces[position.val]'position.isLt) (some ordinary)))
  | _, .nil, position => Fin.elim0 position
  | _, .cons _location _contact _budget _remaining, ⟨0, _bound⟩ => rfl
  | _, .cons _location _contact _budget remaining, ⟨position + 1, bound⟩ =>
      onNumerator_at ordinary positive remaining ⟨position, Nat.lt_of_succ_lt_succ bound⟩

/-- Rebudgeting retains every whole route/contact cache at its same original finite occurrence. -/
theorem onNumerator_geometryAt (ordinary : Ordinary curve.polynomial) (positive : 0 < allowance) :
    ∀ {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      (requests : RouteRequests allowance pieces) (position : Fin pieces.length),
      (requests.onNumerator ordinary positive).geometryAt position = requests.geometryAt position
  | _, .nil, position => Fin.elim0 position
  | _, .cons _location _contact _budget _remaining, ⟨0, _bound⟩ => rfl
  | _, .cons _location _contact _budget remaining, ⟨position + 1, bound⟩ =>
      onNumerator_geometryAt ordinary positive remaining ⟨position, Nat.lt_of_succ_lt_succ bound⟩

section NumeratorReadings

variable {numerator : CoefficientPolynomial} {polynomial : Option (Ordinary curve.polynomial)}
variable {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {numericalIndex : Nat}
  {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source numericalIndex (numerator := numerator) domains}

/-- The actual selected-route partial readings in original fragment order. -/
@[expose] def values (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)} → RouteRequests allowance pieces polynomial → List
      Gaussian.Basic.Canonical
  | _, .nil => []
  | _, .cons (piece := piece) location _ _ tail => RouteContacts.routeValue
    piece location shared :: tail.values shared

/-- Rebudgeting reads the literal same route occurrence values on a GIVEN actual numerator bank. -/
theorem onNumerator_values (ordinary : Ordinary curve.polynomial) (positive : 0 < allowance)
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    ∀ {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      (requests : RouteRequests allowance pieces),
      (requests.onNumerator ordinary positive).values shared = requests.values shared
  | _, .nil => rfl
  | _, .cons (piece := piece) location _contact _budget remaining =>
      congrArg (List.cons (RouteContacts.routeValue piece location shared))
        (onNumerator_values ordinary positive shared remaining)

/-- The constructed request readings are exactly the selected-route readings of the original fragments. -/
theorem build_values (allowance : Fraction.Rational) (positive : 0 < allowance)
    (select : (piece : RootedWords.LiftedFragment axes domains mesh source
      count target) → MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
    (pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)) (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (RouteRequests.build allowance positive select pieces).values
      shared = pieces.map (fun piece => RouteContacts.routeValue piece
      (select piece) shared) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
    exact congrArg (List.cons (RouteContacts.routeValue piece (select piece)
      shared)) ih

/-- The original partial-fragment values minus their retained route-occurrence readings. -/
@[expose] def errors (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)} → RouteRequests allowance pieces polynomial → List
      Gaussian.Basic.Canonical
  | _, .nil => []
  | _, .cons (piece := piece) location _ _ tail =>
      (piece.value shared - RouteContacts.routeValue piece location shared)
        :: RouteRequests.errors shared tail

/-- The actual selected-route reading list retains its original bounded request table in literal order. -/
theorem values_eq_ofFn {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (requests : RouteRequests allowance pieces polynomial) (shared : Face.CommonMeshes.FaceSharedMeshes budgets
        numerics) :
    requests.values shared = List.ofFn (fun position : Fin pieces.length =>
      RouteContacts.routeValue (pieces[position.val]'position.isLt) (requests.at position).1 shared) := by
  induction pieces with
  | nil => cases requests; rfl
  | cons piece pieces following =>
      cases requests with
      | cons location contact budget remaining =>
          exact (congrArg (List.cons (RouteContacts.routeValue piece location shared)) (following remaining)).trans
            (Data.List.OfFn.Basic.ofFn_succ (function := fun position : Fin (piece :: pieces).length =>
              RouteContacts.routeValue ((piece :: pieces)[position.val]'position.isLt)
                ((RouteRequests.cons location contact budget remaining).at position).1 shared)).symm

/-- There is one comparison error per original fragment occurrence. -/
theorem errors_length {pieces : List (RootedWords.LiftedFragment
  axes domains mesh source count target)}
    (requests : RouteRequests allowance pieces polynomial) (shared :
      Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (requests.errors shared).length = pieces.length := by
  induction requests with
  | nil => rfl
  | cons location contact budget tail ih => exact congrArg Nat.succ ih

/-- The actual ordered discrepancy list is its original bounded request table, retaining every occurrence. -/
theorem errors_eq_ofFn {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (requests : RouteRequests allowance pieces polynomial) (shared : Face.CommonMeshes.FaceSharedMeshes budgets
        numerics) :
    requests.errors shared = List.ofFn (fun position : Fin pieces.length =>
      (pieces[position.val]'position.isLt).value shared -
        RouteContacts.routeValue (pieces[position.val]'position.isLt) (requests.at position).1 shared) := by
  induction pieces with
  | nil => cases requests; rfl
  | cons piece pieces following =>
      cases requests with
      | cons location contact budget remaining =>
          exact (congrArg (List.cons (piece.value shared - RouteContacts.routeValue piece location shared))
            (following remaining)).trans
            (Data.List.OfFn.Basic.ofFn_succ (function := fun position : Fin (piece :: pieces).length =>
              ((piece :: pieces)[position.val]'position.isLt).value shared -
                RouteContacts.routeValue ((piece :: pieces)[position.val]'position.isLt)
                  ((RouteRequests.cons location contact budget remaining).at position).1 shared)).symm

/-- The total error is exactly the original fragment sum minus its retained route-reading sum. -/
theorem errors_sum {pieces : List (RootedWords.LiftedFragment axes
  domains mesh source count target)}
    (requests : RouteRequests allowance pieces polynomial) (shared :
      Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    Gaussian.Norm.Sum.Basic.gaussianSum (requests.errors shared) = Gaussian.Norm.Sum.Basic.gaussianSum
      (pieces.map (fun piece => piece.value shared)) - Gaussian.Norm.Sum.Basic.gaussianSum (requests.values shared)
      := by
  induction requests with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons location contact budget tail ih =>
      change (_ - _) + Gaussian.Norm.Sum.Basic.gaussianSum (tail.errors shared) = (_ + _) - (_ + _)
      rw [ih]
      ring1

end NumeratorReadings

variable {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {numericalIndex : Nat}
  {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source numericalIndex domains}

/-- Every original retained fragment error fits the local allowance at a sufficiently late common reading.

The common retained stage dominates each original contact request.
Every occurrence keeps its original route, shared lookup and local allowance. -/
private theorem errors_bounded {pieces : List (RootedWords.LiftedFragment
  axes domains mesh source count target)}
    (requests : RouteRequests allowance pieces) (shared :
      Face.CommonMeshes.FaceSharedMeshes budgets numerics)
    (later : requests.index ≤ numericalIndex)
    (included : ∀ piece ∈ pieces, piece.first ∈ points ∧ piece.last ∈ points) :
    ∀ value ∈ requests.errors shared, Gaussian.Norm.Basic.normSq value ≤ allowance := by
  induction pieces with
  | nil =>
    cases requests with
    | nil => intro value member; exact (List.not_mem_nil member).elim
  | cons piece pieces ih =>
    cases requests with
    | cons location contact budget tail =>
      intro value member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact (contact.accurate budget shared ((Nat.Order.le_max_left _ _).trans later)
          (included piece List.mem_cons_self).1 (included piece List.mem_cons_self).2).le
      · exact ih tail ((Nat.Order.le_max_right _ _).trans later)
          (fun piece member => included piece (List.mem_cons_of_mem _ member)) value member

/-- The complete sum pays both factors of the actual original-fragment
count, including all repeated and reversed occurrences. -/
theorem accurate {pieces : List (RootedWords.LiftedFragment axes domains
  mesh source count target)}
    {requested : Fraction.Rational} (positive : 0 < requested)
    (requests : RouteRequests (Budget.Aggregate.perTerm
      requested pieces.length) pieces) (shared : Face.CommonMeshes.FaceSharedMeshes
      budgets numerics)
    (later : requests.index ≤ numericalIndex)
    (included : ∀ piece ∈ pieces, piece.first ∈ points ∧ piece.last ∈ points) :
    Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece => piece.value
      shared)) - Gaussian.Norm.Sum.Basic.gaussianSum (requests.values shared)) < requested := by
  rw [← requests.errors_sum shared]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  rw [requests.errors_length]
  exact requests.errors_bounded shared later included

end RouteRequests

set_option genInjectivity false in
/-- A whole-word transport request caches the selected scalar floor.

The request keeps the original fragment word and local allowance. Its
cached sufficient index is the maximum of those retained contact requests. -/
structure RouteRequest (pieces : List (RootedWords.LiftedFragment axes
  domains mesh source count target)) (allowance : Fraction.Rational)
    (polynomial : Option (Ordinary curve.polynomial) := none) : Type 2 where
  /-- The original whole-word allowance is positive. -/ positive : 0 < allowance
  /-- The actual original fragment requests at the allocated local tolerance. -/ requests :
    RouteRequests (Budget.Aggregate.perTerm allowance
    pieces.length) pieces polynomial
  /-- The cached common sufficient contact-reading index. -/ index : Nat
  /-- The common index is exactly the maximum of the retained original contact requests. -/ index_eq : index =
    requests.index

constructive_injectivity RouteRequest

namespace RouteRequest

/-- Allocate the positive whole-word allowance over the original occurrence count and cache the actual contact-stage
maximum. -/
@[expose] def build (pieces : List (RootedWords.LiftedFragment axes domains
  mesh source count target))
    (select : (piece : RootedWords.LiftedFragment axes domains mesh source
      count target) → MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
      RouteRequest pieces allowance :=
  let requests := RouteRequests.build
    (Budget.Aggregate.perTerm allowance pieces.length)
    (Budget.Aggregate.perTerm_positive positive _) select pieces
  ⟨positive, requests, requests.index, rfl⟩

/-- Retarget the GIVEN raw request while preserving every actual route/contact geometry cache.

The smaller or larger positive allowance selects real new numerical
budgets before observations. It does not relabel an existing reading or
rebuild a root, contact, Entry, query or prepared source path.
-/
def retarget {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {previous : Fraction.Rational} (request : RouteRequest pieces previous)
    (allowance : Fraction.Rational) (positive : 0 < allowance) : RouteRequest pieces allowance :=
  let requests := request.requests.retarget (Budget.Aggregate.perTerm allowance pieces.length)
    (Budget.Aggregate.perTerm_positive positive pieces.length)
  ⟨positive, requests, requests.index, rfl⟩

/-- The retargeted whole request forwards the original route/contact spine through its exact numerical operation. -/
theorem retarget_requests {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {previous : Fraction.Rational} (request : RouteRequest pieces previous)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    (request.retarget allowance positive).requests = request.requests.retarget
      (Budget.Aggregate.perTerm allowance pieces.length)
      (Budget.Aggregate.perTerm_positive positive pieces.length) := by
  unfold retarget
  rfl

/-- A whole original raw factory derives the actual retargeted factory, without rebuilding its data.

Only the unchanged positive-target and numerical-budget fields are
reselected. The pointwise spine identity transports the whole request and
its cached common floor to the original smaller-target builder expression.
-/
theorem retarget_factory {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {previous : Fraction.Rational} (request : RouteRequest pieces previous)
    (previousPositive : 0 < previous)
    (select : (piece : RootedWords.LiftedFragment axes domains mesh source count target) →
      MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
    (factory : request = RouteRequest.build pieces select previous previousPositive)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    request.retarget allowance positive = RouteRequest.build pieces select allowance positive := by
  cases factory
  have same := RouteRequests.retarget_build (Budget.Aggregate.perTerm previous pieces.length)
    (Budget.Aggregate.perTerm_positive previousPositive pieces.length)
    (Budget.Aggregate.perTerm allowance pieces.length)
    (Budget.Aggregate.perTerm_positive positive pieces.length) select pieces
  exact congrArg (fun actual => RouteRequest.mk positive actual actual.index rfl) same

/-- Select genuine P budgets and their maximum on the SAME complete supplied raw route request.

The original whole-word allowance and literal occurrence list are kept.
Every retained contact is reused through the indexed-spine operation;
no common numerical bank or observation is prepared here.
-/
def onNumerator {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {allowance : Fraction.Rational} (request : RouteRequest pieces allowance)
    (ordinary : Ordinary curve.polynomial) : RouteRequest pieces allowance (some ordinary) :=
  let requests := request.requests.onNumerator ordinary
    (Budget.Aggregate.perTerm_positive request.positive pieces.length)
  ⟨request.positive, requests, requests.index, rfl⟩

/-- The complete P request spine is its one retained-input rebudgeting factory. -/
theorem onNumerator_requests {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {allowance : Fraction.Rational} (request : RouteRequest pieces allowance)
    (ordinary : Ordinary curve.polynomial) :
    (request.onNumerator ordinary).requests = request.requests.onNumerator ordinary
      (Budget.Aggregate.perTerm_positive request.positive pieces.length) := by
  unfold onNumerator
  rfl

variable {pieces : List (RootedWords.LiftedFragment axes domains mesh source
  count target)} {allowance : Fraction.Rational}
  {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {numericalIndex : Nat}
  {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source numericalIndex domains}

set_option genInjectivity false in
/-- The cached selected-route values and their total with the original whole-word transport bound.

The retained values follow the original selected-route word. Their sum
and bound use the same cached request and sufficiently late common index. -/
structure Readings (request : RouteRequest pieces allowance)
  (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) where
  /-- The actual route-occurrence readings in original fragment order. -/ values : List Gaussian.Basic.Canonical
  /-- The cached values are exactly the readings of the retained original requests. -/ values_eq : values =
    request.requests.values shared
  /-- The cached total of the actual retained route readings. -/ sum : Gaussian.Basic.Canonical
  /-- The cached total is exactly the Gaussian sum of the original values. -/ sum_eq : sum =
    Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The original partial-word sum differs from the cached route total by less than the supplied allowance. -/ accurate
    : Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece =>
    piece.value shared)) - sum) < allowance

constructive_injectivity Readings

/-- Read the retained original routes once at a sufficient common stage and cache their total with its paid comparison.
-/
@[expose] def readings (request : RouteRequest pieces allowance)
  (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics)
    (later : request.index ≤ numericalIndex)
    (included : ∀ piece ∈ pieces, piece.first ∈ points ∧ piece.last ∈ points) :
      Readings request shared :=
  let values := request.requests.values shared
  ⟨values, rfl, Gaussian.Norm.Sum.Basic.gaussianSum values, rfl, request.requests.accurate request.positive shared
    (request.index_eq ▸ later) included⟩

end RouteRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
