module
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

public section

/-! Whole-word transport of original partial increments to retained routes. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}

/-- Retain the selected occurrence while reversing its orientation. -/
@[expose] def reverseRoute {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge.reverse) :
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge :=
  match route with
  | .forward location => .backward location
  | .backward location => .forward location

/-- The finite route lookup depends only on the lifted edge and traversal
orientation. The support certificate contributes no numerical data. -/
@[expose] def directedRoute (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (edge : Topology.Polygon.Stokes.OrientedEdge vertices.count)
    (supported : edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (forward : Bool) : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge :=
  if forward then Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.build mesh edge supported
  else Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.reverseRoute
    (Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.build mesh edge.reverse
    (by simpa only [Topology.Polygon.Stokes.OrientedEdge.reverse_reverse] using supported.symm))

/-- The original partial traversal, including a stationary fragment. -/
@[expose] def routeForward (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
  mesh source count target) : Bool :=
  decide (piece.fragment.source.first.parameter ≤ piece.fragment.source.last.parameter)

/-- Use the same finite lookup as the standard grid-walk assignment in the
original fragment's direction. The returned route is reoriented onto its
containing edge, while its face and sheet remain those of that lookup. -/
@[expose] def canonicalRoute (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target) :
    Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge := by
  have supported : piece.occurrence.side.edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces
    ∨
      piece.occurrence.side.edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces :=
        by
    rw [piece.occurrence.side.indexed_eq piece.fragment.source.edge]
    exact Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedEdge_supported mesh
      piece.fragment.source.edge _
  exact Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.directedRoute mesh piece.occurrence.side.edge supported
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.routeForward piece)

set_option genInjectivity false in
/-- Route requests aligned with an original partial word.

Each spine entry keeps its original occurrence, chosen route and contact
request. The indexed word preserves all repeated and reversed occurrences. -/
inductive RouteRequests (allowance : Fraction.Rational) :
    List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source count target)
      → Type 2
  /-- The empty original word requires no route contacts. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance []
  /-- Retain the actual head fragment's selected route, shared contact and budget together with the original tail
    requests. -/ | cons {piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
    mesh source count target}
      {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
        count target)}
      (location : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
      (contact : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.RouteContact piece location)
      (budget : Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget contact.left contact.right
        allowance)
      (tail : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance pieces) :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance (piece :: pieces)

constructive_injectivity RouteRequests

namespace RouteRequests

variable {allowance : Fraction.Rational}

/-- Select one actual route per original fragment and retain its shared contact and scalar request in the same word
order. -/
@[expose] def build (allowance : Fraction.Rational) (positive : 0 < allowance)
    (select : (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target) → Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge) :
    (pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)) → Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance pieces
  | [] => .nil
  | piece :: pieces =>
      let location := select piece
      let contact := Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.RouteContact.build piece location
      .cons location contact (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.RouteContact.budget contact
        allowance positive) (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests.build
        allowance positive select pieces)

/-- The maximum sufficient contact-reading index over the original fragment word. -/
@[expose] def index : {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target)} → Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance
  pieces → Nat
  | _, .nil => 0
  | _, .cons _ _ budget tail => max budget.index tail.index

variable {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {numericalIndex : Nat}
  {budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source numericalIndex domains}

/-- The actual selected-route partial readings in original fragment order. -/
@[expose] def values (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)} → Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance pieces → List
      Gaussian.Basic.Canonical
  | _, .nil => []
  | _, .cons (piece := piece) location _ _ tail => Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue
    piece location shared :: tail.values shared

/-- The constructed request readings are exactly the selected-route readings of the original fragments. -/
theorem build_values (allowance : Fraction.Rational) (positive : 0 < allowance)
    (select : (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target) → Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
    (pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)) (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests.build allowance positive select pieces).values
      shared = pieces.map (fun piece => Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece
      (select piece) shared) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
    exact congrArg (List.cons (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece (select piece)
      shared)) ih

/-- The original partial-fragment values minus their retained route-occurrence readings. -/
@[expose] def errors (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)} → Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance pieces → List
      Gaussian.Basic.Canonical
  | _, .nil => []
  | _, .cons (piece := piece) location _ _ tail =>
      (piece.value shared - Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece location shared)
        :: Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests.errors shared tail

/-- There is one comparison error per original fragment occurrence. -/
private theorem errors_length {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment
  axes domains mesh source count target)}
    (requests : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance pieces) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (requests.errors shared).length = pieces.length := by
  induction requests with
  | nil => rfl
  | cons location contact budget tail ih => exact congrArg Nat.succ ih

/-- The total error is exactly the original fragment sum minus its retained route-reading sum. -/
private theorem errors_sum {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target)}
    (requests : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance pieces) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (requests.errors shared) = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (pieces.map (fun piece => piece.value shared)) - Data.Gaussian.Norm.Sum.Basic.gaussianSum (requests.values shared)
      := by
  induction requests with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons location contact budget tail ih =>
      change (_ - _) + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.errors shared) = (_ + _) - (_ + _)
      rw [ih]
      ring1

/-- Every original retained fragment error fits the local allowance at a sufficiently late common reading.

The common retained stage dominates each original contact request.
Every occurrence keeps its original route, shared lookup and local allowance. -/
private theorem errors_bounded {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment
  axes domains mesh source count target)}
    (requests : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests allowance pieces) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
    (later : requests.index ≤ numericalIndex)
    (included : ∀ piece ∈ pieces, piece.first ∈ points ∧ piece.last ∈ points) :
    ∀ value ∈ requests.errors shared, Data.Gaussian.Norm.Basic.normSq value ≤ allowance := by
  induction requests with
  | nil => intro value member; exact (List.not_mem_nil member).elim
  | @cons piece pieces location contact budget tail ih =>
      intro value member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact (contact.accurate budget shared ((Data.Nat.Order.le_max_left _ _).trans later)
          (included piece List.mem_cons_self).1 (included piece List.mem_cons_self).2).le
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans later)
          (fun piece member => included piece (List.mem_cons_of_mem _ member)) value member

/-- The complete sum pays both factors of the actual original-fragment
count, including all repeated and reversed occurrences. -/
theorem accurate {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
  mesh source count target)}
    {requested : Fraction.Rational} (positive : 0 < requested)
    (requests : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests (Rational.Budget.Aggregate.perTerm
      requested pieces.length) pieces) (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes
      budgets numerics)
    (later : requests.index ≤ numericalIndex)
    (included : ∀ piece ∈ pieces, piece.first ∈ points ∧ piece.last ∈ points) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece => piece.value
      shared)) - Data.Gaussian.Norm.Sum.Basic.gaussianSum (requests.values shared)) < requested := by
  rw [← requests.errors_sum shared]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  rw [requests.errors_length]
  exact requests.errors_bounded shared later included

end RouteRequests

set_option genInjectivity false in
/-- A whole-word transport request caches the selected scalar floor.

The request keeps the original fragment word and local allowance. Its
cached sufficient index is the maximum of those retained contact requests. -/
structure RouteRequest (pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target)) (allowance : Fraction.Rational) : Type 2 where
  /-- The original whole-word allowance is positive. -/ positive : 0 < allowance
  /-- The actual original fragment requests at the allocated local tolerance. -/ requests :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests (Rational.Budget.Aggregate.perTerm allowance
    pieces.length) pieces
  /-- The cached common sufficient contact-reading index. -/ index : Nat
  /-- The common index is exactly the maximum of the retained original contact requests. -/ index_eq : index =
    requests.index

constructive_injectivity RouteRequest

namespace RouteRequest

/-- Allocate the positive whole-word allowance over the original occurrence count and cache the actual contact-stage
maximum. -/
@[expose] def build (pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
  mesh source count target))
    (select : (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target) → Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh piece.occurrence.side.edge)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequest pieces allowance :=
  let requests := Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequests.build
    (Rational.Budget.Aggregate.perTerm allowance pieces.length)
    (Rational.Budget.Aggregate.perTerm_positive positive _) select pieces
  ⟨positive, requests, requests.index, rfl⟩

variable {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
  count target)} {allowance : Fraction.Rational}
  {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {numericalIndex : Nat}
  {budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source numericalIndex domains}

set_option genInjectivity false in
/-- The cached selected-route values and their total with the original whole-word transport bound.

The retained values follow the original selected-route word. Their sum
and bound use the same cached request and sufficiently late common index. -/
structure Readings (request : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequest pieces allowance)
  (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) where
  /-- The actual route-occurrence readings in original fragment order. -/ values : List Gaussian.Basic.Canonical
  /-- The cached values are exactly the readings of the retained original requests. -/ values_eq : values =
    request.requests.values shared
  /-- The cached total of the actual retained route readings. -/ sum : Gaussian.Basic.Canonical
  /-- The cached total is exactly the Gaussian sum of the original values. -/ sum_eq : sum =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The original partial-word sum differs from the cached route total by less than the supplied allowance. -/ accurate
    : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece =>
    piece.value shared)) - sum) < allowance

constructive_injectivity Readings

/-- Read the retained original routes once at a sufficient common stage and cache their total with its paid comparison.
-/
@[expose] def readings (request : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequest pieces allowance)
  (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
    (later : request.index ≤ numericalIndex)
    (included : ∀ piece ∈ pieces, piece.first ∈ points ∧ piece.last ∈ points) :
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequest.Readings request shared :=
  let values := request.requests.values shared
  ⟨values, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum values, rfl, request.requests.accurate request.positive shared
    (request.index_eq ▸ later) included⟩

end RouteRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
