module
import Purelib.Data.List.Filter
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

/-!
# Removing zero movement while retaining actual root transport

A stationary fragment's two original query names agree through its retained
local primitive patch. Its numerical increment is zero in any selected
route. These facts permit removal from the geometric word without dropping
an unproved root handoff or preparing replacement owners.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

public section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Data.List

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

open Purelib.Riemann.Meshes (FramedPuncturedGrid)

open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}

namespace SheetEntries.RegularPrimitiveFragment.SheetEntry

/-- An original root query at the retained first point is equivalent to the same assigned local sample owner.

The original local request and endpoint contact retain the sample's patch membership. Its point comparison uses the
supplied parameter and exact contact equality with that same sample owner. -/
private theorem query_equivalent_at_first {parent : CenteredEdge curve source}
    {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
      {interval : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
    {fragment : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragment axes
      parent partition interval} {request : LocalRequest parent count target}
    (assigned :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
      fragment domains request) (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (equal : parent.edge.point parameter = fragment.located.first) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName parameter inside)
      (Purelib.Riemann.Paths.OwnerTraceReadings.ownerName assigned.sample.owner)) := by
  rcases request with ⟨patch, neighborhood, neighborhoodEq, requested, finishInside⟩
  subst neighborhood
  exact ⟨patch.point_equivalent_at count parameter inside equal
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.neighborhood_endpoints assigned).1 assigned.sample⟩

end SheetEntries.RegularPrimitiveFragment.SheetEntry

namespace RootedWords.LiftedFragment

/-- Both original query names are compared to the same retained sample.

Stationarity identifies the original fragment endpoints. The two retained point comparisons compose through the same
local sample owner to certify the root handoff. -/
theorem stationary_roots (piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains
  mesh source count target)
    (stationary : piece.last = piece.first) : Nonempty (Gaussian.Equivalence.NamedEquivalent piece.firstName
      piece.lastName) := by
  obtain ⟨first⟩ := piece.assigned.original
  obtain ⟨last⟩ := piece.assigned.query_equivalent_at_first piece.interval.upper piece.occurrence.finishInside
    (piece.fragment.located.last_eq.symm.trans stationary)
  exact ⟨first.trans last.symm⟩

/-- A finite geometric subword; all retained entries are original pieces.

The original Boolean endpoint comparison filters the supplied list in order. Every moving occurrence retains its same
parent, request, face assignment and lifted edge cache. -/
@[expose] def movingPieces (pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target)) :
    List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source count target)
      :=
  pieces.filter (fun piece => decide (piece.last ≠ piece.first))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment in
/-- Removing stationary original fragments commutes with ordered concatenation.

The unchanged Boolean predicate acts on both original list spines. Filtering keeps the same accepted occurrences and
their order before concatenating them. -/
theorem movingPieces_append (first last : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment
  axes domains mesh source count target)) :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces (first ++ last) =
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces first ++
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces last := Filter.filter_append _
      first last

/-- Each retained moving fragment is an original list member with distinct endpoints.

The unchanged filter supplies the original occurrence and its true Boolean acceptance certificate. Decoding that same
result certifies the retained endpoint inequality. -/
theorem movingPieces_mem {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target)}
    {piece : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source count
      target} (member : piece ∈ Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces
      pieces) :
    piece ∈ pieces ∧ piece.last ≠ piece.first := by
  have present := Filter.mem_filter.mp member
  exact ⟨present.1, of_decide_eq_true present.2⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment in
/-- Removing stationary increments preserves the original rooted word.

Each removed occurrence supplies its actual query-root handoff through the retained sample owner. The remaining word
keeps its original endpoint equivalences and all moving occurrences. -/
theorem RootedWord.moving {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target)}
    {first last : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord pieces first firstName
      last lastName) :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.RootedWord
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces pieces) first firstName last
      lastName := by
  induction word with
  | nil coordinate root => exact .nil coordinate root
  | cons piece coordinate root tail ih =>
      by_cases stationary : piece.last = piece.first
      · have removed : decide (piece.last ≠ piece.first) = false := decide_eq_false (not_not_intro stationary)
        rewrite [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces,
          Filter.filter_cons_of_neg (head := piece) (predicate := fun item => decide (item.last ≠ item.first)) (fun
            accepted => Bool.noConfusion (removed.symm.trans accepted))]
        obtain ⟨entry⟩ := root
        obtain ⟨through⟩ := piece.stationary_roots stationary
        exact ih.changeStart (coordinate.trans stationary.symm) ⟨entry.trans through⟩
      · rewrite [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces,
          Filter.filter_cons_of_pos (head := piece) (predicate := fun item => decide (item.last ≠ item.first))
            (decide_eq_true stationary)]
        exact .cons piece coordinate root ih

/-- Removing stationary fragments preserves the retained numerical sum.

Each removed occurrence has a certified zero increment for its original route and face selection. Scalar addition
transports the unchanged tail, preserving repeated occurrences and the original moving sum. -/
theorem movingPieces_sum (pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes
  domains mesh source count target))
    {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
    {budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
      {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source index domains}
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces pieces).map (fun piece =>
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute piece) shared)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece =>
        Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute piece) shared)) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      by_cases stationary : piece.last = piece.first
      · have removed : decide (piece.last ≠ piece.first) = false := decide_eq_false (not_not_intro stationary)
        rewrite [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces,
          Filter.filter_cons_of_neg (head := piece) (predicate := fun item => decide (item.last ≠ item.first)) (fun
            accepted => Bool.noConfusion (removed.symm.trans accepted)), List.map_cons]
        change Data.Gaussian.Norm.Sum.Basic.gaussianSum _ =
          Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece
          (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute piece) shared +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum _
        rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.routeValue_stationary piece stationary shared,
          zero_add]
        exact ih
      · rewrite [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces,
          Filter.filter_cons_of_pos (head := piece) (predicate := fun item => decide (item.last ≠ item.first))
            (decide_eq_true stationary), List.map_cons, List.map_cons]
        change Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece
          (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute piece) shared +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum _ = _ + Data.Gaussian.Norm.Sum.Basic.gaussianSum _
        exact congrArg (fun rest => Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts.routeValue piece
          (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute piece) shared + rest) ih

end RootedWords.LiftedFragment

namespace SourceWords

/-- Original segment grouping survives zero-movement removal.

Every original segment retains its rooted word and source certificates on the accepted subword. Concatenation joins the
same ordered segment groups after the certified stationary handoffs. -/
theorem PathSourceWords.moving {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {firstName lastName : Gaussian.Name.Basic.Named}
    {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)}
    (words : Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords path firstName lastName pieces) :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords path firstName lastName
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces pieces) := by
  induction words with
  | nil point equivalent => exact .nil point equivalent
  | cons word original remaining ih =>
      rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces_append]
      exact .cons word.moving (fun piece member => original piece
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces_mem member).1) ih

/-- Remove stationary original fragments from all four retained tour segments while preserving their query-root handoffs
and source grouping.

The original forward, right, backward and left words are filtered independently by the same endpoint predicate. Their
original tour ordering and retained junction certificates compose unchanged. -/
theorem TourSourceWords.moving {tour : ClosedBoundaryDoublePath curve}
    {firstName lastName : Gaussian.Name.Basic.Named}
    {pieces : List (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment axes domains mesh source
      count target)}
    (words : Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.TourSourceWords tour firstName lastName pieces) :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.TourSourceWords tour firstName lastName
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces pieces) := by
  cases words with
  | mk forward right backward left =>
      rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces_append,
        Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces_append,
        Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment.movingPieces_append]
      exact .mk forward.moving right.moving backward.moving left.moving

end SourceWords
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
