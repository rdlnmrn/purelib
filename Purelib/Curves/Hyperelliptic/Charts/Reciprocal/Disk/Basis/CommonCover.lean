module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Periods.PeriodMatrix

section

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels

open Purelib.Data.Vector

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

public section

/-! A complete common mesh retains one original cell per basis row on each
whole interval. Endpoint reads use that interval owner even at cell boundaries. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation (left_le_midpoint midpoint_le_right)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge Endpoint dyadicEdges)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (IntervalOwner)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {data : UniformReciprocalModels.Data patch count}

set_option genInjectivity false in
/-- A common parameter interval retaining one original cell owner for the anchor and every basis row.

All source ownership bounds cover the whole interval, so endpoint readings reuse the same cell identities. -/
structure BasisCommonInterval (cover : Cover data) (covers : BasisSourceCovers
  parent) where
  /-- The actual retained common parameter edge. -/ edge : ParameterEdge
  /-- The retained edge endpoints are weakly ordered. -/ ordered : edge.left.parameter ≤ edge.right.parameter
  /-- The original anchor-cover cell owner for the whole common interval. -/ anchor :
    IntervalOwner data cover.mesh.edges edge
  /-- The original per-basis cell owners covering that same whole interval. -/ sources : DependentVector
    (fun row => IntervalOwner (covers.get row).data (covers.get row).cover.mesh.edges edge)

constructive_injectivity BasisCommonInterval

/-- Attach the actual anchor and basis owners to the supplied dyadic edge list.

Each interval retains its supplied edge and the original cover's cached cell owners.
The recursion preserves the order and multiplicity of the entire input list. -/
@[expose] def entries (cover : Cover data) (covers : BasisSourceCovers parent)
  (depth : Nat)
    (anchorLater : cover.mesh.depth ≤ depth) (sourceLater : ∀ row, (covers.get row).cover.mesh.depth ≤ depth) :
    (edges : List ParameterEdge) → (∀ edge ∈ edges, edge ∈
      dyadicEdges depth firstEndpoint
      lastEndpoint) →
    List (BasisCommonInterval cover covers)
  | [], _ => []
  | edge :: rest, members =>
      ⟨edge, dyadic_ordered depth
        firstEndpoint lastEndpoint (by decide) (members edge
        List.mem_cons_self),
        Cover.intervalOwner cover depth anchorLater edge (members edge List.mem_cons_self),
        DependentVector.ofFn (fun row => Cover.intervalOwner (covers.get row).cover depth (sourceLater row)
          edge (members edge List.mem_cons_self))⟩ ::
        CommonCover.entries cover covers depth anchorLater
          sourceLater rest (fun edge member => members edge (List.mem_cons_of_mem _ member))

/-- Reading the common interval edges returns exactly the supplied edge list.

Structural induction retains each head edge and the same ordered suffix, independently
of the ownership certificates stored alongside them. -/
theorem entries_edges (cover : Cover data) (covers : BasisSourceCovers parent)
  (depth : Nat)
    (anchorLater : cover.mesh.depth ≤ depth) (sourceLater : ∀ row, (covers.get row).cover.mesh.depth ≤ depth)
    (edges : List ParameterEdge) (members : ∀ edge ∈ edges, edge ∈
      dyadicEdges depth firstEndpoint
      lastEndpoint) :
    (entries cover covers depth anchorLater sourceLater
      edges members).map BasisCommonInterval.edge = edges
      := by
  induction edges with
  | nil => rfl
  | cons edge rest ih => exact congrArg (List.cons edge) (ih _)

set_option genInjectivity false in
/-- The full ordered mesh refines the anchor, every basis cover and a supplied minimum depth. It retains original cells
instead of preparing replacement models. -/
structure BasisCommonCover (cover : Cover data) (covers : BasisSourceCovers
  parent) (minimum : Nat) where
  /-- The cached common depth refining the original anchor, every basis cover and the supplied minimum. -/ depth : Nat
  /-- The common depth is the exact maximum of the original minimum and retained cover depths. -/ depth_eq : depth = max
    minimum (max cover.mesh.depth (covers.maximum fun _ source => source.cover.mesh.depth))
  /-- The complete ordered list of original-owner common intervals. -/ intervals : List
    (BasisCommonInterval cover covers)
  /-- The retained interval edges are exactly the full dyadic mesh at the cached common depth. -/ edges_eq :
    intervals.map BasisCommonInterval.edge =
    dyadicEdges depth firstEndpoint
    lastEndpoint

constructive_injectivity BasisCommonCover

/-- Refine the original anchor and all basis covers to one common depth and retain their actual cell owners on every
interval. -/
@[expose] def BasisCommonCover.build (cover : Cover data) (covers :
  BasisSourceCovers parent) (minimum : Nat) :
    BasisCommonCover cover covers minimum :=
  let depth := max minimum (max cover.mesh.depth (covers.maximum fun _ source => source.cover.mesh.depth))
  let anchorLater : cover.mesh.depth ≤ depth := (Data.Nat.Order.le_max_left ..).trans (Data.Nat.Order.le_max_right ..)
  let sourceLater : ∀ row, (covers.get row).cover.mesh.depth ≤ depth := fun row =>
    (covers.get_le_maximum (fun _ source => source.cover.mesh.depth) row).trans
      ((Data.Nat.Order.le_max_right ..).trans (Data.Nat.Order.le_max_right ..))
  let edges := dyadicEdges depth firstEndpoint
    lastEndpoint
  ⟨depth, rfl, entries cover covers depth anchorLater
    sourceLater edges (fun _ member => member),
    entries_edges cover covers depth anchorLater
      sourceLater edges (fun _ member => member)⟩

namespace BasisCommonInterval

variable {cover : Cover data} {covers :
  BasisSourceCovers parent}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {edge : ParameterEdge} {cell :
    Cell data edge} {model :
    RootModel cell} {parameter :
    Coordinate}

/-- Keep the whole-interval owner when reading an endpoint or internal vertex. In particular, a boundary vertex does not
trigger a different cell lookup. -/
@[expose] def locations (interval : BasisCommonInterval
  cover covers) (regular : RegularBounds.Data cap)
    (anchor : Point cap model parameter)
    (between : interval.edge.left.parameter ≤ parameter ∧ parameter ≤ interval.edge.right.parameter) :
    BasisSourceLocations regular anchor covers :=
  DependentVector.ofFn fun row =>
    let retained := interval.sources.get row
    let located : Cells.Located (covers.get row).data (covers.get row).cover.mesh.edges parameter :=
      ⟨retained.owner, retained.member, retained.cell, retained.lower.trans between.1, between.2.trans retained.upper⟩
    let sourceModel := RootModel.build located.cell
    let point := Point.build cap sourceModel parameter located.between
    ⟨located, sourceModel, point, Join.ofRecast anchor point,
      ArcSamples.Data.build regular located.cell,
      EndpointComparison.Data.build regular point⟩

/-- Every point of the interval belongs to the same retained source owner; this supplies both subinterval hypotheses of
the primitive comparison. -/
theorem locations_contains (interval : BasisCommonInterval
  cover covers) (regular : RegularBounds.Data cap)
    (anchor : Point cap model parameter)
    (between : interval.edge.left.parameter ≤ parameter ∧ parameter ≤ interval.edge.right.parameter)
    {other : Coordinate} (inside : interval.edge.left.parameter ≤ other ∧ other ≤
      interval.edge.right.parameter)
    (row : Fin genus) :
    ((interval.locations regular anchor between).owners.get row).edge.left.parameter ≤ other ∧
      other ≤ ((interval.locations regular anchor between).owners.get row).edge.right.parameter := by
  rw [BasisSourceLocations.owners_get]
  unfold locations
  rw [DependentVector.ofFn_get]
  exact ⟨(interval.sources.get row).lower.trans inside.1, inside.2.trans (interval.sources.get row).upper⟩

end BasisCommonInterval
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

end
