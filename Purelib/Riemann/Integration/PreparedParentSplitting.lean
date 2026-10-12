module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.Nat.Multiplication
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Polynomial.Clearance.Box.Region

import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
public import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
public import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# One common mesh for geometrically split prepared requests

The original centered parents and local requests remain the indices of the
cached splitting spine. Rational fragments obtain containing cells without
caller assignments, and all fragment endpoints are inserted into one common
mesh. Exact telescoping preserves the actual retained request sum. Analytic
comparison across successive containing cells is a separate obligation.
-/

namespace Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.List
open Purelib.Data.Nat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Riemann.Branches
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {columns rows : Nat} {geometry : Geometry columns rows}
  {genus : Nat} {curve : HyperellipticCurve genus} {differential :
    Differential genus}

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Paths in
/-- The original prepared parent's point is its exact affine endpoint interpolation. -/
theorem prepared_point_eq (parent : CenteredEdge curve differential) (parameter : Coordinate) :
    parent.edge.point parameter = PreparedSegmentCuts.point (parent.edge.point 0) (parent.edge.point 1) parameter := by
  change parent.edge.localSegment.pointAt parameter = PreparedSegmentCuts.point
    (parent.edge.localSegment.pointAt 0) (parent.edge.localSegment.pointAt 1) parameter
  rw [parent.edge.localSegment.pointAt_zero, parent.edge.localSegment.pointAt_one, PreparedSegmentCuts.point_eq_line]
  exact PreparedPathWinding.ClearSegment.pointAt_eq_line
    parent.edge.localSegment parameter

set_option genInjectivity false in
/-- An ordered bank of geometric segment splits indexed by the original prepared parent list.

Each retained split keeps the exact original parent endpoint values as its segment indices. -/
inductive ParentSplits (cuts : GridCuts geometry) : List (CenteredEdge curve differential) → Type 2
  /-- The empty original parent list has no retained geometric splits. -/ | nil : ParentSplits cuts []
  /-- Retain the exact original head-parent split and dependent tail splitting bank. -/ | cons {parent : CenteredEdge
    curve differential} {rest : List (CenteredEdge curve differential)}
      (split : SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1))
      (tail : ParentSplits cuts rest) : ParentSplits cuts (parent :: rest)

constructive_injectivity ParentSplits

namespace ParentSplits

variable {cuts : GridCuts geometry}

open Purelib.Riemann.Paths in
/-- Split each original prepared parent using the retained grid cuts and exact endpoint coverage. -/
@[expose] def build (cuts : GridCuts geometry) : (parents : List (CenteredEdge curve differential)) →
    (∀ parent ∈ parents, RectangularSegmentSplitting.Geometry.Covers geometry (parent.edge.point 0) ∧
      RectangularSegmentSplitting.Geometry.Covers geometry (parent.edge.point 1)) →
      ParentSplits cuts parents
  | [], _ => .nil
  | parent :: rest, covered =>
      .cons (SegmentSplit.build cuts (parent.edge.point 0) (parent.edge.point 1)
        (covered parent List.mem_cons_self).1 (covered parent List.mem_cons_self).2)
        (build cuts rest (fun parent member => covered parent (List.mem_cons_of_mem _ member)))

/-- Concatenate the original retained split-point lists in parent order. -/
@[expose] def points : {parents : List (CenteredEdge curve differential)} → ParentSplits cuts parents → List Gaussian
  | _, .nil => []
  | _, .cons split tail => split.points ++ tail.points

/-- The total original fragment count of the retained splitting bank. -/
@[expose] def pieceCount : {parents : List (CenteredEdge curve differential)} → ParentSplits cuts parents → Nat
  | _, .nil => 0
  | _, .cons split tail => split.count + tail.pieceCount

/-- The retained split-point list has exactly twice the original fragment count.

Every retained split supplies exactly two endpoint occurrences per original fragment. Concatenation composes their
displayed lengths without changing parent order or any repeated endpoint. -/
theorem points_length {parents : List (CenteredEdge curve differential)} (splits : ParentSplits cuts parents) :
    splits.points.length = 2 * splits.pieceCount := by
  induction splits with
  | nil => rfl
  | cons split tail ih =>
      change (split.points ++ tail.points).length = 2 * (split.count + tail.pieceCount)
      rw [Append.length_append, split.points_length, ih, Nat.mul_add]

/-- The retained total fragment count is bounded by the original parent count times the grid split bound.

Each original segment split retains the same grid fragment ceiling. Natural scalar addition and distributivity compose
those bounds along the exact original parent spine. -/
theorem pieceCount_le {parents : List (CenteredEdge curve differential)} (splits : ParentSplits cuts parents) :
    splits.pieceCount ≤ parents.length * (columns + rows + 5) := by
  induction splits with
  | nil => exact Nat.zero_le _
  | cons split tail ih =>
      change split.count + tail.pieceCount ≤ (_ + 1) * _
      rw [Multiplication.right_distrib, Nat.one_mul]
      exact (Nat.add_le_add split.count_le ih).trans_eq (Nat.add_comm _ _)

/-- A specific retained split occurrence in the original dependent splitting bank.

Repeated original parents retain distinct positions; membership preserves the exact split and spine without owner
equality tests. -/
inductive Member {parent : CenteredEdge curve differential}
    (split : SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)) :
    {parents : List (CenteredEdge curve differential)} → ParentSplits cuts parents → Prop
  /-- The selected original split is the retained head occurrence. -/ | here {rest : List (CenteredEdge curve
    differential)} (tail : ParentSplits cuts rest) : Member split (.cons split tail)
  /-- The selected original split occurs in the retained tail after the exact head split. -/ | there {head :
    CenteredEdge curve differential} {rest : List (CenteredEdge curve differential)}
      (first : SegmentSplit cuts (head.edge.point 0) (head.edge.point 1)) {tail : ParentSplits cuts rest}
      (member : Member split tail) : Member split (.cons first tail)

/-- A point in a retained split occurrence belongs to the exact complete split-point list. -/
theorem point_mem {parents : List (CenteredEdge curve differential)} {splits : ParentSplits cuts parents}
    {parent : CenteredEdge curve differential} {split : SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)}
    (member : Member split splits) {point : Gaussian} (present : point ∈ split.points) : point ∈ splits.points := by
  induction member with
  | here => exact List.mem_append_left _ present
  | there first member ih => exact List.mem_append_right _ ih

/-- Read the original request-polynomial increments at the exact retained fragment endpoints. -/
@[expose] def increments {count : Nat} {target : Coordinate} :
    {parents : List (CenteredEdge curve differential)} → ParentSplits cuts parents →
      RequestedParents count target parents → List Gaussian
  | _, .nil, .nil => []
  | _, .cons split tail, .cons request requests =>
      split.pieces.map (fun piece => request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint) ++ tail.increments requests

/-- The retained fragment increment list has exactly the original total piece count.

Each original fragment contributes one increment evaluated at its retained endpoints. The same split-piece cache and
dependent request tail determine the displayed list count. -/
theorem increments_length {parents : List (CenteredEdge curve differential)} (splits : ParentSplits cuts parents)
    {count : Nat} {target : Coordinate} (requests : RequestedParents count target parents) :
    (splits.increments requests).length = splits.pieceCount := by
  induction splits with
  | nil => cases requests; rfl
  | cons split tail ih =>
      cases requests with
      | cons request requests =>
          rw [increments, Append.length_append, Map.length_map, ih, pieceCount, split.count_eq]

open Purelib.Data.Gaussian in
/-- Geometric splitting preserves the exact original request-bank primitive sum.

Each original polynomial telescopes over its own retained segment split, preserving parent order and all cached request
owners. -/
theorem sum_eq {parents : List (CenteredEdge curve differential)} (splits : ParentSplits cuts parents)
    {count : Nat} {target : Coordinate} (requests : RequestedParents count target parents) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (splits.increments requests) = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      requests.increments
      := by
  have sumAppend (first last : List Gaussian) : Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum first + Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
    induction first with
    | nil =>
        change Data.Gaussian.Norm.Sum.Basic.gaussianSum last = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum last;
        ring1
    | cons first rest ih =>
        change first + Data.Gaussian.Norm.Sum.Basic.gaussianSum (rest ++ last) = (first +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum rest) +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum last
        rw [ih]
        ring1
  induction splits with
  | nil => cases requests; rfl
  | cons split tail ih =>
      cases requests with
      | cons request requests =>
          rw [increments, sumAppend, split.telescope, ih]
          rfl

end ParentSplits

namespace Geometry

/-- Membership in an original row and its row list gives membership in their flattening.

Structural row membership selects its exact original occurrence. Append membership transports that same point occurrence
into the displayed flattening without selecting a new row. -/
private theorem flatten_member {Alpha : Type*} {rows : List (List Alpha)} {row : List Alpha} {point : Alpha}
    (member : row ∈ rows) (present : point ∈ row) : point ∈ rows.flatten := by
  induction rows with
  | nil => exact (List.not_mem_nil member).elim
  | cons first rest ih =>
      rcases Membership.mem_cons.mp member with rfl | member
      · exact List.mem_append_left _ present
      · exact List.mem_append_right _ (ih member)

open Purelib.Riemann.Readings in
/-- Every bounded original column and row pair occurs in the retained all-cell list.

The original column and row witnesses occur in their unchanged bounded-function tables. Their actual row occurrence
supplies the same indexed pair in the displayed row-major flattening. -/
theorem allCells_mem (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (column, row) ∈ (RectangularExteriorBoundary.Geometry.allCells geometry) :=
  flatten_member (row := List.ofFn fun row => (column, row)) (OfFn.Basic.mem_ofFn.mpr ⟨column, rfl⟩)
    (OfFn.Basic.mem_ofFn.mpr ⟨row, rfl⟩)

end Geometry

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Readings in
set_option genInjectivity false in
/-- One original common mesh containing all retained split endpoints and supplied extra points.

The exact point-cache equation preserves parent order and extras, and the mesh remains indexed by that cache and the
complete original cell selection. -/
structure PreparedSplitMesh (cuts : GridCuts geometry) (parents : List (CenteredEdge curve differential))
    (extra : List Gaussian := []) where
  /-- The retained dependent splitting bank indexed by the original parents. -/ splits : ParentSplits cuts parents
  /-- The cached original split endpoints followed by supplied extra points. -/ points : List Gaussian
  /-- The point cache equals the exact retained split list concatenated with the original extras. -/ points_eq : points
    = splits.points ++ extra
  /-- The original common mesh on all cells containing the exact retained point cache. -/ mesh :
    RectangularCommonMesh.RectangularInverseModels.CommonMesh geometry (RectangularExteriorBoundary.Geometry.allCells
    geometry) points

constructive_injectivity PreparedSplitMesh

namespace PreparedSplitMesh

variable {cuts : GridCuts geometry} {parents : List (CenteredEdge curve differential)} {extra : List Gaussian}

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- Split the original covered parent list, cache its endpoints with supplied extras, and build their exact common mesh.
-/
@[expose] def build (cuts : GridCuts geometry) (parents : List (CenteredEdge curve differential))
    (covered : ∀ parent ∈ parents, RectangularSegmentSplitting.Geometry.Covers geometry (parent.edge.point 0) ∧
      RectangularSegmentSplitting.Geometry.Covers geometry (parent.edge.point 1))
    (extra : List Gaussian := []) : PreparedSplitMesh cuts parents extra :=
  let splits := ParentSplits.build cuts parents covered
  let points := splits.points ++ extra
  ⟨splits, points, rfl, RectangularCommonMesh.RectangularInverseModels.CommonMesh.build geometry
    (RectangularExteriorBoundary.Geometry.allCells geometry) points⟩

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Topology in
/-- Build the common split mesh from original traced-parent membership and cleared-box containment.

The retained trace's parent-lineage evidence supplies endpoint coverage on the original uniform geometry; the exact
parent list and extra points remain unchanged. -/
@[expose] def ofTraced {box : Purelib.Geometry.Rational.Box} (proper : box.Proper) (steps : Nat)
    (cuts : GridCuts (Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform box proper steps))
    (clearance : Region.RegionClearance curve.polynomial box)
    {ambient : Purelib.Geometry.Rational.Box} {base finish : Gaussian}
    {source : SquareRootContinuationChain.Owner (curve.polynomial.eval base)}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient base finish}
    (traced : PreparedPathTrace.TracedPath path source) (inside : Polynomial.Geometry.ClearPath.InBox box path)
    (sheet : Fin 2) (parents : List (CenteredEdge curve differential))
    (membership : ∀ parent ∈ parents, parent ∈
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofPreparedPath curve differential sheet
        traced.prepared).parents)
    (extra : List Gaussian := []) : PreparedSplitMesh cuts parents extra :=
  build cuts parents (fun parent member => by
    have reached := Observation.PreparedFaceTracePrefixes.traced_parent_reached clearance differential sheet
      traced inside parent (membership parent member)
    exact ⟨RectangularSegmentSplitting.Geometry.uniform_covers box proper steps reached.first_inside,
      RectangularSegmentSplitting.Geometry.uniform_covers box proper steps reached.last_inside⟩) extra

/-- The retained common point cache is bounded by twice the original grid fragment bound plus the extra count.

The exact point-cache equation contains the original split endpoints followed by the supplied extras. Their retained
lengths and fragment ceiling bound that same cached list. -/
theorem points_length_le (mesh : PreparedSplitMesh cuts parents extra) :
    mesh.points.length ≤ 2 * (parents.length * (columns + rows + 5)) + extra.length := by
  have lengthEq := congrArg List.length mesh.points_eq
  rw [Append.length_append, mesh.splits.points_length] at lengthEq
  rw [lengthEq]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 mesh.splits.pieceCount_le) _

open Purelib.Riemann.Readings in
/-- The original common mesh's triangle count is bounded by its retained cell and point counts. -/
theorem count_le (mesh : PreparedSplitMesh cuts parents extra) :
    mesh.mesh.triangleCount ≤ 2 * ((RectangularExteriorBoundary.Geometry.allCells geometry).length *
      ((2 * (parents.length * (columns + rows + 5)) + extra.length + 1) *
        (2 * (parents.length * (columns + rows + 5)) + extra.length + 1))) := by
  apply mesh.mesh.count_le.trans
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul (Nat.add_le_add_right mesh.points_length_le 1) (Nat.add_le_add_right mesh.points_length_le 1)

set_option genInjectivity false in
/-- Original common-mesh vertex indices for the exact endpoints of a retained fragment.

Both bounded indices refer to the original shared mesh vertex cache. Their coordinate equations retain the exact
fragment endpoints and its original nominal segment indices. -/
structure Contact (mesh : PreparedSplitMesh cuts parents extra)
    {first last : Gaussian} (piece : SegmentPiece geometry first last) where
  /-- The retained common-mesh vertex index of the original fragment start. -/ first : Fin
    mesh.mesh.surface.mesh.vertices.length
  /-- The retained common-mesh vertex index of the original fragment finish. -/ last : Fin
    mesh.mesh.surface.mesh.vertices.length
  /-- The first retained mesh coordinate equals the exact original fragment start. -/ first_eq :
    mesh.mesh.surface.mesh.coordinate first = piece.firstPoint
  /-- The last retained mesh coordinate equals the exact original fragment finish. -/ last_eq :
    mesh.mesh.surface.mesh.coordinate last = piece.lastPoint

constructive_injectivity Contact

/-- Locate a retained fragment's original endpoints in the exact common mesh.

Spine membership supplies the original point-cache membership, and the fragment's retained cell indices supply
containment for both lookups. -/
@[expose] def contact (mesh : PreparedSplitMesh cuts parents extra)
    {parent : CenteredEdge curve differential} {split : SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)}
    (member : ParentSplits.Member split mesh.splits)
    (piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1)) (present : piece ∈ split.pieces) :
    Contact mesh piece :=
  let endpoints := split.points_mem present
  have firstMember : piece.firstPoint ∈ mesh.points := by
    rw [mesh.points_eq]
    exact List.mem_append_left _ (ParentSplits.point_mem member endpoints.1)
  have lastMember : piece.lastPoint ∈ mesh.points := by
    rw [mesh.points_eq]
    exact List.mem_append_left _ (ParentSplits.point_mem member endpoints.2)
  let first := mesh.mesh.lookup piece.firstPoint firstMember piece.column piece.row
    (Geometry.allCells_mem geometry piece.column piece.row) piece.first_inside
  let last := mesh.mesh.lookup piece.lastPoint lastMember piece.column piece.row
    (Geometry.allCells_mem geometry piece.column piece.row) piece.last_inside
  ⟨first.index, last.index, first.coordinate_eq, last.coordinate_eq⟩

end PreparedSplitMesh

end Purelib.Riemann.Integration.PreparedParentSplitting
