module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Endpoints
public import Purelib.Geometry.Path.Gaussian.Lifted.Endpoints
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Approximation.Gaussian.Equivalence

/-! # Original lifted parent cells and continued Point callbacks

The original parent's retained clear segment and sheet provide the lifted
cell. Only its endpoint indices are transported to the existing comparison
endpoints. Each Point callback transports the same patch seed owner to the
same original parent fraction, using the retained endpoint containments.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus count : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {parent : Parent curve differential}

/-- Retain the original parent's clear local segment and sheet, changing only its exact endpoint indices. -/
def liftedCell (data : ParentData cap differential count parent) :
    LiftedCell ⟨data.segment.comparison.first, parent.edge.sheet⟩
      ⟨data.segment.comparison.last, parent.edge.sheet⟩ :=
  (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment).castEndpoints
    (congrArg (fun point : Gaussian => (⟨point, parent.edge.sheet⟩ : LiftedPoint 2))
      (parent.edge.point_zero.symm.trans data.first_eq.symm))
    (congrArg (fun point : Gaussian => (⟨point, parent.edge.sheet⟩ : LiftedPoint 2))
      (parent.edge.point_one.symm.trans data.last_eq.symm))

/-- The retained comparison cell is the actual original parent cell up to its exact endpoint indices. -/
theorem liftedCell_heq (data : ParentData cap differential count parent) :
    HEq data.liftedCell (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment) :=
  LiftedCell.castEndpoints_heq _ _ _

/-- The comparison cell keeps the complete original clear segment's sheet transport. -/
theorem liftedCell_sheetTransport (data : ParentData cap differential count parent) :
    data.liftedCell.sheetTransport =
      (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment).sheetTransport :=
  LiftedCell.sheetTransport_castEndpoints _ _ _

/-- The retained comparison coordinate reads the same original parent at every affine fraction. -/
theorem coordinate_point_eq (data : ParentData cap differential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last)
    (input : Coordinate) : coordinate.point input = parent.edge.point input := by
  unfold Spatial.Coordinate.point
  rewrite [coordinate.displacement_eq, data.first_eq, data.last_eq,
    parent.edge.point_zero, parent.edge.point_one]
  rfl

/-- Acquire continued Points by transporting this same comparison patch's original seed owner. -/
def points (data : ParentData cap differential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last) :
    ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (coordinate.point input) :=
  fun input lower upper => Point.acquire data.terminal.neighborhood.patch (coordinate.point input)
    (coordinate.point_inside data.segment.firstInside data.segment.lastInside lower upper)

/-- Each actual callback result is the original same-patch Point acquisition at that parameter. -/
theorem points_eq (data : ParentData cap differential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    data.points coordinate input lower upper =
      Point.acquire data.terminal.neighborhood.patch (coordinate.point input)
        (coordinate.point_inside data.segment.firstInside data.segment.lastInside lower upper) := by
  rfl

/-- Every callback Point keeps the actual original parent's root generator at the same fraction. -/
def points_owner (data : ParentData cap differential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    NamedEquivalent (parent.edge.rootName input ⟨lower, upper⟩)
      (data.points coordinate input lower upper).certificate.value.name :=
  pointEquivalent data.patch data.terminal.neighborhood.patch data.patch_eq input ⟨lower, upper⟩
    (data.coordinate_point_eq coordinate input).symm
    (coordinate.point_inside data.segment.firstInside data.segment.lastInside lower upper)
    (data.points coordinate input lower upper)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.ParentData

end
