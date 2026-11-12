module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.TraceLengths
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Geometry

open Purelib.Geometry.Rectangle

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.TraceLengths

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Riemann.Paths

open Purelib.Riemann.Normalization

public section

/-! Select the actual stored perimeter segment on each of the four sides.
No trace, owner, or primitive sample is rebuilt by selection. -/
section
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces bottomSelfSide topSelfSide leftSelfSide
  rightSelfSide)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate axisIntervals)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece

/-- Select the varying coordinate axis of the original rectangle side. -/
@[expose] def vertical : GridSide → Bool
  | .bottom | .top => false
  | .right | .left => true

/-- Read the original side's fixed transverse coordinate from its rectangle box. -/
@[expose] def across (box : Rational.Box) : GridSide →
  InverseRootPolynomial.Coordinate
  | .bottom => box.yLower
  | .top => box.yUpper
  | .left => box.xLower
  | .right => box.xUpper

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece

variable {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
  {cuts : GridCuts geometry} {box :
  Rational.Box}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece

/-- Select the actual retained perimeter segment at the original side interval position. -/
@[expose] def piece (mesh : ObservationMesh cuts box) (side : GridSide) :
    Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length → PairedSegmentPiece geometry geometry :=
  match side with
  | .bottom => fun i => (RectangularPerimeterTraces.bottomSelfSide mesh).pieces i
  | .top => fun i => (RectangularPerimeterTraces.topSelfSide mesh).pieces i
  | .left => fun i => (RectangularPerimeterTraces.leftSelfSide mesh).pieces i
  | .right => fun i => (RectangularPerimeterTraces.rightSelfSide mesh).pieces i

/-- Select the actual cached dyadic trace of the original perimeter segment without rebuilding it. -/
@[expose] def trace {mesh : ObservationMesh cuts box} (traces :
  PerimeterTraces mesh) (side : GridSide) :
    (i : Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length) → RectangularPairedPointBanks.Trace
      (RetainedPerimeterPiece.piece mesh side i)
      (RectangularDyadicPairedTrace.dyadicCount mesh.depth) :=
  match side with
  | .bottom => fun i => traces.bottom.segments.get i
  | .top => fun i => traces.top.segments.get i
  | .left => fun i => traces.left.segments.get i
  | .right => fun i => traces.right.segments.get i

/-- The selected original segment starts at its retained axis interval's lower coordinate. -/
theorem first_along (mesh : ObservationMesh cuts box) (side : GridSide)
    (i : Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length) :
    SourceIntervals.axisCoordinate
      (RetainedPerimeterPiece.vertical side)
      (RetainedPerimeterPiece.piece mesh side
      i).first =
      ((SourceIntervals.axisIntervals mesh
        (RetainedPerimeterPiece.vertical
        side))[i.val]'i.isLt).lower := by
  cases side with
  | bottom =>
    change ((RectangularPerimeterTraces.bottomSelfSide mesh).pieces i).first.re = _; rw
      [(RectangularPerimeterTraces.bottomSelfSide mesh).first_eq]; rfl
  | top =>
    change ((RectangularPerimeterTraces.topSelfSide mesh).pieces i).first.re = _; rw
      [(RectangularPerimeterTraces.topSelfSide mesh).first_eq]; rfl
  | left =>
    change ((RectangularPerimeterTraces.leftSelfSide mesh).pieces i).first.im = _; rw
      [(RectangularPerimeterTraces.leftSelfSide mesh).first_eq]; rfl
  | right =>
    change ((RectangularPerimeterTraces.rightSelfSide mesh).pieces i).first.im = _; rw
      [(RectangularPerimeterTraces.rightSelfSide mesh).first_eq]; rfl

/-- The selected original segment ends at its retained axis interval's upper coordinate. -/
theorem last_along (mesh : ObservationMesh cuts box) (side : GridSide)
    (i : Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length) :
    SourceIntervals.axisCoordinate
      (RetainedPerimeterPiece.vertical side)
      (RetainedPerimeterPiece.piece mesh side
      i).last =
      ((SourceIntervals.axisIntervals mesh
        (RetainedPerimeterPiece.vertical
        side))[i.val]'i.isLt).upper := by
  cases side with
  | bottom =>
    change ((RectangularPerimeterTraces.bottomSelfSide mesh).pieces i).last.re = _; rw
      [(RectangularPerimeterTraces.bottomSelfSide mesh).last_eq]; rfl
  | top =>
    change ((RectangularPerimeterTraces.topSelfSide mesh).pieces i).last.re = _; rw
      [(RectangularPerimeterTraces.topSelfSide mesh).last_eq]; rfl
  | left =>
    change ((RectangularPerimeterTraces.leftSelfSide mesh).pieces i).last.im = _; rw
      [(RectangularPerimeterTraces.leftSelfSide mesh).last_eq]; rfl
  | right =>
    change ((RectangularPerimeterTraces.rightSelfSide mesh).pieces i).last.im = _; rw
      [(RectangularPerimeterTraces.rightSelfSide mesh).last_eq]; rfl

/-- The selected original segment starts at the retained side's fixed transverse coordinate. -/
theorem first_across (mesh : ObservationMesh cuts box) (side : GridSide)
    (i : Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length) :
    SourceIntervals.axisCoordinate
      (!(RetainedPerimeterPiece.vertical side))
      (RetainedPerimeterPiece.piece mesh side
      i).first = RetainedPerimeterPiece.across
      box side := by
  cases side with
  | bottom =>
    change ((RectangularPerimeterTraces.bottomSelfSide mesh).pieces i).first.im = box.yLower; rw
      [(RectangularPerimeterTraces.bottomSelfSide mesh).first_eq]; exact mesh.y_first
  | top =>
    change ((RectangularPerimeterTraces.topSelfSide mesh).pieces i).first.im = box.yUpper; rw
      [(RectangularPerimeterTraces.topSelfSide mesh).first_eq]; exact mesh.y_last
  | left =>
    change ((RectangularPerimeterTraces.leftSelfSide mesh).pieces i).first.re = box.xLower; rw
      [(RectangularPerimeterTraces.leftSelfSide mesh).first_eq]; exact mesh.x_first
  | right =>
    change ((RectangularPerimeterTraces.rightSelfSide mesh).pieces i).first.re = box.xUpper; rw
      [(RectangularPerimeterTraces.rightSelfSide mesh).first_eq]; exact mesh.x_last

/-- The selected original segment ends at the retained side's fixed transverse coordinate. -/
theorem last_across (mesh : ObservationMesh cuts box) (side : GridSide)
    (i : Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length) :
    SourceIntervals.axisCoordinate
      (!(RetainedPerimeterPiece.vertical side))
      (RetainedPerimeterPiece.piece mesh side
      i).last = RetainedPerimeterPiece.across box
      side := by
  cases side with
  | bottom =>
    change ((RectangularPerimeterTraces.bottomSelfSide mesh).pieces i).last.im = box.yLower; rw
      [(RectangularPerimeterTraces.bottomSelfSide mesh).last_eq]; exact mesh.y_first
  | top =>
    change ((RectangularPerimeterTraces.topSelfSide mesh).pieces i).last.im = box.yUpper; rw
      [(RectangularPerimeterTraces.topSelfSide mesh).last_eq]; exact mesh.y_last
  | left =>
    change ((RectangularPerimeterTraces.leftSelfSide mesh).pieces i).last.re = box.xLower; rw
      [(RectangularPerimeterTraces.leftSelfSide mesh).last_eq]; exact mesh.x_first
  | right =>
    change ((RectangularPerimeterTraces.rightSelfSide mesh).pieces i).last.re = box.xUpper; rw
      [(RectangularPerimeterTraces.rightSelfSide mesh).last_eq]; exact mesh.x_last

/-- The selected cached segment retains the original unit dyadic parameter list at the mesh depth. -/
theorem parameters_eq {mesh : ObservationMesh cuts box} (traces :
  PerimeterTraces mesh) (side : GridSide)
    (i : Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length) (vertex : Fin (RectangularDyadicPairedTrace.dyadicCount mesh.depth + 1)) :
    (RetainedPerimeterPiece.trace traces side
      i).parameters vertex = DyadicTrace.indexed 0
      (DyadicTrace.tail mesh.depth 0 1) vertex := by
  cases side with
  | bottom => dsimp only
    [RetainedPerimeterPiece.trace, -eq_self,
    -iff_self]; rw [traces.bottom.segments_eq]; exact Data.Vector.Basic.vectorOfFn_apply _ _
  | top => dsimp only
    [RetainedPerimeterPiece.trace, -eq_self,
    -iff_self]; rw [traces.top.segments_eq]; exact Data.Vector.Basic.vectorOfFn_apply _ _
  | left => dsimp only
    [RetainedPerimeterPiece.trace, -eq_self,
    -iff_self]; rw [traces.left.segments_eq]; exact Data.Vector.Basic.vectorOfFn_apply _ _
  | right => dsimp only
    [RetainedPerimeterPiece.trace, -eq_self,
    -iff_self]; rw [traces.right.segments_eq]; exact Data.Vector.Basic.vectorOfFn_apply _ _

/-- Every original cached perimeter trace step is nondecreasing in its retained parameter. -/
theorem increasing {mesh : ObservationMesh cuts box} (traces :
  PerimeterTraces mesh) (side : GridSide)
    (i : Fin (SourceIntervals.axisIntervals mesh
      (RetainedPerimeterPiece.vertical
      side)).length) (edge : Fin (RectangularDyadicPairedTrace.dyadicCount mesh.depth)) :
    (RetainedPerimeterPiece.trace traces side
      i).parameters edge.castSucc ≤
      (RetainedPerimeterPiece.trace traces side
      i).parameters edge.succ := by
  rw [RetainedPerimeterPiece.parameters_eq,
    RetainedPerimeterPiece.parameters_eq]
  exact Dyadic.forward_indexed id 0
    (DyadicTrace.tail mesh.depth 0 1)
    (Dyadic.tail_forward mesh.depth (by decide)) edge

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open
  ExteriorProgram.SurfaceOccurrence
  (sourceAcross)

open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate axisIntervals)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- The original occurrence's fixed source coordinate equals that of its retained physical rectangle side. -/
theorem sourceAcross_side (occurrence : SurfaceOccurrence regular domains differential) :

      SurfaceOccurrence.sourceAcross
      occurrence = RetainedPerimeterPiece.across
      (base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt).cell.box
      occurrence.sideOccurrence.side := by
  have first := congrArg Prod.fst occurrence.endpoints_eq
  change occurrence.start = occurrence.sideEndpoints.1 at first
  unfold SurfaceOccurrence.sourceAcross
  rw [first]
  cases side : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
    simp only [SurfaceOccurrence.sourceVertical, SurfaceOccurrence.sideEndpoints, side, backward,
      RetainedPerimeterPiece.across,
        RectangleEdge.coordinates, GridSide.kind,
      Bool.not_false, Bool.not_true, SourceIntervals.axisCoordinate, if_neg (show (false : Bool) ≠ true from
        Bool.noConfusion), if_pos (show (true : Bool) = true from rfl), -eq_self, -iff_self] <;> rfl

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.LiftedPuncturedGrid.ExteriorProgram

end
