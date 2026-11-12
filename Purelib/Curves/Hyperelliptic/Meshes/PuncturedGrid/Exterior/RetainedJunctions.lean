module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.JoinedTraceIndices
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Geometry.Rectangle
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.RectangularPairedPointBanks
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes

/-! Owner junctions are read from the same whole-side centered cache as
the pieces. Their endpoints coincide geometrically, not numerically. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces bottomSelfSide topSelfSide leftSelfSide
  rightSelfSide)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Geometry.Rectangle.SourceIntervals (axisIntervals axisCoordinate)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces.RetainedPerimeterPiece (vertical
  piece trace first_along last_along)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
variable {columns rows : Nat} {geometry : Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : GridCuts geometry} {box :
  Geometry.Rational.Box}

/-- The actual number of owner junctions on the selected retained rectangle side. -/
@[expose] def junctionCount (mesh : ObservationMesh cuts box) : GridSide
  → Nat
  | .bottom | .top => mesh.boundaryColumns
  | .left | .right => mesh.boundaryRows

/-- Transport a retained side-piece position into the exact original axis-interval index. -/
@[expose] def pieceIndex (mesh : ObservationMesh cuts box) (side :
  GridSide) :
    Fin (RetainedPerimeterPiece.junctionCount mesh
      side + 1) → Fin (SourceIntervals.axisIntervals mesh (RetainedPerimeterPiece.vertical side)).length :=
  match side with
  | .bottom | .top => Fin.cast mesh.boundaryColumns_eq
  | .left | .right => Fin.cast mesh.boundaryRows_eq

variable {mesh : ObservationMesh cuts box} {traces :
  PerimeterTraces mesh}
  {values : Fin (columns + 1) → Fin (rows + 1) → Canonical →
    PrimitivePoint}

/-- Read a paired primitive displacement from two positions of the original centered sample. -/
@[expose] def difference {count : Nat} {values : Fin (count + 1) → PrimitivePoint}
    (sample : Sample values) (first last : Fin (count + 1)) : PrimitivePoint :=
  (sample.centered last).sub (sample.centered first)

/-- The original centered displacement equals the exact difference of the retained uncentered vertex values. -/
private theorem difference_eq {count : Nat} {values : Fin (count + 1) → PrimitivePoint}
    (sample : Sample values) (first last : Fin (count + 1)) :
    RetainedPerimeterPiece.difference
      sample first last = (values last).sub (values first) := by
  unfold RetainedPerimeterPiece.difference
  rw [sample.centered_eq, sample.centered_eq]
  apply congrArg₂ PrimitivePoint.mk <;> dsimp only [PrimitivePoint.sub] <;> ring1

/-- Read the original owner-junction displacement directly from the cached whole-side centered sample. -/
@[expose] def junction (samples : Centered traces values) (side :
  GridSide) : Fin
  (RetainedPerimeterPiece.junctionCount mesh side)
  → PrimitivePoint :=
  match side with
  | .bottom => fun i =>
    RetainedPerimeterPiece.difference
    samples.bottom
      ((Trace.pieceEmbedding traces.bottom i.castSucc).indexOfIndexed (Fin.last
        (RectangularDyadicPairedTrace.dyadicCount mesh.depth)))
      ((Trace.pieceEmbedding traces.bottom i.succ).indexOfIndexed 0)
  | .top => fun i =>
    RetainedPerimeterPiece.difference samples.top
      ((Trace.pieceEmbedding traces.top i.castSucc).indexOfIndexed (Fin.last (RectangularDyadicPairedTrace.dyadicCount
        mesh.depth)))
      ((Trace.pieceEmbedding traces.top i.succ).indexOfIndexed 0)
  | .left => fun i =>
    RetainedPerimeterPiece.difference samples.left
      ((Trace.pieceEmbedding traces.left i.castSucc).indexOfIndexed (Fin.last (RectangularDyadicPairedTrace.dyadicCount
        mesh.depth)))
      ((Trace.pieceEmbedding traces.left i.succ).indexOfIndexed 0)
  | .right => fun i =>
    RetainedPerimeterPiece.difference samples.right
      ((Trace.pieceEmbedding traces.right i.castSucc).indexOfIndexed (Fin.last (RectangularDyadicPairedTrace.dyadicCount
        mesh.depth)))
      ((Trace.pieceEmbedding traces.right i.succ).indexOfIndexed 0)

/-- The cached junction displacement is the exact difference of the adjoining original piece-owner values. -/
theorem junction_eq (samples : Centered traces values) (side :
  GridSide) (i : Fin
  (RetainedPerimeterPiece.junctionCount mesh side))
  :
    let before := RetainedPerimeterPiece.pieceIndex
      mesh side i.castSucc
    let after := RetainedPerimeterPiece.pieceIndex
      mesh side i.succ
    RetainedPerimeterPiece.junction samples side i
      =
      (values (RetainedPerimeterPiece.piece mesh side after).leftColumn (RetainedPerimeterPiece.piece mesh side
        after).leftRow ((RetainedPerimeterPiece.trace traces side after).points 0)).sub
      (values (RetainedPerimeterPiece.piece mesh side before).leftColumn (RetainedPerimeterPiece.piece mesh side
        before).leftRow
        ((RetainedPerimeterPiece.trace traces side before).points (Fin.last (RectangularDyadicPairedTrace.dyadicCount
          mesh.depth)))) := by
  cases side with
  | bottom =>
    dsimp only [RetainedPerimeterPiece.junction]
    rw [RetainedPerimeterPiece.difference_eq,
      (Trace.pieceEmbedding traces.bottom i.castSucc).indexOfIndexed_eq,
      (Trace.pieceEmbedding traces.bottom i.succ).indexOfIndexed_eq]
    rfl
  | top =>
    dsimp only [RetainedPerimeterPiece.junction]
    rw [RetainedPerimeterPiece.difference_eq,
      (Trace.pieceEmbedding traces.top i.castSucc).indexOfIndexed_eq,
      (Trace.pieceEmbedding traces.top i.succ).indexOfIndexed_eq]
    rfl
  | left =>
    dsimp only [RetainedPerimeterPiece.junction]
    rw [RetainedPerimeterPiece.difference_eq,
      (Trace.pieceEmbedding traces.left i.castSucc).indexOfIndexed_eq,
      (Trace.pieceEmbedding traces.left i.succ).indexOfIndexed_eq]
    rfl
  | right =>
    dsimp only [RetainedPerimeterPiece.junction]
    rw [RetainedPerimeterPiece.difference_eq,
      (Trace.pieceEmbedding traces.right i.castSucc).indexOfIndexed_eq,
      (Trace.pieceEmbedding traces.right i.succ).indexOfIndexed_eq]
    rfl

/-- The adjoining retained physical trace endpoints are the identical geometric point. -/
theorem junction_point (traces : PerimeterTraces mesh) (side : GridSide)
  (i : Fin (RetainedPerimeterPiece.junctionCount
  mesh side)) :
    (RetainedPerimeterPiece.trace traces side
      (RetainedPerimeterPiece.pieceIndex mesh side
      i.succ)).points 0 =
      (RetainedPerimeterPiece.trace traces side
        (RetainedPerimeterPiece.pieceIndex mesh
        side i.castSucc)).points (Fin.last (RectangularDyadicPairedTrace.dyadicCount mesh.depth)) := by
  rw [Trace.first_point, Trace.last_point]
  cases side with
  | bottom =>
    exact ((RectangularPerimeterTraces.bottomSelfSide mesh).consecutive i.val (Fin.cast mesh.boundaryColumns_eq
      i.succ).isLt).symm
  | top =>
    exact ((RectangularPerimeterTraces.topSelfSide mesh).consecutive i.val (Fin.cast mesh.boundaryColumns_eq
      i.succ).isLt).symm
  | left =>
    exact ((RectangularPerimeterTraces.leftSelfSide mesh).consecutive i.val (Fin.cast mesh.boundaryRows_eq
      i.succ).isLt).symm
  | right =>
    exact ((RectangularPerimeterTraces.rightSelfSide mesh).consecutive i.val (Fin.cast mesh.boundaryRows_eq
      i.succ).isLt).symm

/-- The adjoining retained physical side intervals share their exact endpoint coordinate. -/
theorem junction_interval (traces : PerimeterTraces mesh) (side :
  GridSide) (i : Fin
  (RetainedPerimeterPiece.junctionCount mesh side))
  :
    ((SourceIntervals.axisIntervals mesh (RetainedPerimeterPiece.vertical
      side))[(RetainedPerimeterPiece.pieceIndex
      mesh side
      i.succ).val]'(pieceIndex
      mesh side i.succ).isLt).lower =
    ((SourceIntervals.axisIntervals mesh (RetainedPerimeterPiece.vertical
      side))[(RetainedPerimeterPiece.pieceIndex
      mesh side
      i.castSucc).val]'(pieceIndex
      mesh side i.castSucc).isLt).upper := by
  have points :=
    RetainedPerimeterPiece.junction_point traces
    side i
  rw [Trace.first_point, Trace.last_point] at points
  have axes := congrArg (SourceIntervals.axisCoordinate (RetainedPerimeterPiece.vertical side)) points
  exact (RetainedPerimeterPiece.first_along mesh side
    (RetainedPerimeterPiece.pieceIndex mesh side
    i.succ)).symm.trans
    (axes.trans (RetainedPerimeterPiece.last_along mesh side
      (RetainedPerimeterPiece.pieceIndex mesh side
      i.castSucc)))

/-- The first retained side interval starts at the original box's lower axis coordinate. -/
theorem first_interval_lower (mesh : ObservationMesh cuts box) (side :
  GridSide) :
    ((SourceIntervals.axisIntervals mesh (RetainedPerimeterPiece.vertical
      side))[(RetainedPerimeterPiece.pieceIndex
      mesh side
      0).val]'(RetainedPerimeterPiece.pieceIndex
      mesh side 0).isLt).lower =
      (if RetainedPerimeterPiece.vertical side then box.yLower else box.xLower) := by
  cases side with
  | bottom | top => exact mesh.x_first
  | left | right => exact mesh.y_first

/-- The final retained side interval finishes at the original box's upper axis coordinate. -/
theorem last_interval_upper (mesh : ObservationMesh cuts box) (side :
  GridSide) :
    ((SourceIntervals.axisIntervals mesh (RetainedPerimeterPiece.vertical
      side))[(RetainedPerimeterPiece.pieceIndex
      mesh side (Fin.last
      (RetainedPerimeterPiece.junctionCount mesh
      side))).val]'
      (RetainedPerimeterPiece.pieceIndex mesh side
        (Fin.last
        (RetainedPerimeterPiece.junctionCount mesh
        side))).isLt).upper =
      (if RetainedPerimeterPiece.vertical side then box.yUpper else box.xUpper) := by
  cases side with
  | bottom | top => exact mesh.x_last
  | left | right => exact mesh.y_last

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.SurfaceOccurrence
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Geometry.Rectangle
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  (sourceForward sourceSpan sourceVertical)
open Purelib.Riemann.Normalization
open Purelib.Geometry.Rectangle.SourceIntervals (axisIntervals)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

/-- The actual first and last retained side intervals recover the original occurrence's signed source span in either
direction. -/
theorem side_span_endpoints (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    (meshes : RegularMeshes domains occurrence.sideOccurrence.sheet) :
    let mesh := meshes.entries.get occurrence.sideOccurrence.position
    let side := occurrence.sideOccurrence.side
    let firstIndex :=
      RetainedPerimeterPiece.pieceIndex mesh side 0
    let lastIndex :=
      RetainedPerimeterPiece.pieceIndex mesh side
      (Fin.last
      (RetainedPerimeterPiece.junctionCount mesh
      side))
    let intervals := SourceIntervals.axisIntervals mesh occurrence.sourceVertical
    (if occurrence.sourceForward then (intervals[firstIndex.val]'firstIndex.isLt).lower
      else -(intervals[lastIndex.val]'lastIndex.isLt).upper) = occurrence.sourceSpan.lower ∧
    (if occurrence.sourceForward then (intervals[lastIndex.val]'lastIndex.isLt).upper
      else -(intervals[firstIndex.val]'firstIndex.isLt).lower) = occurrence.sourceSpan.upper := by
  intro mesh side firstIndex lastIndex intervals
  have lower :=
    RetainedPerimeterPiece.first_interval_lower
    mesh side
  have upper :=
    RetainedPerimeterPiece.last_interval_upper mesh
    side
  have first := congrArg₂ (fun low high : InverseRootPolynomial.Coordinate =>
    if occurrence.sourceForward then low else -high) lower upper
  have last := congrArg₂ (fun low high : InverseRootPolynomial.Coordinate =>
    if occurrence.sourceForward then high else -low) lower upper
  constructor
  · apply first.trans
    cases sideEq : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
      simp only [SurfaceOccurrence.sourceForward, SurfaceOccurrence.sourceSpan, SurfaceOccurrence.sourceVertical,
        sideEq, backward, SourceBlockParameters.signedInterval,
        side, RetainedPerimeterPiece.vertical, Bool.not_false, Bool.not_true, if_neg (by decide : ¬ false = true),
          if_pos (Eq.refl true), -eq_self, -iff_self] <;> rfl
  · apply last.trans
    cases sideEq : occurrence.sideOccurrence.side <;> cases backward : occurrence.sideOccurrence.backward <;>
      simp only [SurfaceOccurrence.sourceForward, SurfaceOccurrence.sourceSpan, SurfaceOccurrence.sourceVertical,
        sideEq, backward, SourceBlockParameters.signedInterval,
        side, RetainedPerimeterPiece.vertical, Bool.not_false, Bool.not_true, if_neg (by decide : ¬ false = true),
          if_pos (Eq.refl true), -eq_self, -iff_self] <;> rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.SurfaceOccurrence
