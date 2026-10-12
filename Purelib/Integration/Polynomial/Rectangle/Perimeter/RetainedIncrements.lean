module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedTracePieces
import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Integration.Path.JoinedTraceIndices
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Tactic.Ring

public section

/-! Each physical exterior piece reads its increments from the retained
whole-side centered vector. Duplicate owner occurrences remain distinct. -/
namespace Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements

open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Rectangle
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Geometry.Rectangle
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

/-- Read consecutive differences from the supplied whole sample's existing centered cache at the retained selected
indices.

Both endpoints are selected from the same cached centered sample. The retained
index function preserves every ordered occurrence without recomputing its values. -/
def cachedIncrements {whole count : Nat} {values : Fin (whole + 1) → Stokes.PrimitivePoint}
    (sample : CenteredBilinearPath.Sample values) (indices : Fin (count + 1) → Fin (whole + 1)) : List PrimitivePoint :=
  List.ofFn (fun edge : Fin count =>
    (sample.centered (indices edge.succ)).sub (sample.centered (indices edge.castSucc)))

/-- Exact selected-vertex readback identifies cached sample differences with the selected original path increments.

The pointwise equality retains the selected vertices and their original whole
sample owner; scalar coordinate cancellation removes only the shared center. -/
theorem cachedIncrements_eq {whole count : Nat} {values : Fin (whole + 1) → Stokes.PrimitivePoint}
    (sample : CenteredBilinearPath.Sample values) (indices : Fin (count + 1) → Fin (whole + 1))
    (selected : Fin (count + 1) → Stokes.PrimitivePoint) (equal : ∀ vertex, values (indices vertex) = selected vertex) :
    Perimeter.RetainedIncrements.cachedIncrements sample indices = CenteredPathIncrements.increments selected := by
  apply OfFn.Basic.ofFn_congr
  intro edge
  rw [sample.centered_eq, sample.centered_eq, equal, equal]
  apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.sub] <;> ring1

variable {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry} {box :
  Purelib.Geometry.Rational.Box}
  {mesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts box} {traces :
    Purelib.Riemann.Paths.RectangularPerimeterTraces.PerimeterTraces mesh}
  {values : Fin (columns + 1) → Fin (rows + 1) → Purelib.Data.Gaussian.Basic.Canonical →
    Purelib.Topology.Polygon.Stokes.PrimitivePoint}

/-- Read each retained perimeter piece's increments from the matching whole-side sample cache.

Each side keeps its original piece index, boundary-count transport and certified embedding into the corresponding side
trace. -/
@[expose] def increments (samples : RectangularCenteredPerimeter.Centered traces values) (side :
  GridLiftedDualSteps.GridSide) :
    Fin (SourceIntervals.axisIntervals mesh (RetainedTracePieces.RetainedPerimeterPiece.vertical side)).length → List
      PrimitivePoint :=
  match side with
  | .bottom => fun i => Perimeter.RetainedIncrements.cachedIncrements samples.bottom
      (RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceEmbedding traces.bottom (Fin.cast
        mesh.boundaryColumns_eq.symm i)).indexOfIndexed
  | .top => fun i => Perimeter.RetainedIncrements.cachedIncrements samples.top
      (RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceEmbedding traces.top (Fin.cast
        mesh.boundaryColumns_eq.symm i)).indexOfIndexed
  | .left => fun i => Perimeter.RetainedIncrements.cachedIncrements samples.left
      (RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceEmbedding traces.left (Fin.cast
        mesh.boundaryRows_eq.symm i)).indexOfIndexed
  | .right => fun i => Perimeter.RetainedIncrements.cachedIncrements samples.right
      (RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceEmbedding traces.right (Fin.cast
        mesh.boundaryRows_eq.symm i)).indexOfIndexed

/-- The retained perimeter piece's cached increments equal the original piece trace's consecutive primitive readings. -/
theorem increments_eq (samples : RectangularCenteredPerimeter.Centered traces values) (side :
  GridLiftedDualSteps.GridSide)
    (i : Fin (SourceIntervals.axisIntervals mesh (RetainedTracePieces.RetainedPerimeterPiece.vertical side)).length) :
    Perimeter.RetainedIncrements.increments samples side i = CenteredPathIncrements.increments
      (fun vertex => values (RetainedTracePieces.RetainedPerimeterPiece.piece mesh side i).leftColumn
        (RetainedTracePieces.RetainedPerimeterPiece.piece mesh side i).leftRow
        ((RetainedTracePieces.RetainedPerimeterPiece.trace traces side i).points vertex)) := by
  cases side with
  | bottom =>
    apply Perimeter.RetainedIncrements.cachedIncrements_eq
    intro vertex
    rw [(RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceEmbedding traces.bottom (Fin.cast
      mesh.boundaryColumns_eq.symm i)).indexOfIndexed_eq]
    rfl
  | top =>
    apply Perimeter.RetainedIncrements.cachedIncrements_eq
    intro vertex
    rw [(RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceEmbedding traces.top (Fin.cast
      mesh.boundaryColumns_eq.symm i)).indexOfIndexed_eq]
    rfl
  | left =>
    apply Perimeter.RetainedIncrements.cachedIncrements_eq
    intro vertex
    rw [(RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceEmbedding traces.left (Fin.cast
      mesh.boundaryRows_eq.symm i)).indexOfIndexed_eq]
    rfl
  | right =>
    apply Perimeter.RetainedIncrements.cachedIncrements_eq
    intro vertex
    rw [(RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceEmbedding traces.right (Fin.cast
      mesh.boundaryRows_eq.symm i)).indexOfIndexed_eq]
    rfl

end Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements

end
