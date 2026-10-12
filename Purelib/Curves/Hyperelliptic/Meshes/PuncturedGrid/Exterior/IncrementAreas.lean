module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceAlignment
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Riemann.Comparison.RectangularPerimeterComparison
public import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

open Purelib

@[expose] public section

/-! The actual exterior side traces expose their complete paired increments.
The cached centered areas certify their internal path areas, with each source
occurrence's orientation kept separate from its natural trace ordering. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {target : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    target}

namespace CenteredPerimeters

/-- Read the complete paired increments of the selected retained rectangle-side sample. -/
def sideIncrements (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache
  i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) : Meshes.GridLiftedDualSteps.GridSide → List
      Topology.Polygon.Stokes.PrimitivePoint
  | .bottom => (Path.CenteredPathIncrements.Sample.increments (((samples.samples.get position).get sheet).bottom))
  | .right => (Path.CenteredPathIncrements.Sample.increments (((samples.samples.get position).get sheet).right))
  | .top => (Path.CenteredPathIncrements.Sample.increments (((samples.samples.get position).get sheet).top))
  | .left => (Path.CenteredPathIncrements.Sample.increments (((samples.samples.get position).get sheet).left))

/-- Split the cached side increments into original trace pieces and singleton
owner-junction blocks. No primitive polynomial is evaluated by extraction. -/
def sideIncrementBlocks (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request
  cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) : Meshes.GridLiftedDualSteps.GridSide → List (List
      Topology.Polygon.Stokes.PrimitivePoint)
  | .bottom => (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.incrementPartition
    (((samples.traces.get position).get sheet).bottom)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).bottom)).blocks
  | .right => (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.incrementPartition (((samples.traces.get
    position).get sheet).right)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).right)).blocks
  | .top => (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.incrementPartition (((samples.traces.get
    position).get sheet).top)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).top)).blocks
  | .left => (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.incrementPartition (((samples.traces.get
    position).get sheet).left)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).left)).blocks

/-- Flattening the original trace-piece and owner-junction blocks recovers the complete retained side increments. -/
theorem sideIncrementBlocks_flatten (samples :
  Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : Meshes.GridLiftedDualSteps.GridSide) :
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sideIncrementBlocks samples)
      position sheet side).flatten =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sideIncrements samples) position
      sheet side := by
  cases side with
  | bottom =>
    exact (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.incrementPartition (((samples.traces.get
      position).get sheet).bottom)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).bottom)).flatten_eq
  | right =>
    exact (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.incrementPartition (((samples.traces.get
      position).get sheet).right)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).right)).flatten_eq
  | top =>
    exact (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.incrementPartition (((samples.traces.get
      position).get sheet).top)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).top)).flatten_eq
  | left =>
    exact (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.incrementPartition (((samples.traces.get
      position).get sheet).left)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
        (((samples.samples.get position).get sheet).left)).flatten_eq

/-- The dependent sample bank follows the actual side, including every
piece and every owner-change junction. These are cached numerical samples,
not caller-supplied area or path-equality assumptions. -/
def SideBlockSamples (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request
  cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) : Meshes.GridLiftedDualSteps.GridSide → Type
  | .bottom => (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.PieceSamples (((samples.traces.get
    position).get sheet).bottom) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i
    j position sheet)) ×
      (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.JunctionSamples (((samples.traces.get
        position).get sheet).bottom) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues
        cache.normalize i j position sheet))
  | .right => (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.PieceSamples (((samples.traces.get
    position).get sheet).right) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i
    j position sheet)) ×
      (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.JunctionSamples (((samples.traces.get
        position).get sheet).right) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues
        cache.normalize i j position sheet))
  | .top => (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.PieceSamples (((samples.traces.get
    position).get sheet).top) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j
    position sheet)) ×
      (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.JunctionSamples (((samples.traces.get
        position).get sheet).top) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize
        i j position sheet))
  | .left => (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.PieceSamples (((samples.traces.get
    position).get sheet).left) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j
    position sheet)) ×
      (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.JunctionSamples (((samples.traces.get
        position).get sheet).left) (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize
        i j position sheet))

/-- Read the side's original trace-piece and owner-junction blocks from its dependent cached samples. -/
def sampledSideBlocks (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request
  cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) :
    (side : Meshes.GridLiftedDualSteps.GridSide) →
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.SideBlockSamples samples) position
      sheet side → List (List Topology.Polygon.Stokes.PrimitivePoint)
  | .bottom, blocks => Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.sampledBlocks
    (((samples.traces.get position).get sheet).bottom)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet) blocks.1
        blocks.2
  | .right, blocks => Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.sampledBlocks
    (((samples.traces.get position).get sheet).right)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet) blocks.1
        blocks.2
  | .top, blocks => Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.sampledBlocks
    (((samples.traces.get position).get sheet).top)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet) blocks.1
        blocks.2
  | .left, blocks => Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.sampledBlocks (((samples.traces.get
    position).get sheet).left)
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet) blocks.1
        blocks.2

/-- The blocks read from the original dependent samples equal the retained complete side increment partition. -/
theorem sampledSideBlocks_eq (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    (side : Meshes.GridLiftedDualSteps.GridSide) (blocks :
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.SideBlockSamples samples) position
      sheet side) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sampledSideBlocks samples) position
      sheet side blocks =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sideIncrementBlocks samples)
      position sheet side := by
  cases side with
  | bottom =>
      exact Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.sampledBlocks_eq (((samples.traces.get
        position).get sheet).bottom)
        (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
          blocks.1 blocks.2 (((samples.samples.get position).get sheet).bottom)
  | right =>
      exact Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.sampledBlocks_eq (((samples.traces.get
        position).get sheet).right)
        (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
          blocks.1 blocks.2 (((samples.samples.get position).get sheet).right)
  | top =>
      exact Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.sampledBlocks_eq (((samples.traces.get
        position).get sheet).top)
        (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
          blocks.1 blocks.2 (((samples.samples.get position).get sheet).top)
  | left =>
      exact Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.sampledBlocks_eq (((samples.traces.get
        position).get sheet).left)
        (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache.normalize i j position sheet)
          blocks.1 blocks.2 (((samples.samples.get position).get sheet).left)

/-- The area field is read from the retained trace, not recomputed from the
increment list. The summary certifies the full internal path area. -/
def sideIncrementSummary (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request
  cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) :
    (side : Meshes.GridLiftedDualSteps.GridSide) → Path.PairedIncrementArea.Summary
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sideIncrements samples) position
      sheet side)
  | .bottom => (Path.CenteredPathIncrements.Sample.incrementSummary (((samples.samples.get position).get sheet).bottom))
  | .right => (Path.CenteredPathIncrements.Sample.incrementSummary (((samples.samples.get position).get sheet).right))
  | .top => (Path.CenteredPathIncrements.Sample.incrementSummary (((samples.samples.get position).get sheet).top))
  | .left => (Path.CenteredPathIncrements.Sample.incrementSummary (((samples.samples.get position).get sheet).left))

/-- The full paired-increment path area equals the cached centered area of the same rectangle side. -/
theorem sideIncrements_area (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : Meshes.GridLiftedDualSteps.GridSide) :
    Path.PairedIncrementArea.area
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sideIncrements samples) position
      sheet side) =
      Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get
        sheet) side := by
  cases side with
  | bottom =>
    exact Path.CenteredPathIncrements.Sample.increments_area (((samples.samples.get position).get sheet).bottom)
  | right => exact Path.CenteredPathIncrements.Sample.increments_area (((samples.samples.get position).get sheet).right)
  | top => exact Path.CenteredPathIncrements.Sample.increments_area (((samples.samples.get position).get sheet).top)
  | left => exact Path.CenteredPathIncrements.Sample.increments_area (((samples.samples.get position).get sheet).left)

/-- The flattened sampled blocks have the exact cached centered area of their original rectangle side. -/
theorem sampledSideBlocks_area (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    (side : Meshes.GridLiftedDualSteps.GridSide) (blocks :
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.SideBlockSamples samples) position
      sheet side) :
    Path.PairedIncrementArea.area
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sampledSideBlocks samples)
      position sheet side blocks).flatten =
      Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get
        sheet) side := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sampledSideBlocks_eq samples,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sideIncrementBlocks_flatten samples]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters.sideIncrements_area samples
    position sheet side

end CenteredPerimeters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters
namespace ExteriorProgram.AllSurfacePreparation
variable {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Equality with the actual full side paths. This is a sum of internal
areas, not the area of a polygon made only from side totals. -/
theorem centeredSideArea_increments (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) :
    prepared.centeredSideArea samples = Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun
      occurrence =>
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence (Path.PairedIncrementArea.area
        (sideIncrements samples occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
          occurrence.sideOccurrence.side)))) := by
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.Map.map_congr_left
  intro occurrence _
  exact congrArg
    (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
    occurrence.sideOccurrence)
    (sideIncrements_area samples occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
      occurrence.sideOccurrence.side).symm

/-- The grouped expression still contains every actual owner-junction edge
and the cross-block polygon; no endpoint cancellation is assumed. -/
theorem centeredSideArea_blocks (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) :
    prepared.centeredSideArea samples = Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun
      occurrence =>
      Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
        occurrence.sideOccurrence (Path.PairedIncrementArea.area
        (sideIncrementBlocks samples occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
          occurrence.sideOccurrence.side).flatten))) := by
  rw
    [centeredSideArea_increments
    prepared samples]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.Map.map_congr_left
  intro occurrence _
  exact congrArg
    (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh.SideOccurrence.oriented
    occurrence.sideOccurrence) (congrArg Path.PairedIncrementArea.area
    (sideIncrementBlocks_flatten samples occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
      occurrence.sideOccurrence.side).symm)

end ExteriorProgram.AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas
