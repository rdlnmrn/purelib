module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Affine

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPairedTraceRequest
public import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation

open Purelib.Geometry.Rational

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Requested comparison of the actual recursive dyadic boundary areas.
The proof uses the indexed common trace and retains its endpoint chords. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DyadicPairedTraceRequest

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation (PairedTracePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation (AreaRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner
    (curve.polynomial.eval start)}
  {leftEntry : Entry firstModels start owner}
    {rightEntry : Entry lastModels start
    owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}
  {count : Nat} {firstDifferential secondDifferential : Differential
    genus} {firstSheet secondSheet : Fin 2}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)

open Purelib.Riemann.Periods.CenteredBilinearPath (area)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadic dyadicCount dyadic_area)
open Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon (dyadicArea)

variable {piece : Purelib.Riemann.Paths.RectangularPairedSegments.PairedSegmentPiece leftDomain.geometry
  rightDomain.geometry}
  {depth : Nat}

/-- The actual indexed common-trace area reads exactly as the original recursive dyadic line area. -/
private theorem sample_area (values : Data.Gaussian.Basic.Canonical → Stokes.PrimitivePoint)
    (readings : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1) → Stokes.PrimitivePoint)
    (readback : ∀ vertex, readings vertex = values ((RectangularDyadicPairedTrace.dyadic piece depth).points vertex))
    (sample : CenteredBilinearPath.Sample readings) :
    sample.originalArea = DyadicBilinearBoundaryRibbon.dyadicArea
      (fun parameter => values (Affine.line piece.first (piece.last - piece.first) parameter)) depth 0 1 := by
  rw [sample.originalArea_eq]
  have equal : CenteredBilinearPath.area readings = CenteredBilinearPath.area (fun vertex : Fin
    (RectangularDyadicPairedTrace.dyadicCount depth + 1) => values ((RectangularDyadicPairedTrace.dyadic piece
    depth).points vertex)) := by
    unfold CenteredBilinearPath.area
    apply FiniteSum.Fin.sumFin_congr
    intro edge
    dsimp only
    rw [readback, readback]
  exact equal.trans (RectangularDyadicPairedTrace.dyadic_area piece depth values)

/-- The retained common-trace endpoint correction is the original endpoint wedge. -/
private theorem sample_endpoint (values : Data.Gaussian.Basic.Canonical → Stokes.PrimitivePoint)
    (readings : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1) → Stokes.PrimitivePoint)
    (readback : ∀ vertex, readings vertex = values ((RectangularDyadicPairedTrace.dyadic piece depth).points vertex))
    (sample : CenteredBilinearPath.Sample readings) :
    sample.endpoint = Stokes.edgeArea (values piece.first) (values piece.last) := by
  rw [sample.endpoint_eq, readback, readback, (RectangularDyadicPairedTrace.dyadic piece depth).first_point,
    (RectangularDyadicPairedTrace.dyadic piece depth).last_point]
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

namespace PairedTracePreparation.AreaRequest

variable {preparation : PairedTracePreparation
  (leftEntry := leftEntry) (rightEntry := rightEntry) (Purelib.Riemann.Paths.RectangularDyadicPairedTrace.dyadic piece
  depth)}
  {target : Coordinate} {floor : Nat}

/-- The actual endpoint-corrected recursive dyadic trace-area discrepancy satisfies the prepared original target at
every paid stage. -/
theorem dyadic_accurate
    (assembled : PairedTracePreparation.AreaRequest preparation firstDifferential secondDifferential firstSheet
      secondSheet target floor)
    {stage : Nat} (later : assembled.request.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage) :
    let leftValue := fun point => (⟨firstLeft.anchors.alignedValue firstLeft.offsets piece.leftColumn piece.leftRow
      point,
      secondLeft.anchors.alignedValue secondLeft.offsets piece.leftColumn piece.leftRow point⟩ : Stokes.PrimitivePoint)
    let rightValue := fun point => (⟨firstRight.anchors.alignedValue firstRight.offsets piece.rightColumn piece.rightRow
      point,
      secondRight.anchors.alignedValue secondRight.offsets piece.rightColumn piece.rightRow point⟩ :
        Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq ((DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => leftValue
      (Affine.line piece.first (piece.last - piece.first) parameter)) depth 0 1 -
      DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => rightValue (Affine.line piece.first (piece.last -
        piece.first) parameter)) depth 0 1) -
      (Stokes.edgeArea (leftValue piece.first) (leftValue piece.last) - Stokes.edgeArea (rightValue piece.first)
        (rightValue piece.last))) < target := by
  intro leftValue rightValue
  let trace := RectangularDyadicPairedTrace.dyadic piece depth
  let leftReadings := fun vertex : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1) => (⟨(trace.leftReadings
    firstLeft.anchors firstLeft.offsets).values vertex,
    (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩ : Stokes.PrimitivePoint)
  let rightReadings := fun vertex : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1) => (⟨(trace.rightReadings
    firstRight.anchors firstRight.offsets).values vertex,
    (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩ : Stokes.PrimitivePoint)
  have leftReadback (vertex : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1)) : leftReadings vertex =
    leftValue (trace.points vertex) := by
    dsimp only [leftReadings, leftValue]
    rw [trace.leftReadings_value, trace.leftReadings_value]
  have rightReadback (vertex : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1)) : rightReadings vertex =
    rightValue (trace.points vertex) := by
    dsimp only [rightReadings, rightValue]
    rw [trace.rightReadings_value, trace.rightReadings_value]
  let left := CenteredBilinearPath.Sample.build leftReadings
  let right := CenteredBilinearPath.Sample.build rightReadings
  have estimate := assembled.accurate later firstLeft firstRight secondLeft secondRight left right
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.DyadicPairedTraceRequest.sample_area leftValue leftReadings leftReadback
    left, Curves.Hyperelliptic.Meshes.PuncturedGrid.DyadicPairedTraceRequest.sample_area rightValue rightReadings
    rightReadback right,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.DyadicPairedTraceRequest.sample_endpoint leftValue leftReadings
      leftReadback left, Curves.Hyperelliptic.Meshes.PuncturedGrid.DyadicPairedTraceRequest.sample_endpoint rightValue
      rightReadings rightReadback right] at estimate
  exact estimate

/-- The actual endpoint-corrected horizontal dyadic boundary discrepancy satisfies the original trace target for
horizontally aligned endpoints. -/
theorem horizontal_accurate
    (assembled : PairedTracePreparation.AreaRequest preparation firstDifferential secondDifferential firstSheet
      secondSheet target floor)
    {stage : Nat} (later : assembled.request.index ≤ stage)
    (aligned : piece.first.im = piece.last.im)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage) :
    let leftValue := fun point => (⟨firstLeft.anchors.alignedValue firstLeft.offsets piece.leftColumn piece.leftRow
      point,
      secondLeft.anchors.alignedValue secondLeft.offsets piece.leftColumn piece.leftRow point⟩ : Stokes.PrimitivePoint)
    let rightValue := fun point => (⟨firstRight.anchors.alignedValue firstRight.offsets piece.rightColumn piece.rightRow
      point,
      secondRight.anchors.alignedValue secondRight.offsets piece.rightColumn piece.rightRow point⟩ :
        Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq ((PreparedBoxBoundary.horizontalBoundary leftValue depth piece.first.re
      piece.last.re piece.first.im -
      PreparedBoxBoundary.horizontalBoundary rightValue depth piece.first.re piece.last.re piece.first.im) -
      (Stokes.edgeArea (leftValue piece.first) (leftValue piece.last) - Stokes.edgeArea (rightValue piece.first)
        (rightValue piece.last))) < target := by
  intro leftValue rightValue
  have side (values : Data.Gaussian.Basic.Canonical → Stokes.PrimitivePoint) :
      PreparedBoxBoundary.horizontalBoundary values depth piece.first.re piece.last.re piece.first.im =
        DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => values (Affine.line piece.first (piece.last -
          piece.first) parameter)) depth 0 1 := by
    have lastEq : (⟨piece.last.re, piece.first.im⟩ : Data.Gaussian.Basic.Canonical) = piece.last :=
      Data.Gaussian.Basic.ext rfl aligned
    have result := DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_lineArea values depth
      piece.first.re piece.last.re piece.first.im
    rw [lastEq] at result
    exact result
  rw [side leftValue, side rightValue]
  exact
    dyadic_accurate
    assembled later firstLeft firstRight secondLeft secondRight

/-- The actual endpoint-corrected vertical dyadic boundary discrepancy satisfies the original trace target for
vertically aligned endpoints. -/
theorem vertical_accurate
    (assembled : PairedTracePreparation.AreaRequest preparation firstDifferential secondDifferential firstSheet
      secondSheet target floor)
    {stage : Nat} (later : assembled.request.index ≤ stage)
    (aligned : piece.first.re = piece.last.re)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage) :
    let leftValue := fun point => (⟨firstLeft.anchors.alignedValue firstLeft.offsets piece.leftColumn piece.leftRow
      point,
      secondLeft.anchors.alignedValue secondLeft.offsets piece.leftColumn piece.leftRow point⟩ : Stokes.PrimitivePoint)
    let rightValue := fun point => (⟨firstRight.anchors.alignedValue firstRight.offsets piece.rightColumn piece.rightRow
      point,
      secondRight.anchors.alignedValue secondRight.offsets piece.rightColumn piece.rightRow point⟩ :
        Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq ((PreparedBoxBoundary.verticalBoundary leftValue depth piece.first.im
      piece.last.im piece.first.re -
      PreparedBoxBoundary.verticalBoundary rightValue depth piece.first.im piece.last.im piece.first.re) -
      (Stokes.edgeArea (leftValue piece.first) (leftValue piece.last) - Stokes.edgeArea (rightValue piece.first)
        (rightValue piece.last))) < target := by
  intro leftValue rightValue
  have side (values : Data.Gaussian.Basic.Canonical → Stokes.PrimitivePoint) :
      PreparedBoxBoundary.verticalBoundary values depth piece.first.im piece.last.im piece.first.re =
        DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => values (Affine.line piece.first (piece.last -
          piece.first) parameter)) depth 0 1 := by
    have lastEq : (⟨piece.first.re, piece.last.im⟩ : Data.Gaussian.Basic.Canonical) = piece.last :=
      Data.Gaussian.Basic.ext aligned rfl
    have result := DyadicBilinearBoundaryRibbon.verticalBoundary_eq_lineArea values depth
      piece.first.im piece.last.im piece.first.re
    rw [lastEq] at result
    exact result
  rw [side leftValue, side rightValue]
  exact
    dyadic_accurate
    assembled later firstLeft firstRight secondLeft secondRight

end PairedTracePreparation.AreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DyadicPairedTraceRequest
