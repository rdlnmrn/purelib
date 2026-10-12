module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
import Purelib.Riemann.Paths.RectangularPairedTraceMagnitude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The paired prefix request obtains its magnitude from the actual common
trace owners, so no numerical magnitude hypothesis remains. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceGeometryBound

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {count : Nat} {firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus}
    {firstSheet secondSheet : Fin 2}

namespace PairedTraceRequest

variable {piece : Paths.RectangularPairedSegments.PairedSegmentPiece leftDomain.geometry rightDomain.geometry}
  {trace : Integration.RectangularPairedPointBanks.Trace piece count}
  {firstBank : Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain
    rightDomain
    (fun vertex => trace.points vertex) firstDifferential firstSheet}
  {secondBank : Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain
    rightDomain
    (fun vertex => trace.points vertex) secondDifferential secondSheet}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The original paired-trace area comparison is below the target after its actual endpoint correction.

The retained common-trace owners supply both magnitude bounds. -/
theorem trace_accurate
    (firstBounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance
      (Readings.PreparedPrimitiveSamples.differentialNumerator firstDifferential))
    (secondBounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance
      (Readings.PreparedPrimitiveSamples.differentialNumerator secondDifferential))
    (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest firstBank secondBank (max
      (Readings.RectangularSeamBounds.boundarySlope firstBounds) (Readings.RectangularSeamBounds.boundarySlope
      secondBounds)) target floor)
    {stage : Nat} (later : request.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨(trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex,
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨(trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex,
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint - right.endpoint)) <
      target :=
  request.accurate later firstLeft firstRight secondLeft secondRight
    (trace.leftReadings firstLeft.anchors firstLeft.offsets) (trace.rightReadings firstRight.anchors firstRight.offsets)
    (trace.leftReadings secondLeft.anchors secondLeft.offsets) (trace.rightReadings secondRight.anchors
      secondRight.offsets)
    left right (Paths.RectangularPairedTraceMagnitude.paired_right_bound trace
      firstRight.anchors firstRight.offsets secondRight.anchors secondRight.offsets
      firstBounds secondBounds rightDomain.patch.cell_refines right)

end PairedTraceRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceGeometryBound
