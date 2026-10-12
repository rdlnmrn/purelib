module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterCornerReadback
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Identify weighted refined-perimeter endpoints with their original corner cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback

open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter (values)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open Purelib.Riemann.Normalization.RectangularInverseModels
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
variable {stage : Nat}
  {mesh : ObservationMesh ((domains.get
    occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).cuts
    (base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt).cell.box}

namespace SharedPerimeter
variable (traces : PerimeterTraces mesh) (cache :
  Numerics domains stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- The weighted original corner cache used by the physical side endpoints. -/
def cornerValue (position : Fin base.faces.regulars.length) (sheet : Fin 2) (corner : Fin 4) : PrimitivePoint :=
  ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
    (cache.atDomain position sheet row).corners.values corner)

/-- The original weighted bottom side's first sampled value equals retained corner 0. -/
theorem bottom_first_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .bottom 0 =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 0 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_bottom_first_eq traces
  rw [traces.bottom.leftReadings_value] at equal
  exact equal

/-- The original weighted bottom side's last sampled value equals retained corner 1. -/
theorem bottom_last_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .bottom (Fin.last
      traces.bottom.vertices.rest.length) =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 1 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_bottom_last_eq traces
  rw [traces.bottom.leftReadings_value] at equal
  exact equal

/-- The original weighted right side's first sampled value equals retained corner 1. -/
theorem right_first_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .right 0 =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 1 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_right_first_eq traces
  rw [traces.right.leftReadings_value] at equal
  exact equal

/-- The original weighted right side's last sampled value equals retained corner 2. -/
theorem right_last_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .right (Fin.last
      traces.right.vertices.rest.length) =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 2 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_right_last_eq traces
  rw [traces.right.leftReadings_value] at equal
  exact equal

/-- The original weighted top side's first sampled value equals retained corner 3. -/
theorem top_first_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .top 0 =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 3 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_top_first_eq traces
  rw [traces.top.leftReadings_value] at equal
  exact equal

/-- The original weighted top side's last sampled value equals retained corner 2. -/
theorem top_last_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .top (Fin.last
      traces.top.vertices.rest.length) =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 2 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_top_last_eq traces
  rw [traces.top.leftReadings_value] at equal
  exact equal

/-- The original weighted left side's first sampled value equals retained corner 0. -/
theorem left_first_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .left 0 =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 0 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_left_first_eq traces
  rw [traces.left.leftReadings_value] at equal
  exact equal

/-- The original weighted left side's last sampled value equals retained corner 3. -/
theorem left_last_corner :
    SharedPerimeter.values (occurrence := occurrence) traces cache coefficients .left (Fin.last
      traces.left.vertices.rest.length) =
      cornerValue cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet 3 := by
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply congrArg (coefficients row * ·)
  have equal := (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet
    row).perimeter_left_last_eq traces
  rw [traces.left.leftReadings_value] at equal
  exact equal

/-- Read the selected side's oriented endpoint-chord area from the original retained corner-value cache. -/
def cachedEndpoint (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : GridLiftedDualSteps.GridSide) :
  Gaussian :=
  let value := cornerValue
    cache coefficients position sheet
  match side with
  | .bottom => Stokes.edgeArea (value 0) (value 1)
  | .right => Stokes.edgeArea (value 1) (value 2)
  | .top => Stokes.edgeArea (value 3) (value 2)
  | .left => Stokes.edgeArea (value 0) (value 3)

/-- Subtracting the initial primitive point from the second endpoint preserves their edge area. -/
private theorem endpoint_chord (first last : Stokes.PrimitivePoint) :
    Stokes.edgeArea first (last.sub first) = Stokes.edgeArea first last := by
  simp only [Stokes.edgeArea, PrimitivePoint.sub]
  ring1

/-- Refinement preserves the literal endpoint chord on the original corner cache. -/
theorem endpoint_eq_cached {side : GridLiftedDualSteps.GridSide} (sample : CenteredBilinearPath.Sample
  (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients side)) :
    sample.endpoint =
      cachedEndpoint cache
      coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet side := by
  rw [sample.endpoint_eq,
    endpoint_chord]
  cases side with
  | bottom =>
      exact congrArg₂ Stokes.edgeArea
        (bottom_first_corner
          traces cache coefficients)
          (bottom_last_corner
          traces cache coefficients)
  | top =>
      exact congrArg₂ Stokes.edgeArea
        (top_first_corner
          traces cache coefficients)
          (top_last_corner
          traces cache coefficients)
  | left =>
      exact congrArg₂ Stokes.edgeArea
        (left_first_corner
          traces cache coefficients)
          (left_last_corner
          traces cache coefficients)
  | right =>
      exact congrArg₂ Stokes.edgeArea
        (right_first_corner
          traces cache coefficients)
          (right_last_corner
          traces cache coefficients)

end SharedPerimeter
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
