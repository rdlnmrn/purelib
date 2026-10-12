module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Topology.Polygon

@[expose] public section
/-! Relate the retained perimeter to actual local triangle wedges, preserving seam and corner terms. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterTriangles
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter (gridValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples.SharedPerimeter (Samples)
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
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Readings.RectangularClippedLocalBoundary (localWedges)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal conjugateDiagonal_sub)
variable {stage : Nat}
  {cuts : GridCuts ((domains.get
    occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox}

namespace SharedPerimeter
variable (cache : Numerics domains
  stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- The unshifted local primitive values used by the Newton triangle estimate. -/
def primitiveValues
    (column row : Fin (((domains.get occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).steps +
      1))
    (point : InverseRootPolynomial.Gaussian) : PrimitivePoint :=
  ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin (fun basisRow => coefficients basisRow *
    (cache.atDomain occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet basisRow).primitives.value
      column row point))

/-- Alignment adds one constant per retained model owner; it cancels in increments taken within that owner, with the
same coefficient vector. -/
theorem grid_difference
    (column row : Fin (((domains.get occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).steps +
      1))
    (first last : InverseRootPolynomial.Gaussian) :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter.gridValues
      (occurrence := occurrence) cache coefficients column row last).sub
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter.gridValues
        cache coefficients column row first) =
    (primitiveValues
      cache coefficients column row last).sub

        (primitiveValues
        cache coefficients column row first) := by
  unfold SharedPerimeter.gridValues
    primitiveValues
  rw [← ConjugatePathReadback.conjugateDiagonal_sub, ← ConjugatePathReadback.conjugateDiagonal_sub]
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  rw [← FiniteSum.Fin.sumFin_sub, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro basisRow
  unfold RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue
  ring1

/-- Only the constant shift within a single triangle's retained owner is cancelled. This makes no claim that a closed
joining polygon has zero area. -/
theorem triangle_offsets_cancel
    (column row : Fin (((domains.get occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).steps +
      1))
    (first second third : InverseRootPolynomial.Gaussian) :
    Stokes.triangleWedgeArea
      (SharedPerimeter.gridValues (occurrence := occurrence) cache coefficients column row first)
      (SharedPerimeter.gridValues cache coefficients column row second) (SharedPerimeter.gridValues cache coefficients
        column row third) =
    Stokes.triangleWedgeArea
      (primitiveValues cache
        coefficients column row first)
      (primitiveValues cache
        coefficients column row second)
        (primitiveValues
        cache coefficients column row third) := by
  change Stokes.edgeArea
    ((SharedPerimeter.gridValues cache coefficients column row second).sub (SharedPerimeter.gridValues cache
      coefficients column row first))
    ((SharedPerimeter.gridValues cache coefficients column row third).sub (SharedPerimeter.gridValues cache coefficients
      column row first)) =
    Stokes.edgeArea
    ((primitiveValues cache
      coefficients column row second).sub
      (primitiveValues cache
      coefficients column row first))
    ((primitiveValues cache
      coefficients column row third).sub
      (primitiveValues cache
      coefficients column row first))
  rw [grid_difference,
    grid_difference]

/-- The complete retained local triangle sum is unchanged by cancelling each triangle owner's constant primitive
alignment offset. -/
theorem localWedges_offsets_cancel
    (triangles : List (RectangularOwnedTriangulation.ModelTriangle
      ((domains.get occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry)) :
    RectangularClippedLocalBoundary.localWedges (SharedPerimeter.gridValues (occurrence := occurrence) cache
      coefficients) triangles =
      RectangularClippedLocalBoundary.localWedges
        (primitiveValues
        cache coefficients) triangles := by
  induction triangles with
  | nil => rfl
  | cons triangle rest ih =>
    exact congrArg₂ (fun first last : InverseRootPolynomial.Gaussian => first + last)

        (triangle_offsets_cancel
        cache coefficients triangle.column triangle.row
        triangle.triangle.first triangle.triangle.second triangle.triangle.third) ih

variable (traces : PerimeterTraces mesh)

/-- Exact accounting of the complete local triangle sum. All owner seams, corner polygons and the four centering chords
remain in the identity. -/
theorem Samples.triangle_boundary (samples : SharedPerimeter.Samples traces cache coefficients)
    (assembly : ObservationMesh.ClippedAssembly mesh (SharedPerimeter.gridValues (occurrence := occurrence) cache
      coefficients))
    (perimeter : assembly.Perimeter) :
    RectangularClippedLocalBoundary.localWedges
      (primitiveValues
      (occurrence := occurrence) cache coefficients) mesh.triangles =
      ((samples.bottom.centeredArea + samples.bottom.endpoint) +
       (samples.right.centeredArea + samples.right.endpoint) -
       (samples.top.centeredArea + samples.top.endpoint) -
       (samples.left.centeredArea + samples.left.endpoint)) + assembly.seams + assembly.cornerTotal := by
  rw [←
    localWedges_offsets_cancel
    cache coefficients,
    mesh.localWedges_eq_boundary, ← assembly.localTotal_eq, assembly.decomposition,
    samples.exterior traces cache coefficients assembly perimeter]

end SharedPerimeter
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterTriangles
