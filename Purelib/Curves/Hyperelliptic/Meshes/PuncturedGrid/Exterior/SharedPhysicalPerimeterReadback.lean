module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings.RectangularObservationAssembly

@[expose] public section

/-! Read cached physical samples back to the actual retained perimeter, including endpoint chords. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadback
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
  (Entries original)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
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
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {firstBank : FacePrimitiveBank
  differential index domains} {secondBank :
  FacePrimitiveBank other index domains}

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
variable {cuts : GridCuts ((domains.get
  occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry} {meshBox :
  Purelib.Geometry.Rational.Box}
  {mesh : ObservationMesh cuts meshBox} {depth : Nat}

namespace SharedPhysicalPerimeterReadings

/-- Read the original two face-bank values at the retained grid owner and point, conjugating the first coordinate. -/
def gridValues (firstBank : PrimitiveData.FacePrimitiveBank differential index domains) (secondBank :
  PrimitiveData.FacePrimitiveBank other index domains)
    (column row : Fin (((domains.get occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).steps +
      1))
    (point : InverseRootPolynomial.Gaussian) : PrimitivePoint :=
  let first := (firstBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  let second := (secondBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  ConjugateIncrementComparison.conjugateFirst ⟨first.anchors.alignedValue first.offsets column row point,
    second.anchors.alignedValue second.offsets column row point⟩

/-- Read the selected rectangle side's already cached perimeter area. -/
def sideArea {assembly : ObservationMesh.ClippedAssembly mesh
  (gridValues
  firstBank secondBank)} (perimeter : assembly.Perimeter) : GridLiftedDualSteps.GridSide →
  InverseRootPolynomial.Gaussian
  | .bottom => perimeter.bottom
  | .top => perimeter.top
  | .left => perimeter.left
  | .right => perimeter.right

/-- The sample uses the very owner values of the perimeter assembly. -/
theorem original_area (traces : RectangularPerimeterTraces.PerimeterTraces mesh) {side : GridLiftedDualSteps.GridSide}
    (readings : SharedPhysicalPerimeterReadings.Entries traces firstBank secondBank side)
    (assembly : ObservationMesh.ClippedAssembly mesh
      (gridValues
      firstBank secondBank)) (perimeter : assembly.Perimeter) :
    (SharedPhysicalPerimeterReadings.original traces readings).originalArea =
      sideArea
      perimeter side := by
  have retained := (SharedPhysicalPerimeterReadings.original traces readings).originalArea_eq
  cases side with
  | bottom => exact retained.trans (traces.bottom_area _ assembly perimeter)
  | top => exact retained.trans (traces.top_area _ assembly perimeter)
  | left => exact retained.trans (traces.left_area _ assembly perimeter)
  | right => exact retained.trans (traces.right_area _ assembly perimeter)

/-- Centering removes an actual endpoint chord. Keep that term when transporting the cap estimate to the uncentered
physical boundary. -/
theorem centered_add_endpoint (traces : RectangularPerimeterTraces.PerimeterTraces mesh) {side :
  GridLiftedDualSteps.GridSide}
    (readings : SharedPhysicalPerimeterReadings.Entries traces firstBank secondBank side)
    (assembly : ObservationMesh.ClippedAssembly mesh
      (gridValues
      firstBank secondBank)) (perimeter : assembly.Perimeter) :
    (SharedPhysicalPerimeterReadings.original traces readings).centeredArea + (SharedPhysicalPerimeterReadings.original
      traces readings).endpoint =
      sideArea
      perimeter side :=
  (SharedPhysicalPerimeterReadings.original traces readings).decomposition.symm.trans
    (original_area
    traces readings assembly perimeter)

end SharedPhysicalPerimeterReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadback
