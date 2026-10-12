module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularObservationAssembly

@[expose] public section
/-! Acquire and retain all four weighted Newton perimeter samples together. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples

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
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback.SharedPerimeter (gridValues
  values exterior_readback)
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
variable {stage : Nat}
  {cuts : GridCuts ((domains.get
    occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox}

namespace SharedPerimeter
variable (traces : PerimeterTraces mesh) (cache :
  Numerics domains stage)

-- Exact field aliases keep the cached trace owners compact.
/-- The retained original shared basis-row reading bank on the bottom perimeter trace. -/
def BottomBank := SharedHorizontalBank.Data (occurrence := occurrence) traces.bottom cache
/-- The retained original shared basis-row reading bank on the top perimeter trace. -/
def TopBank := SharedHorizontalBank.Data (occurrence := occurrence) traces.top cache
/-- The retained original shared basis-row reading bank on the left perimeter trace. -/
def LeftBank := SharedVerticalBank.Data (occurrence := occurrence) traces.left cache
/-- The retained original shared basis-row reading bank on the right perimeter trace. -/
def RightBank := SharedVerticalBank.Data (occurrence := occurrence) traces.right cache

set_option genInjectivity false in
/-- Store each side's basis readings once, including all duplicate junction owners. No row or primitive is reacquired
when the perimeter is read back. -/
structure Banks where
  /-- The cached original basis-row owner readings on the bottom side. -/ bottom :
    BottomBank traces cache
  /-- The cached original basis-row owner readings on the top side. -/ top :
    TopBank traces cache
  /-- The cached original basis-row owner readings on the left side. -/ left :
    LeftBank traces cache
  /-- The cached original basis-row owner readings on the right side. -/ right :
    RightBank traces cache

constructive_injectivity Banks

/-- Cache all four original side reading banks once, preserving their exact trace and numerical owners. -/
def Banks.build : Banks traces
  cache :=
  ⟨SharedHorizontalBank.build traces.bottom cache, SharedHorizontalBank.build traces.top cache,
    SharedVerticalBank.build traces.left cache, SharedVerticalBank.build traces.right cache⟩

variable (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- The centered sample of the exact coefficient-weighted original values on the selected perimeter side. -/
def SideSample (side : GridLiftedDualSteps.GridSide) := CenteredBilinearPath.Sample (SharedPerimeter.values traces cache
  coefficients side)

set_option genInjectivity false in
/-- Cache the four centered areas, original areas and endpoint chords for one coefficient vector; subsequent boundary
comparisons consume these samples. -/
structure Samples where
  /-- The retained weighted bottom side sample with its centered area, original area and endpoint chord. -/ bottom :
    SideSample traces cache
    coefficients .bottom
  /-- The retained weighted top side sample with its centered area, original area and endpoint chord. -/ top :
    SideSample traces cache
    coefficients .top
  /-- The retained weighted left side sample with its centered area, original area and endpoint chord. -/ left :
    SideSample traces cache
    coefficients .left
  /-- The retained weighted right side sample with its centered area, original area and endpoint chord. -/ right :
    SideSample traces cache
    coefficients .right

constructive_injectivity Samples

/-- Compute and cache the four coefficient-weighted samples using the retained original side banks. -/
def Banks.sample (banks :
  Banks traces cache) :
  Samples traces cache
  coefficients :=
  ⟨SharedHorizontalBank.Data.sample banks.bottom coefficients, SharedHorizontalBank.Data.sample banks.top coefficients,
    SharedVerticalBank.Data.sample banks.left coefficients, SharedVerticalBank.Data.sample banks.right coefficients⟩

/-- Read the already cached weighted sample on the selected original perimeter side. -/
def Samples.get (samples :
  Samples traces cache
  coefficients) :
    (side : GridLiftedDualSteps.GridSide) →
      SideSample traces cache
      coefficients side
  | .bottom => samples.bottom
  | .top => samples.top
  | .left => samples.left
  | .right => samples.right

/-- The retained weighted samples reproduce the entire Newton exterior, with all four signs and all endpoint chords. -/
theorem Samples.exterior (samples :
  Samples traces cache
  coefficients)
    (assembly : ObservationMesh.ClippedAssembly mesh (SharedPerimeter.gridValues (occurrence := occurrence) cache
      coefficients))
    (perimeter : assembly.Perimeter) :
    assembly.exterior =
      (samples.bottom.centeredArea + samples.bottom.endpoint) +
      (samples.right.centeredArea + samples.right.endpoint) -
      (samples.top.centeredArea + samples.top.endpoint) -
      (samples.left.centeredArea + samples.left.endpoint) :=
  SharedPerimeter.exterior_readback traces cache coefficients (samples.get traces cache coefficients) assembly perimeter

end SharedPerimeter
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterSamples
