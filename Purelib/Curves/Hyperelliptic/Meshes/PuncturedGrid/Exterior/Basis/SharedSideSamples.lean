module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
import Purelib.Integration.Polynomial.Rectangle.SampleReadback
public import Purelib.Integration.Path.ConjugatePathReadback
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks

open Purelib.Integration.Path

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Riemann.Periods

@[expose] public section
/-! Cache weighted physical samples from the retained Newton basis readings. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (ownedValue)
open Purelib.Riemann.Normalization
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
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
variable {stage depth : Nat}
  {cuts : GridCuts ((domains.get
    occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox}

open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

namespace SharedHorizontalBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank (Data values)
variable {firstRow secondRow : Fin mesh.partition.y.intervals.length}
  {height : Coordinate} {side :
    MatchedHorizontalSide mesh mesh firstRow
    secondRow height}
  {trace : side.Trace depth} {cache :
    Numerics domains stage}
  (bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedHorizontalBank.Data
    trace cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- The coefficient combination of the retained owner readings equals the same combination of the exact original cached
basis-row values. -/
theorem Data.weighted_value (vertex : Fin (trace.vertices.rest.length + 1)) :
    OwnerRequest.ownedValue bank.readings coefficients vertex =
      FiniteSum.Fin.sumFin (fun row => coefficients row * SharedHorizontalBank.values trace cache row
        (trace.vertices.indexed vertex)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  exact congrArg (fun value => coefficients row * value) (bank.readback row vertex)

/-- Compute the weighted vertex vector once from cached scalar readings, then retain its centered area, original area
and endpoint chord together. -/
def Data.sample : CenteredBilinearPath.Sample (fun vertex => ConjugatePathReadback.conjugateDiagonal
    (FiniteSum.Fin.sumFin (fun row => coefficients row * SharedHorizontalBank.values trace cache row
      (trace.vertices.indexed vertex)))) :=
  let points := Data.Vector.Basic.vectorOfFn (fun vertex => ConjugatePathReadback.conjugateDiagonal
    (OwnerRequest.ownedValue bank.readings coefficients vertex))
  SampleReadback.Sample.readback (CenteredBilinearPath.Sample.build (fun vertex => points vertex)) (fun vertex =>
    (Data.Vector.Basic.vectorOfFn_apply _ vertex).trans (congrArg ConjugatePathReadback.conjugateDiagonal
      (Data.weighted_value
      bank coefficients vertex)))

end SharedHorizontalBank

namespace SharedVerticalBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedVerticalBank (Data values)
variable {firstColumn secondColumn : Fin mesh.partition.x.intervals.length}
  {width : Coordinate} {side :
    MatchedVerticalSide mesh mesh
    firstColumn secondColumn width}
  {trace : side.Trace depth} {cache :
    Numerics domains stage}
  (bank : Data trace cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)

/-- The coefficient combination of the retained owner readings equals the same combination of the exact original cached
basis-row values. -/
theorem Data.weighted_value (vertex : Fin (trace.vertices.rest.length + 1)) :
    OwnerRequest.ownedValue bank.readings coefficients vertex =
      FiniteSum.Fin.sumFin (fun row => coefficients row * values trace cache row (trace.vertices.indexed vertex)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  exact congrArg (fun value => coefficients row * value) (bank.readback row vertex)

/-- Compute the weighted vertex vector once from cached scalar readings, then retain its centered area, original area
and endpoint chord together. -/
def Data.sample : CenteredBilinearPath.Sample (fun vertex => ConjugatePathReadback.conjugateDiagonal
    (FiniteSum.Fin.sumFin (fun row => coefficients row * values trace cache row (trace.vertices.indexed vertex)))) :=
  let points := Data.Vector.Basic.vectorOfFn (fun vertex => ConjugatePathReadback.conjugateDiagonal
    (OwnerRequest.ownedValue bank.readings coefficients vertex))
  SampleReadback.Sample.readback (CenteredBilinearPath.Sample.build (fun vertex => points vertex)) (fun vertex =>
    (Data.Vector.Basic.vectorOfFn_apply _ vertex).trans (congrArg ConjugatePathReadback.conjugateDiagonal
      (Data.weighted_value
      bank coefficients vertex)))

end SharedVerticalBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
