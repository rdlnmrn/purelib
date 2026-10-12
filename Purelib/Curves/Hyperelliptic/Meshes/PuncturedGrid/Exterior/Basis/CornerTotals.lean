module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
import Purelib.Integration.Path.CenteredPathIncrements
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PerimeterReadback

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Telescope weighted side increments to the original Newton corner cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter (cornerValue
  bottom_last_corner bottom_first_corner right_last_corner right_first_corner top_last_corner top_first_corner
  left_last_corner left_first_corner)
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

/-- The physical displacement between the original cached side endpoints. -/
def cachedIncrement (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : GridLiftedDualSteps.GridSide) :
  PrimitivePoint :=
  let value := SharedPerimeter.cornerValue cache coefficients position sheet
  match side with
  | .bottom => (value 1).sub (value 0)
  | .right => (value 2).sub (value 1)
  | .top => (value 2).sub (value 3)
  | .left => (value 3).sub (value 0)

/-- The retained bottom sample telescopes to its original corner difference. -/
theorem bottom_total_eq_cached
    (sample : CenteredBilinearPath.Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .bottom)) :
    PairedIncrementArea.total (CenteredPathIncrements.Sample.increments sample) =
      cachedIncrement cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet .bottom := by
  exact (CenteredPathIncrements.Sample.increments_total sample).trans (congrArg₂ PrimitivePoint.sub
    (SharedPerimeter.bottom_last_corner traces cache coefficients) (SharedPerimeter.bottom_first_corner traces cache
      coefficients))

/-- The retained right sample telescopes to its original corner difference. -/
theorem right_total_eq_cached
    (sample : CenteredBilinearPath.Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .right)) :
    PairedIncrementArea.total (CenteredPathIncrements.Sample.increments sample) =
      cachedIncrement cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet .right := by
  exact (CenteredPathIncrements.Sample.increments_total sample).trans (congrArg₂ PrimitivePoint.sub
    (SharedPerimeter.right_last_corner traces cache coefficients) (SharedPerimeter.right_first_corner traces cache
      coefficients))

/-- The retained top sample telescopes to its original corner difference. -/
theorem top_total_eq_cached
    (sample : CenteredBilinearPath.Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .top)) :
    PairedIncrementArea.total (CenteredPathIncrements.Sample.increments sample) =
      cachedIncrement cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet .top := by
  exact (CenteredPathIncrements.Sample.increments_total sample).trans (congrArg₂ PrimitivePoint.sub
    (SharedPerimeter.top_last_corner traces cache coefficients) (SharedPerimeter.top_first_corner traces cache
      coefficients))

/-- The retained left sample telescopes to its original corner difference. -/
theorem left_total_eq_cached
    (sample : CenteredBilinearPath.Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      .left)) :
    PairedIncrementArea.total (CenteredPathIncrements.Sample.increments sample) =
      cachedIncrement cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet .left := by
  exact (CenteredPathIncrements.Sample.increments_total sample).trans (congrArg₂ PrimitivePoint.sub
    (SharedPerimeter.left_last_corner traces cache coefficients) (SharedPerimeter.left_first_corner traces cache
      coefficients))

/-- Each refined side has exactly its original cached displacement. -/
theorem total_eq_cached {side : GridLiftedDualSteps.GridSide}
    (sample : CenteredBilinearPath.Sample (SharedPerimeter.values (occurrence := occurrence) traces cache coefficients
      side)) :
    PairedIncrementArea.total (CenteredPathIncrements.Sample.increments sample) =
      cachedIncrement cache
        coefficients occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet side := by
  cases side with
  | bottom =>
    exact bottom_total_eq_cached
      traces cache coefficients sample
  | right =>
    exact right_total_eq_cached
      traces cache coefficients sample
  | top =>
    exact top_total_eq_cached
      traces cache coefficients sample
  | left =>
    exact left_total_eq_cached
      traces cache coefficients sample

end SharedPerimeter
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
