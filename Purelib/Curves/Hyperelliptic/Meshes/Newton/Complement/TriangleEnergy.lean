module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ContactEnergy
public import Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.RootContinuation.NewtonGlobalTriangleEnergyReadback.SynchronizedSurfaceRequests

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

@[expose] public section

/-! The retained outer corner polygons read the actual shared triangle cache
on the same source mask as the sewn Newton complement. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.TriangleEnergy

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
    {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Fraction.Rational}
  {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage} {coefficients
    : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : Topology.NewtonSynchronizedSurfaceRequests.SynchronizedSurfaceRequests coarse fixed error} {traces
  : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces requests}
  (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)

/-- Sum the original cached corner areas over both sheets on the exact retained complement face mask. -/
def remainingCachedCornerBoundary (cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains
  stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value
    (Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position) (FiniteSum.Fin.sumFin
    (fun sheet : Fin 2 =>
    Periods.BilinearGridBoundary.cornerArea
      (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position
        sheet 0)
      (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position
        sheet 1)
      (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position
        sheet 2)
      (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.cachedValue cache coefficients position
        sheet 3))))

/-- The original retained complement corner boundary equals the sum of its cached corner readings. -/
theorem remaining_cornerBoundary_cached {assemblies :
  Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies requests (cache := cache)
  (coefficients := coefficients)}
    {perimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters requests assemblies}
      (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces requests perimeters) :

      CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingCornerBoundary
      excision faces =
      remainingCachedCornerBoundary
      excision cache coefficients := by
  unfold
    CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingCornerBoundary
    remainingCachedCornerBoundary
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply congrArg (Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value
    (Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position))
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  let face := (faces.get sheet).get position
  change Periods.BilinearGridBoundary.cornerArea
    (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false false)
      (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true false)
    (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face true true)
      (Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value face false true) = _
  rw [Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
    Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
    Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached,
    Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners.value_eq_cached]
  rfl

variable (readings :
  PerimeterSamples.EnergyTriangleReadings
  cache lifted.mesh)

/-- Sum the actual retained triangle energies on the complement of the original annular source masks. -/
def remainingTriangleEnergy (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin (fun source => if !(excision.entries.any (fun entry =>
    Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry source)) then
    RootContinuation.NewtonGlobalTriangleEnergyReadback.SynchronizedSurfaceRequests.PerimeterSamples.triangleEnergy
      readings coefficients source else 0)

/-- The original complement corner boundary reads exactly the triangle-energy cache selected by the same retained source
mask. -/
theorem remaining_cornerBoundary_triangles
    {assemblies : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetAssemblies requests (cache :=
      cache) (coefficients := coefficients)}
    {perimeters : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetPerimeters requests assemblies}
      (faces : Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.SheetFaces requests perimeters) :

      CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples.remainingCornerBoundary
      excision faces =
      remainingTriangleEnergy
      excision readings coefficients := by
  rw
    [remaining_cornerBoundary_cached]
  unfold
    remainingCachedCornerBoundary
    remainingTriangleEnergy
  erw [Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.LiftedMesh.triangle_sum lifted.mesh]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  rw [Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  rw [Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask_triangleIndex,
    Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask_triangleIndex]
  rw [←
    RootContinuation.NewtonGlobalTriangleEnergyReadback.SynchronizedSurfaceRequests.PerimeterSamples.triangleEnergy_pair
    readings position sheet]
  cases Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position with
  | false => exact (add_zero (0 : Gaussian.Basic.Canonical)).symm
  | true => rfl

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.TriangleEnergy
