module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Integration.Energy.Polygon
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyBoundary
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Geometry.Rectangle.Partition.PreparedPartitionBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Polynomial.Dense.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearBoundary
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Mathlib.Order.Basic

open Purelib.Data

public section

/-!
# Complete regular energy on the retained subdivided piece exteriors

The sampled energy lower bound is read through the actual conjugate/value
boundary on each piece. All pieces use the common requested spatial depth.
Their own model cuts remain visible; inter-piece and inter-domain matching
are subsequent obligations, not implicit cancellations in this readback.
-/

namespace Purelib.Riemann.Topology.NewtonObservationSurfaceBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower (surfaceLowerConstant)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2} {stage : Nat}
  {cache : Numerics domains stage} {partitions : SurfacePartitions observations grid}
  {coarse : SurfaceMeshes partitions domains sheet} {fixed : Preflights domains sheet} {error :
    Purelib.Data.Rat.Fraction.Rational}
  {request : SurfaceRequest partitions coarse fixed error} {samples : request.Readings cache}

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Energy in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Topology in
/-- Identify a retained piece energy boundary with its exterior boundary reading.

Uses the actual sampled piece, energy primitive and retained mesh-depth equality, without changing the partition or
coefficient vector. -/
theorem Budget.piece_boundary_eq_exterior (budget : NewtonRequestedSurfaceEnergy.SurfaceRequest.Budget request samples)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (position : Fin grid.faces.regulars.length)
    (piece : Fin (partitions.get position).cuts.boxes.length) :
    (((budget.entries.get position).get piece).sample coefficients).boundaryArea =
      ((request.meshes.get position).entries.get piece).partition.boundary
        (fun point => Polygon.energyPrimitivePoint (((samples.get position).readings.get piece).atPoint coefficients
          point))
        request.depth := by
  rw [Meshes.PuncturedGrid.DomainEnergyBoundary.energy_boundary_eq_exterior ((samples.get position).readings.get piece),
    request.mesh_depth]

open Purelib in
open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Topology in
/-- Lower-bound the sum of retained piece exterior energies.

Transports the surface coercivity estimate through each exact piece-boundary identity using pointwise finite-sum
congruence. -/
theorem piece_exteriors_lower (request : SurfaceRequest partitions coarse fixed error) (later : request.index ≤ stage)
    (samples : request.Readings cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    (surfaceLowerConstant observations - error) * coefficientNormSq coefficients ≤
      FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        (((request.meshes.get position).entries.get piece).partition.boundary
          (fun point => Polygon.energyPrimitivePoint (((samples.get position).readings.get piece).atPoint coefficients
            point))
          request.depth).im / 4)) := by
  apply (NewtonObservationSurfaceLower.SurfaceRequest.boundary_lower request later samples coefficients face).trans_eq
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro piece
  exact congrArg (fun area : Basic.Canonical => area.im / 4)
    (Budget.piece_boundary_eq_exterior (request.budget later samples) coefficients position piece)

end Purelib.Riemann.Topology.NewtonObservationSurfaceBoundary
