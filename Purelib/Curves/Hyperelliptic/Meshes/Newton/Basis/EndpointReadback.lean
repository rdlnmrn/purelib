module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback

open Purelib.Riemann.Meshes

open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Identify common-basis endpoint corrections with the Newton corner cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Normalization
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {current
    : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {partitions : SurfacePartitions
    observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains
    sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet}
    {error : Rational}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter (cornerValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter (cachedEndpoint)
open Purelib.Riemann.RootContinuation.NewtonGlobalPhysicalEndpointReadback.SynchronizedSurfaceRequests.PerimeterSamples
  (cachedSideEndpoint)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback.OuterCorners (cachedValue)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Basic (conj_add conj_mul)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Gaussian conjugation commutes with the original explicit finite basis sum. -/
private theorem conjugate_sum {count : Nat} (values : Fin count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin values) = FiniteSum.Fin.sumFin (fun index =>
      Data.Gaussian.Basic.conj (values index)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, Data.Gaussian.Basic.conj_add]
      exact congrArg (Data.Gaussian.Basic.conj (values 0) + ·) (ih _)

/-- Both weighted corner representations read the same original numerical bank. -/
theorem commonBasis_corner_eq_cached (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (corner : Fin 4) :
    SharedPerimeter.cornerValue (lifted := current) cache coefficients position sheet corner =
      OuterCorners.cachedValue cache coefficients position sheet corner := by
  apply congrArg₂ PrimitivePoint.mk
  · change Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun row => coefficients row * (cache.atDomain
      position sheet row).corners.values corner)) = _
    rw
      [conjugate_sum]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    exact Data.Gaussian.Basic.conj_mul _ _
  · rfl

/-- The common-basis endpoint correction is exactly the Newton cached chord. -/
theorem commonBasis_endpoint_eq_cached (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (side :
  GridLiftedDualSteps.GridSide) :
    SharedPerimeter.cachedEndpoint (lifted := current) cache coefficients position sheet side =
      PerimeterSamples.cachedSideEndpoint cache coefficients position sheet side := by
  cases side <;> exact congrArg₂ Stokes.edgeArea
    (commonBasis_corner_eq_cached
    _ _ _)
    (commonBasis_corner_eq_cached
    _ _ _)

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Basis.EndpointReadback
