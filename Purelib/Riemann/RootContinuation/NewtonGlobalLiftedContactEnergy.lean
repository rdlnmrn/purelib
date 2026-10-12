module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContacts
import Purelib.Integration.Budget.Surface.Contact
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Integration.Path.JoinedTrace
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.CenteredPerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic

public section

/-! Complete-face bounds at the computed piece budget pay the global
contact energy, following the actual two-sheet permutations. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContactEnergy

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes)
open Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests (SynchronizedSurfaceRequests)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces PerimeterSamples)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (pairedCentered)
open Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy.SynchronizedSurfaceRequests (contactTarget)
open Purelib.Riemann.RootContinuation.NewtonGlobalContactEnergy.SynchronizedSurfaceRequests.PerimeterSamples
  (contact_paid)
open Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContacts.SynchronizedSurfaceRequests.PerimeterSamples
  (centered_lifted_error_bound)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational} {grid : NewtonGrid preparation
    target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars}
    {partitions : SurfacePartitions observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet} {error : Data.Rat.Fraction.Rational}
  {stage : Nat} {cache : Numerics domains stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
    genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {vertices : RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
  RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  (mesh : LiftedMesh vertices edges grid.faces)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Lifted per-sheet contact estimates pay the global centered error.

Each matching contact receives one quarter of the genus-scaled local target; the two-sheet comparison cancels that
factor before applying the global contact payment. -/
theorem lifted_contact_paid {allowance : Fraction.Rational} (positive : 0 < allowance)
    (horizontal : ∀ first last, GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      (sheet : Fin 2) → mesh.AtSide last .bottom ((mesh.locateFace first sheet).lifted.sideFinishSheet .top))
    (vertical : ∀ first last, GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      (sheet : Fin 2) → mesh.AtSide last .left ((mesh.locateFace first sheet).lifted.sideFinishSheet .right))
    (horizontalBound : ∀ first last matching sheet, Data.Gaussian.Norm.Basic.normSq
      (((samples.get sheet).get first).top.centeredArea -
        ((samples.get (horizontal first last matching sheet).sheet).get last).bottom.centeredArea) ≤
      (genus : Fraction.Rational) ^ 2 * coefficientNormSq coefficients ^ 2 * contactTarget genus
        grid.faces.regulars.length allowance / 4)
    (verticalBound : ∀ first last matching sheet, Data.Gaussian.Norm.Basic.normSq
      (((samples.get sheet).get first).right.centeredArea -
        ((samples.get (vertical first last matching sheet).sheet).get last).left.centeredArea) ≤
      (genus : Fraction.Rational) ^ 2 * coefficientNormSq coefficients ^ 2 * contactTarget genus
        grid.faces.regulars.length allowance / 4) :
    Data.Gaussian.Norm.Basic.normSq (pairedCentered samples) ≤ (4 * (allowance * coefficientNormSq coefficients)) ^ 2
      := by
  apply contact_paid samples positive
  · intro first last matching
    have bound := centered_lifted_error_bound samples mesh first last .top .bottom
      (horizontal first last matching) (horizontalBound first last matching)
    exact bound.trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  · intro first last matching
    have bound := centered_lifted_error_bound samples mesh first last .right .left
      (vertical first last matching) (verticalBound first last matching)
    exact bound.trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContactEnergy
