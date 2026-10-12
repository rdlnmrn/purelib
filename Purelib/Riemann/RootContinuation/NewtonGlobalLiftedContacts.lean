module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Riemann.Branches.GridLiftedCrossingSheets
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Two-sheet contact bounds follow the actual lifted face matches. -/
namespace Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContacts

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
  (centeredSideSum pairedEndpoints paired_error_bound)
open Purelib.Riemann.Branches.GridLiftedCrossingSheets.LiftedMesh (atSide_difference_bound)
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
  {stage : Nat} {cache : Numerics domains stage} {coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests.PerimeterSamples

variable {requests : SynchronizedSurfaceRequests coarse fixed error} {traces : PerimeterTraces requests}
  (samples : PerimeterSamples requests traces cache coefficients)

/-- Centered area of one retained face side and sheet.

Selects the actual bottom, right, top or left perimeter sample without changing its face owner. -/
@[expose] def centeredValue (side : GridSide) (position : Fin grid.faces.regulars.length) (sheet : Fin 2) : Gaussian :=
  match side with
  | .bottom => ((samples.get sheet).get position).bottom.centeredArea
  | .right => ((samples.get sheet).get position).right.centeredArea
  | .top => ((samples.get sheet).get position).top.centeredArea
  | .left => ((samples.get sheet).get position).left.centeredArea

variable {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
  Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  (mesh : LiftedMesh vertices edges grid.faces)

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Lifted per-sheet contact bounds control the summed side difference.

Uses the actual target-sheet witnesses to compare both sheet sums, with the factor-four squared-norm bound. -/
theorem centered_lifted_error_bound (first last : Fin grid.faces.regulars.length)
    (firstSide lastSide : GridSide)
    (next : (sheet : Fin 2) → mesh.AtSide last lastSide
      ((mesh.locateFace first sheet).lifted.sideFinishSheet firstSide))
    {allowance : Fraction.Rational}
    (bounded : ∀ sheet, Data.Gaussian.Norm.Basic.normSq
      (centeredValue samples firstSide first sheet - centeredValue samples lastSide last (next sheet).sheet) ≤
        allowance) :
    Data.Gaussian.Norm.Basic.normSq
      (centeredSideSum samples firstSide first - centeredSideSum samples lastSide last) ≤ 4 * allowance :=
  atSide_difference_bound next _ _ bounded

/-- Bound the global paired-centered difference using lifted contacts.

Combines horizontal and vertical sheetwise estimates across retained matching interfaces, keeping the factor sixteen and
fourth power of the regular-face count. -/
theorem paired_lifted_error_bound {allowance : Fraction.Rational} (nonnegative : 0 ≤ allowance)
    (horizontal : ∀ first last, GridSide.Matches .top (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      (sheet : Fin 2) → mesh.AtSide last .bottom ((mesh.locateFace first sheet).lifted.sideFinishSheet .top))
    (vertical : ∀ first last, GridSide.Matches .right (grid.faces.regulars[first.val]'first.isLt).cell.box
      (grid.faces.regulars[last.val]'last.isLt).cell.box →
      (sheet : Fin 2) → mesh.AtSide last .left ((mesh.locateFace first sheet).lifted.sideFinishSheet .right))
    (horizontalBound : ∀ first last matching sheet, Data.Gaussian.Norm.Basic.normSq
      (((samples.get sheet).get first).top.centeredArea -
        ((samples.get (horizontal first last matching sheet).sheet).get last).bottom.centeredArea) ≤ allowance)
    (verticalBound : ∀ first last matching sheet, Data.Gaussian.Norm.Basic.normSq
      (((samples.get sheet).get first).right.centeredArea -
        ((samples.get (vertical first last matching sheet).sheet).get last).left.centeredArea) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (samples.paired - pairedEndpoints samples) ≤
      16 * (grid.faces.regulars.length : Fraction.Rational)^4 * allowance := by
  have bound := paired_error_bound samples
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4) nonnegative)
    (fun first last matching => centered_lifted_error_bound samples mesh first last .top .bottom
      (horizontal first last matching) (horizontalBound first last matching))
    (fun first last matching => centered_lifted_error_bound samples mesh first last .right .left
      (vertical first last matching) (verticalBound first last matching))
  exact bound.trans_eq (by ring1)

end SynchronizedSurfaceRequests.PerimeterSamples
end Purelib.Riemann.RootContinuation.NewtonGlobalLiftedContacts
