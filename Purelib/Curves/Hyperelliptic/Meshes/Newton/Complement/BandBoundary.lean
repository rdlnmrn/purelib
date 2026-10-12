module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSynchronizedSurfaceRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonRetainedBandBank
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryBounds
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary.SynchronizedSurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests

open Purelib.Riemann.RootContinuation.NewtonRetainedBandBank.SynchronizedSurfaceRequests

open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters

open Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate

open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary

public section

/-! All retained non-exterior sides are paid on one cached numerical tail. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary

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
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {partitions : SurfacePartitions
    observations grid}
  {coarse : (sheet : Fin 2) → SurfaceMeshes partitions domains
    sheet}
  {fixed : (sheet : Fin 2) → Preflights domains sheet}
    {error : Rational}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace SynchronizedSurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.RootContinuation.NewtonRetainedBandBank.SynchronizedSurfaceRequests.RetainedBandBank (NeighborIndex
  Condition Entry Entries Request)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.CenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (remainingBoundaryCentered)
open Purelib.Riemann.RootContinuation.NewtonGlobalCenteredBoundary.SynchronizedSurfaceRequests.PerimeterSamples
  (centeredSideSum)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryBounds (boundary_sub_exterior_bound)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {lifted : LiftedPuncturedGrid grid.punctured}
  {requests : SynchronizedSurfaceRequests coarse fixed error}
    {traces : PerimeterTraces requests}
  {position : Fin grid.faces.regulars.length} {side : GridSide}

namespace RetainedBandBank

variable (excision : AllHoleExcision grid lifted) (traces :
  PerimeterTraces requests)

set_option genInjectivity false in
/-- The original interface and hole requests for one retained grid side with a common paid stage. -/
structure SideRequests (side : GridLiftedDualSteps.GridSide) where
  /-- The request on retained-to-removed regular interfaces for this side. -/ interfaces : RetainedBandBank.Request
    excision traces side false
  /-- The request on retained physical-hole neighbors for this side. -/ holes : RetainedBandBank.Request excision traces
    side true
  /-- The common threshold of the original interface and hole requests. -/ index : Nat
  /-- The retained interface request is paid at the side stage. -/ interfaces_le : interfaces.index ≤ index
  /-- The retained hole request is paid at the side stage. -/ holes_le : holes.index ≤ index

constructive_injectivity SideRequests

/-- Retain the original interface and hole requests and cache the maximum of their thresholds. -/
@[expose] def SideRequests.build (side : GridLiftedDualSteps.GridSide) :
  SideRequests
  excision traces side :=
  let interfaces := RetainedBandBank.Request.build excision traces side false
  let holes := RetainedBandBank.Request.build excision traces side true
  ⟨interfaces, holes, max interfaces.index holes.index, Data.Nat.Order.le_max_left _ _, Data.Nat.Order.le_max_right _ _⟩

end RetainedBandBank

set_option genInjectivity false in
/-- All four original non-exterior side requests and a common stage paying the surface and requested floor. -/
structure RemainingBandRequest (excision : Excision.AllHoleExcision grid lifted) (traces :
  SynchronizedSurfaceRequests.PerimeterTraces requests)
    (floor : Nat) where
  /-- The retained interface and hole request pair for each of the four grid sides. -/ sides : (side :
    GridLiftedDualSteps.GridSide) →
    Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RetainedBandBank.SideRequests
    excision traces side
  /-- The common threshold of all four side requests, the original surface request and floor. -/ index : Nat
  /-- Every original side request is paid at the common stage. -/ sides_le : ∀ side, (sides side).index ≤ index
  /-- The requested minimum stage is paid. -/ floor_le : floor ≤ index
  /-- The original synchronized surface request is paid. -/ surface_le : requests.index ≤ index

constructive_injectivity RemainingBandRequest

namespace RemainingBandRequest
variable {excision : AllHoleExcision grid lifted} {floor :
  Nat}

/-- Prepare every original side request and retain their common threshold together with the surface and floor bounds. -/
@[expose] def build (excision : Excision.AllHoleExcision grid lifted) (traces :
  SynchronizedSurfaceRequests.PerimeterTraces requests) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest excision
      traces floor := by
  let bottom :=
    RetainedBandBank.SideRequests.build
    excision traces .bottom
  let right :=
    RetainedBandBank.SideRequests.build
    excision traces .right
  let top :=
    RetainedBandBank.SideRequests.build
    excision traces .top
  let left :=
    RetainedBandBank.SideRequests.build
    excision traces .left
  let sides : (side : GridLiftedDualSteps.GridSide) →
    Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RetainedBandBank.SideRequests
    excision traces side
    | .bottom => bottom
    | .right => right
    | .top => top
    | .left => left
  let maximum := max (max bottom.index right.index) (max top.index left.index)
  refine ⟨sides, max (max requests.index floor) maximum, ?_,
    (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _), (Data.Nat.Order.le_max_left _ _).trans
      (Data.Nat.Order.le_max_left _ _)⟩
  intro side
  apply Nat.le_trans (m := maximum) _ (Data.Nat.Order.le_max_right _ _)
  cases side with
  | bottom => exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  | right => exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)
  | top => exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  | left => exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)

open Purelib.Data.Rat.Fraction.Compatibility

/-- A face kept in the complement lies outside the original excision mask. -/
private theorem retained_of_keep (excision : Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length) (kept : ObservationLower.remainingFaceMask excision position = true) :
    AllHoleExcision.fineMask excision position = false := by
  change (!(AllHoleExcision.fineMask excision position)) = true at kept
  cases equal : AllHoleExcision.fineMask excision position with
  | false => rfl
  | true => rw [equal] at kept; cases kept

/-- A face omitted from the complement belongs to the original excision mask. -/
private theorem removed_of_not_keep (excision : Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length) (omitted : ObservationLower.remainingFaceMask excision position = false)
      :
    AllHoleExcision.fineMask excision position = true := by
  change (!(AllHoleExcision.fineMask excision position)) = false at omitted
  cases equal : AllHoleExcision.fineMask excision position with
  | false => rw [equal] at omitted; cases omitted
  | true => rfl

/-- Every non-exterior term is bounded on the computed common tail. The remaining hypothesis is the pre-grid payment for
each original band radius. -/
theorem accurate (request :
  Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest excision
  traces floor) (later : request.index ≤ stage)
    (samples : SynchronizedSurfaceRequests.PerimeterSamples requests traces cache coefficients)
    (neighbors : PuncturedFaces.NeighborBank grid.faces) {component : Fraction.Rational}
    (nonnegative : 0 ≤ component)
    (paid : ∀ index, PreparedBandFamily.areaCoefficient (curve := curve) (current := (BranchCellWinding.state original
      index).raw)
      (preparation.profiles.get index).differentials *
      (grid.bands.entries.get index).selection.sample.output.radius ^ 2 ≤ component) :
    Data.Gaussian.Norm.Basic.normSq (PerimeterSamples.remainingBoundaryCentered excision samples neighbors -
      SelectedPhysicalComponents.componentEvaluation neighbors (ObservationLower.remainingFaceMask excision)
        (PerimeterSamples.centeredSideSum samples) .exterior) ≤
      128 * ((grid.faces.regulars.length : Fraction.Rational) ^ 4 +
        (grid.faces.holes.length : Fraction.Rational) ^ 2 * (grid.faces.regulars.length : Fraction.Rational) ^ 2) *
        ((genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * component)
          := by
  let weight := (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have allowanceNonnegative : 0 ≤ 4 * (weight * component) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.mul_nonneg_direct
      weightNonnegative nonnegative)
  have sideBound (side : GridLiftedDualSteps.GridSide) (isHole : Bool) (position : Fin grid.faces.regulars.length)
      (next : RetainedBandBank.NeighborIndex (grid := grid) isHole)
      (present : RetainedBandBank.Condition excision side position isHole next) :
      Data.Gaussian.Norm.Basic.normSq (PerimeterSamples.centeredSideSum samples side position) ≤ 4 * (weight *
        component) := by
    let bank : RetainedBandBank.Request excision traces side isHole :=
      match isHole with
      | false => (request.sides side).interfaces
      | true => (request.sides side).holes
    have bankLater : bank.index ≤ stage := by
      apply Nat.le_trans (m := (request.sides side).index) _ ((request.sides_le side).trans later)
      cases isHole with
      | false => exact (request.sides side).interfaces_le
      | true => exact (request.sides side).holes_le
    have bound := bank.centered_bound bankLater samples position next present
    exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (paid (((bank.entries.get position).get next).request
        present).entry.hole.index)
        weightNonnegative) (by decide : (0 : Fraction.Rational) ≤ 4))
  have bound := SelectedBoundaryBounds.boundary_sub_exterior_bound neighbors (ObservationLower.remainingFaceMask
    excision)
    (PerimeterSamples.centeredSideSum samples) allowanceNonnegative
    (fun side first last matching kept omitted => sideBound side false first last
      ⟨matching,
        retained_of_keep
        excision first kept,
        removed_of_not_keep
        excision last omitted⟩)
    (fun hole side position matching kept => sideBound side true position hole
      ⟨matching,
        retained_of_keep
        excision position kept⟩)
  exact bound.trans_eq (by dsimp only [weight]; ring1)

end RemainingBandRequest
end SynchronizedSurfaceRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary
