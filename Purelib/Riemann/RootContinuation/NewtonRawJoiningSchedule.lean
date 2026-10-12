module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Riemann.Topology.NewtonRawSurfaceSchedule
public import Purelib.Riemann.Topology.NewtonRawSewingSchedule
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningFamily
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonPhysicalSurfaceSchedule
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Branches.NewtonSharedExteriorCuts
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Acquire every regular joining pair from the actual shared preparations and
sewing magnitude bank, retaining one later numerical threshold. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSurfaceSchedule (SurfaceSchedule)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningFamily (RegularJoiningFamily
  CanonicalJoiningPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_positive)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance rawEnergyAllowance_positive)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin
    2}
  {ordered : Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Data.Rat.Fraction.Rational}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {gridData : RawEnergyGrid observations preparation radius}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {physicalMinimum physicalFloor
    sewingFloor : Nat}
  (surfaceData : SurfaceSchedule gridData regular physicalMinimum physicalFloor)
  (sewingData : SewingSchedule gridData sewingFloor)

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Regular joining family synchronized with surface and sewing schedules.

Retains the actual basis preparations and sewing magnitudes at the raw-energy target, with one common index for all
three request families. -/
structure RawJoiningSchedule (floor : Nat) where
  /-- Actual regular joining family over the retained preparations and magnitudes. -/ joining :
    Meshes.Newton.Regular.JoiningFamily.RegularJoiningFamily (paired := paired) surfaceData.schedule.basis.preparations
    sewingData.prepared.magnitudes
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations))
      floor
  /-- Common surface, sewing and joining numerical index. -/ index : Nat
  /-- Exact nested maximum of the three retained indices. -/ index_eq : index = max surfaceData.index (max
    sewingData.index joining.index)
  /-- The surface schedule index lies below the common index. -/ surface_le : surfaceData.index ≤ index
  /-- The sewing schedule index lies below the common index. -/ sewing_le : sewingData.index ≤ index
  /-- The actual joining-family index lies below the common index. -/ joining_le : joining.index ≤ index

constructive_injectivity RawJoiningSchedule

namespace RawJoiningSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- The retained surface basis preparations are the canonical joining preparations.

Composes the two stored preparation-bank equalities and reads each actual dependent-vector entry. -/
theorem canonical : Meshes.Newton.Regular.JoiningFamily.CanonicalJoiningPreparations
  surfaceData.schedule.basis.preparations := by
  intro first
  have banks := surfaceData.schedule.preparations_eq.trans surfaceData.preparations_eq
  have entry := congrArg (fun entries : Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular
    gridData.domains => entries.get first) banks
  exact entry.trans (Vector.DependentVector.ofFn_get _ first)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in

open Purelib.Curves.Hyperelliptic in
/-- Construct the regular joining family and synchronized index.

Uses the retained canonical preparation witness and sewing magnitudes, then takes the maximum with the original surface
and sewing indices. -/
@[expose] def build (floor : Nat) : RawJoiningSchedule (paired := paired) surfaceData sewingData floor :=
  let joining := Meshes.Newton.Regular.JoiningFamily.RegularJoiningFamily.build surfaceData.schedule.basis.preparations
    (canonical surfaceData)
    sewingData.prepared.magnitudes (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus
      (rawEnergyAllowance observations))
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive (rawEnergyAllowance_positive
      observations)) floor
  ⟨joining, max surfaceData.index (max sewingData.index joining.index), rfl, Data.Nat.Order.le_max_left _ _,
    (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _), (Data.Nat.Order.le_max_right _ _).trans
      (Data.Nat.Order.le_max_right _ _)⟩

end RawJoiningSchedule
end Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule
