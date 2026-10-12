module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule
public import Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.Topology.NewtonRawSurfaceSchedule
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
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PartitionBankCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisSourceCuts
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Shared surface traces supply the contact and remaining-band requests on
one later threshold, without rebuilding the retained surface or sewing banks. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawBoundarySchedule

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSurfaceSchedule (SurfaceSchedule)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule (RawJoiningSchedule)
open Purelib.Riemann.RootContinuation.NewtonGlobalContactRequest.SynchronizedSurfaceRequests (GlobalContactRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests
  (RemainingBandRequest)
open Purelib.Riemann.Topology.NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests (PerimeterTraces)
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

variable {joiningFloor : Nat}
  (joiningData : RawJoiningSchedule (paired := paired) surfaceData sewingData joiningFloor)

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Retained contact and remaining-band requests for a raw surface boundary.

Keeps the original perimeter traces, both contact orientations and remaining-band bank, synchronized with the existing
joining schedule. -/
structure RawBoundarySchedule (floor : Nat) where
  /-- Actual perimeter traces of the retained physical surface request. -/ traces : PerimeterTraces
    surfaceData.schedule.surface
  /-- Global contact request on those traces and original compatible lifted grid. -/ contacts : GlobalContactRequest
    surfaceData.schedule.surface gridData.compatible gridData.lifted.mesh traces
    (rawEnergyAllowance observations) floor
  /-- Remaining-band request retaining the original excision and same traces. -/ remaining :
    Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest gridData.excision traces
    floor
  /-- Common numerical index for joining, contacts and remaining bands. -/ index : Nat
  /-- Exact nested maximum of the three retained indices. -/ index_eq : index = max joiningData.index (max
    contacts.index remaining.index)
  /-- The joining schedule index lies below the common index. -/ joining_le : joiningData.index ≤ index
  /-- The global contact index lies below the common index. -/ contacts_le : contacts.index ≤ index
  /-- The remaining-band index lies below the common index. -/ remaining_le : remaining.index ≤ index

constructive_injectivity RawBoundarySchedule

namespace RawBoundarySchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.RootContinuation in
open Purelib.Riemann.Topology in
/-- Build raw boundary requests from the retained perimeter traces.

Constructs the traces once, reuses them for contact and remaining-band requests, and keeps the exact maximum with the
joining index. -/
@[expose] def build (floor : Nat) : RawBoundarySchedule surfaceData sewingData joiningData floor :=
  let traces := NewtonGlobalSurfaceBoundary.SynchronizedSurfaceRequests.PerimeterTraces.build
    surfaceData.schedule.surface
  let contacts := NewtonGlobalContactRequest.SynchronizedSurfaceRequests.GlobalContactRequest.build
    surfaceData.schedule.surface gridData.compatible gridData.lifted.mesh traces
    (rawEnergyAllowance observations) (rawEnergyAllowance_positive observations) floor
  let remaining := Meshes.Newton.Complement.BandBoundary.SynchronizedSurfaceRequests.RemainingBandRequest.build
    gridData.excision traces floor
  ⟨traces, contacts, remaining, max joiningData.index (max contacts.index remaining.index), rfl,
    Data.Nat.Order.le_max_left _ _, (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _),
    (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)⟩

end RawBoundarySchedule
end Purelib.Riemann.RootContinuation.NewtonRawBoundarySchedule
