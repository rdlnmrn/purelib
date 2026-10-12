module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Topology.NewtonRawSewingSchedule
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Synchronize odd canonical exterior requests with the retained raw sewing preparation. -/
namespace Purelib.Riemann.RootContinuation.NewtonRawOddExteriorSchedule

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance rawEnergyAllowance_positive)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Curves.Hyperelliptic.Meshes.Newton (OddCanonicalExteriorRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Purelib.Data.Rat.Fraction.Rational}
  (gridData : RawEnergyGrid observations preparation radius)

variable {sewingFloor : Nat} (sewingData : SewingSchedule gridData sewingFloor)

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Odd exterior joining request synchronized with the sewing schedule.

Retains the actual joining request on the raw-energy grid and a common index equal to the maximum of sewing and joining
indices. -/
structure OddExteriorSchedule (floor : Nat) where
  /-- Actual odd canonical exterior request for the retained grid and sewing magnitudes. -/ joining :
    Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest (grid :=
    gridData.allocated.family.single.grid) (current := gridData.lifted) sewingData.prepared.magnitudes
    (rawEnergyAllowance observations) floor
  /-- Common sewing and joining numerical index. -/ index : Nat
  /-- The common index is exactly the maximum of sewing and joining indices. -/ index_eq : index = max sewingData.index
    joining.index

constructive_injectivity OddExteriorSchedule

namespace OddExteriorSchedule

open Purelib.Curves.Hyperelliptic in
/-- Construct the odd exterior joining request at the raw-energy allowance.

Uses the retained sewing magnitudes, allocated grid and lift, then keeps the exact maximum numerical index. -/
@[expose] def build (floor : Nat) : OddExteriorSchedule gridData sewingData floor :=
  let joining := Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest.build
    (grid := gridData.allocated.family.single.grid) (current := gridData.lifted) sewingData.prepared.magnitudes
    (rawEnergyAllowance observations) (rawEnergyAllowance_positive observations) floor
  ⟨joining, max sewingData.index joining.index, rfl⟩

variable {floor : Nat} (schedule : OddExteriorSchedule gridData sewingData floor)

/-- The retained sewing index lies below the exterior schedule index. -/
theorem sewing_le : sewingData.index ≤ schedule.index := by
  rw [schedule.index_eq]
  exact Nat.Order.le_max_left _ _

/-- The actual joining request index lies below the common index. -/
theorem joining_le : schedule.joining.index ≤ schedule.index := by
  rw [schedule.index_eq]
  exact Nat.Order.le_max_right _ _

open Purelib.Curves.Hyperelliptic in
/-- The odd exterior schedule respects its requested stage floor. -/
theorem floor_le : floor ≤ schedule.index :=
  (Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest.floor_le
    schedule.joining).trans (schedule.joining_le gridData sewingData)

end OddExteriorSchedule
end Purelib.Riemann.RootContinuation.NewtonRawOddExteriorSchedule
