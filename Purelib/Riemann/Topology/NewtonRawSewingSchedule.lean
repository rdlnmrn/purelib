module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
public import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
public import Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

public section

/-! One cached sewing preparation supplies both the selected-surface comparison
and all annular comparisons on the raw-energy grid. -/
namespace Purelib.Riemann.Topology.NewtonRawSewingSchedule

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance rawEnergyAllowance_positive)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (ConjugateRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_positive)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest (EnergyPreparation)
open Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {observations : ProtectedObservations original} {preparation : NewtonPreparation original} {radius :
    Data.Rat.Fraction.Rational}
  (gridData : RawEnergyGrid observations preparation radius)

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Synchronized sewing and annular requests on a raw-energy grid.

Retains the actual energy preparation and its two requests, with a common numerical index equal to their maximum. -/
structure SewingSchedule (floor : Nat) where
  /-- Energy preparation for the retained cut polygon and face domains. -/ prepared :
    Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation gridData.lifted.cutPolygon gridData.domains
  /-- Sewing request at the raw-energy allowance target and floor. -/ sewing :
    Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request prepared
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations))
      floor
  /-- Homogeneous annular request for the retained outer preparations. -/ annular : HomogeneousAnnularRequest.Request
    (domains := gridData.domains) gridData.outer floor
  /-- Common numerical index for both requests. -/ index : Nat
  /-- The common index is exactly the maximum of the two request indices. -/ index_eq : index = max sewing.index
    annular.index
  /-- The common index follows the sewing request. -/ sewing_le : sewing.index ≤ index
  /-- The common index follows the annular request. -/ annular_le : annular.index ≤ index

constructive_injectivity SewingSchedule

namespace SewingSchedule

open Purelib.Curves.Hyperelliptic in
/-- Prepare sewing and annular comparisons at a retained stage floor.

Uses the raw-energy allowance for the sewing target and constructs the annular request from the same preparation and
outer data. -/
@[expose] def build (floor : Nat) : SewingSchedule gridData floor :=
  let prepared := Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.build gridData.lifted.cutPolygon
    gridData.domains
  let sewing := Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request.build prepared
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations))
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive (rawEnergyAllowance_positive
      observations)) floor
  let annular := HomogeneousAnnularRequest.Request.build gridData.outer prepared floor
  ⟨prepared, sewing, annular, max sewing.index annular.index, rfl, Data.Nat.Order.le_max_left _ _,
    Data.Nat.Order.le_max_right _ _⟩

end SewingSchedule
end Purelib.Riemann.Topology.NewtonRawSewingSchedule
