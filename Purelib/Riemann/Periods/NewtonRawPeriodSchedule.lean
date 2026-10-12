module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Riemann.Topology.NewtonRawSewingSchedule
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid

public section

/-! Acquire the actual corrected-period and cut comparisons from the retained
raw-energy excision and sewing magnitude bank. -/
namespace Purelib.Riemann.Periods.NewtonRawPeriodSchedule

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid (RawEnergyGrid)
open Purelib.Riemann.Topology.NewtonRawSewingSchedule (SewingSchedule)
open Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget (rawEnergyAllowance rawEnergyAllowance_positive)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_positive)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison (Request)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request (CutRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {radius : Purelib.Data.Rat.Fraction.Rational}
  {observations : ProtectedObservations base.bank.toBranchCellBank}
  {gridData : RawEnergyGrid observations preparation radius}
  (prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) {sewingFloor :
    Nat}
  (sewingData : SewingSchedule gridData sewingFloor)

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- Physical period and cut requests on a retained sewing schedule.

Keeps the selected sheet, original excision and sewing magnitudes, with separate numerical floors and quarter
energy-allowance targets. -/
structure RawPeriodSchedule (newSheet : Fin 2) (floor minimum : Nat) where
  /-- Physical comparison for the selected sheet and original excision. -/ request :
    Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet gridData.excision
    sewingData.prepared.magnitudes
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations) /
      4) floor
  /-- Cut comparison retaining that physical request and its quarter allowance. -/ cut :
    Meshes.Newton.HomogeneousCutRequest.Request.CutRequest request
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations) /
      4) minimum

constructive_injectivity RawPeriodSchedule

namespace RawPeriodSchedule

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct the physical and cut requests at positive quarter allowance.

The cut request retains the physical request just constructed and the same sewing preparation, preserving both requested
stage floors. -/
@[expose] def build (newSheet : Fin 2) (floor minimum : Nat) : RawPeriodSchedule prepared sewingData newSheet floor
  minimum :=
  let positive := Fraction.Order.Field.div_pos_direct
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive (rawEnergyAllowance_positive
      observations)) (by decide : (0 : Fraction.Rational) < 4)
  let request := Meshes.Newton.HomogeneousPhysicalComparison.Request.build prepared newSheet gridData.excision
    sewingData.prepared.magnitudes
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations) /
      4) positive floor
  let cut := Meshes.Newton.HomogeneousCutRequest.Request.CutRequest.build request sewingData.prepared
    (Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus (rawEnergyAllowance observations) /
      4) positive minimum
  ⟨request, cut⟩

end RawPeriodSchedule
end Purelib.Riemann.Periods.NewtonRawPeriodSchedule
