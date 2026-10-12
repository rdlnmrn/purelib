module
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundaryInterfaces

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Polynomial.Geometry.Grid.WindowSize
import Purelib.Riemann.RootContinuation.NewtonRequestedOmittedHoleSides
import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceReadback
import Purelib.Riemann.RootContinuation.NewtonSelectedPhysicalHoles
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
import Purelib.Curves.Hyperelliptic.Branches.Cuts
public import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
public import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! Automatic aggregate acquisition for every selected regular interface.
Both sheets and all four directions use a fixed pre-grid count allowance. -/
section

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (outerCount)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests (FamilyFineAreaRequest)
open Purelib.Riemann.Branches.NewtonRequestedCutComparison (CutAnnularReadings)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank (InterfaceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides (physicalEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents (componentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid
  (selectedSideRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
/-- Eight sheet-side occurrences per original regular face fit within the retained squared outer-count budget. -/
theorem
  sheetSide_count
  (request : Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest preparation target radius) :
    8 * request.grid.faces.regulars.length ≤ (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount
      preparation) ^ 2 := by
  have classified := request.grid.faces.length_eq
  have cells := Polynomial.Geometry.Grid.WindowSize.cells_length_le request.grid.shrunk.prepared.grid
  rw [← request.lineCount_eq] at cells
  have regular : request.grid.faces.regulars.length ≤ request.lineCount ^ 2 :=
    (Nat.le_add_right _ _).trans (classified.le.trans cells)
  calc
    _ ≤ 8 * request.lineCount ^ 2 := Nat.mul_le_mul_left 8 regular
    _ ≤ 16 * request.lineCount ^ 2 := Nat.mul_le_mul_right _ (by decide)
    _ = (4 * request.lineCount) * (4 * request.lineCount) := by ring1
    _ ≤ request.count * request.count := Nat.mul_le_mul request.lineCount_le request.lineCount_le
    _ = (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) ^ 2 := by
      rw [request.count_eq, Data.Nat.Multiplication.pow_two]

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Four original fine-component allowances fit within the retained per-hole allowance. -/
theorem
  interface_component_le
  (allocated : Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation target radius) :
    4 * allocated.fine.component ≤ allocated.perHole := by
  have positive : 0 < allocated.perHole := by
    rw [allocated.perHole_eq]
    exact Budget.Aggregate.perTerm_positive allocated.positive _
  have small := Budget.Aggregate.perTerm_le
    (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct positive (by
        decide : (0 : Fraction.Rational) < 4)) (by decide : (0 : Fraction.Rational) < 4)).le
      (Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation)
  rw [← allocated.fine.component_eq] at small
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
      decide : (0 : Fraction.Rational) ≤ 4)
  have equal : 4 * ((allocated.perHole / 4) / 4) = allocated.perHole / 4 :=
    (show 4 * ((allocated.perHole / 4) / 4) = ((allocated.perHole / 4) / 4) * 4 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  exact (scaled.trans_eq equal).trans (Fraction.Order.Field.divide_le_self positive.le (by decide))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest

section
variable {first second : Fin genus} {floor : Nat}

namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

/-- Build the exact selected-interface bank from the retained preparation's original neighbor geometry. -/
@[expose] def interfaceBank
  (prepared : BoundaryPreparation preparation first second target radius floor) :
    InterfaceBank prepared.excision prepared.traces first second :=
  InterfaceBank.build prepared.excision prepared.traces first second
    (PuncturedFaces.NeighborBank.build prepared.fine.family.single.grid.faces
      prepared.fine.family.single.grid.shrunk.prepared.frame)

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The retained interface-bank sum has squared norm below one quarter of the original target.

The preparation and bank stages both precede the exact readings; the original occurrence count and per-hole payment
control the squared finite-sum estimate. -/
theorem interfaces_bound (prepared :
  BoundaryPreparation preparation first second target radius floor)
    (bank : InterfaceBank prepared.excision prepared.traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) (later :
      prepared.index ≤ stage)
    (interfaceLater : bank.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (bank.values
      readings.normalized)) < target / 4 := by
  have bounded (position : Fin prepared.fine.family.single.grid.faces.regulars.length) (side : GridSide) (sheet : Fin 2)
    :
      Data.Gaussian.Norm.Basic.normSq (((bank.rows.get position).sideDecision side).value readings.normalized sheet) ≤
        prepared.fine.perHole := by
    have sideLater := ((bank.rows.get position).index_le side).trans ((bank.index_ge position).trans interfaceLater)
    cases chosen : (bank.rows.get position).sideDecision side with
    | absent certificate =>
      change Data.Gaussian.Norm.Basic.normSq (0 : Basic.Canonical) ≤ _
      rw [Norm.Basic.normSq_zero, prepared.fine.perHole_eq]
      exact (Budget.Aggregate.perTerm_positive prepared.fine.positive _).le
    | present next matching selected discarded allocated =>
      rw [chosen] at sideLater
      exact (NewtonRequestedBoundaryInterfaces.interface_bound prepared allocated readings later sideLater sheet).trans
        prepared.fine.interface_component_le
  have estimate := Norm.Sum.Bounds.normSq_sum_le (bank.values readings.normalized) prepared.fine.perHole
    (bank.values_bound readings.normalized bounded)
  have count : (bank.values readings.normalized).length ≤ prepared.fine.count :=
    (bank.values_length readings.normalized).le.trans
      (prepared.fine.fine.area.sheetSide_count.trans_eq prepared.fine.count_eq.symm)
  have cap := Fraction.Cast.Order.natCast_le_direct count
  have nonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (bank.values readings.normalized).length)
  have positive : 0 < prepared.fine.perHole := by
    rw [prepared.fine.perHole_eq]
    exact Budget.Aggregate.perTerm_positive prepared.fine.positive _
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct cap
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct cap positive.le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative positive.le) (Fraction.Cast.Order.natCast_le_direct
      (Nat.zero_le prepared.fine.count))
  have paid := Budget.Aggregate.count_mul_perTerm_lt prepared.fine.positive prepared.fine.count
  rw [← prepared.fine.perHole_eq] at paid
  exact estimate.trans_lt (product.trans_lt paid)

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

section
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic

namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

/-- Read the selected physical-boundary remainder from the original cached perimeter readings. -/
@[expose] def
  selectedPhysicalRemainder
  (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) : Gaussian
      :=
  Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.physicalEvaluation readings.neighbors (fineMask
    prepared.excision)
    (fun side p => FiniteSum.Fin.sumFin (fun sheet => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder
      readings.normalized p sheet side))

/-- Sum the original selected physical-hole remainder components from the retained readings. -/
@[expose] def selectedHoleRemainder
  (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) : Gaussian
      :=
  FiniteSum.Fin.sumFin (fun hole =>
    Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation readings.neighbors (fineMask prepared.excision)
      (fun side p => FiniteSum.Fin.sumFin (fun sheet =>
        Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder readings.normalized p sheet side)) (.hole hole))

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

end

namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.RootContinuation in
/-- The retained selected physical remainder equals its exact original physical-hole sum. -/
theorem
  selectedPhysicalRemainder_eq_holes
  (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) :
    prepared.selectedPhysicalRemainder readings = prepared.selectedHoleRemainder readings :=
  NewtonSelectedPhysicalHoles.physicalEvaluation_eq_holes prepared.excision readings.neighbors _

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Removing the retained interface sum leaves selected area plus physical remainder below the original target.

The exact cached annular comparison and both retained stage bounds identify the same readings, while their separate
quarter-target payments control the subtraction estimate. -/
theorem interfaces_removed_bound
  (prepared : BoundaryPreparation preparation first second target radius floor)
    (bank : InterfaceBank prepared.excision prepared.traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    {readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache}
    (cached : CutAnnularReadings prepared.comparison readings)
    (later : prepared.index ≤ stage) (interfaceLater : bank.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea + prepared.selectedPhysicalRemainder readings) < target
      := by
  have selected := (cached.selected_boundary_bound ((Data.Nat.Order.le_max_left _ _).trans later)).trans
    prepared.paid.cutTarget_le
  have interfaces := prepared.interfaces_bound bank readings later interfaceLater
  have equal : cached.annuli.selectedArea + prepared.selectedPhysicalRemainder readings =
      (cached.annuli.selectedArea +
        Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder readings.normalized
        readings.neighbors (fineMask prepared.excision)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (bank.values readings.normalized) := by
    have readback : Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder
      readings.normalized readings.neighbors (fineMask prepared.excision) =
        prepared.selectedPhysicalRemainder readings + Data.Gaussian.Norm.Sum.Basic.gaussianSum (bank.values
          readings.normalized)
          :=
      NewtonSelectedInterfaceReadback.InterfaceBank.selected_boundary_eq bank (cache := cache) readings.neighbors
        readings.normalized
    rw [readback]
    ring1
  rw [equal]
  have added := (Fraction.Order.Arithmetic.add_lt_add_left_direct interfaces
    (Data.Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea +
      Meshes.PuncturedGrid.SelectedSideRemainders.LiftedPuncturedGrid.selectedSideRemainder readings.normalized
      readings.neighbors (fineMask prepared.excision)))).trans_le
    (Fraction.Order.Arithmetic.add_le_add_direct selected (le_refl (target / 4)))
  exact ((Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) added)).trans_eq
    ((show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Acquire the original interface bank and perimeter cache at their shared maximum stage with paid readbacks.

The returned dependent package retains the exact bank, cache and readings together with both the quarter-target
interface bound and the target-bound physical remainder. -/
@[expose] def acquireInterfaces
  (prepared : BoundaryPreparation preparation first second target radius floor) :=
  let bank := prepared.interfaceBank
  let stage := max prepared.index bank.index
  let cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage :=
    Vector.DependentVector.ofFn fun row =>
    Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build (standardDifferential row) stage prepared.domains
  let readings := prepared.readAt cache (Data.Nat.Order.le_max_left _ _)
  (⟨bank, cache, readings, prepared.interfaces_bound bank readings.1 (Data.Nat.Order.le_max_left _ _)
    (Data.Nat.Order.le_max_right _ _),
    prepared.interfaces_removed_bound bank readings.2.val (Data.Nat.Order.le_max_left _ _) (Data.Nat.Order.le_max_right
      _ _)⟩ :
    (bank : InterfaceBank prepared.excision prepared.traces first second) ×
      (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains (max prepared.index
        bank.index)) ×
        {readings : prepared.Readings cache // Data.Gaussian.Norm.Basic.normSq
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum (bank.values
          readings.1.normalized)) < target / 4 ∧
          Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.selectedArea + prepared.selectedPhysicalRemainder
            readings.1) < target})

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The retained selected area plus physical-hole remainder has squared norm below the original target.

The exact physical-component identity transports the paid interface-removal estimate under the same cached annular
comparison and original stage bounds. -/
theorem holes_bound (prepared :
  BoundaryPreparation preparation first second target radius floor)
    (bank : InterfaceBank prepared.excision prepared.traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    {readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache}
    (cached : CutAnnularReadings prepared.comparison readings)
    (later : prepared.index ≤ stage) (interfaceLater : bank.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea + prepared.selectedHoleRemainder readings) < target :=
      by
  have bounded := prepared.interfaces_removed_bound bank cached later interfaceLater
  rw [prepared.selectedPhysicalRemainder_eq_holes] at bounded
  exact bounded

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

end
end
