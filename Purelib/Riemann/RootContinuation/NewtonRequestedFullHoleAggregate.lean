module
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Riemann.RootContinuation.NewtonRequestedInterfaceAggregate
import Purelib.Riemann.RootContinuation.NewtonOmittedHoleReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineTransport
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCutBoundary
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! A single requested bank pays the full hole-side correction after annular
excision, including the sides omitted when a hole touches its band boundary. -/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Riemann.Branches.NewtonRequestedCutComparison (CutAnnularReadings)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank (InterfaceBank)
open Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank (OmittedHoleBank)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSelectionPartition (fullHoleEvaluation
  fullHoleEvaluation_partition)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}

variable {first second : Fin genus} {floor : Nat}

/-- Build the omitted-hole bank from the retained preparation's original face-neighbor geometry. -/
@[expose] def omittedBank (prepared
  : BoundaryPreparation preparation first second target radius floor) :
    OmittedHoleBank prepared.excision prepared.traces first second :=
  OmittedHoleBank.build prepared.excision prepared.traces first second
    (PuncturedFaces.NeighborBank.build prepared.fine.family.single.grid.faces
      prepared.fine.family.single.grid.shrunk.prepared.frame)

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The retained omitted-hole sum has squared norm below one quarter of the original target.

The original preparation and omitted-request stages precede the same readings; exact signed-occurrence counts and
retained per-hole payment control their finite sum. -/
theorem omitted_bound (prepared :
  BoundaryPreparation preparation first second target radius floor)
    (bank : OmittedHoleBank prepared.excision prepared.traces first second)
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
    | present hole matching discarded allocated =>
      rw [chosen] at sideLater
      exact (NewtonRequestedBoundaryInterfaces.interface_bound prepared allocated readings later sideLater sheet).trans
        (Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest.interface_component_le prepared.fine)
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

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
/-- Read the full physical-hole evaluation on both sheets from the original perimeter cache. -/
@[expose] def fullHoleRemainder
  (prepared : BoundaryPreparation preparation first second target radius floor)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) : Gaussian
      :=
  Meshes.PuncturedGrid.HoleSelectionPartition.fullHoleEvaluation readings.neighbors
    (fun side p => FiniteSum.Fin.sumFin (fun sheet => Meshes.PuncturedGrid.HoleAreaRemainder.sideAreaRemainder
      readings.normalized p sheet side))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The original full hole remainder splits into the selected-hole remainder and exact omitted-bank sum.

The original face mask and neighbor bank determine both terms, preserving the signed side occurrences in the retained
omitted rows. -/
theorem fullHoleRemainder_eq
  (prepared : BoundaryPreparation preparation first second target radius floor)
    (omitted : OmittedHoleBank prepared.excision prepared.traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache) :
    prepared.fullHoleRemainder readings = prepared.selectedHoleRemainder readings +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (omitted.values readings.normalized) := by
  have readback := NewtonOmittedHoleReadback.OmittedHoleBank.sum_eq_omitted omitted (cache := cache) readings.neighbors
    readings.normalized
  rw [readback]
  exact Meshes.PuncturedGrid.HoleSelectionPartition.fullHoleEvaluation_partition readings.neighbors (fineMask
    prepared.excision) _

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The selected annular area plus full physical-hole remainder is bounded by four times the original target.

The exact interface and omitted-hole banks retain separate paid estimates at the supplied cache stage, and their
original readback identity combines those estimates. -/
theorem full_holes_bound (prepared :
  BoundaryPreparation preparation first second target radius floor)
    (interfaces : InterfaceBank prepared.excision prepared.traces first second)
    (omitted : OmittedHoleBank prepared.excision prepared.traces first second)
    {stage : Nat} {cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage}
    {readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut cache}
    (cached : CutAnnularReadings prepared.comparison readings)
    (later : prepared.index ≤ stage) (interfaceLater : interfaces.index ≤ stage) (omittedLater : omitted.index ≤ stage)
      :
    Data.Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea + prepared.fullHoleRemainder readings) < 4 * target :=
      by
  have selected := prepared.holes_bound interfaces cached later interfaceLater
  have omittedBound := prepared.omitted_bound omitted readings later omittedLater
  have positive : 0 < target := (Fraction.Order.Arithmetic.mul_pos_direct prepared.fine.positive (by
      decide : (0 : Fraction.Rational) < 4)).trans_eq
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have quarter : target / 4 ≤ target := by
    apply (Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
    exact (show target = target * 1 by ring1).le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Fraction.Rational) ≤ 4)
        positive.le)
  have total := Fraction.Order.Arithmetic.add_lt_add_direct selected (omittedBound.trans_le quarter)
  have equal : cached.annuli.selectedArea + prepared.fullHoleRemainder readings =
      (cached.annuli.selectedArea + prepared.selectedHoleRemainder readings) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (omitted.values readings.normalized) := by
    rw [prepared.fullHoleRemainder_eq omitted readings]
    ring1
  rw [equal]
  exact ((Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) total)).trans_eq
      (by ring1)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Acquire both original interface banks and a shared perimeter cache with a paid full-hole readback.

The returned dependent package retains the selected-interface and omitted-hole owners, their common maximum stage, exact
cached readings and the four-target squared-norm certificate. -/
@[expose] def acquireFullHoles
  (prepared : BoundaryPreparation preparation first second target radius floor) :=
  let interfaces := prepared.interfaceBank
  let omitted := prepared.omittedBank
  let stage := max (max prepared.index interfaces.index) omitted.index
  let cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains stage :=
    Vector.DependentVector.ofFn fun row =>
    Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build (standardDifferential row) stage prepared.domains
  let later := (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  let readings := prepared.readAt cache later
  (⟨interfaces, omitted, cache, readings,
    prepared.full_holes_bound interfaces omitted readings.2.val later
      ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)) (Data.Nat.Order.le_max_right _ _)⟩ :
    (interfaces : InterfaceBank prepared.excision prepared.traces first second) ×
    (omitted : OmittedHoleBank prepared.excision prepared.traces first second) ×
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains (max (max prepared.index
      interfaces.index) omitted.index)) ×
    {readings : prepared.Readings cache // Data.Gaussian.Norm.Basic.normSq (readings.2.val.annuli.selectedArea +
      prepared.fullHoleRemainder readings.1) < 4 * target})

end Purelib.Riemann.RootContinuation.NewtonRequestedBoundary.BoundaryPreparation
