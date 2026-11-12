module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.PhysicalAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.SewnPhysicalAggregate
public import Purelib.Riemann.RootContinuation.NewtonRequestedFullHoleAggregate
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOmittedHoleBank
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonRequestedInterfaceAggregate
import Purelib.Riemann.RootContinuation.NewtonSelectedInterfaceBank
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

public section

/-! Cancel the shared physical-hole polygons between the original branch
corrections and the actual sewn annuli, then pay every physical hole side. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.HoleCancellation

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
  {first second : Fin genus} {target radius : Fraction.Rational} {floor : Nat}
  {prepared : RootContinuation.NewtonRequestedBoundary.BoundaryPreparation preparation first second target radius floor}
  {sheet : Branches.BranchIsolation.Data.Index branches → Fin 2}
  {leftFixed : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank prepared.domains
    (Periods.PeriodMatrix.standardDifferential first)}
  {rightFixed : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank prepared.domains
    (Periods.PeriodMatrix.standardDifferential second)}
  {error : Fraction.Rational} {branchFloor : Nat}

/-- Explicit charge after cancelling both shared annular terms. -/
@[expose] def branchHoleCharge (target : Fraction.Rational) : Fraction.Rational :=
  2 * (target + 2 * ((82 / 4 : Fraction.Rational) * (target / 4) + 4 * target))

/-- For a nonnegative target the accumulated original branch-hole charge is at most forty-two times that target. -/
theorem branchHoleCharge_le {target : Fraction.Rational} (nonnegative : 0 ≤ target) :
    HoleCancellation.branchHoleCharge target ≤ 42 * target := by
  have factor : (82 / 4 : Fraction.Rational) ≤ 24 := (Field.div_le_iff_pos (by decide)).mpr
    ((Fraction.Cast.Order.natCast_le_direct (by decide : 82 ≤ 96)).trans_eq (by ring1))
  have product := Arithmetic.mul_le_mul_of_nonneg_right_direct factor
    (Field.div_nonneg_direct nonnegative (by decide : (0 : Fraction.Rational) ≤ 4))
  have paid : (24 : Fraction.Rational) * (target / 4) = 6 * target :=
    (show (24 : Fraction.Rational) * (target / 4) = 6 * (target / 4 * 4) by ring1).trans
      (congrArg ((6 : Fraction.Rational) * ·) (Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)))
  have small := product.trans_eq paid
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
    (le_refl target)
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct small
      (le_refl (4 * target))) (by decide)))
      (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1)

/-- No caller bound on a hole or annular area is required. The construction
retains the same branch requests and works for every later shared sample. -/
@[expose] def branchHoleRequest
    (requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
      error branchFloor prepared.excision.entries)
    (sewing : PuncturedGrid.SewnBilinearRequest.BilinearPreparation prepared.lifted.cutPolygon
      prepared.domains first second)
    (minimum : Nat) :
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains
        stage)
        (readings : PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut
          cache)
        (_cached : Branches.NewtonRequestedCutComparison.CutAnnularReadings prepared.comparison readings)
        (samples : PairedBranchAggregate.PairedBranchRequests.Samples readings.left
          readings.right readings.leftSurface readings.rightSurface requests),
        threshold ≤ stage →
        Gaussian.Norm.Basic.normSq (samples.corrections + prepared.fullHoleRemainder readings) < 42 * target}
          := by
  have positive : 0 < target := (Arithmetic.mul_pos_direct prepared.fine.positive (by
      decide : (0 : Fraction.Rational) < 4)).trans_eq
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  let branch := PhysicalAggregate.physicalCorrectionRequest sewing requests target
    positive minimum
  let annuli := AllHoles.SewnPhysicalAggregate.physicalRequest prepared.comparison sewing
    minimum
  let interfaces := prepared.interfaceBank
  let omitted := prepared.omittedBank
  let threshold := max (max branch.val annuli.val) (max prepared.index (max interfaces.index omitted.index))
  refine ⟨threshold, branch.property.1.trans ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)), ?_⟩
  intro stage cache readings cached samples later
  have comparisons := (Nat.Order.le_max_left _ _).trans later
  have geometry := (Nat.Order.le_max_right _ _).trans later
  have branchBound := branch.property.2 stage cache readings.left readings.right readings.leftSurface
    readings.rightSurface samples
    ((Nat.Order.le_max_left _ _).trans comparisons)
  have annularBound := annuli.property.2 stage cache readings.left readings.right cached.source readings.leftSurface
    readings.rightSurface
    cached.annuli ((Nat.Order.le_max_right _ _).trans comparisons)
  have holeBound := prepared.full_holes_bound interfaces omitted cached ((Nat.Order.le_max_left _ _).trans geometry)
    ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans geometry))
    ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans geometry))
  let physical := Geometry.Grid.CellBoundary.sumValues (fun entry =>
    PhysicalHoleReadback.AnnularEntry.physicalHoleArea entry readings.left readings.right)
    prepared.excision.entries
  change Gaussian.Norm.Basic.normSq (samples.corrections + physical) < target at branchBound
  change Gaussian.Norm.Basic.normSq (cached.annuli.selectedArea + physical) < (82 / 4 : Fraction.Rational) *
    (target / 4) at annularBound
  have difference := (Gaussian.Norm.Bounds.normSq_sub_le_two (cached.annuli.selectedArea + physical)
    (cached.annuli.selectedArea + prepared.fullHoleRemainder readings)).trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
        (Arithmetic.add_lt_add_direct annularBound holeBound))
  rw [show (cached.annuli.selectedArea + physical) -
    (cached.annuli.selectedArea + prepared.fullHoleRemainder readings) = physical - prepared.fullHoleRemainder readings
      by ring1] at difference
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two (samples.corrections + physical) (physical -
    prepared.fullHoleRemainder readings)).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Arithmetic.add_lt_add_direct branchBound difference))
  rw [show (samples.corrections + physical) - (physical - prepared.fullHoleRemainder readings) =
    samples.corrections + prepared.fullHoleRemainder readings by ring1] at estimate
  exact estimate.trans_le (HoleCancellation.branchHoleCharge_le positive.le)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.HoleCancellation
