module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Periods

@[expose] public section

/-! Consume centered hole traces in the actual requested cut pairing. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CenteredHoleCutPairing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest (Readings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (HoleCenteringRequest CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {i j : Fin genus} {target error : Rational} {floor stage : Nat}
  {request : CutPairingRequest lifted domains i j
    target floor} {cache : Numerics
    domains stage}

/-- Replacing a physical correction by a close centered correction combines the original paired bound and the centering
error. -/
private theorem replace_physical {paired physical centered : Data.Gaussian.Basic.Canonical} {firstError secondError :
  Fraction.Rational}
    (pairBound : Data.Gaussian.Norm.Basic.normSq (paired + physical) ≤ firstError)
    (physicalBound : Data.Gaussian.Norm.Basic.normSq (physical - centered) < secondError) :
    Data.Gaussian.Norm.Basic.normSq (paired + centered) < 2 * (firstError + secondError) := by
  have equal : paired + centered = (paired + physical) - (physical - centered) := by ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_le_add_direct pairBound (le_refl _)).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct physicalBound firstError)))

/-- The finite exterior remains explicit alongside the full centered hole areas; only their endpoint mismatch has been
removed. -/
theorem Readings.centered_holes_bound (readings : CutPairingRequest.Readings request cache)
    (allocated : RequestedHoleCentering.HoleCenteringRequest lifted request.fixed i j error)
    (samples : RequestedHoleCentering.CenteredPerimeters request.exterior.prepared.energy cache i j)
    (cutLater : request.index ≤ stage) (endpointsLater : allocated.endpoints.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.paired +
      (PhysicalComponentCorrection.physicalComponentCorrection readings.normalized readings.neighbors readings.left
        readings.right .exterior +
        allocated.centeredTotal samples)) < 2 * (target + error) :=
  replace_physical (readings.corrected_bound cutLater)
    (allocated.physical_accurate samples endpointsLater readings.normalized readings.neighbors readings.left
      readings.right)

/-- Retain the chosen endpoint request and the common numerical bank, so subsequent Newton comparisons consume these
same roots, traces, and values. -/
def CenteredHoleAcquisition (request : RequestedCutPairing.CutPairingRequest lifted domains i j target floor) (error :
  Fraction.Rational) :=
  (allocated : RequestedHoleCentering.HoleCenteringRequest lifted request.fixed i j error) ×
  (cache : RegularMeshes.Numerics domains (max request.index allocated.endpoints.index)) ×
  (readings : CutPairingRequest.Readings request cache) ×
  (samples : RequestedHoleCentering.CenteredPerimeters request.exterior.prepared.energy cache i j) ×
  { centered : Data.Gaussian.Basic.Canonical // centered = allocated.centeredTotal samples ∧
    Data.Gaussian.Norm.Basic.normSq (readings.paired +
      (PhysicalComponentCorrection.physicalComponentCorrection readings.normalized readings.neighbors readings.left
        readings.right .exterior + centered)) <
      2 * (target + error) }

/-- Acquire the original cut readings and centered hole traces once at a shared paid stage.

The result retains the allocated endpoint request, the common numerical cache and the exact centered total together with
its corrected cut-pairing bound. -/
def acquireCenteredHoles (request : RequestedCutPairing.CutPairingRequest lifted domains i j target floor)
    (error : Fraction.Rational) (positive : 0 < error) :
      CenteredHoleAcquisition request error :=
  let allocated := HoleCenteringRequest.build lifted request.fixed i j error positive
  let index := max request.index allocated.endpoints.index
  let cache := DependentVector.ofFn fun row =>
    FacePrimitiveBank.build (PeriodMatrix.standardDifferential row) index domains
  let readings := Readings.build request cache
  let samples := CenteredPerimeters.build request.exterior.prepared.energy cache i j
  ⟨allocated, cache, readings, samples, allocated.centeredTotal samples, rfl,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.CenteredHoleCutPairing.Readings.centered_holes_bound readings allocated
      samples (Data.Nat.Order.le_max_left _ _) (Data.Nat.Order.le_max_right _ _)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CenteredHoleCutPairing
