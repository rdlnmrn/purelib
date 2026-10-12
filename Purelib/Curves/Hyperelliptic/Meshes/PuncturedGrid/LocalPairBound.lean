module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedFaceAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound
import Purelib.Riemann.Readings.RectangularBoundaryTranslations
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearRequest

public section

/-! The retained local perimeters inherit the actual two-row analytic bound. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann
open Purelib.RootIsolation

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Normalization.RectangularInverseModels

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)

namespace LocalPairBound

/-- The original finite Gaussian coordinate vector selecting one row. -/
private def rowVector {count : Nat} (selected : Fin count) : LinearAlgebra.Gaussian.Energy.GaussianVector count
  :=
  Data.Vector.Basic.vectorOfFn fun index => if index = selected then 1 else 0

/-- Pairing with the retained coordinate vector returns the selected row value. -/
private theorem row_sum {count : Nat} (selected : Fin count) (values : Fin count → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector selected index *
      values index) = values selected := by
  have equal (index : Fin count) : Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector selected index * values
    index =
      (if index = selected then values index else 0) := by
    simp only [Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector, Data.Vector.Basic.vectorOfFn_apply,
      -eq_self, -iff_self]
    split <;> simp only [one_mul, zero_mul, -eq_self, -iff_self] <;> rfl
  rw [FiniteSum.Fin.sumFin_congr equal]
  exact FiniteSum.Fin.sumFin_ite_eq selected values

/-- The retained coordinate vector has squared coefficient norm one. -/
private theorem row_norm {count : Nat} (selected : Fin count) :
    Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq
      (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector selected) = 1 := by
  change FiniteSum.Fin.sumFin (fun index => Gaussian.Basic.Canonical.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector selected index)) = 1
  have equal (index : Fin count) : Gaussian.Basic.Canonical.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector selected index) =
      (if index = selected then (1 : Fraction.Rational) else 0) := by
    simp only [Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector, Data.Vector.Basic.vectorOfFn_apply,
      -eq_self, -iff_self]
    split <;> rfl
  rw [FiniteSum.Fin.sumFin_congr equal, FiniteSum.Fin.sumFin_ite_eq selected (fun _ => (1 : Fraction.Rational))]

end LocalPairBound

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {cuts :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage} {i
    j : Fin genus}

namespace LocalPairBound

/-- The original local face perimeter equals the two-coordinate local boundary reading.

The equality preserves all clipped pieces and uses the retained primitive offset as a facewise translation. -/
private theorem local_readback
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (perimeters : Matched.FacePerimeters (request := request.energy)
      cache i j)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :
    ((perimeters.assemblies.get position).get sheet).localTotal =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.localBoundary
        (energy := request.energy) cache (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
          (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j) sheet position := by
  rw [((perimeters.assemblies.get position).get sheet).localTotal_eq]
  unfold Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.localBoundary
  apply Meshes.RectangularObservationMesh.ObservationPieces.localBoundary_eq_of_translation
    ((request.energy.entries.get sheet).meshes.entries.get position).pieces
    (fun column row point =>
      ⟨sumFin (fun k => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i k * (cache.atDomain position sheet
        k).primitives.value column row point),
        FiniteSum.Fin.sumFin (fun k => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j k * (cache.atDomain
          position sheet k).primitives.value column row point)⟩)
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache i j position sheet)
    (fun column row => ⟨(cache.atDomain position sheet i).offsets.values column row,
      (cache.atDomain position sheet j).offsets.values column row⟩)
  intro column row point
  simp only [Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.row_sum, -eq_self, -iff_self]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues
  change (⟨_ + _, _ + _⟩ : Topology.Polygon.Stokes.PrimitivePoint) = ⟨_ + _, _ + _⟩
  exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk (add_comm _ _) (add_comm _ _)

end LocalPairBound

namespace Matched.FacePerimeters

/-- Sum all retained local face totals over their original face positions and both sheets. -/
@[expose] def
  localTotalSum
    (perimeters : FacePerimeters (request := request) cache i
      j) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet => ((perimeters.assemblies.get position).get
    sheet).localTotal))

end Matched.FacePerimeters

namespace LocalPairBound.FacePerimeters

/-- The original local-boundary request pays the squared norm of the complete retained two-row local-total sum. -/
theorem local_bound
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (perimeters : Matched.FacePerimeters (request := request.energy)
      cache i j)
    (later : request.ownership.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq perimeters.localTotalSum ≤ target :=
      by
  have estimate := request.bound later (request.energy.samples cache)
    (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
    (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j)
  rw [Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.row_norm,
    Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.row_norm, one_mul, one_mul] at estimate
  have equal := FiniteSum.Fin.sumFin_congr (fun position : Fin faces.regulars.length =>
    FiniteSum.Fin.sumFin_congr (fun sheet : Fin 2 => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.local_readback
      request perimeters position sheet))
  unfold Matched.FacePerimeters.localTotalSum
  rw [equal, FiniteSum.Fin.sumFin_swap]
  exact estimate

end LocalPairBound.FacePerimeters

namespace LocalPairBound

/-- Retain a Gaussian value when the Boolean selection holds and return zero otherwise. -/
private def selectedValue (keep : Bool) (value : Gaussian.Basic.Canonical) : Gaussian := if keep then value else 0

/-- Read the selected Gaussian value, contributing zero for a discarded occurrence. -/
@[expose] def selectedValue_for_sum (keep : Bool) (value : Gaussian.Basic.Canonical) : Gaussian := if keep then value
  else 0

/-- Boolean restriction preserves a nonnegative squared-norm bound. -/
private theorem selectedValue_bound (keep : Bool) {value : Gaussian.Basic.Canonical} {bound : Fraction.Rational}
    (nonnegative : 0 ≤ bound) (bounded : Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
      Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue keep value) ≤
      bound := by
  cases keep with
  | false =>
      change Data.Gaussian.Norm.Basic.normSq 0 ≤ bound
      rewrite [Gaussian.Norm.Basic.normSq_zero]
      exact nonnegative
  | true => exact bounded

/-- A selected occurrence retains its nonnegative squared-norm bound. -/
theorem selectedValue_bound_for_sum (keep : Bool) {value : Gaussian.Basic.Canonical} {bound : Fraction.Rational}
    (nonnegative : 0 ≤ bound) (bounded : Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
      Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum keep
      value) ≤ bound := by
  cases keep with
  | false =>
      change Data.Gaussian.Norm.Basic.normSq 0 ≤ bound
      rewrite [Gaussian.Norm.Basic.normSq_zero]
      exact nonnegative
  | true => exact bounded

end LocalPairBound

namespace Matched.FacePerimeters

/-- Restrict the original face occurrences, retaining both sheets and all
local clipped pieces. Selection does not prepare another numerical bank. -/
@[expose] def
  selectedLocalSum
    (perimeters : FacePerimeters (request := request) cache i
      j) (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) ((perimeters.assemblies.get
      position).get sheet).localTotal))

end Matched.FacePerimeters

namespace LocalPairBound

/-- The retained two-coordinate clipped combination error is exactly the original pair error. -/
private theorem basis_combinedError {energyTarget : Fraction.Rational}
    {energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      energyTarget}
    (samples : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples energy cache) (sheet :
      Fin 2) (position : Fin faces.regulars.length) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination.combinedError samples
      (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
      (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j) sheet position =
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest.pairError samples i j sheet position := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularClippedCombination.combinedError_eq]
  have inner (first : Fin genus) :
      FiniteSum.Fin.sumFin (fun second => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i first *
        Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j second *
        Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest.pairError samples first second sheet
        position) =
        Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i first *
          Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest.pairError samples first j sheet
          position := by
    rw [FiniteSum.Fin.sumFin_congr (fun second => mul_assoc _ _ _), FiniteSum.Fin.sumFin_mul_left,
      Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.row_sum]
  rw [FiniteSum.Fin.sumFin_congr inner, Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.row_sum]

end LocalPairBound

namespace LocalPairBound.FacePerimeters

/-- The existing per-face and per-sheet budgets pay every selected subset.
In particular, no cancellation between selected and discarded local areas
is used to infer that the selected area is small. -/
theorem selected_local_bound
    (request : Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (perimeters : Matched.FacePerimeters (request := request.energy)
      cache i j)
    (keep : Fin faces.regulars.length → Bool) (later : request.ownership.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (perimeters.selectedLocalSum keep) ≤ target := open Purelib.Approximation in by
  let samples := request.energy.samples cache
  let shared := fun sheet position => Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.sharedBoundary
    samples (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
    (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j) sheet position
  let error := fun sheet position => Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest.pairError
    samples i j sheet position
  have sheetBound (sheet : Fin 2) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position =>
        Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (shared sheet
        position))) ≤
        64 * (request.energyTarget / 2)^2 := by
    let row := request.energy.entries.get sheet
    have rowLater : row.index ≤ stage := (request.energy.index_ge sheet).trans (request.ownership.energy_le.trans later)
    have faceBound (position : Fin faces.regulars.length) : Data.Gaussian.Norm.Basic.normSq (shared sheet position)
      ≤ 64 * row.perFace^2 := by
      have estimate := (row.atStage stage rowLater position).bilinear_bound_on rfl (row.mesh_eq position)
        ((samples.get sheet).readings.get position) (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
          (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j)
      rw [Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.row_norm,
        Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.row_norm, one_mul, one_mul] at estimate
      exact estimate
    have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 64)
      (Fraction.Order.Arithmetic.sq_nonneg_direct row.perFace)
    have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ (64 * row.perFace^2)
      (fun position => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_bound_for_sum (keep position)
        nonnegative (faceBound position))
    have countNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le faces.regulars.length)) row.positive.le
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct countNonnegative row.paid.le 2
    exact estimate.trans ((show (faces.regulars.length : Fraction.Rational)^2 * (64 * row.perFace^2) =
      64 * ((faces.regulars.length : Fraction.Rational) * row.perFace)^2 by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by decide +kernel)))
  have sharedBound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ (64 * (request.energyTarget / 2)^2) sheetBound
  have sharedPaid : Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet => FiniteSum.Fin.sumFin (fun
    position => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (shared sheet
    position)))) ≤
      64 * request.energyTarget^2 := by
    apply sharedBound.trans_eq
    have half : request.energyTarget / 2 * 2 = request.energyTarget :=
      Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
    calc
      _ = 64 * (request.energyTarget / 2 * 2)^2 := by ring1
      _ = _ := by rw [half]
  have facePositive : 0 < request.ownership.perFace := by
    rw [request.ownership.perFace_eq]
    exact Rational.Budget.Aggregate.perTerm_positive
      (Rational.Budget.Aggregate.perTerm_positive request.ownership.positive 2) faces.regulars.length
  have facePaid : (faces.regulars.length : Fraction.Rational)^2 * request.ownership.perFace <
      Rational.Budget.Aggregate.perTerm request.ownershipTarget 2 := by
    have paid := Rational.Budget.Aggregate.count_mul_perTerm_lt
      (Rational.Budget.Aggregate.perTerm_positive request.ownership.positive 2) faces.regulars.length
    rw [← request.ownership.perFace_eq] at paid
    exact (show (faces.regulars.length : Fraction.Rational)^2 * request.ownership.perFace =
      (faces.regulars.length : Fraction.Rational) * ((faces.regulars.length : Fraction.Rational) *
        request.ownership.perFace) by ring1).trans_lt paid
  have perSheet (sheet : Fin 2) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position =>
        Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (error sheet position)))
        ≤
        Rational.Budget.Aggregate.perTerm request.ownershipTarget 2 :=
    ((Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ request.ownership.perFace
      (fun position => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_bound_for_sum (keep position)
        facePositive.le
        (request.ownership.pairError_bound later samples i j sheet position).le)).trans_lt facePaid).le
  have errorBound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _
    (Rational.Budget.Aggregate.perTerm request.ownershipTarget 2) perSheet
  have errorPaid : Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet => FiniteSum.Fin.sumFin (fun
    position => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (error sheet
    position)))) ≤
      request.ownershipTarget :=
    (errorBound.trans_lt ((show ((2 : Nat) : Fraction.Rational)^2 * Rational.Budget.Aggregate.perTerm
      request.ownershipTarget 2 =
      (2 : Fraction.Rational) * (2 * Rational.Budget.Aggregate.perTerm request.ownershipTarget 2) by ring1).trans_lt
      (Rational.Budget.Aggregate.count_mul_perTerm_lt request.ownership.positive 2))).le
  have pointwise (position : Fin faces.regulars.length) (sheet : Fin 2) :
      Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position)
        ((perimeters.assemblies.get position).get sheet).localTotal =
        Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (shared sheet position)
          - Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (error sheet
          position) := by
    have equal := Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.combinedError_eq_shared_sub_local
      samples (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
        (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j) sheet position
    rw [Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.basis_combinedError] at equal
    cases keep position with
    | false => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
    | true =>
      change ((perimeters.assemblies.get position).get sheet).localTotal = shared sheet position - error sheet position
      rw [Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.local_readback request perimeters position sheet]
      exact (show shared sheet position - (shared sheet position -
        Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.localBoundary cache
        (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
        (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j) sheet position) =
        Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryBound.localBoundary cache
        (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector i)
        (Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.rowVector j) sheet position by ring1).symm.trans (congrArg
        (fun value => shared sheet position - value) equal.symm)
  have identity := FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (pointwise position))
  unfold Matched.FacePerimeters.selectedLocalSum
  rw [identity, FiniteSum.Fin.sumFin_swap]
  have separate := FiniteSum.Fin.sumFin_congr (fun sheet => FiniteSum.Fin.sumFin_sub
    (fun position => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (shared
      sheet position))
    (fun position => Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound.selectedValue_for_sum (keep position) (error
      sheet position)))
  rw [separate, FiniteSum.Fin.sumFin_sub]
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sharedPaid errorPaid) (by decide))
  have genusLe : (1 : Fraction.Rational) ≤ (genus : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.succ_le_of_lt ((Nat.zero_le i.val).trans_lt i.isLt))
  have genusSquare : (1 : Fraction.Rational) ≤ (genus : Fraction.Rational)^2 := by
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Fraction.Rational) ≤ 1) genusLe 2
    simpa only [one_pow, -eq_self, -iff_self] using square
  have ownership := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct genusSquare (by decide : (0 : Fraction.Rational) ≤ 2))
    request.ownership.positive.le
  exact estimate.trans ((show 2 * (64 * request.energyTarget^2 + request.ownershipTarget) =
    128 * request.energyTarget^2 + (2 * 1) * request.ownershipTarget by ring1).trans_le
    ((Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) ownership).trans request.paid))

end LocalPairBound.FacePerimeters

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
