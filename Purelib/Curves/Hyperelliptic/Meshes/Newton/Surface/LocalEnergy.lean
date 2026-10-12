module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
public import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Positive complete-surface energy in retained local model boundaries

Choose a squared ownership target from the requested homogeneous energy
allowance. The actual cached energy sample then transfers to all local-owner
piece boundaries, with both the affine and ownership losses explicit.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars} {sheet : Fin
    2}
  {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid} {coarse :
    Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget :
    Fraction.Rational}

/-- Canonical sum of the actual retained local-owner clipped sides. -/
@[expose] def localEnergyArea (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget) {stage : Nat}
    (cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
    ((energy.meshes.get position).entries.get piece).pieces.localBoundary
      (fun column row point => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun rowIndex =>
        coefficients rowIndex * (cache.atDomain position sheet rowIndex).primitives.value column row point)))
      ((energy.meshes.get position).entries.get piece).depth))

namespace ConjugateRequest

/-- Allocate a squared ownership target from the positive energy allowance and the actual genus. -/
@[expose] def energyAllowanceTarget (genus : Nat) (allowance : Fraction.Rational) : Fraction.Rational :=
  (4 * allowance) ^ 2 / ((genus : Fraction.Rational) ^ 2 + 1)

/-- The squared ownership target is positive whenever the original energy allowance is positive. -/
theorem energyAllowanceTarget_positive {allowance : Fraction.Rational} (positive : 0 < allowance) :
    0 < Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) 2)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by
      decide))

/-- Genus squared times the retained ownership target is bounded by the square of four times the energy allowance. -/
theorem energyAllowanceTarget_paid {allowance : Fraction.Rational} (positive : 0 < allowance) :
    (genus : Fraction.Rational) ^ 2 *
      Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance ≤ (4 *
      allowance) ^ 2 := by
  have denominator : 0 < (genus : Fraction.Rational) ^ 2 + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide)
  calc
    _ ≤ ((genus : Fraction.Rational) ^ 2 + 1) *
      Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
        (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive positive).le
    _ = Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance * ((genus
      : Fraction.Rational) ^ 2 + 1) := by
      ring1
    _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ denominator.ne'

/-- Prepare the original conjugate request at the squared target allocated from the supplied positive energy allowance.
-/
@[expose] def forEnergyAllowance (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    ConjugateRequest energy
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance) :=
  ConjugateRequest.build energy _
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive positive)

/-- The sum of imaginary quarter-readings is the imaginary quarter-reading of the exact finite Gaussian sum. -/
private theorem sum_energy {count : Nat} (values : Fin count → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index => (values index).im / 4) = (FiniteSum.Fin.sumFin values).im / 4 := by
  rw [LinearAlgebra.Gaussian.Energy.sumFin_im]
  change FiniteSum.Fin.sumFin (fun index => (values index).im * (4 : Fraction.Rational)⁻¹) = _
  exact FiniteSum.Fin.sumFin_mul_right _ _

variable {energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget} {allowance
  : Fraction.Rational}
  {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}

/-- Every later common sample pays the same coefficient-uniform allowance.
The reference is the full local-owner boundary sum, not the period form. -/
theorem local_energy_lower (request : ConjugateRequest energy
  (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance))
    (positive : 0 < allowance) (later : request.index ≤ stage) (samples : energy.Readings cache)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations - energyTarget - allowance) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.localEnergyArea energy cache coefficients).im / 4 := by
  let budget := energy.budget (request.energy_le.trans later) samples
  let actual := FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
    (((budget.entries.get position).get piece).sample coefficients).boundaryArea))
  have close := Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.boundary_error_bound request later samples
    budget coefficients
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_sub _ _),
    FiniteSum.Fin.sumFin_sub] at close
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational))
      (fun row => Gaussian.Basic.Canonical.normSq (coefficients row))
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have squared : Data.Gaussian.Norm.Basic.normSq (actual -
    Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.localEnergyArea energy cache coefficients) ≤
      (4 * (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    apply close.trans
    calc
      _ = ((genus : Fraction.Rational) ^ 2 *
        Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
        ring1
      _ ≤ (4 * allowance) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid positive)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le actual
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.localEnergyArea energy cache coefficients) (allowance *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le normNonnegative) squared
  have lower := Topology.NewtonObservationSurfaceLower.SurfaceRequest.boundary_lower energy (request.energy_le.trans
    later) samples coefficients face
  have actualEq : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      (((budget.entries.get position).get piece).sample coefficients).boundaryArea.im / 4)) = actual.im / 4 := by
    rw [FiniteSum.Fin.sumFin_congr (fun position =>
      Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.sum_energy (fun piece =>
      (((budget.entries.get position).get piece).sample coefficients).boundaryArea)),
        Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.sum_energy]
  have lowerActual := lower.trans_eq actualEq
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lowerActual
    (le_rfl (a := allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end ConjugateRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
