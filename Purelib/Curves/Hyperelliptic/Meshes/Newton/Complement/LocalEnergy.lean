module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
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

public section

/-! Positive retained-surface energy in the original local model boundaries.
The annular mask removes no observation contribution; ownership errors use
the same common numerical bank and coefficient-independent allowance. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.LocalEnergy

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib
open Purelib.Riemann
open Purelib.RootIsolation

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
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured}
  {fixed : RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget :
    Fraction.Rational}

/-- Canonical sum of the actual retained local-owner clipped sides. -/
@[expose] def remainingLocalEnergyArea (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid
  lifted) (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget) {stage :
  Nat}
    (cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
    if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
    ((energy.meshes.get position).entries.get piece).pieces.localBoundary
      (fun column row point => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun rowIndex =>
        coefficients rowIndex * (cache.atDomain position sheet rowIndex).primitives.value column row point)))
      ((energy.meshes.get position).entries.get piece).depth else 0))

namespace ConjugateRequest

variable {energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget} {allowance
  : Fraction.Rational}
  {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}

/-- Every later common sample pays the same coefficient-uniform allowance.
The reference contains precisely the retained local-owner boundaries. -/
theorem remaining_local_energy_lower (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid
  lifted) (request : Surface.ConjugateRequest energy
  (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance))
    (positive : 0 < allowance) (later : request.index ≤ stage) (samples : energy.Readings cache)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations - energyTarget - allowance) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      (Hyperelliptic.Meshes.Newton.Complement.LocalEnergy.remainingLocalEnergyArea excision energy cache
        coefficients).im / 4 := by
  let budget := energy.budget (request.energy_le.trans later) samples
  let actual := FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
    if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      (((budget.entries.get position).get piece).sample coefficients).boundaryArea else 0))
  have close := Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison.remaining_boundary_error_bound excision
    request later samples budget coefficients
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun piece => ((fun (keep : Bool) (first
    second : Gaussian.Basic.Canonical) =>
      show (if keep then first - second else 0) = (if keep then first else 0) - (if keep then second else 0) from by
        cases keep
        · exact (Data.Gaussian.Basic.sub_zero 0).symm
        · rfl) (Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position) _ _))),
    FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_sub _ _),
    FiniteSum.Fin.sumFin_sub] at close
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have squared : Data.Gaussian.Norm.Basic.normSq (actual -
    Hyperelliptic.Meshes.Newton.Complement.LocalEnergy.remainingLocalEnergyArea excision energy cache coefficients) ≤
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
    (Hyperelliptic.Meshes.Newton.Complement.LocalEnergy.remainingLocalEnergyArea excision energy cache coefficients)
      (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le normNonnegative) squared
  have lower := Hyperelliptic.Meshes.Newton.Complement.ObservationLower.SurfaceRequest.remaining_boundary_lower excision
    energy (request.energy_le.trans later) samples coefficients face
  have actualEq : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
        (((budget.entries.get position).get piece).sample coefficients).boundaryArea.im / 4 else 0)) = actual.im / 4 :=
          by
    rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun piece =>
      ((fun (keep : Bool) (value : Gaussian.Basic.Canonical) =>
        show (if keep then value.im / 4 else 0) = (if keep then value else 0).im / 4 from by
          cases keep
          · change (0 : Fraction.Rational) = 0 / 4
            decide
          · rfl)
        (Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position)
        (((budget.entries.get position).get piece).sample coefficients).boundaryArea)))]
    have inner (position : Fin grid.faces.regulars.length) :
        FiniteSum.Fin.sumFin (fun piece => (if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask
          excision position then
          (((budget.entries.get position).get piece).sample coefficients).boundaryArea else 0).im / 4) =
        (FiniteSum.Fin.sumFin (fun piece => if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask
          excision position then
          (((budget.entries.get position).get piece).sample coefficients).boundaryArea else 0)).im / 4 := by
      rw [LinearAlgebra.Gaussian.Energy.sumFin_im]
      exact FiniteSum.Fin.sumFin_mul_right _ _
    rw [FiniteSum.Fin.sumFin_congr inner]
    change FiniteSum.Fin.sumFin (fun position => (FiniteSum.Fin.sumFin (fun piece =>
      if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
        (((budget.entries.get position).get piece).sample coefficients).boundaryArea else 0)).im / 4) =
      (FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          (((budget.entries.get position).get piece).sample coefficients).boundaryArea else 0))).im / 4
    rw [LinearAlgebra.Gaussian.Energy.sumFin_im]
    exact FiniteSum.Fin.sumFin_mul_right _ _
  have lowerActual := lower.trans_eq actualEq
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lowerActual
    (le_rfl (a := allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end ConjugateRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.LocalEnergy
