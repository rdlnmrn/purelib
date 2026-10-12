module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
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
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.LocalEnergy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
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
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! Stitch the retained pieces using the existing exterior request.
Every joining edge remains in its actual cached assembly. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorEnergy

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.LocalEnergy
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Readings
open Purelib.Riemann.Topology
open Purelib.Topology.BranchedCover.Double

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest (ConjugateExteriorRequest)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius
    : Data.Rat.Fraction.Rational} {grid : Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid
    preparation target radius}
  {observations : Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars}
    {sheet : Fin 2}
  {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid} {coarse :
    Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {fixed : Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget :
    Data.Rat.Fraction.Rational}

namespace ExteriorRequest

variable {energy : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget}
  {error : Data.Rat.Fraction.Rational} {minimum : Nat}
  {stage : Nat} {cache : Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}
  (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)

/-- The actual exterior-area sum of the retained pieces on precisely the unexcised regular faces.

Each original piece keeps its own joining edges and coefficient-weighted assembly. -/
@[expose] def remainingExterior (assemblies : ExteriorRequest.Assemblies energy cache coefficients) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
    if ObservationLower.remainingFaceMask excision position then ((assemblies.get position).get piece).exterior else 0))

/-- The squared finite count times its per-term aggregate allowance is at most the original positive target. -/
private theorem payment {count : Nat} {target : Fraction.Rational} (positive : 0 < target) :
    (count : Fraction.Rational) ^ 2 * Aggregate.perTerm target count ≤ target :=
  (le_of_eq (by ring1)).trans (Aggregate.count_mul_perTerm_lt positive count).le

/-- The retained local-energy sum and actual remaining piece exteriors satisfy the original coefficient-weighted
squared-norm error budget. -/
theorem remaining_error_bound (request : Surface.ExteriorRequest energy error minimum) (later : request.index ≤
  stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (assemblies : ExteriorRequest.Assemblies energy
      cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (LocalEnergy.remainingLocalEnergyArea excision energy cache coefficients -
      remainingExterior excision
      assemblies) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * error := by
  let factor := (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have perFacePositive : 0 < request.perFace := by
    rw [request.perFace_eq]
    exact Aggregate.perTerm_positive request.positive _
  let difference := fun position piece =>
    if ObservationLower.remainingFaceMask excision position then
      ((assemblies.get position).get piece).localTotal - ((assemblies.get position).get piece).exterior else 0
  have faceBound (position : Fin grid.faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (difference position)) ≤ factor * request.perFace
        := by
    have estimate := Indexed.normSq_sumFin_le (difference position)
      (factor * Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length)
      (fun piece => by
        cases kept : ObservationLower.remainingFaceMask excision position with
        | true =>
            dsimp only [difference]
            rw [kept]
            exact ConjugateExteriorRequest.weighted_bound ((request.entries.get position).get piece) ((request.index_ge
              position piece).trans later)
              (cache.atDomain position sheet) coefficients ((assemblies.get position).get piece)
        | false =>
            dsimp only [difference]
            rw [kept]
            simp only [if_neg (by decide : false ≠ true), Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self]
            exact Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
              (Aggregate.perTerm_positive perFacePositive _).le)
    apply estimate.trans
    calc
      _ = factor * (((partitions.get position).cuts.boxes.length : Fraction.Rational) ^ 2 *
        Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length) := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (payment perFacePositive)
        factorNonnegative
  have estimate := Indexed.normSq_sumFin_le _ (factor * request.perFace) faceBound
  have paid : (grid.faces.regulars.length : Fraction.Rational) ^ 2 * (factor * request.perFace) ≤ factor * error := by
    rw [request.perFace_eq]
    calc
      _ = factor * ((grid.faces.regulars.length : Fraction.Rational) ^ 2 *
        Aggregate.perTerm error grid.faces.regulars.length) := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (payment request.positive)
        factorNonnegative
  have total := estimate.trans paid
  have equal : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (difference position)) =
    LocalEnergy.remainingLocalEnergyArea excision energy cache coefficients -
    remainingExterior excision assemblies
    := by
    dsimp only [difference]
    rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun piece => ((fun (keep : Bool) (first
      second : Data.Gaussian.Basic.Canonical) =>
      show (if keep then first - second else 0) = (if keep then first else 0) - (if keep then second else 0) from by
        cases keep
        · exact (Data.Gaussian.Basic.sub_zero 0).symm
        · rfl) (ObservationLower.remainingFaceMask excision position) _ _))),
      FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_sub _ _), FiniteSum.Fin.sumFin_sub]
    apply congrArg (fun localTotal => localTotal - _)
    apply FiniteSum.Fin.sumFin_congr
    intro position
    apply FiniteSum.Fin.sumFin_congr
    intro piece
    exact congrArg (fun value : Data.Gaussian.Basic.Canonical => if ObservationLower.remainingFaceMask excision position
      then value else 0)
      (EnergyAssembly.raw_localTotal_eq (cache.atDomain position sheet) coefficients ((assemblies.get position).get
        piece))
  rw [equal] at total
  exact total

/-- The positive surface margin survives both ownership and seam/corner losses at one common numerical sample. Piece
exteriors keep their joining edges; joining different pieces and faces remains a separate comparison. -/
theorem remaining_energy_lower {ownershipAllowance exteriorAllowance : Fraction.Rational}
    (ownership : Surface.ConjugateRequest energy (ConjugateRequest.energyAllowanceTarget genus
      ownershipAllowance))
    (request : Surface.ExteriorRequest energy (ConjugateRequest.energyAllowanceTarget genus exteriorAllowance)
      ownership.index)
    (ownershipPositive : 0 < ownershipAllowance) (exteriorPositive : 0 < exteriorAllowance)
    (later : request.index ≤ stage) (samples : energy.Readings cache)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face : Attachment.Face)
    (assemblies : ExteriorRequest.Assemblies energy cache coefficients) :
    (NewtonObservationSurfaceLower.surfaceLowerConstant observations - energyTarget - ownershipAllowance -
      exteriorAllowance) * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      (remainingExterior excision
        assemblies).im / 4 := by
  have close := remaining_error_bound
    excision request later coefficients assemblies
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have squared : Data.Gaussian.Norm.Basic.normSq (LocalEnergy.remainingLocalEnergyArea excision energy cache
    coefficients - remainingExterior
    excision assemblies) ≤
      (4 * (exteriorAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    apply close.trans
    calc
      _ = ((genus : Fraction.Rational) ^ 2 * ConjugateRequest.energyAllowanceTarget genus exteriorAllowance) *
        PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
        ring1
      _ ≤ (4 * exteriorAllowance) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (ConjugateRequest.energyAllowanceTarget_paid exteriorPositive) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (LocalEnergy.remainingLocalEnergyArea excision energy cache coefficients)
      (remainingExterior excision
      assemblies) (exteriorAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct exteriorPositive.le normNonnegative) squared
  have lower := ConjugateRequest.remaining_local_energy_lower excision ownership ownershipPositive
    (request.minimum_le.trans later) samples coefficients face
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := exteriorAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end ExteriorRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorEnergy
