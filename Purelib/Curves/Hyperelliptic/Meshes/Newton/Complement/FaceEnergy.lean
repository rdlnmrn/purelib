module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
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
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorEnergy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

public section

/-! Pay the retained faces' internal joining defects before the comparison
across different regular faces. All exteriors use the original cached sides. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorEnergy
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Riemann.Readings
open Purelib.Riemann.Topology
open Purelib.Topology.BranchedCover.Double

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters FaceAssemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower (remainingFaceMask)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_paid)

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
  {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid}
  {surfaceCuts : Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.SurfaceCuts partitions domains} {depth :
    Nat}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {fixed : Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Data.Rat.Fraction.Rational}
  {energy : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
    (Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet
    depth) fixed error}
  {position : Fin grid.faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Integration.Path.BoundaryRibbon (Ribbon)

variable {pieceError : Data.Rat.Fraction.Rational} {minimum : Nat}

variable (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  {stage : Nat} {cache : Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : Surface.ExteriorRequest.Assemblies energy cache
    coefficients} {perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters assemblies}

/-- The sum of the actual retained face exteriors selected by the original excision mask. -/
@[expose] def FaceAssemblies.remainingExterior (faces : FaceAssembly.FaceAssemblies perimeters) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => if ObservationLower.remainingFaceMask excision position then (faces.get
    position).exterior else 0)

/-- The sum of the retained seam and corner defects on the original unexcised faces. -/
@[expose] def FaceAssemblies.remainingDefect (faces : FaceAssembly.FaceAssemblies perimeters) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => if ObservationLower.remainingFaceMask excision position then
    (faces.get position).seams + (faces.get position).cornerTotal else 0)

/-- The retained unexcised piece exteriors split into their complete face exteriors and actual joining defects. -/
theorem FaceAssemblies.remaining_decomposition (faces : FaceAssembly.FaceAssemblies perimeters) :
    Curves.Hyperelliptic.Meshes.Newton.Complement.ExteriorEnergy.ExteriorRequest.remainingExterior excision assemblies =
      Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingExterior excision faces +
        Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingDefect excision faces := by
  unfold ExteriorRequest.remainingExterior
    Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingExterior
    Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingDefect
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  cases ObservationLower.remainingFaceMask excision position with
  | false =>
      change FiniteSum.Fin.sumFin (fun _ : Fin (partitions.get position).cuts.boxes.length => (0 :
        Data.Gaussian.Basic.Canonical)) = 0 + 0
      rw [FiniteSum.Fin.sumFin_zero, add_zero]
  | true =>
      change FiniteSum.Fin.sumFin (fun piece => ((assemblies.get position).get piece).exterior) =
        (faces.get position).exterior + ((faces.get position).seams + (faces.get position).cornerTotal)
      exact (faces.get position).decomposition.trans (by ring1)

namespace DefectRequest

variable {base : Surface.ExteriorRequest energy pieceError minimum}
  {allowance : Data.Rat.Fraction.Rational}

/-- At the paid common stage, the actual unexcised face defects obey the original homogeneous surface allowance. -/
theorem remaining_error_bound (request : Surface.DefectRequest base allowance) (later : request.index ≤ stage)
    (faces : FaceAssembly.FaceAssemblies perimeters) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingDefect excision faces) ≤ (genus
      : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * allowance := by
  have bound := Indexed.normSq_sumFin_le
    (fun position => if ObservationLower.remainingFaceMask excision position then
      (faces.get position).seams + (faces.get position).cornerTotal else 0)
    ((genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
      request.perFace)
    (fun position => by
      cases ObservationLower.remainingFaceMask excision position with
      | true =>
        exact FaceDefectRequest.accurate (request.entries.get position) ((request.index_ge position).trans later)
          (faces.get position)
      | false =>
          simp only [if_neg (by decide : false ≠ true), Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self]
          have perFacePositive : 0 < request.perFace := by
            rw [request.perFace_eq]
            exact Aggregate.perTerm_positive request.positive _
          exact Fraction.Order.Arithmetic.mul_nonneg_direct
            (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
              (Fraction.Order.Arithmetic.sq_nonneg_direct _)) perFacePositive.le)
  have payment : (grid.faces.regulars.length : Fraction.Rational) ^ 2 * request.perFace ≤ allowance := by
    rw [request.perFace_eq]
    exact (le_of_eq (by ring1)).trans (Aggregate.count_mul_perTerm_lt request.positive _).le
  apply bound.trans
  calc
    _ = ((genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2) *
      ((grid.faces.regulars.length : Fraction.Rational) ^ 2 * request.perFace) := by ring1
    _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct payment
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The retained regular-face exterior inherits the independent observation lower bound after all internal ownership,
seam and corner losses are paid. -/
theorem remaining_energy_lower {ownershipAllowance exteriorAllowance faceAllowance : Fraction.Rational}
    (ownership : Surface.ConjugateRequest energy (ConjugateRequest.energyAllowanceTarget genus
      ownershipAllowance))
    (base : Surface.ExteriorRequest energy (ConjugateRequest.energyAllowanceTarget genus exteriorAllowance)
      ownership.index)
    (request : Surface.DefectRequest base (ConjugateRequest.energyAllowanceTarget genus faceAllowance))
    (ownershipPositive : 0 < ownershipAllowance) (exteriorPositive : 0 < exteriorAllowance)
    (facePositive : 0 < faceAllowance) (later : request.index ≤ stage) (samples : energy.Readings cache)
    (face : Attachment.Face) (faces : FaceAssembly.FaceAssemblies perimeters) :
    (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance - exteriorAllowance -
      faceAllowance) *
        PreparedObservationCoercivity.coefficientNormSq coefficients ≤
          (Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingExterior excision faces).im
          / 4 := by
  have close := remaining_error_bound excision
    request later faces
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Data.Gaussian.Norm.Basic.normSq_nonneg (coefficients row))
    have same := FiniteSum.Fin.sumFin_congr
      (fun row : Fin genus => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
    change 0 ≤ FiniteSum.Fin.sumFin (fun row => (coefficients row).normSq)
    rw [← same]
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have difference : ExteriorRequest.remainingExterior excision assemblies -
    (Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingExterior excision faces) =
    (Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingDefect excision faces) := by
    rw [Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remaining_decomposition excision faces]
    ring1
  have squared : Data.Gaussian.Norm.Basic.normSq (ExteriorRequest.remainingExterior excision assemblies -
    (Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingExterior excision faces)) ≤
      (4 * (faceAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    rw [difference]
    apply close.trans
    calc
      _ = ((genus : Fraction.Rational) ^ 2 * ConjugateRequest.energyAllowanceTarget genus faceAllowance) *
        PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
        ring1
      _ ≤ (4 * faceAllowance) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (ConjugateRequest.energyAllowanceTarget_paid facePositive) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (ExteriorRequest.remainingExterior excision assemblies)
      (Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy.FaceAssemblies.remainingExterior excision faces)
      (faceAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct facePositive.le normNonnegative) squared
  have lower := ExteriorRequest.remaining_energy_lower excision ownership base ownershipPositive exteriorPositive
    (request.base_le.trans later)
    samples coefficients face assemblies
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := faceAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end DefectRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.FaceEnergy
