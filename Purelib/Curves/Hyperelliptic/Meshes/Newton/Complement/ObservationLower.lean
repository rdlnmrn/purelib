module
import Purelib.Data.List.Search
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleOverlap
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceArea
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Periods.AffineBasisBilinear
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Readings.ContainedObservationEnergy
import Purelib.Riemann.Readings.ProtectedObservationRegion
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

public section

/-! Observation positivity on the actual complement of the Newton annuli.
Every retained piece uses the existing complete-surface sample and budget. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open Purelib.Data.Rat
open Purelib.Geometry.Rational.Box
open Purelib.Geometry.Rectangle.Partition
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.AffineBasisEnergy
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.NewtonObservationSurfaceArea
open Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower.SurfacePartition.LocalMeshes
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
open Purelib.Riemann.Topology.NewtonSewnExcision
open Purelib.Topology.BranchedCover.Double

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_left sumFin_mul_right)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower (observationDensity surfaceLowerConstant)

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
    {sheet : Fin 2} {stage : Nat}
  {cache : Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid grid.punctured}

/-- Select the retained regular faces outside every actual excised Newton hole. -/
@[expose] def remainingFaceMask (excision : Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length) : Bool :=
  !(excision.entries.any (fun entry => entry.keep (grid.faces.regulars[position.val]'position.isLt)))

/-- The lifted triangle mask agrees exactly with the remaining-face mask on both sheets and both face triangles. -/
theorem remainingFaceMask_triangleIndex (excision : Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (upper : Bool) :
    (!(excision.entries.any (fun entry => AllHoleExcision.sourceMask entry
      (lifted.mesh.triangleIndex position sheet upper)))) =
        Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position := by
  apply congrArg Bool.not
  induction excision.entries with
  | nil => rfl
  | cons entry tail ih =>
      change (AllHoleExcision.sourceMask entry _ || _) = (entry.keep _ || _)
      rw [AllHoleExcision.sourceMask_triangleIndex, ih]

/-- Every observation overlap on an excised face has zero area because the protected observation region lies below its
retained Newton band. -/
theorem SurfacePartition.removed_observationArea_zero
    {position : Fin grid.faces.regulars.length} (partition : NewtonObservationSurfacePartition.SurfacePartition
      observations grid position)
    (excision : Excision.AllHoleExcision grid lifted) (removed :
      Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position = false)
    (site : Fin genus) (piece : Fin partition.cuts.boxes.length) : SurfacePartition.observationArea partition site piece
      = 0 := by
  have selected : excision.entries.any (fun entry => entry.keep (grid.faces.regulars[position.val]'position.isLt)) =
    true :=
    by
      cases value : excision.entries.any (fun entry => entry.keep (grid.faces.regulars[position.val]'position.isLt))
        with
      | false =>
          change (!excision.entries.any (fun entry => entry.keep (grid.faces.regulars[position.val]'position.isLt))) =
            false at removed
          rw [value] at removed
          nomatch removed
      | true => rfl
  obtain ⟨entry, _, kept⟩ := Data.List.Search.any_witness _ _ selected
  have band := (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.bands.entries.get
    entry.hole.index).selection.sample.output.strictCurrent)
  have faceIn : (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box entry.hole.index) :=
    of_decide_eq_true kept
  have pieceIn := partition.cuts.refines (List.getElem_mem piece.isLt)
  have below := ((observations.energy.box_refines_region site).2.2.2.trans_lt
    (observations.region.below_state entry.hole.index)).trans_le
      (band.2.2.1.trans (faceIn.2.2.1.trans pieceIn.2.2.1))
  rw [SurfacePartition.observationArea_eq_content partition]
  exact PreparedRectangleOverlap.content_separated (Or.inr (Or.inr (Or.inr below.le)))

namespace SurfacePartition.LocalMeshes.Samples

variable {position : Fin grid.faces.regulars.length} {partition :
  Riemann.Topology.NewtonObservationSurfacePartition.SurfacePartition observations grid position}
  {meshes : Riemann.Topology.NewtonObservationSurfaceEnergy.LocalMeshes partition domains sheet}

/-- The retained observation lower bound survives masking an excised piece, whose observation overlap is zero. -/
theorem remaining_observation_lower (samples : LocalMeshes.Samples meshes cache)
    (excision : Excision.AllHoleExcision grid lifted) (piece : Fin partition.cuts.boxes.length)
    (budget : AffineBasis.SurfaceBudget (samples.readings.get piece).affine)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face : Attachment.Face) (site : Fin genus) :
    SurfacePartition.observationArea partition site piece * (NewtonObservationSurfaceLower.observationDensity
      observations coefficients site / 4) ≤
      if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
        (budget.sample coefficients).affineEnergy else 0 := by
  cases kept : Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position with
  | true => exact Samples.observation_lower samples piece budget coefficients face site
  | false =>
      rw [Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.SurfacePartition.removed_observationArea_zero
        partition excision kept site piece, zero_mul]
      exact le_refl _

end SurfacePartition.LocalMeshes.Samples

namespace SurfaceRequest

variable {partitions : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid} {coarse :
  Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Data.Rat.Fraction.Rational}
  {request : Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error} {samples :
    request.Readings cache}

/-- The sum of retained complement affine energies pays the observation lower bound after the finite genus factor. -/
theorem Budget.remaining_observation_lower (excision : Excision.AllHoleExcision grid lifted) (budget :
  SurfaceRequest.Budget request samples) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Attachment.Face) :
    observations.energy.lower * PreparedObservationCoercivity.coefficientNormSq coefficients / 4 ≤
      (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        (if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          (((budget.entries.get position).get piece).sample coefficients).affineEnergy else 0))) := by
  have siteBound (site : Fin genus) :
      observations.energy.area * (NewtonObservationSurfaceLower.observationDensity observations coefficients site / 4) ≤
        FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => (if
          Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          (((budget.entries.get position).get piece).sample coefficients).affineEnergy else 0))) := by
    have bound := Order.Positivity.sumFin_mono _ _ (fun position => Order.Positivity.sumFin_mono _ _
      (fun piece =>
        SurfacePartition.LocalMeshes.Samples.remaining_observation_lower
        (samples.get position) excision piece ((budget.entries.get position).get piece) coefficients face site))
    have area : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      SurfacePartition.observationArea (partitions.get position) site piece *
        (NewtonObservationSurfaceLower.observationDensity observations coefficients site / 4))) =
        observations.energy.area * (NewtonObservationSurfaceLower.observationDensity observations coefficients site / 4)
          := by
      rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_mul_right (SurfacePartition.observationArea
        (partitions.get position) site) _),
        FiniteSum.Fin.sumFin_mul_right, NewtonObservationSurfaceArea.surface_observation_area]
    exact (le_of_eq area.symm).trans bound
  have bound := Order.Positivity.sumFin_mono _ _ siteBound
  rw [Algebra.FiniteSum.Fin.Rational.sum_constant] at bound
  have original := observations.uniform_lower coefficients face
  rw [observations.energy.surfaceEnergy_eq] at original
  have divided := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct original
    (show (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹ by decide)
  have equal : FiniteSum.Fin.sumFin (fun site => observations.energy.area *
    (NewtonObservationSurfaceLower.observationDensity observations coefficients site / 4)) =
      (observations.energy.area * FiniteSum.Fin.sumFin (fun site => NewtonObservationSurfaceLower.observationDensity
        observations coefficients site)) * (4 : Fraction.Rational)⁻¹ := by
    rw [FiniteSum.Fin.sumFin_congr (fun site => show observations.energy.area *
      (NewtonObservationSurfaceLower.observationDensity observations coefficients site / 4) =
      (observations.energy.area * NewtonObservationSurfaceLower.observationDensity observations coefficients site) * (4
        : Fraction.Rational)⁻¹ from by
        rw [Fraction.Field.div_eq_mul_inv_direct]; ring1), FiniteSum.Fin.sumFin_mul_right,
          FiniteSum.Fin.sumFin_mul_left]
  rw [equal] at bound
  exact divided.trans bound

/-- Homogeneous positive affine energy on the retained complement. -/
theorem Budget.remaining_affine_lower (excision : Excision.AllHoleExcision grid lifted) (budget : SurfaceRequest.Budget
  request samples) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Attachment.Face) :
    NewtonObservationSurfaceLower.surfaceLowerConstant observations * PreparedObservationCoercivity.coefficientNormSq
      coefficients ≤
      FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        (if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          (((budget.entries.get position).get piece).sample coefficients).affineEnergy else 0))) := by
  let energy := FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
    (if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      (((budget.entries.get position).get piece).sample coefficients).affineEnergy else 0)))
  have nonnegative : 0 ≤ energy := by
    have inner (position : Fin grid.faces.regulars.length) := Order.Positivity.sumFin_mono
      (fun _ => (0 : Fraction.Rational))
      (fun piece => if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision
        position then
        (((budget.entries.get position).get piece).sample coefficients).affineEnergy else 0) (fun piece =>
        by
        cases Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position with
        | false => exact le_refl _
        | true =>
          exact (samples.get position).piece_affine_nonnegative piece ((budget.entries.get position).get piece)
            coefficients)
    have nonnegativeInner (position : Fin grid.faces.regulars.length) : 0 ≤ FiniteSum.Fin.sumFin (fun piece =>
        (if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          (((budget.entries.get position).get piece).sample coefficients).affineEnergy else 0)) :=
      (FiniteSum.Fin.sumFin_zero).symm.trans_le (inner position)
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ => (0 : Fraction.Rational)) _ nonnegativeInner)
  have factorPositive : 0 < (genus : Fraction.Rational) + 1 := by
    calc
      0 < (1 : Fraction.Rational) := by decide
      _ = 0 + 1 := by ring1
      _ ≤ (genus : Fraction.Rational) + 1 := Fraction.Order.Arithmetic.add_le_add_right_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus)) 1
  have genusLe : (genus : Fraction.Rational) ≤ (genus : Fraction.Rational) + 1 := by
    calc
      (genus : Fraction.Rational) = (genus : Fraction.Rational) + 0 := by ring1
      _ ≤ (genus : Fraction.Rational) + 1 :=
        Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) (by decide)
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := (genus : Fraction.Rational) + 1) _ factorPositive
  calc
    _ = (NewtonObservationSurfaceLower.surfaceLowerConstant observations * ((genus : Fraction.Rational) + 1)) *
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
      ring1
    _ = (observations.energy.lower / 4) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
      rw [NewtonObservationSurfaceLower.surfaceLowerConstant, Fraction.Field.div_mul_cancel_of_ne _ _
        factorPositive.ne']
    _ = observations.energy.lower * PreparedObservationCoercivity.coefficientNormSq coefficients / 4 := by
      rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]; ring1
    _ ≤ (genus : Fraction.Rational) * energy :=
      Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.SurfaceRequest.Budget.remaining_observation_lower
      excision budget coefficients face
    _ ≤ ((genus : Fraction.Rational) + 1) * energy := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      genusLe nonnegative
    _ = _ := by ring1

/-- The retained boundary sum keeps the observation margin. The full error budget pays every retained piece, so excision
cannot hide a negative error. -/
theorem remaining_boundary_lower (excision : Excision.AllHoleExcision grid lifted) (request :
  NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error) (later : request.index ≤ stage)
    (samples : request.Readings cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Attachment.Face) :
    (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error) *
      PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        (if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          ((((request.budget later samples).entries.get position).get piece).sample coefficients).boundaryArea.im / 4
          else 0))) := by
  let budget := request.budget later samples
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational))
      (fun row => Data.Gaussian.Basic.Canonical.normSq (coefficients row))
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have pieceLower (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length)
    :
      (if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
        (((budget.entries.get position).get piece).sample coefficients).affineEnergy else 0) -
        PreparedObservationCoercivity.coefficientNormSq coefficients * ((budget.entries.get position).get piece).total ≤
      (if Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
        (((budget.entries.get position).get piece).sample coefficients).boundaryArea.im / 4 else 0) := by
    cases Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position with
    | true => exact ((budget.entries.get position).get piece).energy_lower coefficients
    | false =>
        have totalNonnegative : 0 ≤ ((budget.entries.get position).get piece).total := by
          let entry := (budget.entries.get position).get piece
          rw [entry.total_eq]
          have bound := Order.Positivity.sumFin_mono
            (fun _ => (0 : Fraction.Rational)) (fun face => (entry.triangles.get face).total)
            (fun face => by
              rw [(entry.triangles.get face).total_eq]
              exact add_nonneg (add_nonneg (entry.triangles.get face).products.first_nonnegative
                (entry.triangles.get face).products.second_nonnegative)
                (entry.triangles.get face).products.mixed_nonnegative)
          exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
        have bound := Fraction.Order.Arithmetic.neg_le_neg_direct
          (Fraction.Order.Arithmetic.mul_nonneg_direct normNonnegative totalNonnegative)
        calc
          0 - PreparedObservationCoercivity.coefficientNormSq coefficients *
            ((budget.entries.get position).get piece).total =
              -(PreparedObservationCoercivity.coefficientNormSq coefficients *
                ((budget.entries.get position).get piece).total) := by ring1
          _ ≤ -(0 : Fraction.Rational) := bound
          _ = 0 := by decide
  have boundary := Order.Positivity.sumFin_mono _ _ (fun position => Order.Positivity.sumFin_mono _ _
    (pieceLower position))
  have errorSum : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      PreparedObservationCoercivity.coefficientNormSq coefficients * ((budget.entries.get position).get piece).total)) =
      PreparedObservationCoercivity.coefficientNormSq coefficients * budget.total := by
    rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_mul_left _ (fun piece => ((budget.entries.get
      position).get piece).total)),
      FiniteSum.Fin.sumFin_mul_left, budget.total_eq]
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_sub _ _),
    FiniteSum.Fin.sumFin_sub, errorSum] at boundary
  have positive :=
    Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower.SurfaceRequest.Budget.remaining_affine_lower excision
    budget coefficients face
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.budget_total_lt later samples).le
    normNonnegative
  have lower := (Fraction.Order.Arithmetic.sub_le_sub_direct positive paid).trans boundary
  exact (le_of_eq (by ring1)).trans lower

end SurfaceRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
