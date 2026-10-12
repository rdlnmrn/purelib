module
import Purelib.Algebra.FiniteSum.Fin.Rational
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Riemann.RootContinuation.NewtonObservationPartitions
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Readings.ProtectedObservationRegion
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Readings.ContainedObservationEnergy
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Readings.AffineBasisEnergy
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Data

public section

/-!
# Requested homogeneous energy on every protected observation piece

Spatial depths are chosen from fixed derivative ceilings. All pieces and
standard differentials then share one later model index and the original
face primitive bank. The requested aggregate error is proved, including
empty banks and every growing dyadic face count. This is local observation
boundary energy, not yet its identification with the global period boundary.
-/

namespace Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest (EnergyRequest)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonObservationPartitions.ProtectedObservations (GridPartitions)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy (LocalMeshes)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {partitions : GridPartitions observations grid} {sheet : Fin 2}

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data
/-- The lazy energy-preflight bank for every exact original regular domain on the retained sheet. -/
abbrev Preflights (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet :
  Fin 2) :=
  Vector.DependentVector (fun position : Fin grid.faces.regulars.length => Thunk
    (Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight ((domains.get position).domain sheet)))

/-- Cache a delayed energy preflight for each original regular-face domain and sheet. -/
@[expose] def preflights (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars)
  (sheet : Fin 2) : Preflights domains sheet :=
  Vector.DependentVector.ofFn fun position => ⟨fun _ => Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.build
    ((domains.get position).domain sheet)⟩

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Paid local energy requests on the original observation meshes with a common retained stage.

The positive per-piece allowance pays the exact flattened occurrence count. Each entry keeps its original preflight and
coarse mesh, and the common index covers all original model requests. -/
structure Request (coarse : LocalMeshes partitions domains sheet) (fixed : Preflights domains sheet) (target :
  Fraction.Rational) where
  /-- The retained common allowance for every original local piece request. -/ perPiece : Fraction.Rational
  /-- The original per-piece allowance is strictly positive. -/ positive : 0 < perPiece
  /-- The exact original flattened piece count times its allowance is below the requested target. -/ paid :
    (partitions.indices.length : Fraction.Rational) * perPiece < target
  /-- The dependent requests indexed by the exact original observation occurrences, preflights and coarse meshes. -/
    entries : Vector.DependentVector (fun index : Fin partitions.indices.length =>
    Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest (fixed.get (partitions.position index)).get
      (coarse.entries.get index) perPiece)
  /-- The common retained model stage for all original local requests. -/ index : Nat
  /-- Every original entry's model request is covered by the common stage. -/ index_ge : ∀ piece, (entries.get
    piece).modelRequest.index ≤ index

constructive_injectivity Request

namespace Request

variable {coarse : LocalMeshes partitions domains sheet} {fixed : Preflights domains sheet} {totalTarget :
  Purelib.Data.Rat.Fraction.Rational}

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Allocate one paid energy request for every original flattened observation occurrence.

The target is divided by the exact count plus one; the same preflight and coarse mesh feed each request, and the maximum
retained model stage covers all entries. -/
@[expose] def build (coarse : LocalMeshes partitions domains sheet) (fixed : Preflights domains sheet)
    (target : Fraction.Rational) (positive : 0 < target) : Request coarse fixed target := by
  let count := Budget.Aggregate.countCoordinate partitions.indices.length
  have countEq : count = (partitions.indices.length : Fraction.Rational) := Budget.Aggregate.countCoordinate_eq _
  have denominatorPositive : 0 < count + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    ((Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)).trans_eq countEq.symm) (by decide)
  let perPiece := target / (count + 1)
  have perPiecePositive : 0 < perPiece := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  let entries := Vector.DependentVector.ofFn fun index =>
    Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest.build (fixed.get (partitions.position index)).get
      (coarse.entries.get index) perPiece perPiecePositive
  exact
    { perPiece := perPiece
      positive := perPiecePositive
      paid := by
        rw [← countEq]
        calc
          count * perPiece < (count + 1) * perPiece := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
            (by
              have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
                (by decide : (0 : Fraction.Rational) < 1) count
              rewrite [show count + 0 = count by ring1] at shifted
              exact shifted) perPiecePositive
          _ = perPiece * (count + 1) := by ring1
          _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
      entries := entries
      index := entries.maximum (fun _ request => request.modelRequest.index)
      index_ge := entries.get_le_maximum (fun _ request => request.modelRequest.index) }

section
open Purelib.Data
/-- Read the refined meshes of the same original dependent energy-request bank. -/
@[expose] def meshes (request : Request coarse fixed totalTarget) : LocalMeshes partitions domains sheet :=
  ⟨Vector.DependentVector.ofFn fun index => (request.entries.get index).mesh⟩

/-- The mesh at an original occurrence is exactly the mesh retained by that occurrence's request. -/
theorem mesh_eq (request : Request coarse fixed totalTarget) (index : Fin partitions.indices.length) :
    request.meshes.entries.get index = (request.entries.get index).mesh := Vector.DependentVector.ofFn_get _ index

end

/-- Refine the exact retained occurrence request to a stage covering the original common index. -/
@[expose] def atStage (request : Request coarse fixed totalTarget) (stage : Nat) (later : request.index ≤ stage)
    (index : Fin partitions.indices.length) :=
  (request.entries.get index).refineIndex stage ((request.index_ge index).trans later)

variable {stage : Nat} {cache : Numerics domains stage}

section
open Purelib.Algebra
open Purelib.Data
/-- Cache the exact local surface budgets from the retained requests and supplied numerical readings.

Every entry uses the original mesh equality and source occurrence at the same later stage; the total is the finite sum
of these exact budgets. -/
@[expose] def budget (request : Request coarse fixed totalTarget) (later : request.index ≤ stage)
    (samples : Samples request.meshes cache) : Samples.Budget samples :=
  let entries := Vector.DependentVector.ofFn fun index =>
    (request.atStage stage later index).surfaceBudgetOn rfl (request.mesh_eq index) (samples.readings.get index)
  ⟨entries, FiniteSum.Fin.sumFin (fun index => (entries.get index).total), rfl⟩

/-- The retained local surface budget total is strictly below the original requested target. -/
theorem budget_total_lt (request : Request coarse fixed totalTarget) (later : request.index ≤ stage)
    (samples : Samples request.meshes cache) : (request.budget later samples).total < totalTarget := by
  rw [(request.budget later samples).total_eq]
  have pointwise (index : Fin partitions.indices.length) :
      ((request.budget later samples).entries.get index).total ≤ request.perPiece := by
    dsimp only [budget]
    rw [Vector.DependentVector.ofFn_get]
    exact ((request.atStage stage later index).surfaceBudgetOn_total_lt rfl (request.mesh_eq index)
      (samples.readings.get index)).le
  have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono _ (fun _ : Fin partitions.indices.length =>
    request.perPiece) pointwise
  rw [FiniteSum.Fin.Rational.sum_constant] at estimate
  exact estimate.trans_lt request.paid

end

open Purelib in
open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- The retained boundary energy controls quarter-coercivity minus the requested homogeneous error.

The stage covers every original model request, and the estimate uses the exact cached local samples and same coefficient
vector. -/
theorem energy_lower (request : Request coarse fixed totalTarget) (later : request.index ≤ stage)
    (samples : Samples request.meshes cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    (observations.energy.lower / 4 - totalTarget) * coefficientNormSq coefficients ≤
      ((request.budget later samples).bound coefficients).boundaryEnergy := by
  let result := (request.budget later samples).bound coefficients
  have nonnegative : 0 ≤ coefficientNormSq coefficients := by
    have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational))
      (fun row => Basic.Canonical.normSq (coefficients row)) (fun row => by
        have scalar := Norm.Basic.normSq_nonneg (coefficients row)
        rw [Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar)
    simpa only [coefficientNormSq, FiniteSum.Fin.sumFin_zero] using estimate
  have bound := result.valid face
  rw [result.lower_eq, result.error_homogeneous] at bound
  have error := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.budget_total_lt later samples).le
    nonnegative
  have estimate := (Fraction.Order.Arithmetic.sub_le_sub_left_direct error
    (observations.energy.lower * coefficientNormSq coefficients / 4)).trans bound
  exact (le_of_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1)).trans estimate

open Purelib.Data.Rat in
/-- Allocate the original local requests at one eighth of the retained observation energy lower coefficient. -/
@[expose] def forPositiveEnergy (coarse : LocalMeshes partitions domains sheet) (fixed : Preflights domains sheet) :
    Request coarse fixed (observations.energy.lower / 8) :=
  build coarse fixed _ (Fraction.Order.Field.div_pos_direct observations.energy.lower_positive (by decide))

open Purelib in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- The original eighth-coercivity term is bounded by the retained local boundary energy. -/
theorem positive_energy (request : Request coarse fixed (observations.energy.lower / 8)) (later : request.index ≤ stage)
    (samples : Samples request.meshes cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face) :
    (observations.energy.lower / 8) * coefficientNormSq coefficients ≤
      ((request.budget later samples).bound coefficients).boundaryEnergy := by
  have estimate := request.energy_lower later samples coefficients face
  have equal : observations.energy.lower / 4 - observations.energy.lower / 8 = observations.energy.lower / 8 := by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    have fractions : (4 : Fraction.Rational)⁻¹ - (8 : Fraction.Rational)⁻¹ = (8 : Fraction.Rational)⁻¹ := by decide
    calc
      _ = observations.energy.lower * ((4 : Fraction.Rational)⁻¹ - (8 : Fraction.Rational)⁻¹) := by ring1
      _ = _ := by rw [fractions]
  rw [equal] at estimate
  exact estimate

end Request

open Purelib.Curves.Hyperelliptic in
set_option genInjectivity false in
/-- The complete retained observation-energy construction with its exact shared numerical cache.

The record keeps the original coarse meshes, lazy preflights, positive-energy request, refined-mesh samples and
dependent budget, with an equality to that request's original budget readback. -/
structure PositiveEnergy (partitions : GridPartitions observations grid)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet : Fin 2) where
  /-- The retained original coarse observation meshes on the same partitions and domains. -/ coarse : LocalMeshes
    partitions domains sheet
  /-- The original lazy preflight bank on the retained regular domains and sheet. -/ fixed : Preflights domains sheet
  /-- The exact local energy request at one eighth of the observation lower coefficient. -/ request : Request coarse
    fixed (observations.energy.lower / 8)
  /-- The shared original numerical bank acquired at the exact retained request stage. -/ numerics : Numerics domains
    request.index
  /-- The basis readings on the request's exact refined meshes from that same numerical cache. -/ samples : Samples
    request.meshes numerics
  /-- The retained dependent local surface budget on these exact samples. -/ budget : Samples.Budget samples
  /-- The retained budget is the exact original request budget at its common stage. -/ budget_eq : budget =
    request.budget (le_refl _) samples

constructive_injectivity PositiveEnergy

namespace PositiveEnergy

open Purelib.Curves.Hyperelliptic in
/-- Build and retain the original coarse meshes, requests, shared numerical cache and certified local energy samples.

The single cache is acquired at the exact common request stage and reused by all samples and their original dependent
budget entries. -/
@[expose] def build (partitions : GridPartitions observations grid) (domains :
  Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet : Fin 2) :
    PositiveEnergy partitions domains sheet :=
  let coarse := LocalMeshes.build partitions domains sheet 0
  let fixed := preflights domains sheet
  let request := Request.forPositiveEnergy coarse fixed
  let cache := LocalMeshes.numerics domains request.index
  let samples := Samples.ofNumerics request.meshes cache
  ⟨coarse, fixed, request, cache, samples, request.budget (le_refl _) samples, rfl⟩

open Purelib in
open Purelib.LinearAlgebra.Gaussian in
/-- The retained certified boundary energy bounds one eighth of the original observation lower coefficient times
coefficient norm squared. -/
theorem lower (prepared : PositiveEnergy partitions domains sheet) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (face : Topology.BranchedCover.Double.Attachment.Face) : (observations.energy.lower / 8) * coefficientNormSq
      coefficients ≤
      (prepared.budget.bound coefficients).boundaryEnergy := by
  rw [prepared.budget_eq]
  exact prepared.request.positive_energy (le_refl _) prepared.samples coefficients face

open Purelib in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- A nonzero original coefficient vector gives strictly positive retained boundary energy. -/
theorem positive (prepared : PositiveEnergy partitions domains sheet) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector
  genus)
    (nonzero : Energy.NonzeroGaussianVector coefficients) (face : Topology.BranchedCover.Double.Attachment.Face) :
    0 < (prepared.budget.bound coefficients).boundaryEnergy :=
  (Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Field.div_pos_direct observations.energy.lower_positive (by decide))
    (PreparedObservationCoercivity.coefficientNormSq_positive nonzero)).trans_le (prepared.lower coefficients face)

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.RootIsolation in
/-- Build positive observation energy on the original branch bank's Newton grid and zero sheet.

The positive target and radius retain the exact constructed preparation, protected observations, partitions, root frames
and original face-domain bank. -/
@[expose] def ofGrid (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) :
    PositiveEnergy
      (GridPartitions.build (ProtectedObservations.build original)
        (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive))
      (Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank.build
        (RootIsolation.SquareRoot.Grid.RootFrames.build (NewtonGrid.build (NewtonPreparation.build original) positive
          radiusPositive).shrunk.prepared.grid)
        (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).faces.regulars)
      0 :=
  PositiveEnergy.build _ _ 0

end PositiveEnergy

namespace PositiveEnergy

open Purelib in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Periods in
/-- An exact identification transports the retained boundary lower bound to the original sampled period energy.

The supplied equality names the actual period data and sample index; it preserves the original coefficient vector and
retained observation lower constant. -/
theorem rawEnergyLower_of_boundaryEnergy_eq
    (prepared : PositiveEnergy partitions domains sheet)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face)
    {data : PeriodMatrix.PeriodData curve} {sampleIndex : Nat}
    (identified : (prepared.budget.bound coefficients).boundaryEnergy =
      Energy.unnormalizedEnergyForm coefficients
        (PeriodMatrix.sampledMatrix data.aMatrix sampleIndex)
        (PeriodMatrix.sampledMatrix data.bMatrix sampleIndex)) :
    observations.energy.lower / 8 * coefficientNormSq coefficients ≤
      Energy.unnormalizedEnergyForm coefficients
        (PeriodMatrix.sampledMatrix data.aMatrix sampleIndex)
        (PeriodMatrix.sampledMatrix data.bMatrix sampleIndex) :=
  identified ▸ prepared.lower coefficients face

end PositiveEnergy
end Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
