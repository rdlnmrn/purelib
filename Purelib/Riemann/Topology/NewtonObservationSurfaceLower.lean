module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Content
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonObservationSurfaceArea
import Purelib.Tactic.Ring

public section

/-!
# Transfer of observation positivity to the complete regular surface

Each observation density contributes on its certified inside pieces. Exact
area recovery transfers the original homogeneous observation lower sum.
Summing the per-observation inequalities costs only the finite genus factor;
no unproved identification of local observation boundaries with periods is
used here.
-/

namespace Purelib.Riemann.Topology.NewtonObservationSurfaceLower

open Purelib.LinearAlgebra.Gaussian

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
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2} {stage : Nat}
  {cache : Numerics domains stage}

open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian.Energy in
/-- The original observation's numerator lower bound divided by its retained denominator scale. -/
@[expose] def observationDensity (observations : ProtectedObservations original)
    (coefficients : Energy.GaussianVector genus) (site : Fin genus) : Rat.Fraction.Rational :=
  observations.energy.original.boxes.numeratorLower coefficients site /
    observations.energy.original.boxes.denominatorScale

namespace SurfacePartition.LocalMeshes.Samples

variable {position : Fin grid.faces.regulars.length} {partition : SurfacePartition observations grid position}
  {meshes : Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy.LocalMeshes partition domains sheet}

open Purelib.Geometry.Rational.Box in
open Purelib.LinearAlgebra.Gaussian.Energy in
open Purelib.Riemann.Readings.AffineBasisEnergy in
open Purelib.Riemann.Topology.NewtonObservationSurfaceArea in
open Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy in
open Purelib.Riemann.Topology.PreparedSurfacePartitions in
open Purelib.Topology.BranchedCover.Double in
/-- A certified observation piece contributes its density-weighted area to the actual affine energy.

Inside pieces use the retained observation cell; outside pieces have zero observation area and consume nonnegativity of
the same sampled affine basis. -/
theorem observation_lower (samples : LocalMeshes.Samples meshes cache) (piece : Fin partition.cuts.boxes.length)
    (budget : AffineBasis.SurfaceBudget (samples.readings.get piece).affine)
    (coefficients : Energy.GaussianVector genus) (face : Attachment.Face) (site : Fin genus) :
    SurfacePartition.observationArea partition site piece * (observationDensity observations coefficients site / 4) ≤
      (budget.sample coefficients).affineEnergy := by
  generalize placementEq : (partition.placements.get piece).get site = placement
  cases placement with
  | inside contained =>
      have area : SurfacePartition.observationArea partition site piece =
          Content.boxContent (partition.cuts.boxes[piece.val]'piece.isLt) := by
        unfold SurfacePartition.observationArea
        rw [placementEq]
      rw [area]
      let cell := BoxPartition.restrictCell
        (observations.energy.surfaceCell coefficients face site)
        (partition.cuts.boxes[piece.val]'piece.isLt) (partition.cuts.proper (List.getElem_mem piece.isLt)) contained
      exact (samples.readings.get piece).affineEnergy_lower budget coefficients cell rfl
  | outside separated =>
      have area : SurfacePartition.observationArea partition site piece = 0 := by
        unfold SurfacePartition.observationArea
        rw [placementEq]
      rw [area, zero_mul]
      exact samples.piece_affine_nonnegative piece budget coefficients

end SurfacePartition.LocalMeshes.Samples

open Purelib.Data in
/-- The positive observation margin divided by four and by the genus plus one.

This coefficient-independent surface constant remains defined and positive for an empty basis. -/
@[expose] def surfaceLowerConstant (observations : ProtectedObservations original) : Rat.Fraction.Rational :=
  (observations.energy.lower / 4) / ((genus : Rat.Fraction.Rational) + 1)

open Purelib.Data.Rat.Fraction.Cast in
open Purelib.Data.Rat.Fraction.Order in
/-- The retained surface observation margin is strictly positive. -/
theorem surfaceLowerConstant_positive (observations : ProtectedObservations original) :
    0 < surfaceLowerConstant observations :=
  Field.div_pos_direct
    (Field.div_pos_direct observations.energy.lower_positive (by decide))
    (Arithmetic.add_pos_of_nonneg_of_pos_direct (Order.natCast_le_direct (Nat.zero_le genus)) (by decide))

namespace SurfaceRequest

variable {partitions : SurfacePartitions observations grid} {coarse : SurfaceMeshes partitions domains sheet}
  {fixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {error :
    Purelib.Data.Rat.Fraction.Rational}
  {request : SurfaceRequest partitions coarse fixed error} {samples : request.Readings cache}

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.LinearAlgebra.Gaussian.Energy in
open Purelib.Riemann in
open Purelib.Riemann.Topology.NewtonObservationSurfaceArea in
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower.SurfacePartition.LocalMeshes in
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy in
open Purelib.Topology.BranchedCover.Double in
/-- Transfer the complete observation lower sum to the retained regular-surface affine energy.

Exact recovery of each observation area and its certified inside pieces pays the original homogeneous lower bound, with
the finite genus factor from summing site inequalities. -/
theorem Budget.observation_lower (budget : SurfaceRequest.Budget request samples) (coefficients : Energy.GaussianVector
  genus)
    (face : Attachment.Face) :
    observations.energy.lower * coefficientNormSq coefficients / 4 ≤
      (genus : Rat.Fraction.Rational) * FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        (((budget.entries.get position).get piece).sample coefficients).affineEnergy)) := by
  have siteBound (site : Fin genus) :
      observations.energy.area * (observationDensity observations coefficients site / 4) ≤
        FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => (((budget.entries.get position).get
          piece).sample coefficients).affineEnergy)) := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun position =>
      FiniteSum.Rational.Order.Positivity.sumFin_mono _ _
      (fun piece => Samples.observation_lower (samples.get position) piece ((budget.entries.get position).get piece)
        coefficients face site))
    have area : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      SurfacePartition.observationArea (partitions.get position) site piece *
        (observationDensity observations coefficients site / 4))) =
        observations.energy.area * (observationDensity observations coefficients site / 4) := by
      rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_mul_right (SurfacePartition.observationArea
        (partitions.get position) site) _),
        FiniteSum.Fin.sumFin_mul_right, Topology.NewtonObservationSurfaceArea.surface_observation_area]
    exact (le_of_eq area.symm).trans bound
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ siteBound
  rw [FiniteSum.Fin.Rational.sum_constant] at bound
  have original := observations.uniform_lower coefficients face
  rw [observations.energy.surfaceEnergy_eq] at original
  have divided := Arithmetic.mul_le_mul_of_nonneg_right_direct original
    (show (0 : Rat.Fraction.Rational) ≤ (4 : Rat.Fraction.Rational)⁻¹ by decide)
  have equal : FiniteSum.Fin.sumFin (fun site => observations.energy.area * (observationDensity observations
    coefficients site / 4)) =
      (observations.energy.area * FiniteSum.Fin.sumFin (fun site => observationDensity observations coefficients site))
        * (4 : Rat.Fraction.Rational)⁻¹ := by
    rw [FiniteSum.Fin.sumFin_congr (fun site => show observations.energy.area * (observationDensity observations
      coefficients site / 4) =
      (observations.energy.area * observationDensity observations coefficients site) * (4 : Rat.Fraction.Rational)⁻¹
        from by
        rw [Fraction.Field.div_eq_mul_inv_direct]; ring1), FiniteSum.Fin.sumFin_mul_right,
          FiniteSum.Fin.sumFin_mul_left]
  rw [equal] at bound
  exact divided.trans bound

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Cast in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.LinearAlgebra.Gaussian.Energy in
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy in
open Purelib.Topology.BranchedCover.Double in
/-- The complete regular surface has the retained homogeneous affine-energy lower bound.

Nonnegative piece energies and the genus-plus-one denominator transfer the observation estimate for every coefficient
vector, including an empty basis. -/
theorem Budget.affine_lower (budget : SurfaceRequest.Budget request samples) (coefficients : Energy.GaussianVector
  genus)
    (face : Attachment.Face) :
    surfaceLowerConstant observations * coefficientNormSq coefficients ≤
      FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        (((budget.entries.get position).get piece).sample coefficients).affineEnergy)) := by
  let energy := FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
    (((budget.entries.get position).get piece).sample coefficients).affineEnergy))
  have nonnegative : 0 ≤ energy := by
    have inner (position : Fin grid.faces.regulars.length) := FiniteSum.Rational.Order.Positivity.sumFin_mono
      (fun _ => (0 : Rat.Fraction.Rational)) _ (fun piece =>
        (samples.get position).piece_affine_nonnegative piece ((budget.entries.get position).get piece) coefficients)
    have nonnegativeInner (position : Fin grid.faces.regulars.length) : 0 ≤ FiniteSum.Fin.sumFin (fun piece =>
        (((budget.entries.get position).get piece).sample coefficients).affineEnergy) :=
      (FiniteSum.Fin.sumFin_zero).symm.trans_le (inner position)
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Rat.Fraction.Rational)) _ nonnegativeInner)
  have factorPositive : 0 < (genus : Rat.Fraction.Rational) + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (Order.natCast_le_direct (Nat.zero_le genus)) (by decide)
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := (genus : Rat.Fraction.Rational) + 1) _ factorPositive
  calc
    _ = (surfaceLowerConstant observations * ((genus : Rat.Fraction.Rational) + 1)) * coefficientNormSq coefficients :=
      by
      ring1
    _ = (observations.energy.lower / 4) * coefficientNormSq coefficients := by
      rw [surfaceLowerConstant, Fraction.Field.div_mul_cancel_of_ne _ _ factorPositive.ne']
    _ = observations.energy.lower * coefficientNormSq coefficients / 4 := by
      rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]; ring1
    _ ≤ (genus : Rat.Fraction.Rational) * energy := observation_lower budget coefficients face
    _ ≤ ((genus : Rat.Fraction.Rational) + 1) * energy := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_right (by decide)) nonnegative
    _ = _ := by ring1

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.LinearAlgebra.Gaussian.Energy in
open Purelib.Riemann.Topology.NewtonObservationSurfaceLower.SurfaceRequest in
open Purelib.Topology.BranchedCover.Double in
/-- Transfer the observation margin to the complete retained boundary sum after paying its requested error.

All regular pieces use the same numerical cache, coefficient vector and request stage. The coefficient norm multiplies
both the original positive margin and the actual aggregate error allowance. -/
theorem boundary_lower (request : SurfaceRequest partitions coarse fixed error) (later : request.index ≤ stage)
    (samples : request.Readings cache) (coefficients : Energy.GaussianVector genus) (face : Attachment.Face) :
    (surfaceLowerConstant observations - error) * coefficientNormSq coefficients ≤
      FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        ((((request.budget later samples).entries.get position).get piece).sample coefficients).boundaryArea.im / 4)) :=
          by
  let budget := request.budget later samples
  have boundary := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun position =>
    FiniteSum.Rational.Order.Positivity.sumFin_mono _ _
    (fun piece => ((budget.entries.get position).get piece).energy_lower coefficients))
  have errorSum : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      coefficientNormSq coefficients * ((budget.entries.get position).get piece).total)) =
      coefficientNormSq coefficients * budget.total := by
    rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_mul_left _ (fun piece => ((budget.entries.get
      position).get piece).total)),
      FiniteSum.Fin.sumFin_mul_left, budget.total_eq]
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_sub _ _),
    FiniteSum.Fin.sumFin_sub, errorSum] at boundary
  have positive := Budget.affine_lower budget coefficients face
  have normNonnegative : 0 ≤ coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Rat.Fraction.Rational))
      (fun row => Basic.Canonical.normSq (coefficients row))
      (fun row => Basic.Canonical.normSq_nonneg (coefficients row))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct (request.budget_total_lt later samples).le normNonnegative
  have lower := (Arithmetic.sub_le_sub_direct positive paid).trans boundary
  exact (le_of_eq (by ring1)).trans lower

end SurfaceRequest
end Purelib.Riemann.Topology.NewtonObservationSurfaceLower
