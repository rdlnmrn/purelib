module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
public import Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

/-! The actual sewn complement replaces the full surface plus its cached
physical hole polygons, uniformly over coefficient vectors on one annular tail. -/

namespace Purelib.Riemann.RootContinuation.NewtonHomogeneousRemainingComparison

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision
  (OuterPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs energyBoundary
  energyBoundary_pairs)
open Purelib.Topology.Surface.Sewing.SewnSelectedEnergy (SelectedEnergySamples)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (sourceMask)
open Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest.HomogeneousAnnularRequest (Request Samples)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request (HoleSamples)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_paid)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Rational}
  {family : FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid family.single.grid.punctured}
  {excision : AllHoleExcision family.single.grid lifted}
  {domains : FaceDomainBank lifted.frames
    family.single.grid.faces.regulars}
  {prepared :
    OuterPreparations
    excision}

namespace HomogeneousAnnularRequest

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {floor stage : Nat} {cache :
  Numerics domains stage}
  {triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
    TriangleReadings (cache.get basis) lifted.mesh)}
  {surfaces : EnergySurfaces lifted.cutPolygon.patch (fun basis =>
    (triangles.get basis).values)}
  {pairs : EnergyPairs surfaces} {request : Request (domains :=
    domains) prepared floor}

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Bound a remaining conjugate basis-pair area against the full sewn boundary and retained holes.

Beyond the common annular request stage, the squared discrepancy is at most 82/4 times the target, using the original
selected triangles and physical hole samples. -/
private theorem pair_remaining_bound (samples : Samples triangles surfaces pairs request) (later : request.index ≤
  stage)
    (selected : SelectedEnergySamples surfaces pairs
      (fun source => !(excision.entries.any (fun entry => sourceMask entry source))))
    (holes : HoleSamples (base := base) (grid :=
      family.single.grid) (current := lifted) triangles excision) (first second : Fin genus) :
    normSq (selected.areas first second - (((pairs.get first).get second).boundaryArea +
      holes.values first second)) ≤
      (82 / 4 : Rational) * target := by
  let sample := (samples.get first).get second
  let retained := Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateSample.Excision.build sample
  have area : selected.areas first second = retained.remainingArea :=
    (selected.area_readback first second retained.retained.remaining).trans retained.remainingArea_eq.symm
  have hole : holes.values first second = sample.holes := (holes.values_eq first second).trans
    sample.holes_readback.symm
  rw [area, hole, retained.remaining_difference, normSq_neg]
  exact (((request.entries.get first).get second).accurate stage cache (triangles.get first) (triangles.get second)
    (surfaces.get first) (surfaces.get second) ((pairs.get first).get second) sample
    ((request.index_ge first second).trans later)).le

open Purelib.Algebra
open Purelib.Riemann
open Purelib.Curves
open Purelib.Topology
open Purelib.Data
open Purelib.LinearAlgebra
/-- Bound the selected complement's energy against the full sewn energy and physical hole area.

The estimate is homogeneous in the coefficient squared norm and uses one retained annular tail for every basis pair. -/
theorem Samples.remaining_accurate (samples : Samples triangles surfaces pairs request) (later : request.index ≤ stage)
    (selected : SelectedEnergySamples surfaces pairs
      (fun source => !(excision.entries.any (fun entry => sourceMask entry source))))
    (holes : HoleSamples (base := base) (grid :=
      family.single.grid) (current := lifted) triangles excision) (coefficients :
        Gaussian.Energy.GaussianVector
      genus) :
    normSq (selected.energy coefficients -
      (Surface.Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + holes.area coefficients)) ≤
      (genus : Rational)^2 * coefficientNormSq coefficients^2 * ((82 / 4 : Rational) * target)
        := by
  rw [Surface.Sewing.SewnEnergyCombination.energyBoundary_pairs surfaces pairs coefficients]
  unfold SelectedEnergySamples.energy
    HoleSamples.area
  rw [← sumFin_add, ← sumFin_sub]
  have scalar := sumFin_congr fun first => show
      sumFin (fun second => conj (coefficients first) * coefficients second *
        selected.areas first second) -
        (sumFin (fun second => conj (coefficients first) * coefficients second *
          ((pairs.get first).get second).boundaryArea) +
          sumFin (fun second => conj (coefficients first) * coefficients second *
            holes.values first second)) =
      sumFin (fun second => conj (coefficients first) * coefficients second *
        (selected.areas first second - (((pairs.get first).get second).boundaryArea + holes.values first second))) by
    rw [← sumFin_add, ← sumFin_sub]
    apply sumFin_congr
    intro second
    ring1
  rw [scalar]
  have estimate := Periods.BilinearCombination.combination_bound (fun basis => conj
    (coefficients basis)) coefficients _
    (pair_remaining_bound samples later selected holes)
  rw [sumFin_congr (fun basis => normSq_conj (coefficients basis))] at estimate
  rw [sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_eq_canonical
    (coefficients basis))] at estimate
  exact estimate.trans_eq (by unfold coefficientNormSq; ring1)

/-- Pay the annular replacement by a coefficient-independent scalar allowance.

The resulting energy loss is allowance times the coefficient squared norm; an arbitrary common exterior offset is
retained on both sides. -/
theorem Samples.remaining_sub_energy_lower (samples : Samples triangles surfaces pairs request) (later : request.index ≤
  stage)
    (selected : SelectedEnergySamples surfaces pairs
      (fun source => !(excision.entries.any (fun entry => sourceMask entry source))))
    (holes : HoleSamples (base := base) (grid :=
      family.single.grid) (current := lifted) triangles excision) (coefficients :
        Gaussian.Energy.GaussianVector
      genus)
    {allowance : Rational} (positive : 0 < allowance)
    (paid : (82 / 4 : Rational) * target ≤
      Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance) (offset :
      Gaussian.Basic.Canonical) :
    (selected.energy coefficients - offset).im / 4 - allowance * coefficientNormSq coefficients ≤
      (Surface.Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + holes.area coefficients - offset).im
        / 4 := by
  have nonnegative : 0 ≤ coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Rational)) _
      (fun basis => Gaussian.Norm.Basic.normSq_nonneg (coefficients basis))
    rw [sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients basis))] at bound
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  have bound := Samples.remaining_accurate samples later selected holes coefficients
  have payment : (genus : Rational)^2 * coefficientNormSq coefficients^2 * ((82 / 4 :
    Rational) * target) ≤
      (4 * (allowance * coefficientNormSq coefficients))^2 := by
    calc
      _ ≤ (genus : Rational)^2 * coefficientNormSq coefficients^2 *
        Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct paid
          (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
          (Arithmetic.sq_nonneg_direct _))
      _ = ((genus : Rational)^2 *
        Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance) *
        coefficientNormSq coefficients^2 := by
        ring1
      _ ≤ (4 * allowance)^2 * coefficientNormSq coefficients^2 :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid positive)
          (Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have scalar (remaining whole holes offset : Gaussian.Basic.Canonical) :
      (remaining - offset) - (whole + holes - offset) = remaining - (whole + holes) := by ring1
  exact Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le _ _ _
    (Arithmetic.mul_nonneg_direct positive.le nonnegative)
    (by rw [scalar]; exact bound.trans payment)

end HomogeneousAnnularRequest
end Purelib.Riemann.RootContinuation.NewtonHomogeneousRemainingComparison
