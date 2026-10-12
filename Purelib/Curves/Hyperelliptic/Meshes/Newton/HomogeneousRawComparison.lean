module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

@[expose] public section

/-! The squared finite comparison yields a homogeneous scalar raw-energy
inequality, with the actual hole and exterior areas still displayed. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousRawComparison

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {newSheet : Fin 2}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current}
  {magnitudes : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential basis))}
  {error : Fraction.Rational} {floor : Nat}

namespace Request

open Purelib.Data.Rat.Fraction.Compatibility

variable {allowance : Fraction.Rational}
  {request : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance / 4) floor}
  {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) current.mesh)}
  {surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces current.cutPolygon.patch (fun basis =>
    (triangles.get basis).values)}
  {pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces}

open Purelib.Algebra in
open Purelib.Integration in
/-- The finite coefficient combination satisfies a homogeneous raw-energy lower bound.

The positive allowance pays the squared comparison error at the common cut stage. The actual hole contribution and twice
the exterior contribution remain in the displayed boundary energy. -/
theorem Samples.raw_lower (samples : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles
  surfaces pairs request)
    {minimum : Nat} (cut : Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request.CutRequest request
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance / 4)
      minimum)
    (later : cut.index ≤ stage) (positive : 0 < allowance)
    (holes : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles excision)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    let values := fun basis => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
      (triangles.get basis).values
    let aMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared grid.shrunk.included current.edges
      current.vertices newSheet values false
    let bMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared grid.shrunk.included current.edges
      current.vertices newSheet values true
    (Topology.Surface.Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + holes.area coefficients - 2 *
      samples.exterior coefficients).im / 4 -
      allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
        LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients aMatrix bMatrix := by
  intro values aMatrix bMatrix
  let target := Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance
  let period := Energy.Polygon.energyBoundaryArea
    (LinearAlgebra.Gaussian.Energy.periodCombination coefficients aMatrix)
      (LinearAlgebra.Gaussian.Energy.periodCombination coefficients bMatrix)
  have close := Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.Samples.physical_accurate samples cut
    later holes coefficients
  have coefficientSumEq :
      (FiniteSum.Fin.sumFin fun basis => Data.Gaussian.Norm.Basic.normSq (coefficients basis)) =
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    unfold Readings.PreparedObservationCoercivity.coefficientNormSq
    apply FiniteSum.Fin.sumFin_congr
    intro basis
    exact Gaussian.Norm.Basic.normSq_eq_canonical (coefficients basis)
  rw [coefficientSumEq] at close
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun basis => Gaussian.Norm.Basic.normSq_nonneg (coefficients basis))
    rw [FiniteSum.Fin.sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients basis))]
      at estimate
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le estimate
  have allocation : 2 * (target / 4 + target / 4) = target :=
    (by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))
  have paid : 2 * (genus : Fraction.Rational)^2 * Readings.PreparedObservationCoercivity.coefficientNormSq
    coefficients^2 * (target / 4 + target / 4) ≤
      (4 * (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    calc
      _ = ((genus : Fraction.Rational)^2 * (2 * (target / 4 + target / 4))) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients^2 := by
        ring1
      _ = ((genus : Fraction.Rational)^2 * target) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients^2 := by
        rw [allocation]
      _ ≤ (4 * allowance)^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients^2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid positive)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have scalar (surface holes exterior period : Gaussian.Basic.Canonical) :
      surface + holes - 2 * exterior - period = surface + holes - (period + 2 * exterior) := by ring1
  have squared : Data.Gaussian.Norm.Basic.normSq ((Topology.Surface.Sewing.SewnEnergyCombination.energyBoundary
    surfaces coefficients + holes.area coefficients -
      2 * samples.exterior coefficients) - period) ≤ (4 * (allowance *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    rw [scalar]
    change Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + holes.area coefficients -
        (period + 2 * samples.exterior coefficients)) ≤
      2 * (genus : Fraction.Rational)^2 *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients^2 * (target / 4 + target / 4) at close
    exact close.trans paid
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (Topology.Surface.Sewing.SewnEnergyCombination.energyBoundary surfaces coefficients + holes.area coefficients - 2 *
      samples.exterior coefficients)
    period (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct positive.le normNonnegative) squared
  unfold LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm
  rw [Energy.Polygon.periodPairingEnergy_eq_boundaryArea_im_div_four]
  exact comparison

end Request
end Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousRawComparison
