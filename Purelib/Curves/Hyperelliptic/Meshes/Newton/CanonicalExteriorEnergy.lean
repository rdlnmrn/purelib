module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Integration.Path.PairedEnergyCombination
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

open Purelib.Topology.Polygon

public section

/-! Homogeneous comparison with actual canonical exterior polygons in either degree shape. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.CanonicalExteriorEnergy
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request (Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
open Purelib.Integration.Path.PairedEnergyCombination (component_areas_energy_combination)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_mul_left)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars}
  {newSheet : Fin 2} {excision : AllHoleExcision grid
    current}
  {magnitudes : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential basis))}
  {error : Rational} {floor stage : Nat}
  {cache : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential basis) stage domains)}
  {triangles : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    TriangleReadings (cache.get basis)
    current.mesh)}
  {surfaces : EnergySurfaces current.cutPolygon.patch (fun basis
    => (triangles.get basis).values)}
  {pairs : EnergyPairs surfaces}
  {request : Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision
    magnitudes error floor}

/-- Pairwise comparison budgets are independent of the coefficient vector. The contraction retains all canonical
component polygons and terminal-product errors. -/
theorem Samples.exterior_components_bound (samples : HomogeneousPhysicalComparison.Request.Samples triangles surfaces
  pairs request)
    {pairBound : Fraction.Rational}
    (bounded : ∀ first second,
      Data.Gaussian.Norm.Basic.normSq (2 * ConjugatePhysicalRequest.exterior (paired := paired) newSheet
        (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values)
        (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
          PairedIncrementArea.area (word.map (fun edge =>
            (⟨conj (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values edge),
              CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values edge⟩ :
                Stokes.PrimitivePoint)))))) ≤ pairBound)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (2 * samples.exterior coefficients -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge)))))) ≤
      (genus : Fraction.Rational) ^ 2 * Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients ^ 2 * pairBound := by
  let residual := fun first second => 2 * ((samples.get first).get second).exterior -
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
          PairedIncrementArea.area (word.map (fun edge =>
            (⟨conj (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values edge),
              CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values edge⟩ :
                Stokes.PrimitivePoint)))))
  have bounds (first second : Fin genus) : Data.Gaussian.Norm.Basic.normSq (residual first second) ≤ pairBound
    := by
    dsimp only [residual]
    rw [((samples.get first).get second).exterior_eq]
    exact bounded first second
  have estimate := BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj (coefficients
    basis)) coefficients residual bounds
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Data.Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at estimate
  have expanded : FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
    Data.Gaussian.Basic.conj (coefficients first) * coefficients second * residual first second)) =
      2 * samples.exterior coefficients - Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map
        (fun word =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge))))) := by
    calc
      _ = FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
        2 * (Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
          second).exterior) -
          Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
            Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
          PairedIncrementArea.area (word.map (fun edge =>
            (⟨conj (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values edge),
              CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values edge⟩ :
                Stokes.PrimitivePoint))))))) := by
        apply FiniteSum.Fin.sumFin_congr
        intro first
        apply FiniteSum.Fin.sumFin_congr
        intro second
        dsimp only [residual]
        ring1
      _ = _ := by
        simp only [-eq_self, -iff_self, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_mul_left]
        exact congrArg (2 * samples.exterior coefficients - ·)
          (PairedEnergyCombination.component_areas_energy_combination coefficients
            (fun row edge => CanonicalEdgeValues.edgeValuation current.mesh (triangles.get row).values edge)
            current.exteriorBoundaries).symm
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients basis))]
    at estimate
  exact (congrArg Data.Gaussian.Norm.Basic.normSq expanded.symm).trans_le (estimate.trans_eq (by
    unfold PreparedObservationCoercivity.coefficientNormSq; ring1))

/-- A scalar budget on the basis pairs pays the energy comparison uniformly, including the zero coefficient vector. -/
theorem Samples.exterior_components_energy_upper (samples : HomogeneousPhysicalComparison.Request.Samples triangles
  surfaces pairs request)
    {pairBound allowance : Fraction.Rational}
    (bounded : ∀ first second,
      Data.Gaussian.Norm.Basic.normSq (2 * ConjugatePhysicalRequest.exterior (paired := paired) newSheet
        (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values)
        (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
          PairedIncrementArea.area (word.map (fun edge =>
            (⟨conj (CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values edge),
              CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values edge⟩ :
                Stokes.PrimitivePoint)))))) ≤ pairBound)
    (nonnegative : 0 ≤ allowance) (paid : (genus : Fraction.Rational) ^ 2 * pairBound ≤ 16 * allowance ^ 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (2 * samples.exterior coefficients - Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map
      (fun word =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge)))))).im / 4 ≤
      allowance * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have close := Curves.Hyperelliptic.Meshes.Newton.CanonicalExteriorEnergy.Samples.exterior_components_bound samples
    bounded coefficients
  have payment := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct (PreparedObservationCoercivity.coefficientNormSq coefficients))
  have scaled : (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
    pairBound ≤
      (4 * (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    calc
      _ = ((genus : Fraction.Rational) ^ 2 * pairBound) * PreparedObservationCoercivity.coefficientNormSq coefficients ^
        2 := by
        ring1
      _ ≤ (16 * allowance ^ 2) * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := payment
      _ = _ := by ring1
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Data.Gaussian.Norm.Basic.normSq_nonneg (coefficients row))
    rw [FiniteSum.Fin.sumFin_congr (fun row => Data.Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))]
      at bound
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  let residual := 2 * samples.exterior coefficients - Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (current.exteriorBoundaries.map (fun word =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge)))))
  have squared : Data.Gaussian.Norm.Basic.normSq (residual - 0) ≤ (4 * (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    rewrite [Data.Gaussian.Basic.sub_zero]
    exact close.trans scaled
  have bound := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le residual 0
    (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative normNonnegative) squared
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct bound (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)
  have left : residual.im / 4 - allowance * PreparedObservationCoercivity.coefficientNormSq coefficients + allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients = residual.im / 4 := by ring1
  rw [left] at shifted
  exact shifted.trans_eq (by
    change (0 : Fraction.Rational) / 4 + _ = _
    rw [show (0 : Fraction.Rational) / 4 = 0 by decide, Fraction.Field.zero_add])

end Purelib.Curves.Hyperelliptic.Meshes.Newton.CanonicalExteriorEnergy
