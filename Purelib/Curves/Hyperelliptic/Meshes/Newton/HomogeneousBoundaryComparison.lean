module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
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
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
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

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Integration

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.Polynomial

open Purelib.Riemann

public section

/-! Pay all cut corrections in the homogeneous period comparison. The
remaining signed expression contains the cached exterior and actual holes. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

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

open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}
  (triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) current.mesh))
  {surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces current.cutPolygon.patch (fun basis =>
    (triangles.get basis).values)}
  {pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces}
  {request : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes
    error floor}

set_option genInjectivity false in
/-- Evaluate each pair's physical-hole sum once; coefficient combinations
consume these cached values rather than retraversing the hole polygons. -/
structure HoleSamples (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current) where
  /-- The cached matrix of original pairwise physical-hole area totals. -/ values :
    LinearAlgebra.Gaussian.Energy.GaussianMatrix genus
  /-- Each matrix entry is the exact original conjugate physical-hole sum for its two retained basis readings. -/
    values_eq : ∀ first second, values first second =
    Geometry.Grid.CellBoundary.sumValues (fun entry => entry.conjugatePhysicalHoleArea (triangles.get first)
      (triangles.get second)) excision.entries

constructive_injectivity HoleSamples

/-- Evaluate and cache each original pairwise physical-hole total with its exact matrix readback. -/
@[expose] def HoleSamples.build (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
  : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles excision :=
  ⟨matrixOfFn (fun first second => Geometry.Grid.CellBoundary.sumValues
    (fun entry => entry.conjugatePhysicalHoleArea (triangles.get first) (triangles.get second)) excision.entries),
    fun first second => SquareMatrix.matrixOfFn_apply _ first second⟩

variable {triangles}

/-- Combine the cached original hole totals with the supplied conjugate coefficient products. -/
@[expose] def HoleSamples.area (holes : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples
  triangles excision) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients first)
    * coefficients second * holes.values first second

/-- The same common index pays the full coefficient-weighted cut correction
and the positive physical-hole polygons, with all pair multiplicities counted. -/
theorem Samples.cut_accurate (samples : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples
  triangles surfaces pairs request)
    {bound : Fraction.Rational} {minimum : Nat} (cut :
      Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request.CutRequest request bound minimum) (later : cut.index ≤
      stage)
    (holes : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles excision)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (samples.correction coefficients + holes.area coefficients) ≤
      (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun basis => Data.Gaussian.Norm.Basic.normSq
        (coefficients basis)))^2 * bound := by
  let residual := fun first second => ((samples.get first).get second).correction + holes.values first second
  have bounded (first second : Fin genus) : Data.Gaussian.Norm.Basic.normSq (residual first second) ≤ bound := by
    change Data.Gaussian.Norm.Basic.normSq (((samples.get first).get second).correction + holes.values first second)
      ≤ bound
    rw [holes.values_eq first second]
    exact (((cut.entries.get first).get second).property.2 stage cache
      (triangles.get first) (triangles.get second) (surfaces.get first) (surfaces.get second)
      ((pairs.get first).get second) ((samples.get first).get second)
      ((cut.index_ge first second).trans later)).le
  have estimate := Periods.BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj
    (coefficients basis))
    (fun basis => coefficients basis) residual bounded
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at estimate
  have read : samples.correction coefficients + holes.area coefficients =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) * coefficients second * residual first second)) := by
    have expanded := FiniteSum.Fin.sumFin_congr fun first : Fin genus => FiniteSum.Fin.sumFin_congr fun second : Fin
      genus => show
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second * residual first second =
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
          second).correction +
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second * holes.values first second by
      unfold residual
      ring1
    exact (expanded.trans (by simp only [FiniteSum.Fin.sumFin_add]; rfl)).symm
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_le (estimate.trans_eq (by ring1))

/-- All original cut corrections have now been paid. The physical holes and
exterior remain on their actual samples, with the corrected A/B matrices. -/
theorem Samples.physical_accurate (samples : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples
  triangles surfaces pairs request)
    {bound : Fraction.Rational} {minimum : Nat} (cut :
      Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request.CutRequest request bound minimum) (later : cut.index ≤
      stage)
    (holes : Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.HoleSamples triangles excision)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    let values := fun basis => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
      (triangles.get basis).values
    let aMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared grid.shrunk.included current.edges
      current.vertices newSheet values false
    let bMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared grid.shrunk.included current.edges
      current.vertices newSheet values true
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewnEnergyCombination.energyBoundary surfaces
      coefficients + holes.area coefficients -
      (Energy.Polygon.energyBoundaryArea (LinearAlgebra.Gaussian.Energy.periodCombination coefficients aMatrix)
        (LinearAlgebra.Gaussian.Energy.periodCombination coefficients bMatrix) + 2 * samples.exterior coefficients)) ≤
      2 * (genus : Fraction.Rational)^2 * (FiniteSum.Fin.sumFin (fun basis => Data.Gaussian.Norm.Basic.normSq
        (coefficients basis)))^2 * (error + bound) := by
  intro values aMatrix bMatrix
  have period := Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples.period_accurate samples
    (cut.period_le.trans later) coefficients
  have correction := Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison.Request.Samples.cut_accurate samples cut
    later holes coefficients
  have scalar (surface correction holes period exterior : Gaussian.Basic.Canonical) :
      surface + holes - (period + 2 * exterior) =
        (surface - correction - (period + 2 * exterior)) + (correction + holes) := by ring1
  rw [scalar _ (samples.correction coefficients)]
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct period
      correction) (by decide))
  exact estimate.trans_eq (by ring1)

end Request
end Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousBoundaryComparison
