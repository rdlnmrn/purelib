module
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Integration.PrimitiveBasis
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Periods.AffineBasisBilinear
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration.PrimitiveBasis

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.AffineBasisBilinear

open Purelib.Topology.Polygon

@[expose] public section

/-! The existing domain request pays the actual two-differential boundary
error on its own shared mesh. No second spatial or root preparation is needed. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy (BasisReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest (EnergyRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {domain : PeriodDomain models sheet} {box :
    Box}
  {preflight : EnergyPreflight domain} {coarse :
    ObservationMesh domain.cuts box} {target : Coordinate}
  {stage : Nat} {cached : (row : Fin genus) →
    DomainPrimitives domain
    (PeriodMatrix.standardDifferential row) stage}

/-- Build the paired affine-boundary budget on the exact retained surface budget and cached basis readings. -/
def bilinearBudget
    (request : DomainEnergyRequest.EnergyRequest preflight coarse target) (stage_eq : stage =
      request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface) : AffineBasisBilinear.BilinearBudget
      (request.surfaceBudget stage_eq readings) :=
  BilinearBudget.build (request.surfaceBudget stage_eq readings)

/-- The full growing face count is already paid by the energy request. The squared wedge allowance is quadratic in that
requested energy tolerance. -/
theorem
  bilinearBudget_total_lt
    (request : DomainEnergyRequest.EnergyRequest preflight coarse target) (stage_eq : stage =
      request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface) :
    (request.bilinearBudget stage_eq readings).total < 64 * target ^ 2 := by
  let budget := request.surfaceBudget stage_eq readings
  have uniform (index : Fin (request.mesh.triangles.map ModelTriangle.triangle).length) :
      (budget.triangles.get index).total = request.tolerance.epsilon * request.distance * (2 *
        preflight.coefficientScale + 3) := by
    dsimp only [budget, EnergyRequest.surfaceBudget]
    rw [DependentVector.ofFn_get, request.triangleBudget_total]
  have estimate := (request.bilinearBudget stage_eq readings).total_le_energy_sq _ uniform
  have bounded := request.surfaceBudget_total_lt stage_eq readings
  have squares : budget.total ^ 2 < target ^ 2 := by
    have first := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bounded.le
      (SurfaceBudget.total_nonnegative budget)
    have last := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct request.target_positive bounded
    exact (le_of_eq (by ring1)).trans_lt ((first.trans_lt last).trans_eq (by ring1))
  exact estimate.trans_lt (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide +kernel : (0 : Coordinate) < 64) squares)

/-- Both primitive combinations are read from the supplied domain bank. The result also covers zero coefficient vectors
without a fixed error floor. -/
theorem bilinear_bound
    (request : DomainEnergyRequest.EnergyRequest preflight coarse target) (stage_eq : stage =
      request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus)
      :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
      (fun vertex => ⟨readings.affine.value left vertex, readings.affine.value right vertex⟩)
      request.mesh.surface.mesh.triangulation.boundary) ≤
      coefficientNormSq left * coefficientNormSq right * (64 * target ^ 2) :=
  (request.bilinearBudget stage_eq readings).boundary_bound left right |>.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.bilinearBudget_total_lt stage_eq readings).le
      (Fraction.Order.Arithmetic.mul_nonneg_direct
      (coefficientNorm_nonnegative left)
        (coefficientNorm_nonnegative right)))

/-- Consume a mesh already retained by a surrounding synchronized bank. -/
theorem bilinear_bound_on
    (request : DomainEnergyRequest.EnergyRequest preflight coarse target) (stage_eq : stage =
      request.modelRequest.index)
    {mesh : ObservationMesh domain.cuts box} (equal : mesh = request.mesh)
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
      (fun vertex => ⟨readings.affine.value left vertex, readings.affine.value right vertex⟩)
      mesh.surface.mesh.triangulation.boundary) ≤
      coefficientNormSq left * coefficientNormSq right * (64 * target ^ 2) := by
  cases equal
  exact request.bilinear_bound stage_eq readings left right

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
