module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Integration.RectangularOwnedTriangulation

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
public import Purelib.Riemann.Integration.AffineBasisUniformBudget
import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Energy.Cell
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

section

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.AffineBasisEnergy

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.PrimitiveSurfaceBudget

public section

/-!
# A sufficient finite spatial and model request for domain energy

The fixed derivative ceilings choose the spatial depth first. The remaining
owner-reading allowance then chooses one common Newton index for all basis
rows. The complete dyadic face count is included in the target payment.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Topology.PrimitiveSurfaceBudget (SurfaceTolerance)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds (EnergyPreflight)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy (BasisReadings)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy (SurfaceCell)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Integration.AffineBasisUniformBudget
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_pos quarterRadius_nonneg)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {domain : PeriodDomain models sheet} {box :
    Box}

set_option genInjectivity false in
/-- A paid spatial refinement and synchronized basis-model request for the original observation domain.

The retained derivative bounds determine a finite mesh depth before the common model index; exact distance and
face-count payments keep the final surface error below the supplied target. -/
structure EnergyRequest (preflight : DomainBasisBounds.EnergyPreflight domain) (coarse :
  RectangularObservationMesh.ObservationMesh domain.cuts box) (target : InverseRootPolynomial.Coordinate) where
  /-- The supplied total energy-error target is positive. -/ target_positive : 0 < target
  /-- The cached squared-diameter ceiling of the original observation box. -/ diameter :
    InverseRootPolynomial.Coordinate
  /-- The diameter ceiling equals the original squared diagonal plus one. -/ diameter_eq : diameter = box.diagonalSq + 1
  /-- The retained surface tolerance pays the original coarse box count and coefficient scale. -/ tolerance :
    PrimitiveSurfaceBudget.SurfaceTolerance preflight.coefficientScale ((coarse.partition.boxes.length :
    InverseRootPolynomial.Coordinate) * diameter) target
  /-- The cached dyadic spatial refinement depth. -/ depth : Nat
  /-- The cached squared movement ceiling at the retained depth. -/ distance : InverseRootPolynomial.Coordinate
  /-- The movement ceiling is the exact quarter-radius refinement of the retained diameter. -/ distance_eq : distance =
    Geometric.Basic.quarterRadius diameter depth
  /-- The retained Taylor scale times the movement ceiling fits the squared surface tolerance. -/ taylor_small :
    preflight.taylorScale * distance ≤ tolerance.epsilon ^ 2
  /-- The cached common target for every basis-row model request. -/ readingTarget : InverseRootPolynomial.Coordinate
  /-- The retained common reading target is positive. -/ reading_positive : 0 < readingTarget
  /-- The genus-scaled reading allowance fits the squared tolerance times the actual movement ceiling. -/ reading_small
    : 32 * (genus : InverseRootPolynomial.Coordinate) ^ 2 * readingTarget ≤ tolerance.epsilon ^ 2 * distance
  /-- The synchronized retained model requests for all original basis rows. -/ modelRequest : preflight.Request
    readingTarget
  /-- The cached actual refined observation mesh on the original domain cuts. -/ mesh :
    RectangularObservationMesh.ObservationMesh domain.cuts box
  /-- The retained mesh is exactly the original coarse mesh refined to the cached depth. -/ mesh_eq : mesh =
    coarse.atDepth depth

constructive_injectivity EnergyRequest

namespace EnergyRequest

variable {preflight : EnergyPreflight domain}
  {coarse : ObservationMesh domain.cuts box} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Select the finite spatial depth from retained Taylor bounds, then acquire all basis-row model requests at the
resulting paid reading target. -/
@[expose] def build (preflight : DomainBasisBounds.EnergyPreflight domain) (coarse :
  RectangularObservationMesh.ObservationMesh domain.cuts box)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target := by
  let diameter := box.diagonalSq + 1
  have diameterPositive : 0 < diameter := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    box.diagonalSq_nonneg (by decide)
  let tolerance := SurfaceTolerance.build preflight.coefficientScale
    ((coarse.partition.boxes.length : InverseRootPolynomial.Coordinate) * diameter) target
      preflight.coefficientScale_nonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) diameterPositive.le) positive
  have squaredPositive := Fraction.Order.Arithmetic.pow_pos_direct tolerance.positive 2
  let depth := Search.firstQuarterBelow (preflight.taylorScale * diameter) 0 (tolerance.epsilon ^ 2)
  let distance := Geometric.Basic.quarterRadius diameter depth
  have distancePositive : 0 < distance := Geometric.Basic.quarterRadius_pos diameterPositive depth
  let factor := 32 * Aggregate.countCoordinate genus ^ 2
  have factorEq : factor = 32 * (genus : InverseRootPolynomial.Coordinate) ^ 2 := by dsimp only [factor]; rw
    [Aggregate.countCoordinate_eq]
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have denominatorPositive : 0 < factor + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    factorNonnegative (by decide)
  let readingTarget := tolerance.epsilon ^ 2 * distance / (factor + 1)
  have readingPositive : 0 < readingTarget := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct squaredPositive distancePositive) denominatorPositive
  exact
    { target_positive := positive
      diameter := diameter
      diameter_eq := rfl
      tolerance := tolerance
      depth := depth
      distance := distance
      distance_eq := rfl
      taylor_small := by
        have selected := (Search.firstQuarterBelow_accurate _
          (Fraction.Order.Arithmetic.mul_nonneg_direct preflight.taylorScale_nonnegative diameterPositive.le) 0 _
            squaredPositive).le
        apply le_trans (le_of_eq ?_) selected
        simp only [distance, Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
      readingTarget := readingTarget
      reading_positive := readingPositive
      reading_small := by
        rw [← factorEq]
        calc
          factor * readingTarget ≤ (factor + 1) * readingTarget :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
              readingPositive.le
          _ = readingTarget * (factor + 1) := by ring1
          _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
      modelRequest := EnergyPreflight.Request.build preflight readingTarget readingPositive
      mesh := coarse.atDepth depth
      mesh_eq := rfl }

/-- The retained movement ceiling is strictly positive at every selected finite depth. -/
theorem distance_positive (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) : 0 < request.distance := by
  rw [request.distance_eq, request.diameter_eq]
  exact Geometric.Basic.quarterRadius_pos (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    box.diagonalSq_nonneg (by decide)) request.depth

/-- The cached observation mesh has exactly the retained refinement depth. -/
theorem mesh_depth (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight
  coarse target) : request.mesh.depth = request.depth := by
  rw [request.mesh_eq]; rfl

/-- Both actual outgoing edges of every retained observation triangle satisfy the cached squared movement ceiling. -/
theorem movement_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight
  coarse target)
    (index : Fin (request.mesh.triangles.map ModelTriangle.triangle).length) :
    let triangle := request.mesh.surface.mesh.triangulation.faces index
    Data.Gaussian.Norm.Basic.normSq (request.mesh.surface.mesh.coordinate triangle.second -
      request.mesh.surface.mesh.coordinate triangle.first) ≤ request.distance ∧
      Data.Gaussian.Norm.Basic.normSq (request.mesh.surface.mesh.coordinate triangle.third -
        request.mesh.surface.mesh.coordinate triangle.first) ≤ request.distance := by
  have estimate := request.mesh.face_movement_le index
  have larger : Geometric.Basic.quarterRadius box.diagonalSq request.mesh.depth ≤ request.distance := by
    rw [request.mesh_depth, request.distance_eq, request.diameter_eq,
      Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) request.depth)
  exact ⟨estimate.1.trans larger, estimate.2.trans larger⟩

/-- Synchronize with a later global period request without changing this spatial mesh, face count, or any of its fixed
error allowances. -/
@[expose] def refineIndex (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (index : Nat) (later : request.modelRequest.index ≤ index) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target :=
  { request with modelRequest := request.modelRequest.refineIndex index later }

/-- A shared finer spatial depth requires a correspondingly smaller owner-reading allowance. The fixed derivative
ceilings and surface tolerance are reused. -/
@[expose] def refineDepth (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (depth : Nat) (later : request.depth ≤ depth) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight coarse target := by
  have diameterPositive : 0 < request.diameter := by
    rw [request.diameter_eq]
    exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct box.diagonalSq_nonneg (by decide)
  let distance := Geometric.Basic.quarterRadius request.diameter depth
  have distancePositive : 0 < distance := Geometric.Basic.quarterRadius_pos diameterPositive depth
  let factor := 32 * Aggregate.countCoordinate genus ^ 2
  have factorEq : factor = 32 * (genus : InverseRootPolynomial.Coordinate) ^ 2 := by
    dsimp only [factor]
    rw [Aggregate.countCoordinate_eq]
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have denominatorPositive : 0 < factor + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    factorNonnegative (by decide)
  let readingTarget := request.tolerance.epsilon ^ 2 * distance / (factor + 1)
  have readingPositive : 0 < readingTarget := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (Fraction.Order.Arithmetic.pow_pos_direct request.tolerance.positive 2)
      distancePositive) denominatorPositive
  refine { request with
    depth := depth
    distance := distance
    distance_eq := rfl
    taylor_small := ?_
    readingTarget := readingTarget
    reading_positive := readingPositive
    reading_small := ?_
    modelRequest := EnergyPreflight.Request.build preflight readingTarget readingPositive
    mesh := coarse.atDepth depth
    mesh_eq := rfl }
  · have distanceLe : distance ≤ request.distance := by
      rw [request.distance_eq]
      exact quarterRadius_antitone diameterPositive.le later
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distanceLe
      preflight.taylorScale_nonnegative).trans request.taylor_small
  · rw [← factorEq]
    calc
      factor * readingTarget ≤ (factor + 1) * readingTarget :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
          readingPositive.le
      _ = readingTarget * (factor + 1) := by ring1
      _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'

/-- Refining the retained request to a supplied later spatial depth keeps that exact depth. -/
@[simp] theorem refineDepth_depth (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (depth : Nat) (later : request.depth ≤ depth) :
    (request.refineDepth depth later).depth = depth := rfl

variable {stage : Nat} {cached : (row : Fin genus) →
  DomainPrimitives domain
  (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential row) stage}

/-- Build the actual triangle's affine energy budget from its retained readings, Taylor bound and paid common model
request. -/
@[expose] def triangleBudget (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (stage_eq : stage = request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface)
    (index : Fin (request.mesh.triangles.map ModelTriangle.triangle).length) : AffineBasis.TriangleBudget
      readings.affine index := by
  have movement (last) (which : last = (request.mesh.surface.mesh.triangulation.faces index).second ∨
      last = (request.mesh.surface.mesh.triangulation.faces index).third) :
      Data.Gaussian.Norm.Basic.normSq (request.mesh.surface.mesh.coordinate last -
        request.mesh.surface.mesh.coordinate (request.mesh.surface.mesh.triangulation.faces index).first) ≤
          request.distance := by
    rcases which with rfl | rfl
    · exact (request.movement_le index).1
    · exact (request.movement_le index).2
  refine AffineBasis.TriangleBudget.uniform readings.affine index preflight.coefficientScale request.tolerance.epsilon
    request.distance
    preflight.coefficientScale_nonnegative request.tolerance.positive.le request.tolerance.le_one
      request.distance_positive.le
    (fun last which => readings.affine_scale_bound preflight index last (movement last which)) ?_
  intro last which
  have inside : (domain.geometry.box (request.mesh.surface.faceSource index).column (request.mesh.surface.faceSource
    index).row).Contains
      (request.mesh.surface.mesh.coordinate last) := by
    rcases which with rfl | rfl
    · exact (request.mesh.surface.face_inside index).2.1
    · exact (request.mesh.surface.face_inside index).2.2
  have estimate := readings.error_scale_bound preflight request.modelRequest stage_eq index last inside (movement last
    which)
  have taylor := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct request.taylor_small
    request.distance_positive.le
  have bound := add_le_add request.reading_small taylor
  exact estimate.trans (by convert bound using 1 <;> ring1)

/-- Each actual retained triangle budget has the same exact tolerance-times-distance coefficient ceiling. -/
theorem triangleBudget_total (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (stage_eq : stage = request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface)
    (index : Fin (request.mesh.triangles.map ModelTriangle.triangle).length) :
    (request.triangleBudget stage_eq readings index).total = request.tolerance.epsilon * request.distance * (2 *
      preflight.coefficientScale + 3) := rfl

/-- The finite sum of a constant rational coordinate equals its index count times that coordinate. -/
private theorem sum_constant (count : Nat) (value : InverseRootPolynomial.Coordinate) : FiniteSum.Fin.sumFin (fun _ :
  Fin count => value) = (count : InverseRootPolynomial.Coordinate) * value := by
  induction count with
  | zero => change 0 = 0 * value; ring1
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

/-- The same affine surface interface now carries a proved requested total, not merely an error budget which might
dominate the observation signal. -/
@[expose] def surfaceBudget (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (stage_eq : stage = request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface) : AffineBasis.SurfaceBudget readings.affine
      :=
  let triangles := DependentVector.ofFn fun index => request.triangleBudget stage_eq readings index
  { triangles := triangles
    total := Aggregate.countCoordinate (request.mesh.triangles.map ModelTriangle.triangle).length *
      (request.tolerance.epsilon * request.distance * (2 * preflight.coefficientScale + 3))
    total_eq := by
      rw [Aggregate.countCoordinate_eq]
      rw [FiniteSum.Fin.sumFin_congr (fun index => by rw [DependentVector.ofFn_get, request.triangleBudget_total])]
      exact (sum_constant _ _).symm }

/-- The actual cached total surface budget is strictly below the original requested energy target. -/
theorem surfaceBudget_total_lt (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (stage_eq : stage = request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface) : (request.surfaceBudget stage_eq
      readings).total < target := by
  change Aggregate.countCoordinate (request.mesh.triangles.map ModelTriangle.triangle).length *
    (request.tolerance.epsilon * request.distance * (2 * preflight.coefficientScale + 3)) < target
  rw [Aggregate.countCoordinate_eq, request.mesh.face_count, request.mesh_depth, request.distance_eq]
  have partition : request.mesh.partition.boxes = coarse.partition.boxes := by rw [request.mesh_eq]; rfl
  rw [partition, Purelib.Algebra.NatCast.mul]
  calc
    _ = request.tolerance.epsilon * (2 * preflight.coefficientScale + 3) * (coarse.partition.boxes.length :
      InverseRootPolynomial.Coordinate) *
        (((2 * 4 ^ request.depth : Nat) : InverseRootPolynomial.Coordinate) * Geometric.Basic.quarterRadius
          request.diameter request.depth) := by ring1
    _ = request.tolerance.epsilon * (2 * preflight.coefficientScale + 3) * (coarse.partition.boxes.length :
      InverseRootPolynomial.Coordinate) *
        (2 * request.diameter) := by rw [Riemann.Topology.PrimitiveSurfaceBudget.face_count_cancel]
    _ = 2 * ((coarse.partition.boxes.length : InverseRootPolynomial.Coordinate) * request.diameter) *
        (2 * preflight.coefficientScale + 3) * request.tolerance.epsilon := by ring1
    _ < target := request.tolerance.accurate

/-- The original energy-cell contribution minus the coefficient-scaled paid target bounds the actual retained boundary
energy. -/
theorem energy_lower (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest preflight
  coarse target) (stage_eq : stage = request.modelRequest.index)
    (readings : DomainBasisEnergy.BasisReadings cached request.mesh.surface) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector
      genus)
    (cell : PreparedEnergy.SurfaceCell curve coefficients) (box_eq : cell.box = box) :
    cell.toEnergyCell.contribution / 4 - PreparedObservationCoercivity.coefficientNormSq coefficients * target ≤
      ((request.surfaceBudget stage_eq readings).sample coefficients).boundaryArea.im / 4 := by
  have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have estimate := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate))
      (fun row => Data.Gaussian.Basic.Canonical.normSq (coefficients row)) (fun row => by
        have scalar := Data.Gaussian.Norm.Basic.normSq_nonneg (coefficients row)
        rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar)
    simpa only [PreparedObservationCoercivity.coefficientNormSq, FiniteSum.Fin.sumFin_zero] using estimate
  have error := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (request.surfaceBudget_total_lt stage_eq readings).le nonnegative
  have lower := readings.contribution_sub_error_le_boundaryEnergy (request.surfaceBudget stage_eq readings) coefficients
    cell box_eq
  exact (Fraction.Order.Arithmetic.sub_le_sub_left_direct error _).trans lower

/-- The erased equality permits a surrounding cached mesh vector to reuse this exact surface without rebuilding its
coordinate or primitive data. -/
@[expose] def surfaceBudgetOn (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (stage_eq : stage = request.modelRequest.index)
    {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box} (equal : mesh = request.mesh)
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) : AffineBasis.SurfaceBudget readings.affine := by
  cases equal
  exact request.surfaceBudget stage_eq readings

/-- Transporting the retained surface budget along equality of its actual mesh preserves the original strict target
payment. -/
theorem surfaceBudgetOn_total_lt (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest
  preflight coarse target) (stage_eq : stage = request.modelRequest.index)
    {mesh : RectangularObservationMesh.ObservationMesh domain.cuts box} (equal : mesh = request.mesh)
    (readings : DomainBasisEnergy.BasisReadings cached mesh.surface) : (request.surfaceBudgetOn stage_eq equal
      readings).total < target := by
  cases equal
  exact request.surfaceBudget_total_lt stage_eq readings

end EnergyRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest

end
