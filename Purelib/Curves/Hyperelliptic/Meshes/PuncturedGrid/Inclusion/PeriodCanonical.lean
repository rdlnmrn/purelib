module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Pay the routed-mesh, triangle-corner and canonical-chart comparisons
without replacing the original period program or its numerical bank. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh
open Purelib.Data.Rat
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests (RouteChartRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm countCoordinate countCoordinate_eq)

/-- Select the original-period tolerance before acquiring its polynomials. This pays the entire routed word's corner
error, independently of the later number of analytic fragments. -/
theorem requested_corner_bound {target : Fraction.Rational} (positive : 0 < target) (count pieces : Nat) :
    Aggregate.countCoordinate count * (Aggregate.countCoordinate count *
      (16 * (Aggregate.perTerm (Aggregate.perTerm target count / 4) pieces / 64))) < target := by
  let inner := Aggregate.perTerm target count
  have innerPositive := Aggregate.perTerm_positive positive count
  have quarterPositive := Fraction.Order.Field.div_pos_direct innerPositive (by decide : (0 : Fraction.Rational) < 4)
  have divided : 16 * (Aggregate.perTerm (inner / 4) pieces / 64) = Aggregate.perTerm (inner / 4) pieces / 4 := by
    generalize Aggregate.perTerm (inner / 4) pieces = allowance
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ = allowance * (16 * (64 : Fraction.Rational)⁻¹) := by ring1
      _ = _ := by
        rw [show (16 : Fraction.Rational) * (64 : Fraction.Rational)⁻¹ = (4 : Fraction.Rational)⁻¹ by decide +kernel]
  have localBound : 16 * (Aggregate.perTerm (inner / 4) pieces / 64) ≤ inner :=
    divided.trans_le ((Fraction.Order.Field.divide_le_self
      (Aggregate.perTerm_positive quarterPositive pieces).le (by decide)).trans
        ((Aggregate.perTerm_le quarterPositive.le pieces).trans
          (Fraction.Order.Field.divide_le_self innerPositive.le (by decide))))
  have nonnegative : 0 ≤ Aggregate.countCoordinate count := by
    rw [Aggregate.countCoordinate_eq]
    exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localBound nonnegative) nonnegative).trans_lt (by
      rw [Aggregate.countCoordinate_eq]
      exact Aggregate.count_mul_perTerm_lt positive count)

/-- The nested four-error squared-norm estimate fits a positive target when each error is allotted one thirty-second of
it. -/
private theorem four_error_budget {target : Fraction.Rational} (positive : 0 < target) :
    2 * (2 * (target / 32 + target / 32) + 2 * (target / 32 + target / 32)) < target := by
  have less := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 32))
    (by decide +kernel : (16 : Fraction.Rational) < 32)
  have equal : target / 32 * 32 = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  exact (show 2 * (2 * (target / 32 + target / 32) + 2 * (target / 32 + target / 32)) = target / 32 * 16 by
    ring1).trans_lt
    (less.trans_eq equal)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    LiftedMesh vertices edges base.faces}
  {source : Differential genus} {domains :
    FaceDomainBank frames base.faces.regulars}
  {points : List Purelib.Data.Gaussian.Basic.Canonical} {tolerance : Rational} {stage : Nat}
  {budgets : FaceMeshBudgets source points tolerance
    domains} {numerics : FacePrimitiveBank source
    stage domains}
  {shared : FaceSharedMeshes budgets numerics}
    {ambient : Purelib.Geometry.Rational.Box} {first last : Purelib.Data.Gaussian.Basic.Canonical}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last} {assigned :
    PathFaces mesh path}

/-- Both errors use the literal supplied primitive bank. In particular the triangle readings do not introduce another
approximation stage. -/
theorem canonical_bound (readings : PathFaces.MeshWordReadings shared assigned)
    {target : Fraction.Rational} (charts : RouteChartRequests.RouteChartRequest assigned.routeSpine source domains
      target)
    (later : charts.index ≤ stage) (triangles : TrianglePrimitiveReadings.TriangleReadings numerics mesh) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh
      triangles.values) assigned.indexed - readings.value) <
      2 * (target + readings.bound) := by
  have chart := charts.accurate later triangles
  rw [assigned.routeSpine_values, ← readings.cornerValue_eq_triangles triangles] at chart
  rw [show SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed -
    readings.value =
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed -
      readings.cornerValue) +
      (readings.cornerValue - readings.value) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_lt_add_right_direct chart _).trans_le
        (add_le_add le_rfl readings.accurate)))

/-- A four-error budget closes the original-period to canonical-word comparison: original integration, routing, shared
corners and chart change. All four must be paid; neither closure nor sheet matching erases an error. -/
theorem period_accurate (readings : PathFaces.MeshWordReadings shared assigned)
    {target : Fraction.Rational} (positive : 0 < target)
    (charts : RouteChartRequests.RouteChartRequest assigned.routeSpine source domains (target / 32))
    (later : charts.index ≤ stage) (triangles : TrianglePrimitiveReadings.TriangleReadings numerics mesh)
    (sample original : Data.Gaussian.Basic.Canonical)
    (period : Data.Gaussian.Norm.Basic.normSq (original - sample) < target / 32)
    (routing : Data.Gaussian.Norm.Basic.normSq (original - readings.value) < target / 32)
    (corners : readings.bound < target / 32) :
    Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh
      triangles.values) assigned.indexed - sample) < target := by
  have canonical := (canonical_bound readings charts
    later triangles).trans
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_left_direct corners (target / 32)))
  have reversed : Data.Gaussian.Norm.Basic.normSq (readings.value - original) < target / 32 := by
    rw [show readings.value - original = -(original - readings.value) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact routing
  have tail : Data.Gaussian.Norm.Basic.normSq (readings.value - sample) < 2 * (target / 32 + target / 32) := by
    rw [show readings.value - sample = (readings.value - original) + (original - sample) by ring1]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
        ((Fraction.Order.Arithmetic.add_lt_add_right_direct reversed _).trans
          (Fraction.Order.Arithmetic.add_lt_add_left_direct period _)))
  rw [show SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed -
    sample =
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed -
      readings.value) +
      (readings.value - sample) by ring1]
  have total := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_lt_add_right_direct canonical _).trans
        (Fraction.Order.Arithmetic.add_lt_add_left_direct tail _)))
  exact total.trans (four_error_budget positive)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical

end
