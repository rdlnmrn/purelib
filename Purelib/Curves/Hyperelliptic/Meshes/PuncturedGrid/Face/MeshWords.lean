module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-!
# Actual routed face words in the shared fine meshes

The retained route fixes the face, sheet and orientation. Its fine-mesh
increment and fixed corner increment read the same primitive bank; both
endpoint-owner discrepancies are paid before the whole word is summed.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {source :
    Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat}
  {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational}
  {budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source index domains}

namespace FaceMeshBudgets

/-- Select the original route's face budget and transport it along the retained face equality. -/
@[expose] def atRoute (budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points
  tolerance domains)
    {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count} (route :
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudget (domains.atRoute route) source points tolerance
      :=
  (Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets.get budgets route.position).castFace
    route.face_eq

end FaceMeshBudgets

namespace FaceSharedMeshes

/-- Read the original route's retained shared mesh data using its exact face and sheet owner. -/
@[expose] def atRoute (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
      Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshReadings
      (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceMeshBudgets.atRoute budgets route)
      (Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.atRoute numerics route) :=
  (Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes.get shared route.position).castFace
    route.face_eq

/-- Only two cached point lookups are evaluated. -/
@[expose] def edgeIncrement (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets
  numerics) {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) : Gaussian :=
  let readings := ((Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.atRoute shared route).atSheet
    route.sheet).readings
  Readings.RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint readings (vertices.coordinate edge.finish) -
    Readings.RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint readings (vertices.coordinate edge.start)

/-- The original fixed-corner and shared-mesh increments differ in squared norm by at most sixteen times the retained
tolerance. -/
theorem edgeIncrement_accurate (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets
  numerics)
    (included : ∀ vertex, vertices.coordinate vertex ∈ points)
    {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count} (route :
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.edgeIncrement numerics route -
      Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route) ≤ 16 * tolerance :=
      open Purelib.Integration in by
  let domain := (domains.atRoute route).domain route.sheet
  let budget := (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceMeshBudgets.atRoute budgets route).atSheet
    route.sheet
  let data := (Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.atRoute numerics route).atSheet
    route.sheet
  let owned := (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.atRoute shared route).atSheet
    route.sheet
  let accuracy := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex budget.accuracy index
    owned.later
  let firstCell := Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.PeriodDomain.locate domain (vertices.coordinate
    edge.start) route.endpoints_inside.1
  let lastCell := Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.PeriodDomain.locate domain (vertices.coordinate
    edge.finish) route.endpoints_inside.2
  let first := budget.mesh.lookup (vertices.coordinate edge.start) (included edge.start)
    firstCell.column firstCell.row (Integration.PreparedParentSplitting.Geometry.allCells_mem domain.geometry _ _)
      firstCell.inside
  let last := budget.mesh.lookup (vertices.coordinate edge.finish) (included edge.finish)
    lastCell.column lastCell.row (Integration.PreparedParentSplitting.Geometry.allCells_mem domain.geometry _ _)
      lastCell.inside
  have firstEq : budget.mesh.surface.mesh.coordinate first.index = vertices.coordinate edge.start := first.coordinate_eq
  have lastEq : budget.mesh.surface.mesh.coordinate last.index = vertices.coordinate edge.finish := last.coordinate_eq
  have estimate := Readings.RectangularPointReadings.GridPrimitiveAccuracy.point_increment_bound accuracy data.corners
    owned.readings domain.patch.cell_refines
    route.corners.start route.corners.finish first.index last.index
    (firstEq.trans (congrArg Prod.fst route.corner_coordinates).symm)
    (lastEq.trans (congrArg Prod.snd route.corner_coordinates).symm)
  rw [← Readings.RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint_coordinate owned.readings first.index, ←
    Readings.RectangularPrimitiveBoundary.SharedPrimitiveValues.atPoint_coordinate owned.readings last.index,
    firstEq, lastEq] at estimate
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accuracy.accurate.le
    (by decide +kernel))

end FaceSharedMeshes

namespace LiftedMesh.PathFaces

variable {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical} {path :
  Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}

/-- Read the ordered corner-minus-mesh increment errors along the retained assigned path.

The signed difference at each occurrence reads the same retained corner and
shared-mesh banks. Repeated and reversed occurrences keep their original order. -/
@[expose] def errors (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  (assigned : Meshes.GridLiftedMesh.LiftedMesh.PathFaces mesh path) : List Gaussian :=
  assigned.values fun _ route => Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.edgeIncrement
    numerics route - Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route

/-- The sum of per-edge errors equals the difference of the retained corner and mesh word sums.

Finite structural induction separates the current signed difference and
transports the unchanged tail sums by scalar equality. -/
theorem errors_sum (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  (assigned : Meshes.GridLiftedMesh.LiftedMesh.PathFaces mesh path) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors shared assigned) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route =>
        Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.edgeIncrement numerics route) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route =>
          Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route) := by
  induction assigned with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons first rest ih =>
      change (_ - _) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors shared rest) = (_ + _) - (_ + _)
      rw [ih]
      ring1

/-- The retained error list has exactly one entry for each indexed path occurrence.

Its length follows the retained path spine without deleting repeated or
reversed occurrences, matching the original indexed word count. -/
theorem errors_length (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  (assigned : Meshes.GridLiftedMesh.LiftedMesh.PathFaces mesh path) :
    (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors shared assigned).length =
      assigned.indexed.length := by
  induction assigned with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

/-- The sum of squared edge errors is bounded by the retained word count times sixteen times its mesh tolerance.

Each retained occurrence satisfies the same squared-error bound. The finite
sum preserves the word count and the supplied common mesh tolerance. -/
theorem errors_bounded (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
    (included : ∀ vertex, vertices.coordinate vertex ∈ points) (assigned : Meshes.GridLiftedMesh.LiftedMesh.PathFaces
      mesh path) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum
      (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors shared assigned) ≤
      Rational.Budget.Aggregate.countCoordinate assigned.indexed.length * (16 * tolerance) := by
  induction assigned with
  | nil =>
    change (0 : Fraction.Rational) ≤ Rational.Budget.Aggregate.countCoordinate 0 * _; rw
      [Rational.Budget.Aggregate.countCoordinate_eq, Nat.cast_zero, Fraction.Field.zero_mul_direct]
  | cons first rest ih =>
      have firstScalar := Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement_accurate
        shared included first.location
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar
      change Gaussian.Basic.Canonical.normSq
        (Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.edgeIncrement numerics first.location -
          Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared first.location) +
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum
          (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors shared rest) ≤
          Rational.Budget.Aggregate.countCoordinate (rest.indexed.length + 1) * (16 * tolerance)
      rw [Rational.Budget.Aggregate.countCoordinate_eq, Algebra.NatCast.add, Nat.cast_one]
      have tailScalar := ih
      rw [Rational.Budget.Aggregate.countCoordinate_eq] at tailScalar
      exact (Fraction.Order.Arithmetic.add_le_add_direct firstScalar tailScalar).trans_eq (by ring1)

set_option genInjectivity false in
/-- Paired cached word readings on the retained face occurrences.

Both lists retain reversed edges and repeated sheets in the original order.
The comparison bound retains both word-count factors and its mesh tolerance. -/
structure MeshWordReadings (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets
  numerics) (assigned : Meshes.GridLiftedMesh.LiftedMesh.PathFaces mesh path) where
  /-- The original ordered shared-mesh increments, including repeated and reversed occurrences. -/ values : List
    Gaussian.Basic.Canonical
  /-- The retained mesh values are exactly the original assigned route readings. -/ values_eq : values = assigned.values
    fun _ route => Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route
  /-- The original ordered fixed-corner increments of those same route occurrences. -/ corners : List
    Gaussian.Basic.Canonical
  /-- The retained corner values are exactly the original assigned route readings. -/ corners_eq : corners =
    assigned.values fun _ route => Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.edgeIncrement
    numerics route
  /-- The retained finite sum of the original shared-mesh increments. -/ value : Gaussian.Basic.Canonical
  /-- The stored mesh total equals the sum of its exact retained values. -/ value_eq : value =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The retained finite sum of the original fixed-corner increments. -/ cornerValue : Gaussian.Basic.Canonical
  /-- The stored corner total equals the sum of its exact retained corner values. -/ cornerValue_eq : cornerValue =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum corners
  /-- The original indexed word-occurrence count. -/ count : Nat
  /-- The stored count equals the length of the original assigned indexed path. -/ count_eq : count =
    assigned.indexed.length
  /-- The retained squared-norm allowance for the complete original word comparison. -/ bound : Fraction.Rational
  /-- The allowance retains both original word-count factors and the sixteen-fold mesh tolerance. -/ bound_eq : bound =
    Rational.Budget.Aggregate.countCoordinate count * (Rational.Budget.Aggregate.countCoordinate count * (16 *
    tolerance))
  /-- The original corner and shared-mesh totals satisfy the retained complete-word bound. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (cornerValue - value) ≤ bound

constructive_injectivity MeshWordReadings

namespace MeshWordReadings

/-- Cache both original word readings and their exact count-squared comparison bound using the shared mesh bank. -/
@[expose] def build (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets numerics)
  (included : ∀ vertex, vertices.coordinate vertex ∈ points)
    (assigned : Meshes.GridLiftedMesh.LiftedMesh.PathFaces mesh path) :
      Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.MeshWordReadings shared assigned := by
  let values := assigned.values fun _ route =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared route
  let corners := assigned.values fun _ route =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.edgeIncrement numerics route
  let count := assigned.indexed.length
  have estimate := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le
    (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors shared assigned)
  rw [Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors_length,
    Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors_sum] at estimate
  have paid := estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.errors_bounded shared included assigned)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
  refine ⟨values, rfl, corners, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum values, rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum corners, rfl, count, rfl,
    Rational.Budget.Aggregate.countCoordinate count * (Rational.Budget.Aggregate.countCoordinate count * (16 *
      tolerance)), rfl, ?_⟩
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  simpa only [Rational.Budget.Aggregate.countCoordinate_eq] using paid

/-- The retained corner-word total equals the exact original triangle-source increment sum. -/
theorem cornerValue_eq_triangles {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes budgets
  numerics} {assigned : Meshes.GridLiftedMesh.LiftedMesh.PathFaces mesh path}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.MeshWordReadings shared assigned)
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics mesh) :
    readings.cornerValue = Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route =>
      route.sourceEdge.increment triangles.values) := by
  rw [readings.cornerValue_eq, readings.corners_eq]
  clear readings
  congr 1
  induction assigned with
  | nil => rfl
  | cons first rest ih =>
    exact congrArg₂ List.cons
      (Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.route_increment triangles
        first.location).symm ih

end MeshWordReadings
end LiftedMesh.PathFaces
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords

end
