module
import Purelib.Polynomial.Dense.Gaussian.Basic
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

open Purelib.Riemann.Meshes

open Purelib.Approximation.Rational.Budget

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

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedGridFaces.PuncturedFaces bank} {mesh : GridLiftedMesh.LiftedMesh vertices edges faces}
  {domains : DomainBanks.FaceDomainBank frames faces.regulars} {source :
    Differentials.Basic.Differential genus} {index : Nat}
  {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational}
  {budgets : CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}

namespace FaceMeshBudgets

/-- Select the original route's face budget and transport it along the retained face equality. -/
@[expose] def atRoute (budgets : CommonMeshes.FaceMeshBudgets source points
  tolerance (numerator := numerator) domains)
    {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count} (route :
      MeshPathWalks.EdgeRoute mesh edge) :
    CommonMeshes.FaceMeshBudget (domains.atRoute route) source points tolerance (numerator := numerator)
      :=
  (CommonMeshes.FaceMeshBudgets.get budgets route.position).castFace
    route.face_eq

end FaceMeshBudgets

namespace FaceSharedMeshes

/-- Read the original route's retained shared mesh data using its exact face and sheet owner. -/
@[expose] def atRoute (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
  {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge) :
      CommonMeshes.FaceMeshReadings
      (FaceMeshBudgets.atRoute budgets route)
      (PrimitiveData.FacePrimitiveBank.atRoute numerics route) :=
  (CommonMeshes.FaceSharedMeshes.get shared route.position).castFace
    route.face_eq

/-- Only two cached point lookups are evaluated. -/
@[expose] def edgeIncrement (shared : CommonMeshes.FaceSharedMeshes budgets
  numerics) {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge) : Gaussian :=
  let readings := ((FaceSharedMeshes.atRoute shared route).atSheet
    route.sheet).readings
  SharedValues.atPoint readings (vertices.coordinate edge.finish) -
    SharedValues.atPoint readings (vertices.coordinate edge.start)

/-- The original fixed-corner and shared-mesh increments differ in squared norm by at most sixteen times the retained
tolerance. -/
theorem edgeIncrement_accurate (shared : CommonMeshes.FaceSharedMeshes budgets
  numerics)
    (included : ∀ vertex, vertices.coordinate vertex ∈ points)
    {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count} (route :
      MeshPathWalks.EdgeRoute mesh edge) :
    Gaussian.Norm.Basic.normSq
      (PrimitiveData.FacePrimitiveBank.edgeIncrement numerics route -
      FaceSharedMeshes.edgeIncrement shared route) ≤ 16 * tolerance :=
      open Purelib.Integration in by
  let domain := (domains.atRoute route).domain route.sheet
  let budget := (FaceMeshBudgets.atRoute budgets route).atSheet
    route.sheet
  let data := (PrimitiveData.FacePrimitiveBank.atRoute numerics route).atSheet
    route.sheet
  let owned := (FaceSharedMeshes.atRoute shared route).atSheet
    route.sheet
  let accuracy := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex budget.accuracy index
    owned.later
  let firstCell := EnteredPaths.PeriodDomain.locate domain (vertices.coordinate
    edge.start) route.endpoints_inside.1
  let lastCell := EnteredPaths.PeriodDomain.locate domain (vertices.coordinate
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
  rw [← SharedValues.atPoint_coordinate owned.readings first.index, ←
    SharedValues.atPoint_coordinate owned.readings last.index,
    firstEq, lastEq] at estimate
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accuracy.accurate.le
    (by decide +kernel))

end FaceSharedMeshes

namespace LiftedMesh.PathFaces

variable {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical} {path :
  Geometry.ClearPath curve.polynomial ambient start finish}

/-- Read the ordered corner-minus-mesh increment errors along the retained assigned path.

The signed difference at each occurrence reads the same retained corner and
shared-mesh banks. Repeated and reversed occurrences keep their original order. -/
@[expose] def errors (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
  (assigned : GridLiftedMesh.LiftedMesh.PathFaces mesh path) : List Gaussian :=
  assigned.values fun _ route => PrimitiveData.FacePrimitiveBank.edgeIncrement
    numerics route - FaceSharedMeshes.edgeIncrement shared route

/-- The sum of per-edge errors equals the difference of the retained corner and mesh word sums.

Finite structural induction separates the current signed difference and
transports the unchanged tail sums by scalar equality. -/
theorem errors_sum (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
  (assigned : GridLiftedMesh.LiftedMesh.PathFaces mesh path) :
    Gaussian.Norm.Sum.Basic.gaussianSum
      (PathFaces.errors shared assigned) =
      Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route =>
        PrimitiveData.FacePrimitiveBank.edgeIncrement numerics route) -
        Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route =>
          FaceSharedMeshes.edgeIncrement shared route) := by
  induction assigned with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons first rest ih =>
      change (_ - _) + Gaussian.Norm.Sum.Basic.gaussianSum
        (PathFaces.errors shared rest) = (_ + _) - (_ + _)
      rw [ih]
      ring1

/-- The retained error list has exactly one entry for each indexed path occurrence.

Its length follows the retained path spine without deleting repeated or
reversed occurrences, matching the original indexed word count. -/
theorem errors_length (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
  (assigned : GridLiftedMesh.LiftedMesh.PathFaces mesh path) :
    (PathFaces.errors shared assigned).length =
      assigned.indexed.length := by
  induction assigned with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

/-- The sum of squared edge errors is bounded by the retained word count times sixteen times its mesh tolerance.

Each retained occurrence satisfies the same squared-error bound. The finite
sum preserves the word count and the supplied common mesh tolerance. -/
theorem errors_bounded (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
    (included : ∀ vertex, vertices.coordinate vertex ∈ points) (assigned : GridLiftedMesh.LiftedMesh.PathFaces
      mesh path) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum
      (PathFaces.errors shared assigned) ≤
      Aggregate.countCoordinate assigned.indexed.length * (16 * tolerance) := by
  induction assigned with
  | nil =>
    change (0 : Fraction.Rational) ≤ Aggregate.countCoordinate 0 * _; rw
      [Aggregate.countCoordinate_eq, Nat.cast_zero, Fraction.Field.zero_mul_direct]
  | cons first rest ih =>
      have firstScalar := FaceSharedMeshes.edgeIncrement_accurate
        shared included first.location
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar
      change Gaussian.normSq
        (PrimitiveData.FacePrimitiveBank.edgeIncrement numerics first.location -
          FaceSharedMeshes.edgeIncrement shared first.location) +
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum
          (PathFaces.errors shared rest) ≤
          Aggregate.countCoordinate (rest.indexed.length + 1) * (16 * tolerance)
      rw [Aggregate.countCoordinate_eq, Algebra.NatCast.add, Nat.cast_one]
      have tailScalar := ih
      rw [Aggregate.countCoordinate_eq] at tailScalar
      exact (Fraction.Order.Arithmetic.add_le_add_direct firstScalar tailScalar).trans_eq (by ring1)

set_option genInjectivity false in
/-- Paired cached word readings on the retained face occurrences.

Both lists retain reversed edges and repeated sheets in the original order.
The comparison bound retains both word-count factors and its mesh tolerance. -/
structure MeshWordReadings (shared : CommonMeshes.FaceSharedMeshes budgets
  numerics) (assigned : GridLiftedMesh.LiftedMesh.PathFaces mesh path) where
  /-- The original ordered shared-mesh increments, including repeated and reversed occurrences. -/ values : List
    Gaussian.Basic.Canonical
  /-- The retained mesh values are exactly the original assigned route readings. -/ values_eq : values = assigned.values
    fun _ route => FaceSharedMeshes.edgeIncrement shared route
  /-- The original ordered fixed-corner increments of those same route occurrences. -/ corners : List
    Gaussian.Basic.Canonical
  /-- The retained corner values are exactly the original assigned route readings. -/ corners_eq : corners =
    assigned.values fun _ route => PrimitiveData.FacePrimitiveBank.edgeIncrement
    numerics route
  /-- The retained finite sum of the original shared-mesh increments. -/ value : Gaussian.Basic.Canonical
  /-- The stored mesh total equals the sum of its exact retained values. -/ value_eq : value =
    Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The retained finite sum of the original fixed-corner increments. -/ cornerValue : Gaussian.Basic.Canonical
  /-- The stored corner total equals the sum of its exact retained corner values. -/ cornerValue_eq : cornerValue =
    Gaussian.Norm.Sum.Basic.gaussianSum corners
  /-- The original indexed word-occurrence count. -/ count : Nat
  /-- The stored count equals the length of the original assigned indexed path. -/ count_eq : count =
    assigned.indexed.length
  /-- The retained squared-norm allowance for the complete original word comparison. -/ bound : Fraction.Rational
  /-- The allowance retains both original word-count factors and the sixteen-fold mesh tolerance. -/ bound_eq : bound =
    Aggregate.countCoordinate count * (Aggregate.countCoordinate count * (16 *
    tolerance))
  /-- The original corner and shared-mesh totals satisfy the retained complete-word bound. -/ accurate :
    Gaussian.Norm.Basic.normSq (cornerValue - value) ≤ bound

constructive_injectivity MeshWordReadings

namespace MeshWordReadings

/-- Cache both original word readings and their exact count-squared comparison bound using the shared mesh bank. -/
@[expose] def build (shared : CommonMeshes.FaceSharedMeshes budgets numerics)
  (included : ∀ vertex, vertices.coordinate vertex ∈ points)
    (assigned : GridLiftedMesh.LiftedMesh.PathFaces mesh path) :
      MeshWordReadings shared assigned := by
  let values := assigned.values fun _ route =>
    FaceSharedMeshes.edgeIncrement shared route
  let corners := assigned.values fun _ route =>
    PrimitiveData.FacePrimitiveBank.edgeIncrement numerics route
  let count := assigned.indexed.length
  have estimate := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le
    (PathFaces.errors shared assigned)
  rw [PathFaces.errors_length,
    PathFaces.errors_sum] at estimate
  have paid := estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (PathFaces.errors_bounded shared included assigned)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
  refine ⟨values, rfl, corners, rfl, Gaussian.Norm.Sum.Basic.gaussianSum values, rfl,
    Gaussian.Norm.Sum.Basic.gaussianSum corners, rfl, count, rfl,
    Aggregate.countCoordinate count * (Aggregate.countCoordinate count * (16 *
      tolerance)), rfl, ?_⟩
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  simpa only [Aggregate.countCoordinate_eq] using paid

/-- The retained corner-word total equals the exact original triangle-source increment sum. -/
theorem cornerValue_eq_triangles {shared : CommonMeshes.FaceSharedMeshes budgets
  numerics} {assigned : GridLiftedMesh.LiftedMesh.PathFaces mesh path}
    (readings : MeshWordReadings shared assigned)
    (triangles : TrianglePrimitiveReadings.TriangleReadings numerics mesh) :
    readings.cornerValue = Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route =>
      route.sourceEdge.increment triangles.values) := by
  rw [readings.cornerValue_eq, readings.corners_eq]
  clear readings
  congr 1
  induction assigned with
  | nil => rfl
  | cons first rest ih =>
    exact congrArg₂ List.cons
      (TrianglePrimitiveReadings.TriangleReadings.route_increment triangles
        first.location).symm ih

end MeshWordReadings
end LiftedMesh.PathFaces
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords

end
