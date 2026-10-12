module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Square.Symmetric.Norm
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples
public import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples

open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rational.Box.Square

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathParentCaches

@[expose] public section

/-!
# Reciprocal samples of retained paths on the fixed period ambient

The coefficient-derived `Ambient curve` has radius at least one. Its boundary
is therefore uniformly apart from zero, including every rational point on an
actual prepared side. The retained period-segment parent cache supplies all
reciprocal denominators and dyadic movement/count certificates automatically.
This compares actual finite samples; gluing an exterior primitive patch and
transporting its root ownership remain separate obligations.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary SameSide)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

/-- Every point on the coefficient-derived ambient boundary has squared norm at least one. -/
theorem boundary_norm_lower {point : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient
  curve) point) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq point := by
  have radius := RootRadius.one_le_denseLargeSquareRadius curve.polynomial
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Fraction.Rational) ≤ 1) radius 2
  rw [one_pow] at squared
  exact squared.trans (Symmetric.Norm.symmetric_boundary_norm_bounds
    (RootRadius.denseLargeSquareRadius_pos curve.polynomial).le boundary).1

/-- The original coefficient-derived ambient boundary avoids zero. -/
theorem boundary_nonzero {point : Data.Gaussian.Basic.Canonical} (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve)
  point) : point ≠ 0 := by
  intro zero
  have lower := boundary_norm_lower boundary
  rw [zero, Data.Gaussian.Norm.Basic.normSq_zero] at lower
  exact (by decide : ¬((1 : Fraction.Rational) ≤ 0)) lower

/-- Nonvanishing holds along the actual whole source segment, not just at its two endpoints or at the sampled dyadic
vertices. -/
theorem parent_point_nonzero {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) {parameter : Fraction.Rational}
      (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    parent.edge.point parameter ≠ 0 :=
      boundary_nonzero (boundary.point inside)

/-- Cache reciprocal endpoints, transformed coefficient and sample for an original prepared ambient-side parent.

Nonvanishing is supplied by the retained whole-segment boundary certificate and no root or coefficient is recomputed. -/
def parentSample (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) :
    ReciprocalPathSamples.Cell parent.model :=
  Cell.build ⟨parent.center.value, rfl⟩
    (parent_point_nonzero (parameter := 0) boundary
      (by constructor <;> decide))
    (parent_point_nonzero (parameter := 1) boundary
      (by constructor <;> decide))

/-- This is the original prepared cell's polynomial coefficient, not a new root evaluation. Inversion and coefficient
transport are finite arithmetic. -/
theorem parentSample_coefficient (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) :
    (parentSample parent boundary).coefficient =
      -(parent.edge.point 0 ^ 2 * parent.center.value) := rfl

/-- The reciprocal sample parametrization is the pointwise inverse of the original parent edge. -/
theorem parentSample_point (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (parameter :
  Fraction.Rational) :
    ReciprocalPathSamples.point parent.model parameter = (parent.edge.point parameter)⁻¹ := by
  apply congrArg Inv.inv
  change parent.edge.localSegment.pointAt 0 + Scale.scale parameter
    (parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0) = parent.edge.localSegment.pointAt
      parameter
  rw [ClearSegment.pointAt_zero, ClearSegment.pointAt_one]
  rfl

/-- Build the reciprocal sample spine for the original ordered prepared boundary parents.

Each cell retains its original centered coefficient and endpoint evidence; recursion follows the exact source list. -/
def parentSamples : (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) →
    (∀ parent ∈ parents, PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) →
      ReciprocalPathSamples.Cells (parents.map CenteredEdge.model)
  | [], _ => .nil
  | parent :: tail, boundary => .cons (parentSample
    parent (boundary parent (List.mem_cons_self ..)))
      (parentSamples tail (fun other member =>
        boundary other (List.mem_cons_of_mem _ member)))

/-- A uniform bound on the original cached parent coefficients bounds the corresponding reciprocal sample spine. -/
theorem parentSamples_coefficients (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential))
    (boundary : ∀ parent ∈ parents, PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) {density :
      Fraction.Rational}
    (bounded : ∀ parent ∈ parents, Data.Gaussian.Norm.Basic.normSq parent.center.value ≤ density) :
    (parentSamples parents
      boundary).CoefficientsBounded density := by
  induction parents with
  | nil => trivial
  | cons parent tail ih => exact ⟨bounded parent (List.mem_cons_self ..),
      ih (fun other member => boundary other (List.mem_cons_of_mem _ member))
        (fun other member => bounded other (List.mem_cons_of_mem _ member))⟩

namespace Segment

variable {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment :
  ClearSegment curve.polynomial
  (Ambient curve) start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}

/-- The retained covered segment starts inside the original ambient square. -/
public theorem first_inside (piece : PreparedPathDecomposition.CoveredSegment segment owner) : (Cuts.Ambient
  curve).Contains start := by
  simpa only [ClearSegment.pointAt_zero] using segment.pointAt_contains piece.within 0 (by decide)

/-- The retained covered segment finishes inside the original ambient square. -/
public theorem last_inside (piece : PreparedPathDecomposition.CoveredSegment segment owner) : (Cuts.Ambient
  curve).Contains finish := by
  simpa only [ClearSegment.pointAt_one] using segment.pointAt_contains piece.within 1 (by decide)

/-- The source is an existing covered period segment on a displayed ambient side. Its cache, owners, coefficients and
ambient are all retained. -/
def samples (cache : PreparedClearPathModels.ParentCache piece.path differential sheet) (side :
  PreparedBoundarySegments.SameSide (Cuts.Ambient curve) start finish) :
    ReciprocalPathSamples.Cells (cache.parents.map CenteredEdge.model) :=
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal.parentSamples cache.parents (fun _ member =>
    PreparedSegmentBoundaryGeometry.segment_parent_boundary cache
    (first_inside piece)
      (last_inside piece) side member)

/-- The retained dyadic mesh controls the finite reciprocal path-sample discrepancy.

The bound uses the original coefficient density, segment displacement and mesh depth, with denominator separation
supplied by the same ambient boundary. -/
theorem error_bound (cache : PreparedClearPathModels.ParentCache piece.path differential sheet) (side :
  PreparedBoundarySegments.SameSide (Cuts.Ambient curve) start finish)
    {density : Fraction.Rational} (bounded : ∀ parent ∈ cache.parents, Data.Gaussian.Norm.Basic.normSq
      parent.center.value ≤ density) :
    Data.Gaussian.Norm.Basic.normSq ((PathModel.mk (cache.parents.map CenteredEdge.model)).integralSample -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (samples cache side).values) ≤
        density * Data.Gaussian.Norm.Basic.normSq (finish - start) * Geometric.Basic.quarterRadius
          (Data.Gaussian.Norm.Basic.normSq (finish - start)) piece.mesh.depth := by
  have estimate := (samples cache
    side).dyadic_error_bound (lower := 1) piece.mesh.depth
    (by rw [Map.length_map]; exact PreparedSegmentBoundaryGeometry.segment_parentCount cache) (by decide)
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal.parentSamples_coefficients cache.parents _
      bounded)
    (fun cell member => by
      obtain ⟨parent, inParents, rfl⟩ := Map.mem_map.mp member
      exact Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal.boundary_norm_lower
        ((PreparedSegmentBoundaryGeometry.segment_parent_boundary cache
        (first_inside piece)
          (last_inside piece) side
          inParents).point (fraction := 1) (by constructor <;> decide)))
    (fun cell member => by
      obtain ⟨parent, inParents, rfl⟩ := Map.mem_map.mp member
      have movement := PreparedSegmentBoundaryGeometry.segment_parent_movement cache inParents
      change Data.Gaussian.Norm.Basic.normSq (parent.edge.point 1 - parent.edge.point 0) ≤ _
      rw [parent.edge.point_one, parent.edge.point_zero]
      exact movement.le)
  have divideOne : density / 1 = density :=
    (show density / 1 = (density / 1) * 1 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  simpa only [divideOne] using estimate

end Segment
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
