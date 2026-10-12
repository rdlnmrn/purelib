module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.List.Membership
import Purelib.Algebra.Group.Negation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

public section

/-!
# Complete reciprocal covers of retained boundary parents

The uniform radius yields a bounded finite mesh of the entire original
parent, not a requested-accuracy-dependent prefix. Every inverted subarc is
contained in its cached reciprocal model box. Synchronized refinements have
the source sheet throughout each subarc, fixed by exact agreement at its cut.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover

open Purelib.Data.List
open Purelib.Algebra.Group
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Geometry.Rational.Box.Square

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Branches

open Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary SameSide)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath (StrictParameterEdges dyadicEdges_strictParameterEdges)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (lastEndpoint)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge dyadicEdges)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Gaussian Coordinate Box)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}

set_option genInjectivity false in
/-- A retained finite dyadic cover of the entire original parent with its common reciprocal-radius payment.

The cached depth, edge count and exact dyadic spine share one strict movement bound for the retained parent
displacement. -/
structure Mesh (data : UniformReciprocalModels.Data patch count) where
  /-- The retained dyadic subdivision depth selected from the original source displacement and common radius. -/ depth :
    Nat
  /-- The cached number of retained dyadic parameter edges. -/ edgeCount : Nat
  /-- The retained edge count is exactly two raised to the subdivision depth. -/ edgeCount_eq : edgeCount = 2 ^ depth
  /-- The retained dyadic parameter edges covering the original unit interval. -/ edges : List Subdivision.ParameterEdge
  /-- The retained edge spine is exactly the original dyadic subdivision between the fixed zero and one endpoints. -/
    edges_eq : edges = Subdivision.dyadicEdges depth UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint
  /-- The original dyadic source movement bound is strictly below the common reciprocal radius squared. -/ small :
    Geometric.Basic.quarterRadius (Data.Gaussian.Norm.Basic.normSq parent.model.displacement) depth <
    data.radius ^ 2

constructive_injectivity Mesh

namespace Mesh

variable {data : Data patch count}

/-- Compute the first dyadic depth whose original source movement fits the shared reciprocal radius, retaining its exact
full edge spine. -/
@[expose] def build (data : UniformReciprocalModels.Data patch count) :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data :=
  let depth := Search.firstQuarterBelow (Data.Gaussian.Norm.Basic.normSq parent.model.displacement) 0
    (data.radius ^ 2)
  ⟨depth, 2 ^ depth, rfl, Subdivision.dyadicEdges depth UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint, rfl,
    Search.firstQuarterBelow_accurate _ (Data.Gaussian.Norm.Basic.normSq_nonneg _) 0 _
      (Fraction.Order.Arithmetic.pow_pos_direct data.radius_positive 2)⟩

/-- The retained edge list length equals its cached dyadic edge count. -/
theorem edges_length (mesh : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data) :
  mesh.edges.length = mesh.edgeCount := by
  rw [mesh.edges_eq, Subdivision.dyadicEdges_length, mesh.edgeCount_eq]

/-- Every edge of the retained strict parameter spine has strictly ordered endpoints. -/
private theorem strict_member {edges : List Subdivision.ParameterEdge}
    (strict : PreparedPath.StrictParameterEdges edges)
    {edge : Subdivision.ParameterEdge} (member : edge ∈ edges) : edge.left.parameter < edge.right.parameter := by
  induction edges with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first remaining ih =>
      rcases Membership.mem_cons.mp member with same | member
      · subst edge; exact strict.1
      · exact ih strict.2 member

/-- Every original edge in the retained dyadic cover has strictly increasing parameters. -/
theorem edge_strict (mesh : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data) {edge :
  Subdivision.ParameterEdge} (member : edge ∈ mesh.edges) :
    edge.left.parameter < edge.right.parameter := by
  apply strict_member _ member
  rw [mesh.edges_eq]
  exact PreparedPath.dyadicEdges_strictParameterEdges _ _ _ (by decide)

/-- The source movement inside an original dyadic edge is strictly below the common reciprocal radius squared. -/
theorem point_distance (mesh : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data) {edge :
  Subdivision.ParameterEdge} (member : edge ∈ mesh.edges)
    {parameter : InverseRootPolynomial.Coordinate} (between : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (parent.edge.point parameter - parent.edge.point edge.left.parameter) <
      data.radius ^ 2 := by
  have width := UniformPrimitiveMesh.dyadicEdges_width mesh.depth UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint edge
    (mesh.edges_eq ▸ member)
  change (edge.right.parameter - edge.left.parameter) ^ 2 = Geometric.Basic.quarterRadius ((1 - 0 :
    InverseRootPolynomial.Coordinate) ^ 2) mesh.depth at width
  change Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt parameter -
    parent.edge.localSegment.pointAt edge.left.parameter) < _
  rw [parent.edge.localSegment.normSq_pointAt_sub_pointAt]
  have displacement : parent.model.displacement =
      parent.edge.segment.pointAt parent.edge.request.endpoint.parameter -
        parent.edge.segment.pointAt parent.edge.left.parameter := by
    change parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0 = _
    rw [ClearSegment.pointAt_one, ClearSegment.pointAt_zero]
  rw [← displacement]
  calc
    _ ≤ (edge.right.parameter - edge.left.parameter) ^ 2 * Data.Gaussian.Norm.Basic.normSq
      parent.model.displacement :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct between.1)
          (Fraction.Order.Arithmetic.sub_le_sub_right_direct between.2 _) 2) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ = Geometric.Basic.quarterRadius (Data.Gaussian.Norm.Basic.normSq parent.model.displacement) mesh.depth :=
      by
      rw [width, Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1
    _ < _ := mesh.small

/-- Every actual inverted point of the original dyadic subarc belongs to the corresponding retained reciprocal box. -/
theorem contains (mesh : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data) {edge :
  Subdivision.ParameterEdge} (member : edge ∈ mesh.edges)
    {parameter : InverseRootPolynomial.Coordinate} (between : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    (data.box edge.left.parameter).Contains (parent.edge.point parameter)⁻¹ :=
  Centered.centeredBox_contains_of_normSq_sub_le data.radius_positive.le
    ((PreparedReciprocalSamples.inverse_movement_between (data.boundary.point edge.left.inside)
      (data.boundary.point ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩)).trans
        (mesh.point_distance member between).le)

/-- Locate an original unit-interval parameter in the retained complete dyadic edge spine. -/
@[expose] def locate (mesh : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data) (parameter :
  InverseRootPolynomial.Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    UniformPrimitiveMesh.Located mesh.edges parameter := by
  rw [mesh.edges_eq]
  exact UniformPrimitiveMesh.locateDyadic _ _ _ parameter inside

end Mesh

set_option genInjectivity false in
/-- A materialized model and its entire actual inverted subarc. The model equation ties its executable cache to the
shared source construction.

The cached model is indexed by its retained edge, and the containment certificate covers every parameter between those
endpoints. -/
structure Cell (data : UniformReciprocalModels.Data patch count) (edge : Subdivision.ParameterEdge) where
  /-- The original covered edge has strictly increasing parameter endpoints. -/ ordered : edge.left.parameter <
    edge.right.parameter
  /-- The cached reciprocal inverse-root model of the exact original edge. -/ model : InverseRootPolynomial.Model
    (HyperellipticReciprocal.polynomial curve) (data.box edge.left.parameter)
  /-- The cached cell model is exactly the model constructed from the shared source polynomial at its original left
    endpoint. -/ model_eq : model = data.modelAt edge.left.parameter edge.left.inside
  /-- Every actual reciprocal image point between the original edge endpoints belongs to its retained model box. -/
    contains : ∀ parameter, edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter →
    (data.box edge.left.parameter).Contains (parent.edge.point parameter)⁻¹

constructive_injectivity Cell

namespace Cell

variable {data : Data patch count} {edge :
  ParameterEdge}

/-- Materialize the original edge's reciprocal model from the shared source cache and retain whole-subarc coverage. -/
@[expose] def build (mesh : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data) (edge :
  Subdivision.ParameterEdge) (member : edge ∈ mesh.edges) :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge :=
  ⟨mesh.edge_strict member, data.modelAt edge.left.parameter edge.left.inside, rfl,
    fun _ between => mesh.contains member between⟩

/-- The original parent point is its retained starting point plus the scaled original displacement. -/
theorem point_line (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (parameter :
  InverseRootPolynomial.Coordinate) :
    parent.edge.point parameter = Affine.line (parent.edge.point 0) parent.model.displacement parameter := by
  change parent.edge.localSegment.pointAt parameter = Affine.line (parent.edge.localSegment.pointAt 0)
    (parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0) parameter
  rw [ClearSegment.pointAt_zero, ClearSegment.pointAt_one]
  apply Data.Gaussian.Basic.ext <;>
    simp only [ClearSegment.pointAt, Affine.line,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im,
      Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1

/-- Every synchronized refinement preserves exact source transport at the retained cell's original starting cut. -/
theorem initial_transport (cell : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge) (index :
  Nat) :
    ReciprocalInverseModelOverlap.value curve (cell.model.refine index) (parent.edge.point edge.left.parameter) =
      (data.source.refine index).value.eval (parent.edge.point edge.left.parameter) := by
  rw [cell.model_eq]
  exact data.modelAt_refine_transport _ _ index

/-- Exact initial agreement fixes the comparison sign across the whole inverted cell.

Both inverse polynomials may be refined without shrinking it. -/
theorem flip_false (cell : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge) (index : Nat)
  (parameter : InverseRootPolynomial.Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    (SignAlignment.build ((data.source.refine index).value.eval
      (parent.edge.point parameter))
      (ReciprocalInverseModelOverlap.value curve (cell.model.refine index) (parent.edge.point parameter))).flip = false
        := by
  let interval : Data.Rat.Interval.Bounds := ⟨edge.left.parameter, edge.right.parameter, cell.ordered.le⟩
  have sourceInside (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      (patch.neighborhood count).base.box.Contains (Affine.line (parent.edge.point 0) parent.model.displacement
        parameter) := by
    rw [← point_line]
    exact data.source_inside ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩
  have reciprocalInside (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      (data.box edge.left.parameter).Contains (Affine.line (parent.edge.point 0) parent.model.displacement parameter)⁻¹
        := by
    rw [← point_line]
    exact cell.contains parameter inside
  have lower (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) :
      1 ≤ Data.Gaussian.Norm.Basic.normSq (Affine.line (parent.edge.point 0) parent.model.displacement
        parameter) := by
    rw [← point_line]
    exact PreparedExteriorReciprocal.boundary_norm_lower
      (data.boundary.point ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩)
  have same := ReciprocalInverseModelOverlap.flip_eq (data.source.refine index) (cell.model.refine index)
    (parent.edge.point 0) parent.model.displacement interval sourceInside reciprocalInside lower
    (first := edge.left.parameter) (last := parameter) ⟨le_rfl, cell.ordered.le⟩ between
  rw [← point_line, ←
    point_line, cell.initial_transport] at same
  rw [← same]
  let value := (data.source.refine index).value.eval (parent.edge.point edge.left.parameter)
  have nearest : normSq (value - value) ≤ normSq (value + value) := by
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.Canonical.normSq_zero]
    exact Data.Gaussian.Basic.Canonical.normSq_nonneg (value + value)
  unfold SignAlignment.build
  rw [dif_pos nearest]

/-- Throughout the original covered subarc, synchronized inverse models satisfy the retained residual and
inverse-ceiling discrepancy bound. -/
theorem distance_le (cell : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge) (index : Nat)
  (parameter : InverseRootPolynomial.Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq ((data.source.refine index).value.eval (parent.edge.point parameter) -
      ReciprocalInverseModelOverlap.value curve (cell.model.refine index) (parent.edge.point parameter)) ≤
      6 * ((data.source.refine index).bound + (cell.model.refine index).bound) * data.inverseUpper := by
  have inside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  let left := data.source.refine index
  let right := cell.model.refine index
  let alignment := SignAlignment.build (left.value.eval (parent.edge.point parameter))
    (ReciprocalInverseModelOverlap.value curve right (parent.edge.point parameter))
  have leftResidual : Data.Gaussian.Norm.Basic.normSq (1 - curve.polynomial.eval (parent.edge.point parameter)
    *
      (left.value.eval (parent.edge.point parameter)) ^ 2) ≤ left.bound := by
    rw [← left.residual_eq, Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact left.residualBound _ (data.source_inside inside)
  have rightResidual := ReciprocalInverseModelOverlap.residual right
    (PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside) (cell.contains parameter between)
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at leftResidual rightResidual
  have bound := alignment.distance_le leftResidual rightResidual left.bound_small
  simp only [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  have selected : alignment.value = ReciprocalInverseModelOverlap.value curve right (parent.edge.point parameter) := by
    rw [alignment.value_eq, cell.flip_false index parameter between]
    rfl
  rw [selected] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (data.source_refine_norm_le index inside)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.bound_nonnegative right.bound_nonnegative)))

end Cell

set_option genInjectivity false in
/-- The model bank follows the retained dyadic edge spine.

Each constructor retains the head model and exact tail bank indexed by the same ordered edge list. -/
inductive Cells (data : UniformReciprocalModels.Data patch count) : List Subdivision.ParameterEdge → Type
  /-- The empty original edge spine has no retained reciprocal models. -/ | nil :
    Cells data []
  /-- Retain the original head edge model and the exact remaining model spine. -/ | cons {edge :
    Subdivision.ParameterEdge} {remaining : List Subdivision.ParameterEdge}
      (head : Cell data edge) (tail :
        Cells data remaining) :
        Cells data (edge :: remaining)

constructive_injectivity Cells

namespace Cells

variable {data : Data patch count}

/-- Materialize the reciprocal models of the original edge list in order from the shared-source mesh. -/
@[expose] def build (mesh : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh data) : (edges : List
  Subdivision.ParameterEdge) →
    (∀ edge ∈ edges, edge ∈ mesh.edges) → Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cells data edges
  | [], _ => .nil
  | edge :: remaining, member =>
      .cons (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell.build mesh edge (member edge
        (List.mem_cons_self ..)))
        (build mesh remaining (fun other
          found => member other (List.mem_cons_of_mem _ found)))

set_option genInjectivity false in
/-- A retained original edge and its cached cell covering the requested original source parameter.

Its membership and interval witnesses refer to the selected edge of the supplied cached bank. -/
structure Located (data : UniformReciprocalModels.Data patch count) (edges : List Subdivision.ParameterEdge) (parameter
  : InverseRootPolynomial.Coordinate) where
  /-- The retained original parameter edge selected from the cached cover. -/ edge : Subdivision.ParameterEdge
  /-- The selected edge belongs to the original retained edge list. -/ member : edge ∈ edges
  /-- The original cached reciprocal model and coverage certificate for the selected edge. -/ cell :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge
  /-- The requested original parameter lies between the retained selected endpoints. -/ between : edge.left.parameter ≤
    parameter ∧ parameter ≤ edge.right.parameter

constructive_injectivity Located

/-- Read a stored cell by finite rational comparisons; the existential coverage proof is used only to certify that the
scan cannot fall off its end. -/
@[expose] def locate (parameter : InverseRootPolynomial.Coordinate) : {edges : List Subdivision.ParameterEdge} → (cells
  : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cells data edges) →
    (∃ edge ∈ edges, edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) →
      Located data edges parameter
  | [], .nil, covered => by
      exact False.elim (by
        obtain ⟨edge, member, _⟩ := covered
        exact List.not_mem_nil member)
  | edge :: remaining, .cons head tail, covered =>
      if between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter then
        ⟨edge, List.mem_cons_self .., head, between⟩
      else
        let found := locate parameter tail
          (by
          obtain ⟨other, member, inside⟩ := covered
          rcases Membership.mem_cons.mp member with same | member
          · subst other; exact False.elim (between inside)
          · exact ⟨other, member, inside⟩)
        ⟨found.edge, List.mem_cons_of_mem _ found.member, found.cell, found.between⟩

end Cells

set_option genInjectivity false in
/-- A complete finite dyadic mesh and its retained reciprocal-model bank for the original source parent.

The model bank is indexed by the exact edge spine stored in its retained mesh. -/
structure Cover (data : UniformReciprocalModels.Data patch count) where
  /-- The retained common-radius dyadic mesh of the whole original source parent. -/ mesh :
    Mesh data
  /-- The cached reciprocal models indexed by the exact retained mesh edge spine. -/ cells :
    Cells data mesh.edges

constructive_injectivity Cover

namespace Cover

variable {data : Data patch count}

/-- Cache the complete original dyadic mesh and its matching reciprocal-model spine. -/
@[expose] def build (data : UniformReciprocalModels.Data patch count) :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data :=
  let mesh := Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Mesh.build data
  ⟨mesh, Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cells.build mesh mesh.edges (fun _ member =>
    member)⟩

/-- Every rational parameter of the entire original parent is covered by one of the materialized reciprocal models,
without another owner request. -/
@[expose] def locate (cover : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data) (parameter :
  InverseRootPolynomial.Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cells.Located data cover.mesh.edges parameter :=
  cover.cells.locate parameter (by
    let found := cover.mesh.locate parameter inside
    exact ⟨found.edge, found.member, found.between⟩)

end Cover

set_option genInjectivity false in
/-- Covers of the actual retained parent spine, including each original primitive patch. No replacement period path or
second owner trace is built.

Each retained parent carries its existing patch, common model data and full reciprocal cover in the same source order.
-/
inductive ParentCovers : List (PreparedSubdivisionModelCore.CenteredEdge curve differential) → Type 2
  /-- The empty original source-parent list has no retained reciprocal covers. -/ | nil :
    ParentCovers []
  /-- Retain the original head parent patch, shared model data and complete cover with the exact parent tail. -/ | cons
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {remaining : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      (patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent) (data : UniformReciprocalModels.Data patch
        genus) (cover : Cover data)
      (tail : ParentCovers remaining) :
        ParentCovers (parent :: remaining)

constructive_injectivity ParentCovers

namespace ParentCovers

/-- Construct complete reciprocal covers for every original retained source parent from its existing covered primitive
cache. -/
@[expose] def build : (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) →
    UniformPreparedMesh.CoveredParents genus parents →
    (∀ parent ∈ parents, PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) →
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents
  | [], .nil, _ => .nil
  | parent :: remaining, .cons patch finishInside tail, boundary =>
      let data := Data.build patch genus (boundary parent (List.mem_cons_self ..)) finishInside
      .cons patch data (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover.build data)
        (build remaining tail (fun
          other member => boundary other (List.mem_cons_of_mem _ member)))

end ParentCovers

namespace Segment

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)

variable {start finish : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian} {segment :
  Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial
  (Ambient curve) start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}

/-- A complete reciprocal model bank for an existing period segment on an ambient side. Every bound and finite mesh is
derived from its retained cache. -/
@[expose] def acquire (cache : PreparedClearPathModels.ParentCache piece.path differential sheet) (side :
  PreparedBoundarySegments.SameSide (Cuts.Ambient curve) start finish) :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers cache.parents :=
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers.build cache.parents cache.covered (fun _
    member => PreparedSegmentBoundaryGeometry.segment_parent_boundary cache
    (by simpa only [ClearSegment.pointAt_zero] using segment.pointAt_contains piece.within 0 (by decide))
    (by simpa only [ClearSegment.pointAt_one] using segment.pointAt_contains piece.within 1 (by decide)) side member)

end Segment
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
