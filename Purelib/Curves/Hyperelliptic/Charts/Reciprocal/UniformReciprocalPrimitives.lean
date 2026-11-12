module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian.Norm

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian.Primitive
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathParentCaches
open Purelib.Riemann.Readings

/-!
# Requested primitive comparison on a complete reciprocal parent cover

All reciprocal cells share one source primitive and one refinement index.
The dyadic squared count cancels the squared cell width, so the whole-parent
error tends geometrically to zero without shrinking or replacing its cover.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cells Mesh Cover ParentCovers)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (lastEndpoint)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge Endpoint dyadicEdges)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Polynomial.Dense.Basic.DensePolynomial (eval_mul)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)

variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent} {data :
    Data patch count}

namespace Data

/-- The common coefficient discrepancy density from the original differential numerator and reciprocal inverse bound. -/
@[expose] def density (data : Data patch count) : Coordinate :=
  6 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant (differentialNumerator differential)
    (patch.neighborhood count).base.box *
    data.inverseUpper

/-- The common coefficient discrepancy density is strictly positive. -/
theorem density_positive (data : Data patch count) : 0 <
  density data :=
  Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (by decide) (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _))
    data.inverseUpper_positive

/-- The shared geometric primitive-error scale including the original parent displacement. -/
@[expose] def errorScale (data : Data patch count) : Coordinate :=
  2 * density data * (data.source.bound + 1 /
    16) * Basic.normSq parent.model.displacement

/-- The shared geometric primitive-error scale is nonnegative. -/
theorem errorScale_nonnegative (data : Data patch count) : 0 ≤
  errorScale data :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        (density_positive data).le)
      (add_nonneg data.source.bound_nonnegative (by decide))) (Basic.normSq_nonneg _)

end Data

set_option genInjectivity false in
/-- One materialized source coefficient and primitive is shared by every reciprocal cell of a parent. The semantic
equation is the refinement link. -/
structure SourcePrimitive (data : Data patch count) (index : Nat) where
  /-- The cached differential coefficient polynomial for this retained primitive. -/ coefficient :
    Polynomial
  /-- At every point the cached coefficient is the original differential numerator times the retained inverse-polynomial
    sample. -/ coefficient_eq : ∀ point, coefficient.eval point = (differentialNumerator
    differential).eval point *
    (data.source.refine index).value.eval point
  /-- The certified polynomial primitive of the same cached coefficient on its original rectangle. -/ primitive :
    DensePrimitive coefficient (patch.neighborhood count).base.box

constructive_injectivity SourcePrimitive

namespace SourcePrimitive

/-- Materialize the original source inverse-polynomial coefficient and its certified primitive once at the shared
refinement stage. -/
@[expose] def build (data : Data patch count) (index : Nat) :
  SourcePrimitive data index :=
  let model := data.source.refine index
  let coefficient := differentialNumerator differential * model.value
  ⟨coefficient, fun _ => eval_mul .., DensePrimitive.ofPolynomial coefficient _⟩

/-- Evaluate the retained source primitive difference at the original subedge endpoints. -/
@[expose] def increment (source : SourcePrimitive
  data index) (edge : ParameterEdge) : Gaussian :=
  source.primitive.value.eval (parent.edge.point edge.right.parameter) -
    source.primitive.value.eval (parent.edge.point edge.left.parameter)

/-- Reuse the exact cached source primitive in the existing sheet-aware prepared integral interface. Restricting its box
computes no new polynomial. -/
@[expose] def asPrepared (source : SourcePrimitive
  data index) :
    InverseRootPrimitive.PrimitiveModel (patch.neighborhood count) (2 + index)
      (differentialNumerator differential) where
  coefficient := source.coefficient
  coefficient_eq := fun point => by rw [source.coefficient_eq, data.source_refine_eq]
  primitive :=
    { value := source.primitive.value
      derivative_eq := source.primitive.derivative_eq
      remainderBound := source.primitive.remainderBound
      remainderBound_nonnegative := source.primitive.remainderBound_nonnegative
      increment_bound := fun firstInside lastInside => source.primitive.increment_bound
        ((patch.neighborhood count).box_refines.contains firstInside)
        ((patch.neighborhood count).box_refines.contains lastInside) }

end SourcePrimitive

set_option genInjectivity false in
/-- A reciprocal cell's cached inverse polynomial, differential coefficient, certified primitive and signed increment.

All caches retain defining equalities to the original cover cell and common refinement index. -/
structure CellPrimitive (data : Data patch count) (index : Nat) (edge :
  ParameterEdge) where
  /-- The original reciprocal cover cell for this exact parameter edge. -/ cell : Cell data edge
  /-- The cached reciprocal inverse-polynomial model. -/ inverse : Model
    (HyperellipticReciprocal.polynomial curve) (data.box edge.left.parameter)
  /-- The cached inverse model is exactly the original cell model refined at the shared index. -/ inverse_eq : inverse =
    cell.model.refine index
  /-- The cached differential coefficient polynomial for this retained primitive. -/ coefficient :
    Polynomial
  /-- At every point the cached coefficient is the original differential numerator times the retained inverse-polynomial
    sample. -/ coefficient_eq : ∀ point, coefficient.eval point =
    (differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)).eval
      point *
      (cell.model.refine index).value.eval point
  /-- The certified polynomial primitive of the same cached coefficient on its original rectangle. -/ primitive :
    DensePrimitive coefficient (data.box edge.left.parameter)
  /-- Evaluate the retained source primitive difference at the original subedge endpoints. -/ increment :
    Gaussian
  /-- The cached reciprocal increment is the negative primitive difference at the original inverse endpoints. -/
    increment_eq : increment = -(primitive.value.eval (parent.edge.point edge.right.parameter)⁻¹ -
    primitive.value.eval (parent.edge.point edge.left.parameter)⁻¹)

constructive_injectivity CellPrimitive

namespace CellPrimitive

variable {edge : ParameterEdge}

/-- Cache the original reciprocal cell's inverse polynomial, coefficient, primitive and signed endpoint increment. -/
@[expose] def build (cell : Cell data edge) (index : Nat) :
  CellPrimitive data index edge :=
  let model := cell.model.refine index
  let coefficient := differentialNumerator (HyperellipticReciprocal.reversedDifferential
    differential) * model.value
  let primitive := DensePrimitive.ofPolynomial coefficient (data.box edge.left.parameter)
  ⟨cell, model, rfl, coefficient, fun _ => eval_mul .., primitive,
    -(primitive.value.eval (parent.edge.point edge.right.parameter)⁻¹ -
      primitive.value.eval (parent.edge.point edge.left.parameter)⁻¹), rfl⟩

/-- The original source coefficient and reciprocal pullback coefficient differ by the common density times their
retained residual bounds. -/
theorem coefficient_distance_le (source :
  SourcePrimitive data index) (right :
  CellPrimitive data index edge)
    (parameter : Coordinate) (between : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Basic.normSq (source.coefficient.eval (parent.edge.point parameter) - (parent.edge.point
      parameter)⁻¹ ^ 2 *
      right.coefficient.eval (parent.edge.point parameter)⁻¹) ≤
      (Data.density data) * ((data.source.refine
        index).bound + (right.cell.model.refine index).bound) := by
  let point := parent.edge.point parameter
  have inside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have nonzero := PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside
  have identity : source.coefficient.eval point - point⁻¹ ^ 2 * right.coefficient.eval point⁻¹ =
      (differentialNumerator differential).eval point * ((data.source.refine index).value.eval
        point -
        ReciprocalInverseModelOverlap.value curve (right.cell.model.refine index) point) := by
    rw [source.coefficient_eq, right.coefficient_eq]
    dsimp only [ReciprocalInverseModelOverlap.value]
    have factor := numerator_factor differential point nonzero
    calc
      _ = (differentialNumerator differential).eval point * (data.source.refine
        index).value.eval point -
          ((differentialNumerator differential).eval point * ReciprocalRootNames.factor genus
            point) *
            (right.cell.model.refine index).value.eval point⁻¹ := by rw [factor]; ring1
      _ = _ := by ring1
  rw [identity, Basic.normSq_mul]
  have estimate := Arithmetic.mul_le_mul_direct
    (Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant (differentialNumerator
      differential) (data.source_inside inside))
    (right.cell.distance_le index parameter between) (Basic.normSq_nonneg _)
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _).le
  exact estimate.trans_eq (by
      dsimp only [Data.density];
      ring1)

/-- The primitive discrepancy has the same geometric bound on every subinterval, as needed by the boundary ribbon's
drift estimate. -/
theorem comparison_error (source : SourcePrimitive
  data index) (right : CellPrimitive data index edge)
    {first last : Coordinate}
    (firstInside : edge.left.parameter ≤ first ∧ first ≤ edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Basic.normSq (Comparison.comparisonValue parent source.primitive right.primitive last -
      Comparison.comparisonValue parent source.primitive right.primitive first) ≤
      quarterRadius (Data.errorScale
        data) index * (last - first) ^ 2 := by
  let interval : Interval.Bounds := ⟨edge.left.parameter, edge.right.parameter, right.cell.ordered.le⟩
  have within (parameter : Coordinate) (inside : interval.Contains parameter) : 0 ≤ parameter ∧
    parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩
  have estimate := Comparison.increment_difference_le data.boundary interval within
    source.primitive right.primitive (fun parameter inside => data.source_inside (within parameter inside))
    right.cell.contains ((Data.density data) *
      ((data.source.refine index).bound + (right.cell.model.refine index).bound))
    (right.coefficient_distance_le source) firstInside lastInside
  apply estimate.trans_eq
  rw [Model.refine_bound, Model.refine_bound, right.cell.model_eq]
  change 2 * ((Data.density data) *
    (quarterRadius data.source.bound index + quarterRadius (1 / 16) index)) *
      Basic.normSq parent.model.displacement * (last - first) ^ 2 = _
  simp only [quarterRadius_eq_mul_pow,
    Data.errorScale, -eq_self, -iff_self]
  ring1

/-- A whole-cell primitive bound with no Taylor remainder and no fixed source-model error floor. The coefficient is
common to every mesh cell. -/
theorem increment_error (source : SourcePrimitive
  data index) (right : CellPrimitive data index edge)
  :
    Basic.normSq (source.increment edge - right.increment) ≤
      quarterRadius (Data.errorScale
        data) index * (edge.right.parameter - edge.left.parameter) ^ 2 := by
  have identity : source.increment edge - right.increment =
      Comparison.comparisonValue parent source.primitive right.primitive edge.right.parameter -
        Comparison.comparisonValue parent source.primitive right.primitive edge.left.parameter := by
    rw [right.increment_eq]
    dsimp only [SourcePrimitive.increment,
      Comparison.comparisonValue]
    ring1
  rw [identity]
  exact right.comparison_error source ⟨le_rfl, right.cell.ordered.le⟩ ⟨right.cell.ordered.le, le_rfl⟩

end CellPrimitive

set_option genInjectivity false in
/-- Cached reciprocal primitive data indexed by the original finite edge spine and one shared refinement stage.

Each head retains its exact cover cell and the tail retains the remaining original edge occurrences. -/
inductive PrimitiveCells (data : Data patch count) (index : Nat) : List
  ParameterEdge → Type
  /-- The empty original occurrence spine retains no primitive requests. -/ | nil :
    PrimitiveCells data index []
  /-- Retain the exact head occurrence's primitive request followed by the matching original tail. -/ | cons {edge :
    ParameterEdge} {remaining : List
    ParameterEdge}
      (head : CellPrimitive data index edge) (tail :
        PrimitiveCells data index remaining)
        :
        PrimitiveCells data index (edge ::
          remaining)

constructive_injectivity PrimitiveCells

namespace PrimitiveCells

/-- Build cached primitive data for the exact original cover-cell spine at one shared stage. -/
@[expose] def build (index : Nat) : {edges : List ParameterEdge} →
  Cells data edges →
  PrimitiveCells data index edges
  | _, .nil => .nil
  | _, .cons head tail => .cons (CellPrimitive.build
    head index) (build index
    tail)

/-- Read the cached reciprocal increments in the retained edge order. -/
@[expose] def values : {edges : List ParameterEdge} →
  PrimitiveCells data index edges → List
  Gaussian
  | _, .nil => []
  | _, .cons head tail => head.increment :: tail.values

/-- Read the source increment minus its corresponding cached reciprocal increment at each original occurrence. -/
@[expose] def errors (source : SourcePrimitive data
  index) : {edges : List ParameterEdge} →
  PrimitiveCells data index edges → List
  Gaussian
  | _, .nil => []
  | edge :: _, .cons head tail => (source.increment edge - head.increment) :: tail.errors source

/-- There is exactly one retained discrepancy for each original edge or parent occurrence. -/
theorem errors_length {edges : List ParameterEdge} (cells :
  PrimitiveCells data index edges) (source :
  SourcePrimitive data index) :
    (cells.errors source).length = edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The finite discrepancy sum equals the source sum minus the reciprocal sum. -/
theorem errors_sum {edges : List ParameterEdge} (cells :
  PrimitiveCells data index edges) (source :
  SourcePrimitive data index) :
    gaussianSum (cells.errors source) = gaussianSum
      (edges.map source.increment) - gaussianSum cells.values := by
  induction cells with
  | nil => change (0 : Gaussian) = 0 - 0; ring1
  | @cons edge remaining head tail ih =>
      change (source.increment edge - head.increment) + gaussianSum (tail.errors
        source) = _
      rw [ih]
      change (source.increment edge - head.increment) +
        (gaussianSum (remaining.map source.increment) -
          gaussianSum tail.values) =
        (source.increment edge + gaussianSum (remaining.map source.increment)) -
          (head.increment + gaussianSum tail.values)
      ring1

/-- Each retained discrepancy satisfies the common bound for its original finite request. -/
private theorem errors_bounded (mesh : Mesh data) {edges : List
  ParameterEdge}
    (cells : PrimitiveCells data index edges) (source
      : SourcePrimitive data index)
    (members : ∀ edge ∈ edges, edge ∈ mesh.edges) :
    ∀ value ∈ cells.errors source, Basic.normSq value ≤ quarterRadius
      (Data.errorScale data) index *
      quarterRadius 1 mesh.depth := by
  induction cells with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons edge remaining head tail ih =>
      intro value member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst value
        have width := UniformPrimitiveMesh.dyadicEdges_width mesh.depth firstEndpoint
          lastEndpoint edge
          (mesh.edges_eq ▸ members edge (List.mem_cons_self ..))
        have unit : (UniformPrimitiveMesh.lastEndpoint.parameter - UniformPrimitiveMesh.firstEndpoint.parameter) ^ 2 =
          (1 : Coordinate) := by decide
        rw [unit] at width
        exact (head.increment_error source).trans_eq (by rw [width])
      · exact ih (fun other found => members other (List.mem_cons_of_mem _ found)) value member

/-- Gaussian summation preserves finite-list concatenation. -/
private theorem sum_append (first last : List Gaussian) :
  gaussianSum (first ++ last) = gaussianSum first +
  gaussianSum last := by
  induction first with
  | nil =>
    change gaussianSum last = 0 + gaussianSum last;
      rw [Data.Gaussian.Basic.zero_add]
  | cons value remaining ih =>
      change value + gaussianSum (remaining ++ last) = (value +
        gaussianSum remaining) + gaussianSum last
      rw [ih, Data.Gaussian.Basic.add_assoc]

/-- Differences of one fixed value function telescope across the retained dyadic edge subdivision. -/
private theorem dyadic_telescope (value : Coordinate → Gaussian) (depth :
  Nat) (left right : Endpoint) :
    gaussianSum ((dyadicEdges depth left right).map
      (fun edge => value edge.right.parameter - value edge.left.parameter)) =
      value right.parameter - value left.parameter := by
  induction depth generalizing left right with
  | zero => change (value right.parameter - value left.parameter) + 0 = _; rw [Data.Gaussian.Basic.add_zero]
  | succ depth ih =>
      rw [dyadicEdges, Data.List.Map.map_append,
        sum_append, ih, ih]
      ring1

/-- Both factors of the finite cell count are paid. Exact telescoping uses the shared source primitive; reciprocal cells
keep their own local offsets. -/
theorem whole_parent_error (mesh : Mesh data) (cells :
  PrimitiveCells data index mesh.edges)
    (source : SourcePrimitive data index) :
    Basic.normSq ((source.primitive.value.eval (parent.edge.point 1) -
      source.primitive.value.eval (parent.edge.point 0)) -
      gaussianSum cells.values) ≤ quarterRadius
        (Data.errorScale data) index := by
  have telescope : gaussianSum (mesh.edges.map source.increment) =
      source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval (parent.edge.point 0) := by
    rw [mesh.edges_eq]
    exact dyadic_telescope (fun
      parameter => source.primitive.value.eval (parent.edge.point parameter)) _ _ _
  rw [← telescope, ← cells.errors_sum source]
  have estimate := Sum.Bounds.normSq_sum_le (cells.errors source) _
    (cells.errors_bounded mesh source (fun _ member => member))
  rw [cells.errors_length source, mesh.edges_length, mesh.edgeCount_eq] at estimate
  apply estimate.trans_eq
  calc
    _ = quarterRadius
      (Data.errorScale data) index *
        (((2 ^ mesh.depth : Nat) : Coordinate) * (((2 ^ mesh.depth : Nat) :
          Coordinate) * quarterRadius 1 mesh.depth)) := by ring1
    _ = _ := by rw [DyadicCount.dyadic_count_cancel, Fraction.Field.mul_one_direct]

end PrimitiveCells

namespace Cover

set_option genInjectivity false in
/-- A requested whole-parent comparison retaining one source primitive and the complete original reciprocal cover.

The cached increments share a polynomial stage and carry their exact geometric discrepancy bound and target payment. -/
structure Request (cover : Cover data) (target : Coordinate) where
  /-- The common retained polynomial refinement index. -/ index : Nat
  /-- The cached source primitive shared by all original reciprocal cover cells. -/ source :
    SourcePrimitive data index
  /-- The retained cell primitives at that same source refinement stage. -/ cells :
    PrimitiveCells data index cover.mesh.edges
  /-- The cached whole-parent source primitive increment. -/ sourceIncrement : Gaussian
  /-- The cached source increment is the difference at the original parent endpoints. -/ sourceIncrement_eq :
    sourceIncrement = source.primitive.value.eval (parent.edge.point 1) -
    source.primitive.value.eval (parent.edge.point 0)
  /-- The cached sum of reciprocal primitive increments over the original cover. -/ reciprocalIncrement :
    Gaussian
  /-- The cached reciprocal increment is the finite sum of the retained cell values. -/ reciprocalIncrement_eq :
    reciprocalIncrement = gaussianSum cells.values
  /-- The cached squared-norm discrepancy bound for these exact retained samples. -/ error :
    Coordinate
  /-- The cached whole-parent error is the shared scale's geometric quarter-radius at the retained stage. -/ error_eq :
    error = quarterRadius
    (Data.errorScale data) index
  /-- The cached discrepancy bound is strictly below the requested target. -/ error_lt : error < target
  /-- The squared norm of the retained source-minus-reciprocal discrepancy satisfies the cached bound. -/ close :
    Basic.normSq (sourceIncrement - reciprocalIncrement) ≤ error

constructive_injectivity Request

/-- Requested matching over the entire original parent. The cover is fixed before the request. A consumer may supply a
later shared source index that also pays its prepared-integral or face-comparison obligations. -/
@[expose] def Request.ofSource (cover : Cover data) (source :
  SourcePrimitive data index) (target :
  Coordinate)
    (accurate : quarterRadius
      (Data.errorScale data) index < target) :
      Request cover target :=
  let cells := PrimitiveCells.build index cover.cells
  ⟨index, source, cells,
    source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval (parent.edge.point 0), rfl,
    gaussianSum cells.values, rfl, quarterRadius
      (Data.errorScale data) index, rfl,
    accurate,
    cells.whole_parent_error cover.mesh source⟩

/-- Choose a shared polynomial stage paying the positive target and cache the source and reciprocal primitive
increments. -/
@[expose] def request (cover : Cover data) (target : Coordinate) (positive
  : 0 < target) : Request cover target :=
  let index := firstQuarterBelow
    (Data.errorScale data) 0 target
  Request.ofSource cover
    (SourcePrimitive.build data index) target
    (firstQuarterBelow_accurate _
      (Data.errorScale_nonnegative data) 0 _
      positive)

end Cover

namespace ParentCovers

set_option genInjectivity false in
/-- Requested primitive data follows the same original parent/cover spine. -/
inductive Requests (target : Coordinate) : {parents : List
  (CenteredEdge curve differential)} → ParentCovers parents → Type 2
  /-- The empty original occurrence spine retains no primitive requests. -/ | nil :
    Requests target .nil
  /-- Retain the exact head occurrence's primitive request followed by the matching original tail. -/ | cons {parent :
    CenteredEdge curve differential} {remaining : List
    (CenteredEdge curve differential)}
      {patch : PreparedPatch parent} {data : Data patch
        genus} {cover : Cover data} {tail : ParentCovers remaining}
      (head : Cover.Request cover target) (rest :
        Requests target tail) :
        Requests target (.cons
        patch data cover tail)

constructive_injectivity Requests

namespace Requests

/-- Request each original parent cover at the same positive per-parent error target. -/
@[expose] def build (target : Coordinate) (positive : 0 < target) :
    {parents : List (CenteredEdge curve differential)} → (covers :
      ParentCovers parents) →
      Requests target covers
  | _, .nil => .nil
  | _, .cons _ _ cover tail => .cons (Cover.request
    cover target positive)
    (build target
    positive tail)

/-- Read the cached source increments in original parent order. -/
@[expose] def sourceValues {target : Coordinate} : {parents : List
  (CenteredEdge curve differential)} →
    {covers : ParentCovers parents} →
      Requests target covers → List
      Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => head.sourceIncrement :: tail.sourceValues

/-- Read the cached reciprocal increments in original parent order. -/
@[expose] def reciprocalValues {target : Coordinate} : {parents : List
  (CenteredEdge curve differential)} →
    {covers : ParentCovers parents} →
      Requests target covers → List
      Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => head.reciprocalIncrement :: tail.reciprocalValues

/-- Read the source increment minus its corresponding cached reciprocal increment at each original occurrence. -/
@[expose] def errors {target : Coordinate} : {parents : List
  (CenteredEdge curve differential)} →
    {covers : ParentCovers parents} →
      Requests target covers → List
      Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => (head.sourceIncrement - head.reciprocalIncrement) :: tail.errors

/-- There is exactly one retained discrepancy for each original edge or parent occurrence. -/
theorem errors_length {target : Coordinate} {parents : List
  (CenteredEdge curve differential)} {covers : ParentCovers parents}
    (requests : Requests target covers)
      : requests.errors.length = parents.length := by
  induction requests with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The finite discrepancy sum equals the source sum minus the reciprocal sum. -/
theorem errors_sum {target : Coordinate} {parents : List
  (CenteredEdge curve differential)} {covers : ParentCovers parents}
    (requests : Requests target covers)
      :
    gaussianSum requests.errors = gaussianSum
      requests.sourceValues - gaussianSum requests.reciprocalValues := by
  induction requests with
  | nil => change (0 : Gaussian) = 0 - 0; ring1
  | cons head tail ih =>
      change (head.sourceIncrement - head.reciprocalIncrement) + gaussianSum
        tail.errors = _
      rw [ih]
      change (head.sourceIncrement - head.reciprocalIncrement) +
        (gaussianSum tail.sourceValues - gaussianSum
          tail.reciprocalValues) =
        (head.sourceIncrement + gaussianSum tail.sourceValues) -
          (head.reciprocalIncrement + gaussianSum tail.reciprocalValues)
      ring1

/-- Each retained discrepancy satisfies the common bound for its original finite request. -/
theorem errors_bounded {target : Coordinate} {parents : List
  (CenteredEdge curve differential)} {covers : ParentCovers parents}
    (requests : Requests target covers)
      : ∀ value ∈ requests.errors, Basic.normSq value ≤ target := by
  induction requests with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      intro value member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst value; exact head.close.trans head.error_lt.le
      · exact ih value member

end Requests

set_option genInjectivity false in
/-- A finite requested comparison of the original source and reciprocal primitive sums.

Each parent keeps its original cover, while the aggregate budget pays the exact squared parent count. -/
structure Request {parents : List (CenteredEdge curve differential)} (covers :
  ParentCovers parents) (target : Coordinate) where
  /-- The cached per-parent budget paying both factors of the original parent count. -/ localTarget :
    Coordinate
  /-- The local target is the finite aggregate per-term budget for the requested target and exact parent length. -/
    localTarget_eq : localTarget = Aggregate.perTerm target parents.length
  /-- The retained primitive requests on the original parent and cover spine. -/ requests :
    Requests localTarget covers
  /-- The cached finite sum of original source primitive increments. -/ sourceIntegral : Gaussian
  /-- The cached source integral is exactly the sum of retained source request values. -/ sourceIntegral_eq :
    sourceIntegral = gaussianSum requests.sourceValues
  /-- The cached finite sum of reciprocal cover increments. -/ reciprocalIntegral : Gaussian
  /-- The cached reciprocal integral is exactly the sum of retained reciprocal request values. -/ reciprocalIntegral_eq
    : reciprocalIntegral = gaussianSum requests.reciprocalValues
  /-- The cached squared-norm discrepancy bound for these exact retained samples. -/ error :
    Coordinate
  /-- The cached aggregate error is the per-parent target multiplied by both factors of the original parent count. -/
    error_eq : error = (parents.length : Coordinate) * ((parents.length :
    Coordinate) * localTarget)
  /-- The cached discrepancy bound is strictly below the requested target. -/ error_lt : error < target
  /-- The squared norm of the retained source-minus-reciprocal discrepancy satisfies the cached bound. -/ close :
    Basic.normSq (sourceIntegral - reciprocalIntegral) ≤ error

constructive_injectivity Request

/-- Choose a shared polynomial stage paying the positive target and cache the source and reciprocal primitive
increments. -/
@[expose] def request {parents : List (CenteredEdge curve differential)} (covers :
  ParentCovers parents)
    (target : Coordinate) (positive : 0 < target) :
      Request covers target := by
  let localTarget := Aggregate.perTerm target parents.length
  let requests := Requests.build
    localTarget (Aggregate.perTerm_positive positive _) covers
  refine ⟨localTarget, rfl, requests, gaussianSum requests.sourceValues, rfl,
    gaussianSum requests.reciprocalValues, rfl,
    (parents.length : Coordinate) * ((parents.length : Coordinate) *
      localTarget), rfl,
    Aggregate.count_mul_perTerm_lt positive _, ?_⟩
  rw [← requests.errors_sum]
  have estimate := Sum.Bounds.normSq_sum_le requests.errors _ requests.errors_bounded
  rw [requests.errors_length] at estimate
  exact estimate

end ParentCovers

namespace Segment

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)

variable {start finish : Gaussian} {segment :
  Geometry.ClearPath.ClearSegment curve.polynomial
  (Ambient curve) start finish}
  {owner : Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}

/-- Choose a shared polynomial stage paying the positive target and cache the source and reciprocal primitive
increments. -/
@[expose] def request (cache : ParentCache piece.path differential sheet) (side :
  SameSide (Ambient curve) start finish)
    (target : Coordinate) (positive : 0 < target) :
    (covers : ParentCovers cache.parents) ×
      ParentCovers.Request covers target :=
  let covers := Segment.acquire cache side
  ⟨covers, ParentCovers.request covers target
    positive⟩

end Segment
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
