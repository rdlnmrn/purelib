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
@[expose] def density (data : UniformReciprocalModels.Data patch count) : Coordinate :=
  6 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant (PreparedPrimitiveSamples.differentialNumerator differential)
    (patch.neighborhood count).base.box *
    data.inverseUpper

/-- The common coefficient discrepancy density is strictly positive. -/
theorem density_positive (data : UniformReciprocalModels.Data patch count) : 0 <
  density data :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _))
    data.inverseUpper_positive

/-- The shared geometric primitive-error scale including the original parent displacement. -/
@[expose] def errorScale (data : UniformReciprocalModels.Data patch count) : Coordinate :=
  2 * density data * (data.source.bound + 1 /
    16) * Data.Gaussian.Norm.Basic.normSq parent.model.displacement

/-- The shared geometric primitive-error scale is nonnegative. -/
theorem errorScale_nonnegative (data : UniformReciprocalModels.Data patch count) : 0 ≤
  errorScale data :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (density_positive data).le)
      (add_nonneg data.source.bound_nonnegative (by decide))) (Data.Gaussian.Norm.Basic.normSq_nonneg _)

end Data

set_option genInjectivity false in
/-- One materialized source coefficient and primitive is shared by every reciprocal cell of a parent. The semantic
equation is the refinement link. -/
structure SourcePrimitive (data : UniformReciprocalModels.Data patch count) (index : Nat) where
  /-- The cached differential coefficient polynomial for this retained primitive. -/ coefficient :
    InverseRootPolynomial.Polynomial
  /-- At every point the cached coefficient is the original differential numerator times the retained inverse-polynomial
    sample. -/ coefficient_eq : ∀ point, coefficient.eval point = (PreparedPrimitiveSamples.differentialNumerator
    differential).eval point *
    (data.source.refine index).value.eval point
  /-- The certified polynomial primitive of the same cached coefficient on its original rectangle. -/ primitive :
    Certificate.DensePrimitive coefficient (patch.neighborhood count).base.box

constructive_injectivity SourcePrimitive

namespace SourcePrimitive

/-- Materialize the original source inverse-polynomial coefficient and its certified primitive once at the shared
refinement stage. -/
@[expose] def build (data : UniformReciprocalModels.Data patch count) (index : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index :=
  let model := data.source.refine index
  let coefficient := PreparedPrimitiveSamples.differentialNumerator differential * model.value
  ⟨coefficient, fun _ => DensePolynomial.eval_mul .., DensePrimitive.ofPolynomial coefficient _⟩

/-- Evaluate the retained source primitive difference at the original subedge endpoints. -/
@[expose] def increment (source : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive
  data index) (edge : ClearSheetContinuation.Subdivision.ParameterEdge) : Gaussian :=
  source.primitive.value.eval (parent.edge.point edge.right.parameter) -
    source.primitive.value.eval (parent.edge.point edge.left.parameter)

/-- Reuse the exact cached source primitive in the existing sheet-aware prepared integral interface. Restricting its box
computes no new polynomial. -/
@[expose] def asPrepared (source : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive
  data index) :
    InverseRootPrimitive.PrimitiveModel (patch.neighborhood count) (2 + index)
      (PreparedPrimitiveSamples.differentialNumerator differential) where
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
structure CellPrimitive (data : UniformReciprocalModels.Data patch count) (index : Nat) (edge :
  ClearSheetContinuation.Subdivision.ParameterEdge) where
  /-- The original reciprocal cover cell for this exact parameter edge. -/ cell : UniformReciprocalCover.Cell data edge
  /-- The cached reciprocal inverse-polynomial model. -/ inverse : InverseRootPolynomial.Model
    (HyperellipticReciprocal.polynomial curve) (data.box edge.left.parameter)
  /-- The cached inverse model is exactly the original cell model refined at the shared index. -/ inverse_eq : inverse =
    cell.model.refine index
  /-- The cached differential coefficient polynomial for this retained primitive. -/ coefficient :
    InverseRootPolynomial.Polynomial
  /-- At every point the cached coefficient is the original differential numerator times the retained inverse-polynomial
    sample. -/ coefficient_eq : ∀ point, coefficient.eval point =
    (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)).eval
      point *
      (cell.model.refine index).value.eval point
  /-- The certified polynomial primitive of the same cached coefficient on its original rectangle. -/ primitive :
    Certificate.DensePrimitive coefficient (data.box edge.left.parameter)
  /-- Evaluate the retained source primitive difference at the original subedge endpoints. -/ increment :
    InverseRootPolynomial.Gaussian
  /-- The cached reciprocal increment is the negative primitive difference at the original inverse endpoints. -/
    increment_eq : increment = -(primitive.value.eval (parent.edge.point edge.right.parameter)⁻¹ -
    primitive.value.eval (parent.edge.point edge.left.parameter)⁻¹)

constructive_injectivity CellPrimitive

namespace CellPrimitive

variable {edge : ParameterEdge}

/-- Cache the original reciprocal cell's inverse polynomial, coefficient, primitive and signed endpoint increment. -/
@[expose] def build (cell : UniformReciprocalCover.Cell data edge) (index : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive data index edge :=
  let model := cell.model.refine index
  let coefficient := PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential
    differential) * model.value
  let primitive := DensePrimitive.ofPolynomial coefficient (data.box edge.left.parameter)
  ⟨cell, model, rfl, coefficient, fun _ => DensePolynomial.eval_mul .., primitive,
    -(primitive.value.eval (parent.edge.point edge.right.parameter)⁻¹ -
      primitive.value.eval (parent.edge.point edge.left.parameter)⁻¹), rfl⟩

/-- The original source coefficient and reciprocal pullback coefficient differ by the common density times their
retained residual bounds. -/
theorem coefficient_distance_le (source :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive data index edge)
    (parameter : InverseRootPolynomial.Coordinate) (between : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (source.coefficient.eval (parent.edge.point parameter) - (parent.edge.point
      parameter)⁻¹ ^ 2 *
      right.coefficient.eval (parent.edge.point parameter)⁻¹) ≤
      (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.density data) * ((data.source.refine
        index).bound + (right.cell.model.refine index).bound) := by
  let point := parent.edge.point parameter
  have inside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans between.1, between.2.trans edge.right.inside.2⟩
  have nonzero := PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside
  have identity : source.coefficient.eval point - point⁻¹ ^ 2 * right.coefficient.eval point⁻¹ =
      (PreparedPrimitiveSamples.differentialNumerator differential).eval point * ((data.source.refine index).value.eval
        point -
        ReciprocalInverseModelOverlap.value curve (right.cell.model.refine index) point) := by
    rw [source.coefficient_eq, right.coefficient_eq]
    dsimp only [ReciprocalInverseModelOverlap.value]
    have factor := PreparedReciprocalPrimitiveGlue.numerator_factor differential point nonzero
    calc
      _ = (PreparedPrimitiveSamples.differentialNumerator differential).eval point * (data.source.refine
        index).value.eval point -
          ((PreparedPrimitiveSamples.differentialNumerator differential).eval point * ReciprocalRootNames.factor genus
            point) *
            (right.cell.model.refine index).value.eval point⁻¹ := by rw [factor]; ring1
      _ = _ := by ring1
  rw [identity, Data.Gaussian.Norm.Basic.normSq_mul]
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_direct
    (Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant (PreparedPrimitiveSamples.differentialNumerator
      differential) (data.source_inside inside))
    (right.cell.distance_le index parameter between) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _).le
  exact estimate.trans_eq (by
      dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.density];
      ring1)

/-- The primitive discrepancy has the same geometric bound on every subinterval, as needed by the boundary ribbon's
drift estimate. -/
theorem comparison_error (source : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive
  data index) (right : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive data index edge)
    {first last : InverseRootPolynomial.Coordinate}
    (firstInside : edge.left.parameter ≤ first ∧ first ≤ edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (Comparison.comparisonValue parent source.primitive right.primitive last -
      Comparison.comparisonValue parent source.primitive right.primitive first) ≤
      Geometric.Basic.quarterRadius (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale
        data) index * (last - first) ^ 2 := by
  let interval : Data.Rat.Interval.Bounds := ⟨edge.left.parameter, edge.right.parameter, right.cell.ordered.le⟩
  have within (parameter : InverseRootPolynomial.Coordinate) (inside : interval.Contains parameter) : 0 ≤ parameter ∧
    parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans inside.1, inside.2.trans edge.right.inside.2⟩
  have estimate := Comparison.increment_difference_le data.boundary interval within
    source.primitive right.primitive (fun parameter inside => data.source_inside (within parameter inside))
    right.cell.contains ((Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.density data) *
      ((data.source.refine index).bound + (right.cell.model.refine index).bound))
    (right.coefficient_distance_le source) firstInside lastInside
  apply estimate.trans_eq
  rw [Model.refine_bound, Model.refine_bound, right.cell.model_eq]
  change 2 * ((Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.density data) *
    (Geometric.Basic.quarterRadius data.source.bound index + Geometric.Basic.quarterRadius (1 / 16) index)) *
      Data.Gaussian.Norm.Basic.normSq parent.model.displacement * (last - first) ^ 2 = _
  simp only [Geometric.Basic.quarterRadius_eq_mul_pow,
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale, -eq_self, -iff_self]
  ring1

/-- A whole-cell primitive bound with no Taylor remainder and no fixed source-model error floor. The coefficient is
common to every mesh cell. -/
theorem increment_error (source : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive
  data index) (right : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive data index edge)
  :
    Data.Gaussian.Norm.Basic.normSq (source.increment edge - right.increment) ≤
      Geometric.Basic.quarterRadius (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale
        data) index * (edge.right.parameter - edge.left.parameter) ^ 2 := by
  have identity : source.increment edge - right.increment =
      Comparison.comparisonValue parent source.primitive right.primitive edge.right.parameter -
        Comparison.comparisonValue parent source.primitive right.primitive edge.left.parameter := by
    rw [right.increment_eq]
    dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive.increment,
      Comparison.comparisonValue]
    ring1
  rw [identity]
  exact right.comparison_error source ⟨le_rfl, right.cell.ordered.le⟩ ⟨right.cell.ordered.le, le_rfl⟩

end CellPrimitive

set_option genInjectivity false in
/-- Cached reciprocal primitive data indexed by the original finite edge spine and one shared refinement stage.

Each head retains its exact cover cell and the tail retains the remaining original edge occurrences. -/
inductive PrimitiveCells (data : UniformReciprocalModels.Data patch count) (index : Nat) : List
  ClearSheetContinuation.Subdivision.ParameterEdge → Type
  /-- The empty original occurrence spine retains no primitive requests. -/ | nil :
    PrimitiveCells data index []
  /-- Retain the exact head occurrence's primitive request followed by the matching original tail. -/ | cons {edge :
    ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge}
      (head : CellPrimitive data index edge) (tail :
        PrimitiveCells data index remaining)
        :
        PrimitiveCells data index (edge ::
          remaining)

constructive_injectivity PrimitiveCells

namespace PrimitiveCells

/-- Build cached primitive data for the exact original cover-cell spine at one shared stage. -/
@[expose] def build (index : Nat) : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  UniformReciprocalCover.Cells data edges →
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index edges
  | _, .nil => .nil
  | _, .cons head tail => .cons (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.build
    head index) (build index
    tail)

/-- Read the cached reciprocal increments in the retained edge order. -/
@[expose] def values : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index edges → List
  InverseRootPolynomial.Gaussian
  | _, .nil => []
  | _, .cons head tail => head.increment :: tail.values

/-- Read the source increment minus its corresponding cached reciprocal increment at each original occurrence. -/
@[expose] def errors (source : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data
  index) : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index edges → List
  InverseRootPolynomial.Gaussian
  | _, .nil => []
  | edge :: _, .cons head tail => (source.increment edge - head.increment) :: tail.errors source

/-- There is exactly one retained discrepancy for each original edge or parent occurrence. -/
theorem errors_length {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index edges) (source :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index) :
    (cells.errors source).length = edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The finite discrepancy sum equals the source sum minus the reciprocal sum. -/
theorem errors_sum {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index edges) (source :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (cells.errors source) = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (edges.map source.increment) - Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.values := by
  induction cells with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | @cons edge remaining head tail ih =>
      change (source.increment edge - head.increment) + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.errors
        source) = _
      rw [ih]
      change (source.increment edge - head.increment) +
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum (remaining.map source.increment) -
          Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.values) =
        (source.increment edge + Data.Gaussian.Norm.Sum.Basic.gaussianSum (remaining.map source.increment)) -
          (head.increment + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.values)
      ring1

/-- Each retained discrepancy satisfies the common bound for its original finite request. -/
private theorem errors_bounded (mesh : UniformReciprocalCover.Mesh data) {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge}
    (cells : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index edges) (source
      : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index)
    (members : ∀ edge ∈ edges, edge ∈ mesh.edges) :
    ∀ value ∈ cells.errors source, Data.Gaussian.Norm.Basic.normSq value ≤ Geometric.Basic.quarterRadius
      (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale data) index *
      Geometric.Basic.quarterRadius 1 mesh.depth := by
  induction cells with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons edge remaining head tail ih =>
      intro value member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst value
        have width := UniformPrimitiveMesh.dyadicEdges_width mesh.depth UniformPrimitiveMesh.firstEndpoint
          UniformPrimitiveMesh.lastEndpoint edge
          (mesh.edges_eq ▸ members edge (List.mem_cons_self ..))
        have unit : (UniformPrimitiveMesh.lastEndpoint.parameter - UniformPrimitiveMesh.firstEndpoint.parameter) ^ 2 =
          (1 : InverseRootPolynomial.Coordinate) := by decide
        rw [unit] at width
        exact (head.increment_error source).trans_eq (by rw [width])
      · exact ih (fun other found => members other (List.mem_cons_of_mem _ found)) value member

/-- Gaussian summation preserves finite-list concatenation. -/
private theorem sum_append (first last : List InverseRootPolynomial.Gaussian) :
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first +
  Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
  induction first with
  | nil =>
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum last = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum last;
      rw [Data.Gaussian.Basic.zero_add]
  | cons value remaining ih =>
      change value + Data.Gaussian.Norm.Sum.Basic.gaussianSum (remaining ++ last) = (value +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum remaining) + Data.Gaussian.Norm.Sum.Basic.gaussianSum last
      rw [ih, Data.Gaussian.Basic.add_assoc]

/-- Differences of one fixed value function telescope across the retained dyadic edge subdivision. -/
private theorem dyadic_telescope (value : InverseRootPolynomial.Coordinate → InverseRootPolynomial.Gaussian) (depth :
  Nat) (left right : ClearSheetContinuation.Subdivision.Endpoint) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((ClearSheetContinuation.Subdivision.dyadicEdges depth left right).map
      (fun edge => value edge.right.parameter - value edge.left.parameter)) =
      value right.parameter - value left.parameter := by
  induction depth generalizing left right with
  | zero => change (value right.parameter - value left.parameter) + 0 = _; rw [Data.Gaussian.Basic.add_zero]
  | succ depth ih =>
      rw [ClearSheetContinuation.Subdivision.dyadicEdges, Data.List.Map.map_append,
        sum_append, ih, ih]
      ring1

/-- Both factors of the finite cell count are paid. Exact telescoping uses the shared source primitive; reciprocal cells
keep their own local offsets. -/
theorem whole_parent_error (mesh : UniformReciprocalCover.Mesh data) (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index mesh.edges)
    (source : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index) :
    Data.Gaussian.Norm.Basic.normSq ((source.primitive.value.eval (parent.edge.point 1) -
      source.primitive.value.eval (parent.edge.point 0)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.values) ≤ Geometric.Basic.quarterRadius
        (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale data) index := by
  have telescope : Data.Gaussian.Norm.Sum.Basic.gaussianSum (mesh.edges.map source.increment) =
      source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval (parent.edge.point 0) := by
    rw [mesh.edges_eq]
    exact dyadic_telescope (fun
      parameter => source.primitive.value.eval (parent.edge.point parameter)) _ _ _
  rw [← telescope, ← cells.errors_sum source]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le (cells.errors source) _
    (cells.errors_bounded mesh source (fun _ member => member))
  rw [cells.errors_length source, mesh.edges_length, mesh.edgeCount_eq] at estimate
  apply estimate.trans_eq
  calc
    _ = Geometric.Basic.quarterRadius
      (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale data) index *
        (((2 ^ mesh.depth : Nat) : InverseRootPolynomial.Coordinate) * (((2 ^ mesh.depth : Nat) :
          InverseRootPolynomial.Coordinate) * Geometric.Basic.quarterRadius 1 mesh.depth)) := by ring1
    _ = _ := by rw [DyadicCount.dyadic_count_cancel, Fraction.Field.mul_one_direct]

end PrimitiveCells

namespace Cover

set_option genInjectivity false in
/-- A requested whole-parent comparison retaining one source primitive and the complete original reciprocal cover.

The cached increments share a polynomial stage and carry their exact geometric discrepancy bound and target payment. -/
structure Request (cover : UniformReciprocalCover.Cover data) (target : InverseRootPolynomial.Coordinate) where
  /-- The common retained polynomial refinement index. -/ index : Nat
  /-- The cached source primitive shared by all original reciprocal cover cells. -/ source :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index
  /-- The retained cell primitives at that same source refinement stage. -/ cells :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges
  /-- The cached whole-parent source primitive increment. -/ sourceIncrement : InverseRootPolynomial.Gaussian
  /-- The cached source increment is the difference at the original parent endpoints. -/ sourceIncrement_eq :
    sourceIncrement = source.primitive.value.eval (parent.edge.point 1) -
    source.primitive.value.eval (parent.edge.point 0)
  /-- The cached sum of reciprocal primitive increments over the original cover. -/ reciprocalIncrement :
    InverseRootPolynomial.Gaussian
  /-- The cached reciprocal increment is the finite sum of the retained cell values. -/ reciprocalIncrement_eq :
    reciprocalIncrement = Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.values
  /-- The cached squared-norm discrepancy bound for these exact retained samples. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The cached whole-parent error is the shared scale's geometric quarter-radius at the retained stage. -/ error_eq :
    error = Geometric.Basic.quarterRadius
    (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale data) index
  /-- The cached discrepancy bound is strictly below the requested target. -/ error_lt : error < target
  /-- The squared norm of the retained source-minus-reciprocal discrepancy satisfies the cached bound. -/ close :
    Data.Gaussian.Norm.Basic.normSq (sourceIncrement - reciprocalIncrement) ≤ error

constructive_injectivity Request

/-- Requested matching over the entire original parent. The cover is fixed before the request. A consumer may supply a
later shared source index that also pays its prepared-integral or face-comparison obligations. -/
@[expose] def Request.ofSource (cover : UniformReciprocalCover.Cover data) (source :
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index) (target :
  InverseRootPolynomial.Coordinate)
    (accurate : Geometric.Basic.quarterRadius
      (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale data) index < target) :
      Request cover target :=
  let cells := Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells.build index cover.cells
  ⟨index, source, cells,
    source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval (parent.edge.point 0), rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.values, rfl, Geometric.Basic.quarterRadius
      (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale data) index, rfl,
    accurate,
    cells.whole_parent_error cover.mesh source⟩

/-- Choose a shared polynomial stage paying the positive target and cache the source and reciprocal primitive
increments. -/
@[expose] def request (cover : UniformReciprocalCover.Cover data) (target : InverseRootPolynomial.Coordinate) (positive
  : 0 < target) : Request cover target :=
  let index := Search.firstQuarterBelow
    (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale data) 0 target
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Cover.Request.ofSource cover
    (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive.build data index) target
    (Search.firstQuarterBelow_accurate _
      (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Data.errorScale_nonnegative data) 0 _
      positive)

end Cover

namespace ParentCovers

set_option genInjectivity false in
/-- Requested primitive data follows the same original parent/cover spine. -/
inductive Requests (target : InverseRootPolynomial.Coordinate) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → UniformReciprocalCover.ParentCovers parents → Type 2
  /-- The empty original occurrence spine retains no primitive requests. -/ | nil :
    Requests target .nil
  /-- Retain the exact head occurrence's primitive request followed by the matching original tail. -/ | cons {parent :
    PreparedSubdivisionModelCore.CenteredEdge curve differential} {remaining : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus} {cover : UniformReciprocalCover.Cover data} {tail : UniformReciprocalCover.ParentCovers remaining}
      (head : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Cover.Request cover target) (rest :
        Requests target tail) :
        Requests target (.cons
        patch data cover tail)

constructive_injectivity Requests

namespace Requests

/-- Request each original parent cover at the same positive per-parent error target. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → (covers :
      UniformReciprocalCover.ParentCovers parents) →
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests target covers
  | _, .nil => .nil
  | _, .cons _ _ cover tail => .cons (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.Cover.request
    cover target positive)
    (build target
    positive tail)

/-- Read the cached source increments in original parent order. -/
@[expose] def sourceValues {target : InverseRootPolynomial.Coordinate} : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} →
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests target covers → List
      InverseRootPolynomial.Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => head.sourceIncrement :: tail.sourceValues

/-- Read the cached reciprocal increments in original parent order. -/
@[expose] def reciprocalValues {target : InverseRootPolynomial.Coordinate} : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} →
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests target covers → List
      InverseRootPolynomial.Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => head.reciprocalIncrement :: tail.reciprocalValues

/-- Read the source increment minus its corresponding cached reciprocal increment at each original occurrence. -/
@[expose] def errors {target : InverseRootPolynomial.Coordinate} : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} →
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests target covers → List
      InverseRootPolynomial.Gaussian
  | _, _, .nil => []
  | _, _, .cons head tail => (head.sourceIncrement - head.reciprocalIncrement) :: tail.errors

/-- There is exactly one retained discrepancy for each original edge or parent occurrence. -/
theorem errors_length {target : InverseRootPolynomial.Coordinate} {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers : UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests target covers)
      : requests.errors.length = parents.length := by
  induction requests with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The finite discrepancy sum equals the source sum minus the reciprocal sum. -/
theorem errors_sum {target : InverseRootPolynomial.Coordinate} {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers : UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests target covers)
      :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.errors = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      requests.sourceValues - Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.reciprocalValues := by
  induction requests with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons head tail ih =>
      change (head.sourceIncrement - head.reciprocalIncrement) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        tail.errors = _
      rw [ih]
      change (head.sourceIncrement - head.reciprocalIncrement) +
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.sourceValues - Data.Gaussian.Norm.Sum.Basic.gaussianSum
          tail.reciprocalValues) =
        (head.sourceIncrement + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.sourceValues) -
          (head.reciprocalIncrement + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.reciprocalValues)
      ring1

/-- Each retained discrepancy satisfies the common bound for its original finite request. -/
theorem errors_bounded {target : InverseRootPolynomial.Coordinate} {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers : UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests target covers)
      : ∀ value ∈ requests.errors, Data.Gaussian.Norm.Basic.normSq value ≤ target := by
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
structure Request {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (covers :
  UniformReciprocalCover.ParentCovers parents) (target : InverseRootPolynomial.Coordinate) where
  /-- The cached per-parent budget paying both factors of the original parent count. -/ localTarget :
    InverseRootPolynomial.Coordinate
  /-- The local target is the finite aggregate per-term budget for the requested target and exact parent length. -/
    localTarget_eq : localTarget = Aggregate.perTerm target parents.length
  /-- The retained primitive requests on the original parent and cover spine. -/ requests :
    Requests localTarget covers
  /-- The cached finite sum of original source primitive increments. -/ sourceIntegral : InverseRootPolynomial.Gaussian
  /-- The cached source integral is exactly the sum of retained source request values. -/ sourceIntegral_eq :
    sourceIntegral = Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.sourceValues
  /-- The cached finite sum of reciprocal cover increments. -/ reciprocalIntegral : InverseRootPolynomial.Gaussian
  /-- The cached reciprocal integral is exactly the sum of retained reciprocal request values. -/ reciprocalIntegral_eq
    : reciprocalIntegral = Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.reciprocalValues
  /-- The cached squared-norm discrepancy bound for these exact retained samples. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The cached aggregate error is the per-parent target multiplied by both factors of the original parent count. -/
    error_eq : error = (parents.length : InverseRootPolynomial.Coordinate) * ((parents.length :
    InverseRootPolynomial.Coordinate) * localTarget)
  /-- The cached discrepancy bound is strictly below the requested target. -/ error_lt : error < target
  /-- The squared norm of the retained source-minus-reciprocal discrepancy satisfies the cached bound. -/ close :
    Data.Gaussian.Norm.Basic.normSq (sourceIntegral - reciprocalIntegral) ≤ error

constructive_injectivity Request

/-- Choose a shared polynomial stage paying the positive target and cache the source and reciprocal primitive
increments. -/
@[expose] def request {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (covers :
  UniformReciprocalCover.ParentCovers parents)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      Request covers target := by
  let localTarget := Aggregate.perTerm target parents.length
  let requests := Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Requests.build
    localTarget (Aggregate.perTerm_positive positive _) covers
  refine ⟨localTarget, rfl, requests, Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.sourceValues, rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.reciprocalValues, rfl,
    (parents.length : InverseRootPolynomial.Coordinate) * ((parents.length : InverseRootPolynomial.Coordinate) *
      localTarget), rfl,
    Aggregate.count_mul_perTerm_lt positive _, ?_⟩
  rw [← requests.errors_sum]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le requests.errors _ requests.errors_bounded
  rw [requests.errors_length] at estimate
  exact estimate

end ParentCovers

namespace Segment

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)

variable {start finish : Gaussian} {segment :
  Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial
  (Ambient curve) start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}

/-- Choose a shared polynomial stage paying the positive target and cache the source and reciprocal primitive
increments. -/
@[expose] def request (cache : PreparedClearPathModels.ParentCache piece.path differential sheet) (side :
  PreparedBoundarySegments.SameSide (Cuts.Ambient curve) start finish)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    (covers : UniformReciprocalCover.ParentCovers cache.parents) ×
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.Request covers target :=
  let covers := Segment.acquire cache side
  ⟨covers, Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.ParentCovers.request covers target
    positive⟩

end Segment
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
