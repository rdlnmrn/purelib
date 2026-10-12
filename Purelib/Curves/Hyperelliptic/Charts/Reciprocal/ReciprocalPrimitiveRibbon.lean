module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
public import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitiveGlue
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
open Purelib.Riemann.Readings
open Purelib.Riemann.Branches

/-!
# Area comparison on actual reciprocal primitive arcs

Anchor both primitives at the same source cut. The finite ribbon estimate
pays their pointwise mismatch and its changing increments at every spatial
depth. The open endpoint correction is bounded explicitly, not discarded.
-/

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive CellPrimitive)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Integration.Path.BoundaryRibbon (area area_bound)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea dyadicDifference)

variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {patch : PreparedPatch parent} {data :
    Data patch count}
  {edge : ParameterEdge}

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data

/-- The original source primitive's common squared-increment ceiling, including differential and parent displacement
bounds. -/
@[expose] def sourceSlope (data : UniformReciprocalModels.Data patch count) : Coordinate :=
  2 * (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant (PreparedPrimitiveSamples.differentialNumerator differential)
    (patch.neighborhood count).base.box *
    data.inverseUpper) * Data.Gaussian.Norm.Basic.normSq parent.model.displacement

/-- The original source primitive slope ceiling is nonnegative. -/
theorem sourceSlope_nonnegative (data : UniformReciprocalModels.Data patch count) : 0 ≤ data.sourceSlope :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _).le
        data.inverseUpper_positive.le))
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)

/-- The pre-refinement geometric scale paying reciprocal ribbon and open-endpoint area errors. -/
@[expose] def areaScale (data : UniformReciprocalModels.Data patch count) : Coordinate :=
  (UniformReciprocalPrimitives.Data.errorScale data) * (144 * data.sourceSlope + 160 *
    (UniformReciprocalPrimitives.Data.errorScale data))

/-- The retained geometric area-error scale is nonnegative. -/
theorem areaScale_nonnegative (data : UniformReciprocalModels.Data patch count) : 0 ≤ data.areaScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (UniformReciprocalPrimitives.Data.errorScale_nonnegative data)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) data.sourceSlope_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (UniformReciprocalPrimitives.Data.errorScale_nonnegative data)))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive

/-- The original source primitive increment is bounded by the common slope ceiling times the squared parameter
displacement. -/
theorem increment_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) {first last :
  InverseRootPolynomial.Coordinate}
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (source.primitive.value.eval (parent.edge.point last) -
      source.primitive.value.eval (parent.edge.point first)) ≤
      data.sourceSlope * (last - first) ^ 2 := by
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩
  have inside (parameter : InverseRootPolynomial.Coordinate) (contained : interval.Contains parameter) :
      (patch.neighborhood count).base.box.Contains (Affine.line (parent.edge.point 0) parent.model.displacement
        parameter) := by
    rw [← UniformReciprocalCover.Cell.point_line]
    exact data.source_inside contained
  have coefficientBound (parameter : InverseRootPolynomial.Coordinate) (contained : interval.Contains parameter) :
      Data.Gaussian.Norm.Basic.normSq (source.coefficient.eval (Affine.line (parent.edge.point 0)
        parent.model.displacement parameter)) ≤
        Dense.Gaussian.Bounds.Box.denseEvalNormMajorant (PreparedPrimitiveSamples.differentialNumerator differential)
          (patch.neighborhood count).base.box * data.inverseUpper := by
    rw [← UniformReciprocalCover.Cell.point_line, source.coefficient_eq, Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant (PreparedPrimitiveSamples.differentialNumerator
        differential) (data.source_inside contained))
      (data.source_refine_norm_le index contained) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _).le
  have estimate := DensePrimitive.segment_increment_le source.primitive (parent.edge.point 0) parent.model.displacement
    interval inside _ coefficientBound
    (first := last) (last := first) lastInside firstInside
  rw [← UniformReciprocalCover.Cell.point_line, ← UniformReciprocalCover.Cell.point_line] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive

/-- The retained source primitive evaluated relative to the original cell's left endpoint. -/
@[expose] def sourceValue (source : UniformReciprocalPrimitives.SourcePrimitive data index) (edge :
  ClearSheetContinuation.Subdivision.ParameterEdge) (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  source.primitive.value.eval (parent.edge.point parameter) - source.primitive.value.eval (parent.edge.point
    edge.left.parameter)

/-- The negative reciprocal primitive difference from the original cell's inverse left endpoint. -/
@[expose] def reciprocalValue (right : UniformReciprocalPrimitives.CellPrimitive data index edge) (parameter :
  InverseRootPolynomial.Coordinate) : Gaussian :=
  -(right.primitive.value.eval (parent.edge.point parameter)⁻¹ - right.primitive.value.eval (parent.edge.point
    edge.left.parameter)⁻¹)

/-- The anchored original source primitive vanishes at the cell's left endpoint. -/
theorem sourceValue_left (source : UniformReciprocalPrimitives.SourcePrimitive data index) :
  sourceValue source edge
  edge.left.parameter = 0 := _root_.sub_self _

/-- The anchored reciprocal primitive vanishes at the original cell's left endpoint. -/
theorem reciprocalValue_left (right : UniformReciprocalPrimitives.CellPrimitive data index edge) : right.reciprocalValue
  edge.left.parameter = 0 := by
  simp only [reciprocalValue,
    Data.Gaussian.Basic.sub_self, neg_zero, -eq_self, -iff_self]
  rfl

/-- The source-minus-reciprocal discrepancy increment satisfies the retained geometric error times squared parameter
displacement. -/
theorem drift_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge)
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      ((sourceValue source edge last -
      right.reciprocalValue last) -
      (sourceValue source edge first -
        right.reciprocalValue first)) ≤
      Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (last - first) ^ 2 := by
  have identity : (sourceValue source
    edge last - right.reciprocalValue last) -
      (sourceValue source edge first -
        right.reciprocalValue first) =
      Comparison.comparisonValue parent source.primitive right.primitive last -
        Comparison.comparisonValue parent source.primitive right.primitive first := by
    dsimp only [sourceValue,
      reciprocalValue,
      Comparison.comparisonValue]
    ring1
  rw [identity]
  exact right.comparison_error source firstInside lastInside

/-- The anchored source-minus-reciprocal discrepancy is uniformly bounded by the retained geometric error times squared
cell width. -/
theorem point_error_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge)
    {parameter : InverseRootPolynomial.Coordinate} (inside : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      (sourceValue source edge
      parameter - right.reciprocalValue parameter) ≤
      Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (edge.right.parameter -
        edge.left.parameter) ^ 2 := by
  have estimate := right.drift_bound source ⟨le_rfl, right.cell.ordered.le⟩ inside
  rw [sourceValue_left,
    reciprocalValue_left,
    Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.sub_zero] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct inside.1)
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2 _) 2)
    (Geometric.Basic.quarterRadius_nonneg (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index))

/-- The reciprocal primitive increment is controlled by the source slope and retained geometric discrepancy. -/
theorem reciprocal_increment_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge)
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (right.reciprocalValue last - right.reciprocalValue first) ≤
      (2 * (data.sourceSlope + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index))
        * (last - first) ^ 2 := by
  have sourceBound : Data.Gaussian.Norm.Basic.normSq
    (sourceValue source edge last -
    sourceValue source edge first) ≤
    data.sourceSlope * (last - first) ^ 2 := by
    have identity : sourceValue source
      edge last - sourceValue source
      edge first =
        source.primitive.value.eval (parent.edge.point last) - source.primitive.value.eval (parent.edge.point first) :=
          by
      dsimp only [sourceValue]; ring1
    rw [identity]
    exact source.increment_bound ⟨edge.left.inside.1.trans firstInside.1, firstInside.2.trans edge.right.inside.2⟩
      ⟨edge.left.inside.1.trans lastInside.1, lastInside.2.trans edge.right.inside.2⟩
  have identity : right.reciprocalValue last - right.reciprocalValue first =
      (sourceValue source edge last -
        sourceValue source edge first)
        -
        ((sourceValue source edge last
          - right.reciprocalValue last) -
          (sourceValue source edge
          first - right.reciprocalValue first)) := by ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add sourceBound (right.drift_bound source firstInside lastInside)) (by decide)).trans_eq (by ring1))

/-- The complete finite ribbon retains its open endpoint correction. The bound is independent of the additional dyadic
spatial depth. -/
theorem ribbon_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicDifference
      (sourceValue source edge)
      right.reciprocalValue depth edge.left.parameter edge.right.parameter) ≤
      8 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (8 * data.sourceSlope
        + 9 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have estimate := DyadicBoundaryRibbon.dyadicDifference_bound
    (sourceValue source edge)
    right.reciprocalValue
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg
      (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (fun _ inside => right.point_error_bound source inside)
    (fun _ _ firstInside lastInside => right.reciprocal_increment_bound source firstInside lastInside)
    (fun _ _ firstInside lastInside => right.drift_bound source firstInside lastInside)
    depth ⟨le_rfl, right.cell.ordered.le⟩ ⟨right.cell.ordered.le, le_rfl⟩ right.cell.ordered.le
  exact estimate.trans_eq (by ring1)

/-- Paying, rather than dropping, the endpoint term compares the full anchored primitive areas. All intermediate dyadic
excursions are retained. -/
theorem area_error (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea
      (sourceValue source edge) depth
      edge.left.parameter edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea right.reciprocalValue depth edge.left.parameter edge.right.parameter) ≤
      Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (144 * data.sourceSlope +
        160 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  let endpoint := BoundaryRibbon.area (right.reciprocalValue edge.right.parameter)
    (sourceValue source edge
      edge.right.parameter - right.reciprocalValue edge.right.parameter)
  have rightBound := right.reciprocal_increment_bound source
    ⟨le_rfl, right.cell.ordered.le⟩ ⟨right.cell.ordered.le, le_rfl⟩
  rw [reciprocalValue_left,
    Data.Gaussian.Basic.sub_zero] at rightBound
  have endpointBound : Data.Gaussian.Norm.Basic.normSq endpoint ≤
      8 * (data.sourceSlope + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) *
        Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct rightBound
      (right.point_error_bound source ⟨right.cell.ordered.le, le_rfl⟩) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg data.sourceSlope_nonnegative (Geometric.Basic.quarterRadius_nonneg
            (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index)))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    calc
      Data.Gaussian.Norm.Basic.normSq endpoint ≤ 4 * Data.Gaussian.Norm.Basic.normSq
        (right.reciprocalValue edge.right.parameter) *
          Data.Gaussian.Norm.Basic.normSq
            (sourceValue source edge
            edge.right.parameter - right.reciprocalValue edge.right.parameter) := BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq (right.reciprocalValue edge.right.parameter) *
          Data.Gaussian.Norm.Basic.normSq
            (sourceValue source edge
            edge.right.parameter - right.reciprocalValue edge.right.parameter)) := by ring1
      _ ≤ 4 * ((2 * (data.sourceSlope + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data)
        index) * (edge.right.parameter - edge.left.parameter) ^ 2) *
          (Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index *
            (edge.right.parameter - edge.left.parameter) ^ 2)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct multiplied (by decide)
      _ = _ := by ring1
  have identity : DyadicBoundaryRibbon.dyadicArea
    (sourceValue source edge) depth
    edge.left.parameter edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea right.reciprocalValue depth edge.left.parameter edge.right.parameter =
      DyadicBoundaryRibbon.dyadicDifference
        (sourceValue source edge)
        right.reciprocalValue depth edge.left.parameter edge.right.parameter + endpoint := by
    rw [DyadicBoundaryRibbon.dyadicDifference,
      sourceValue_left,
      reciprocalValue_left]
    dsimp only [endpoint, BoundaryRibbon.area]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (right.ribbon_bound source depth) endpointBound) (by decide)).trans_eq (by ring1))

/-- A pre-index scale supplies the geometric area rate at every spatial depth. Increasing the inverse-model index
controls the entire local area, not merely the final integral. -/
theorem area_error_geometric (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea
      (sourceValue source edge) depth
      edge.left.parameter edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea right.reciprocalValue depth edge.left.parameter edge.right.parameter) ≤
      Geometric.Basic.quarterRadius data.areaScale index * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have errorLe : Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index ≤
    (UniformReciprocalPrimitives.Data.errorScale data) := by
    simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) (Nat.zero_le
        index)
  apply (right.area_error source depth).trans
  have coefficient : Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (144 *
    data.sourceSlope + 160 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) ≤
      Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (144 * data.sourceSlope +
        160 * (UniformReciprocalPrimitives.Data.errorScale data)) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide +kernel)))
      (Geometric.Basic.quarterRadius_nonneg (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index)
  have identity : Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (144 *
    data.sourceSlope + 160 * (UniformReciprocalPrimitives.Data.errorScale data)) =
      Geometric.Basic.quarterRadius data.areaScale index := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data.areaScale]
    ring1
  rw [identity] at coefficient
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Order.Arithmetic.sub_nonneg_direct right.cell.ordered.le) 4)

set_option genInjectivity false in
/-- Executable area readbacks account for every fine vertex and retain the endpoint correction. Consumers need not
recompute either area to inspect its certified comparison. -/
structure AreaSample (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge) (depth : Nat) where
  /-- The cached dyadic area of the original anchored source primitive. -/ sourceArea : InverseRootPolynomial.Gaussian
  /-- The cached source area is the exact finite dyadic area at the retained spatial depth and original cell endpoints.
  -/
  sourceArea_eq : sourceArea = DyadicBoundaryRibbon.dyadicArea
    (sourceValue source edge) depth
    edge.left.parameter edge.right.parameter
  /-- The cached dyadic area of the original anchored reciprocal primitive. -/ reciprocalArea :
    InverseRootPolynomial.Gaussian
  /-- The cached reciprocal area is the exact finite dyadic area at the same original depth and endpoints. -/
    reciprocalArea_eq : reciprocalArea = DyadicBoundaryRibbon.dyadicArea right.reciprocalValue depth edge.left.parameter
    edge.right.parameter
  /-- The cached open-endpoint cross term between the reciprocal value and its source discrepancy. -/ endpointCorrection
    : InverseRootPolynomial.Gaussian
  /-- The cached correction uses the retained reciprocal endpoint and its exact source-minus-reciprocal difference. -/
    endpointCorrection_eq : endpointCorrection = BoundaryRibbon.area (right.reciprocalValue edge.right.parameter)
    (sourceValue source edge
      edge.right.parameter - right.reciprocalValue edge.right.parameter)
  /-- The cached squared-norm ceiling for the source-minus-reciprocal area discrepancy. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The cached error is the retained geometric area rate multiplied by the fourth power of original cell width. -/
    error_eq : error = Geometric.Basic.quarterRadius data.areaScale index * (edge.right.parameter - edge.left.parameter)
    ^ 4
  /-- The two retained finite primitive areas satisfy the cached discrepancy bound. -/ close :
    Data.Gaussian.Norm.Basic.normSq (sourceArea - reciprocalArea) ≤ error

constructive_injectivity AreaSample

/-- Cache both original finite dyadic primitive areas, their open-endpoint correction and the certified geometric
discrepancy bound. -/
@[expose] def AreaSample.build (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge) (depth : Nat) :
    AreaSample source right depth :=
  ⟨dyadicArea (sourceValue source edge)
    depth edge.left.parameter edge.right.parameter, rfl,
    DyadicBoundaryRibbon.dyadicArea right.reciprocalValue depth edge.left.parameter edge.right.parameter, rfl,
    BoundaryRibbon.area (right.reciprocalValue edge.right.parameter)
      (sourceValue source edge
      edge.right.parameter - right.reciprocalValue edge.right.parameter), rfl,
    Geometric.Basic.quarterRadius data.areaScale index * (edge.right.parameter - edge.left.parameter) ^ 4, rfl,
    right.area_error_geometric source depth⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive
