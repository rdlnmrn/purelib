module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization

/-!
# Full finite area comparison on an actual reciprocal cap arc

The source/cap drift estimate controls every dyadic intermediate vertex.
Its ribbon estimate retains and pays the open endpoint correction, and the
resulting area request is independent of the additional spatial depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive (sourceValue
  sourceValue_left)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcComparison.Sample (comparisonValue comparison_error)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.BoundaryRibbon (area area_bound)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea dyadicDifference)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {comparison :
    Data regular cell}
  {index : Nat} {box : Geometry.Rational.Box} {capSample :
    Cap.Primitives.Sample cap differential index box}

namespace Data

/-- The fixed full inverse-arc area comparison scale from the original source slope and coefficient discrepancy. -/
@[expose] def areaScale (comparison : Data regular cell) : Coordinate :=
  comparison.scale * (144 * data.sourceSlope + 160 * comparison.scale)

/-- The original source slope and coefficient discrepancy give a nonnegative full-area scale. -/
theorem areaScale_nonnegative (comparison : Data regular cell) : 0 ≤
  (areaScale comparison) :=
  Arithmetic.mul_nonneg_direct comparison.scale_nonnegative
    (add_nonneg (Arithmetic.mul_nonneg_direct (by decide +kernel) data.sourceSlope_nonnegative)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) comparison.scale_nonnegative))

end Data

namespace Sample

/-- Anchor the actual inverse-arc polynomial at its cached first value. -/
@[expose] def capValue (sample : Sample comparison capSample) (parameter : Coordinate)
  : Gaussian :=
  sample.pullback.value.eval (parent.edge.point parameter)⁻¹ - sample.firstValue

/-- The retained anchored cap primitive vanishes at its original left endpoint. -/
theorem capValue_left (sample : Sample comparison capSample) :
  (capValue sample) edge.left.parameter = 0 := by
  rw [capValue, sample.firstValue_eq,
    Data.Gaussian.Basic.sub_self]

/-- The retained anchored cap primitive equals its cached increment at the original right endpoint. -/
theorem capValue_right (sample : Sample comparison capSample) :
  (capValue sample) edge.right.parameter = sample.increment
  := by
  rw [capValue, sample.increment_eq, sample.lastValue_eq]

/-- The source-to-cap primitive drift on any original subinterval satisfies the retained geometric discrepancy times its
squared width. -/
theorem drift_bound (source : SourcePrimitive data index) (right : Sample
  comparison capSample)
    {first last : Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Basic.normSq ((CellPrimitive.sourceValue source edge last -
      (capValue right) last) -
      (CellPrimitive.sourceValue source edge first -
        (capValue right) first)) ≤
      quarterRadius comparison.scale index * (last - first) ^ 2 := by
  have identity : (CellPrimitive.sourceValue source edge last -
    (capValue right) last) -
      (CellPrimitive.sourceValue source edge first -
        (capValue right) first) =
      comparisonValue right source last - comparisonValue right source first
        := by
    dsimp only [CellPrimitive.sourceValue, capValue,
      comparisonValue]
    ring1
  rw [identity]
  exact comparison_error right source firstInside lastInside

/-- The original anchored source and cap values differ by at most the retained cell-width discrepancy bound. -/
theorem point_error_bound (source : SourcePrimitive data index) (right : Sample
  comparison capSample)
    {parameter : Coordinate} (inside : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Basic.normSq (CellPrimitive.sourceValue source edge parameter -
      (capValue right) parameter) ≤
      quarterRadius comparison.scale index * (edge.right.parameter - edge.left.parameter) ^ 2 := by
  have estimate := drift_bound source right ⟨le_rfl,
    cell.ordered.le⟩ inside
  rw [CellPrimitive.sourceValue_left, capValue_left,
    Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.sub_zero] at estimate
  exact estimate.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.pow_le_pow_direct (Arithmetic.sub_nonneg_direct inside.1)
      (Arithmetic.sub_le_sub_right_direct inside.2 _) 2)
    (quarterRadius_nonneg comparison.scale_nonnegative index))

/-- Every actual cap subarc increment satisfies the original source slope and retained geometric discrepancy ceiling. -/
theorem cap_increment_bound (source : SourcePrimitive data index) (right : Sample
  comparison capSample)
    {first last : Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Basic.normSq ((capValue
      right) last - (capValue right) first) ≤
      (2 * (data.sourceSlope + quarterRadius comparison.scale index)) * (last - first) ^ 2 := by
  have sourceBound : Basic.normSq (CellPrimitive.sourceValue source edge last -
    CellPrimitive.sourceValue source edge first) ≤ data.sourceSlope * (last - first) ^ 2 := by
    have identity : CellPrimitive.sourceValue source edge last - CellPrimitive.sourceValue source edge first =
        source.primitive.value.eval (parent.edge.point last) - source.primitive.value.eval (parent.edge.point first) :=
          by
      dsimp only [CellPrimitive.sourceValue]; ring1
    rw [identity]
    exact source.increment_bound ⟨edge.left.inside.1.trans firstInside.1, firstInside.2.trans edge.right.inside.2⟩
      ⟨edge.left.inside.1.trans lastInside.1, lastInside.2.trans edge.right.inside.2⟩
  have identity : (capValue right) last -
    (capValue right) first =
      (CellPrimitive.sourceValue source edge last - CellPrimitive.sourceValue source edge first) -
        ((CellPrimitive.sourceValue source edge last -
          (capValue right) last) - (CellPrimitive.sourceValue
          source edge first - (capValue right) first)) := by
          ring1
  rw [identity]
  exact (Bounds.normSq_sub_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add sourceBound (drift_bound source right
        firstInside lastInside)) (by decide)).trans_eq (by ring1))

/-- The complete finite ribbon retains its open endpoint correction. The bound is independent of the additional dyadic
spatial depth. -/
theorem ribbon_bound (source : SourcePrimitive data index) (right : Sample
  comparison capSample) (depth : Nat) :
    Basic.normSq (dyadicDifference (CellPrimitive.sourceValue source
      edge) (capValue right) depth edge.left.parameter
      edge.right.parameter) ≤
      8 * quarterRadius comparison.scale index * (8 * data.sourceSlope + 9 *
        quarterRadius comparison.scale index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have estimate := DyadicBoundaryRibbon.dyadicDifference_bound (CellPrimitive.sourceValue source edge)
    (capValue right)
    (Arithmetic.mul_nonneg_direct (quarterRadius_nonneg comparison.scale_nonnegative
      index)
      (Arithmetic.sq_nonneg_direct _))
    (fun _ inside => point_error_bound source right inside)
    (fun _ _ firstInside lastInside => cap_increment_bound
      source right firstInside lastInside)
    (fun _ _ firstInside lastInside => drift_bound source
      right firstInside lastInside)
    depth ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩ cell.ordered.le
  exact estimate.trans_eq (by ring1)

/-- Paying, rather than dropping, the endpoint term compares the full anchored primitive areas. All intermediate dyadic
excursions are retained. -/
theorem area_error (source : SourcePrimitive data index) (right : Sample
  comparison capSample) (depth : Nat) :
    Basic.normSq (dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      dyadicArea (capValue right) depth
        edge.left.parameter edge.right.parameter) ≤
      quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 *
        quarterRadius comparison.scale index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  let endpoint := area ((capValue right)
    edge.right.parameter)
    (CellPrimitive.sourceValue source edge edge.right.parameter -
      (capValue right) edge.right.parameter)
  have rightBound := cap_increment_bound source right
    ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩
  rw [capValue_left, Data.Gaussian.Basic.sub_zero] at rightBound
  have endpointBound : Basic.normSq endpoint ≤
      8 * (data.sourceSlope + quarterRadius comparison.scale index) * quarterRadius
        comparison.scale index *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
    have multiplied := Arithmetic.mul_le_mul_direct rightBound
      (point_error_bound source right ⟨cell.ordered.le,
        le_rfl⟩) (Basic.normSq_nonneg _)
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg data.sourceSlope_nonnegative (quarterRadius_nonneg comparison.scale_nonnegative
            index)))
        (Arithmetic.sq_nonneg_direct _))
    calc
      Basic.normSq endpoint ≤ 4 * Basic.normSq
        ((capValue right) edge.right.parameter) *
          Basic.normSq (CellPrimitive.sourceValue source edge edge.right.parameter -
            (capValue right) edge.right.parameter) :=
            area_bound _ _
      _ = 4 * (Basic.normSq
        ((capValue right) edge.right.parameter) *
          Basic.normSq (CellPrimitive.sourceValue source edge edge.right.parameter -
            (capValue right) edge.right.parameter)) := by
            ring1
      _ ≤ 4 * ((2 * (data.sourceSlope + quarterRadius comparison.scale index) * (edge.right.parameter -
        edge.left.parameter) ^ 2) *
          (quarterRadius comparison.scale index * (edge.right.parameter - edge.left.parameter) ^ 2)) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct multiplied (by decide)
      _ = _ := by ring1
  have identity : dyadicArea (CellPrimitive.sourceValue source edge) depth edge.left.parameter
    edge.right.parameter -
      dyadicArea (capValue right) depth
        edge.left.parameter edge.right.parameter =
      dyadicDifference (CellPrimitive.sourceValue source edge)
        (capValue right) depth edge.left.parameter
        edge.right.parameter + endpoint := by
    rw [dyadicDifference, CellPrimitive.sourceValue_left,
      capValue_left]
    dsimp only [endpoint, area]
    ring1
  rw [identity]
  exact (Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (ribbon_bound source right depth)
        endpointBound) (by decide)).trans_eq (by ring1))

/-- A pre-index scale supplies the geometric area rate at every spatial depth. Increasing the inverse-model index
controls the entire local area, not merely the final integral. -/
theorem area_error_geometric (source : SourcePrimitive data index) (right :
  Sample comparison capSample) (depth : Nat) :
    Basic.normSq (dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      dyadicArea (capValue right) depth
        edge.left.parameter edge.right.parameter) ≤
      quarterRadius (Data.areaScale comparison)
        index * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have errorLe : quarterRadius comparison.scale index ≤ comparison.scale := by
    simpa only [quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone comparison.scale_nonnegative (Nat.zero_le index)
  apply (area_error source right depth).trans
  have coefficient : quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 *
    quarterRadius comparison.scale index) ≤
      quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 * comparison.scale) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl (Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide +kernel)))
      (quarterRadius_nonneg comparison.scale_nonnegative index)
  have identity : quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 *
    comparison.scale) =
      quarterRadius (Data.areaScale comparison)
        index := by
    rw [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow,
      Data.areaScale]
    ring1
  rw [identity] at coefficient
  exact Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
    (Arithmetic.pow_nonneg_direct (Arithmetic.sub_nonneg_direct cell.ordered.le) 4)

end Sample

set_option genInjectivity false in
/-- A certified finite stage controls the complete local area at every additional dyadic spatial depth. The quartic
cell-width factor is retained. -/
structure AreaRequest (comparison : Data regular cell) (target : Coordinate) (floor :
  Nat) where
  /-- The cached fixed full-area comparison scale. -/ scale : Coordinate
  /-- The cached scale is the original arc comparison's area scale. -/ scale_eq : scale =
    (Data.areaScale comparison)
  /-- The retained polynomial stage paying the original area target. -/ index : Nat
  /-- The stage is the first geometric quarter-radius search result at or above the original floor. -/ index_eq : index
    = firstQuarterBelow scale floor target
  /-- The retained stage respects the original caller floor. -/ floor_le : floor ≤ index
  /-- The cached geometric area discrepancy scale at the retained stage. -/ error : Coordinate
  /-- The cached discrepancy is the quarter-radius of the original area scale. -/ error_eq : error =
    quarterRadius scale index
  /-- The cached discrepancy is strictly below the original requested target. -/ error_lt : error < target

constructive_injectivity AreaRequest

namespace AreaRequest

/-- Select a common polynomial stage paying the full original inverse-arc area target at every additional spatial depth.
-/
@[expose] def build (comparison : Data regular cell) (target : Coordinate) (positive :
  0 < target) (floor : Nat) :
    AreaRequest comparison target floor :=
  let scale := (Data.areaScale comparison)
  let index := firstQuarterBelow scale floor target
  ⟨scale, rfl, index, rfl, Search.firstQuarterBelow_ge _ _ _, quarterRadius scale index, rfl,
    Search.firstQuarterBelow_accurate _ (Data.areaScale_nonnegative
      comparison) _ _ positive⟩

/-- Every later shared polynomial stage pays the full original arc-area target with its fourth-power cell-width factor.
-/
theorem accurate {target : Coordinate} {floor : Nat} (request :
  AreaRequest comparison target floor)
    (source : SourcePrimitive data index) (sample : Sample comparison capSample)
      (later : request.index ≤ index) (depth : Nat) :
    Basic.normSq (dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      dyadicArea (Sample.capValue sample) depth
        edge.left.parameter edge.right.parameter) <
      target * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have positive : 0 < (edge.right.parameter - edge.left.parameter) ^ 4 :=
    Arithmetic.pow_pos_direct (Arithmetic.sub_pos_direct cell.ordered) 4
  have laterError : quarterRadius (Data.areaScale
    comparison) index ≤ request.error :=
    (quarterRadius_antitone (Data.areaScale_nonnegative
      comparison) later).trans_eq
      (by rw [request.error_eq, request.scale_eq])
  exact ((Sample.area_error_geometric source sample depth).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct laterError positive.le)).trans_lt
      (Arithmetic.mul_lt_mul_of_pos_right_direct request.error_lt positive)

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
