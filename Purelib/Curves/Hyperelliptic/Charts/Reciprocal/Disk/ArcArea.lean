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

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {comparison :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace Data

/-- The fixed full inverse-arc area comparison scale from the original source slope and coefficient discrepancy. -/
@[expose] def areaScale (comparison : ArcSamples.Data regular cell) : Coordinate :=
  comparison.scale * (144 * data.sourceSlope + 160 * comparison.scale)

/-- The original source slope and coefficient discrepancy give a nonnegative full-area scale. -/
theorem areaScale_nonnegative (comparison : ArcSamples.Data regular cell) : 0 ≤
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale comparison) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct comparison.scale_nonnegative
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) data.sourceSlope_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) comparison.scale_nonnegative))

end Data

namespace Sample

/-- Anchor the actual inverse-arc polynomial at its cached first value. -/
@[expose] def capValue (sample : ArcSamples.Sample comparison capSample) (parameter : InverseRootPolynomial.Coordinate)
  : Gaussian :=
  sample.pullback.value.eval (parent.edge.point parameter)⁻¹ - sample.firstValue

/-- The retained anchored cap primitive vanishes at its original left endpoint. -/
theorem capValue_left (sample : ArcSamples.Sample comparison capSample) :
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue sample) edge.left.parameter = 0 := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue, sample.firstValue_eq,
    Data.Gaussian.Basic.sub_self]

/-- The retained anchored cap primitive equals its cached increment at the original right endpoint. -/
theorem capValue_right (sample : ArcSamples.Sample comparison capSample) :
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue sample) edge.right.parameter = sample.increment
  := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue, sample.increment_eq, sample.lastValue_eq]

/-- The source-to-cap primitive drift on any original subinterval satisfies the retained geometric discrepancy times its
squared width. -/
theorem drift_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right : ArcSamples.Sample
  comparison capSample)
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq ((CellPrimitive.sourceValue source edge last -
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) last) -
      (CellPrimitive.sourceValue source edge first -
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) first)) ≤
      Geometric.Basic.quarterRadius comparison.scale index * (last - first) ^ 2 := by
  have identity : (CellPrimitive.sourceValue source edge last -
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) last) -
      (CellPrimitive.sourceValue source edge first -
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) first) =
      ArcComparison.Sample.comparisonValue right source last - ArcComparison.Sample.comparisonValue right source first
        := by
    dsimp only [CellPrimitive.sourceValue, Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue,
      ArcComparison.Sample.comparisonValue]
    ring1
  rw [identity]
  exact ArcComparison.Sample.comparison_error right source firstInside lastInside

/-- The original anchored source and cap values differ by at most the retained cell-width discrepancy bound. -/
theorem point_error_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right : ArcSamples.Sample
  comparison capSample)
    {parameter : InverseRootPolynomial.Coordinate} (inside : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (CellPrimitive.sourceValue source edge parameter -
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) parameter) ≤
      Geometric.Basic.quarterRadius comparison.scale index * (edge.right.parameter - edge.left.parameter) ^ 2 := by
  have estimate := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.drift_bound source right ⟨le_rfl,
    cell.ordered.le⟩ inside
  rw [CellPrimitive.sourceValue_left, Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue_left,
    Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.sub_zero] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct inside.1)
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2 _) 2)
    (Geometric.Basic.quarterRadius_nonneg comparison.scale_nonnegative index))

/-- Every actual cap subarc increment satisfies the original source slope and retained geometric discrepancy ceiling. -/
theorem cap_increment_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right : ArcSamples.Sample
  comparison capSample)
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue
      right) last - (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) first) ≤
      (2 * (data.sourceSlope + Geometric.Basic.quarterRadius comparison.scale index)) * (last - first) ^ 2 := by
  have sourceBound : Data.Gaussian.Norm.Basic.normSq (CellPrimitive.sourceValue source edge last -
    CellPrimitive.sourceValue source edge first) ≤ data.sourceSlope * (last - first) ^ 2 := by
    have identity : CellPrimitive.sourceValue source edge last - CellPrimitive.sourceValue source edge first =
        source.primitive.value.eval (parent.edge.point last) - source.primitive.value.eval (parent.edge.point first) :=
          by
      dsimp only [CellPrimitive.sourceValue]; ring1
    rw [identity]
    exact source.increment_bound ⟨edge.left.inside.1.trans firstInside.1, firstInside.2.trans edge.right.inside.2⟩
      ⟨edge.left.inside.1.trans lastInside.1, lastInside.2.trans edge.right.inside.2⟩
  have identity : (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) last -
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) first =
      (CellPrimitive.sourceValue source edge last - CellPrimitive.sourceValue source edge first) -
        ((CellPrimitive.sourceValue source edge last -
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) last) - (CellPrimitive.sourceValue
          source edge first - (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) first)) := by
          ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add sourceBound (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.drift_bound source right
        firstInside lastInside)) (by decide)).trans_eq (by ring1))

/-- The complete finite ribbon retains its open endpoint correction. The bound is independent of the additional dyadic
spatial depth. -/
theorem ribbon_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right : ArcSamples.Sample
  comparison capSample) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicDifference (CellPrimitive.sourceValue source
      edge) (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) depth edge.left.parameter
      edge.right.parameter) ≤
      8 * Geometric.Basic.quarterRadius comparison.scale index * (8 * data.sourceSlope + 9 *
        Geometric.Basic.quarterRadius comparison.scale index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have estimate := DyadicBoundaryRibbon.dyadicDifference_bound (CellPrimitive.sourceValue source edge)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg comparison.scale_nonnegative
      index)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (fun _ inside => Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.point_error_bound source right inside)
    (fun _ _ firstInside lastInside => Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.cap_increment_bound
      source right firstInside lastInside)
    (fun _ _ firstInside lastInside => Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.drift_bound source
      right firstInside lastInside)
    depth ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩ cell.ordered.le
  exact estimate.trans_eq (by ring1)

/-- Paying, rather than dropping, the endpoint term compares the full anchored primitive areas. All intermediate dyadic
excursions are retained. -/
theorem area_error (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right : ArcSamples.Sample
  comparison capSample) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) depth
        edge.left.parameter edge.right.parameter) ≤
      Geometric.Basic.quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 *
        Geometric.Basic.quarterRadius comparison.scale index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  let endpoint := BoundaryRibbon.area ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right)
    edge.right.parameter)
    (CellPrimitive.sourceValue source edge edge.right.parameter -
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) edge.right.parameter)
  have rightBound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.cap_increment_bound source right
    ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩
  rw [capValue_left, Data.Gaussian.Basic.sub_zero] at rightBound
  have endpointBound : Data.Gaussian.Norm.Basic.normSq endpoint ≤
      8 * (data.sourceSlope + Geometric.Basic.quarterRadius comparison.scale index) * Geometric.Basic.quarterRadius
        comparison.scale index *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct rightBound
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.point_error_bound source right ⟨cell.ordered.le,
        le_rfl⟩) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg data.sourceSlope_nonnegative (Geometric.Basic.quarterRadius_nonneg comparison.scale_nonnegative
            index)))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    calc
      Data.Gaussian.Norm.Basic.normSq endpoint ≤ 4 * Data.Gaussian.Norm.Basic.normSq
        ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) edge.right.parameter) *
          Data.Gaussian.Norm.Basic.normSq (CellPrimitive.sourceValue source edge edge.right.parameter -
            (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) edge.right.parameter) :=
            BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq
        ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) edge.right.parameter) *
          Data.Gaussian.Norm.Basic.normSq (CellPrimitive.sourceValue source edge edge.right.parameter -
            (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) edge.right.parameter)) := by
            ring1
      _ ≤ 4 * ((2 * (data.sourceSlope + Geometric.Basic.quarterRadius comparison.scale index) * (edge.right.parameter -
        edge.left.parameter) ^ 2) *
          (Geometric.Basic.quarterRadius comparison.scale index * (edge.right.parameter - edge.left.parameter) ^ 2)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct multiplied (by decide)
      _ = _ := by ring1
  have identity : DyadicBoundaryRibbon.dyadicArea (CellPrimitive.sourceValue source edge) depth edge.left.parameter
    edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) depth
        edge.left.parameter edge.right.parameter =
      DyadicBoundaryRibbon.dyadicDifference (CellPrimitive.sourceValue source edge)
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) depth edge.left.parameter
        edge.right.parameter + endpoint := by
    rw [DyadicBoundaryRibbon.dyadicDifference, CellPrimitive.sourceValue_left,
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue_left]
    dsimp only [endpoint, BoundaryRibbon.area]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.ribbon_bound source right depth)
        endpointBound) (by decide)).trans_eq (by ring1))

/-- A pre-index scale supplies the geometric area rate at every spatial depth. Increasing the inverse-model index
controls the entire local area, not merely the final integral. -/
theorem area_error_geometric (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  ArcSamples.Sample comparison capSample) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue right) depth
        edge.left.parameter edge.right.parameter) ≤
      Geometric.Basic.quarterRadius (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale comparison)
        index * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have errorLe : Geometric.Basic.quarterRadius comparison.scale index ≤ comparison.scale := by
    simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone comparison.scale_nonnegative (Nat.zero_le index)
  apply (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.area_error source right depth).trans
  have coefficient : Geometric.Basic.quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 *
    Geometric.Basic.quarterRadius comparison.scale index) ≤
      Geometric.Basic.quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 * comparison.scale) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide +kernel)))
      (Geometric.Basic.quarterRadius_nonneg comparison.scale_nonnegative index)
  have identity : Geometric.Basic.quarterRadius comparison.scale index * (144 * data.sourceSlope + 160 *
    comparison.scale) =
      Geometric.Basic.quarterRadius (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale comparison)
        index := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale]
    ring1
  rw [identity] at coefficient
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Order.Arithmetic.sub_nonneg_direct cell.ordered.le) 4)

end Sample

set_option genInjectivity false in
/-- A certified finite stage controls the complete local area at every additional dyadic spatial depth. The quartic
cell-width factor is retained. -/
structure AreaRequest (comparison : ArcSamples.Data regular cell) (target : InverseRootPolynomial.Coordinate) (floor :
  Nat) where
  /-- The cached fixed full-area comparison scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The cached scale is the original arc comparison's area scale. -/ scale_eq : scale =
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale comparison)
  /-- The retained polynomial stage paying the original area target. -/ index : Nat
  /-- The stage is the first geometric quarter-radius search result at or above the original floor. -/ index_eq : index
    = Search.firstQuarterBelow scale floor target
  /-- The retained stage respects the original caller floor. -/ floor_le : floor ≤ index
  /-- The cached geometric area discrepancy scale at the retained stage. -/ error : InverseRootPolynomial.Coordinate
  /-- The cached discrepancy is the quarter-radius of the original area scale. -/ error_eq : error =
    Geometric.Basic.quarterRadius scale index
  /-- The cached discrepancy is strictly below the original requested target. -/ error_lt : error < target

constructive_injectivity AreaRequest

namespace AreaRequest

/-- Select a common polynomial stage paying the full original inverse-arc area target at every additional spatial depth.
-/
@[expose] def build (comparison : ArcSamples.Data regular cell) (target : InverseRootPolynomial.Coordinate) (positive :
  0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.AreaRequest comparison target floor :=
  let scale := (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale comparison)
  let index := Search.firstQuarterBelow scale floor target
  ⟨scale, rfl, index, rfl, Search.firstQuarterBelow_ge _ _ _, Geometric.Basic.quarterRadius scale index, rfl,
    Search.firstQuarterBelow_accurate _ (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale_nonnegative
      comparison) _ _ positive⟩

/-- Every later shared polynomial stage pays the full original arc-area target with its fourth-power cell-width factor.
-/
theorem accurate {target : InverseRootPolynomial.Coordinate} {floor : Nat} (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.AreaRequest comparison target floor)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (sample : ArcSamples.Sample comparison capSample)
      (later : request.index ≤ index) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue sample) depth
        edge.left.parameter edge.right.parameter) <
      target * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have positive : 0 < (edge.right.parameter - edge.left.parameter) ^ 4 :=
    Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.sub_pos_direct cell.ordered) 4
  have laterError : Geometric.Basic.quarterRadius (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale
    comparison) index ≤ request.error :=
    (quarterRadius_antitone (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Data.areaScale_nonnegative
      comparison) later).trans_eq
      (by rw [request.error_eq, request.scale_eq])
  exact ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.area_error_geometric source sample depth).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct laterError positive.le)).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct request.error_lt positive)

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
