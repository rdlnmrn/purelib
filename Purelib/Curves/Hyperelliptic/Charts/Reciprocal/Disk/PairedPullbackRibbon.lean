module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

/-! Two parity-independent source/pullback comparisons on a common parameter interval.
Reciprocal covers may differ. The bilinear ribbon keeps both endpoint terms
and bounds all intermediate excursions independently of spatial depth. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Rat
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive (sourceValue)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample (capValue capValue_left point_error_bound
  cap_increment_bound drift_bound)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : ParameterEdge} {cell :
    Cell data edge} {otherCell :
    Cell otherData otherEdge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {comparison :
    Data regular cell} {otherComparison :
    Data regular otherCell}
  {index : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}

/-- Increasing the original comparison scale increases its quarter-radius at every fixed stage. -/
private theorem quarter_mono {left right : InverseRootPolynomial.Coordinate} (order : left ≤ right) (index : Nat) :
    Geometric.Basic.quarterRadius left index ≤ Geometric.Basic.quarterRadius right index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide) index)

/-- The squared width of an original ordered covered parameter edge is at most one. -/
private theorem edge_width_le_one (edge : ClearSheetContinuation.Subdivision.ParameterEdge) (ordered :
  edge.left.parameter ≤ edge.right.parameter) :
    (edge.right.parameter - edge.left.parameter)^2 ≤ 1 := by
  have width := Fraction.Order.Arithmetic.sub_le_sub_direct edge.right.inside.2 edge.left.inside.1
  rw [(show ∀ x : Fraction.Rational, x - 0 = x by intro x; ring1)] at width
  exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) width
    2).trans_eq (by decide)

namespace PairedPullback

/-- Pair the two original source primitives at the common parameter while retaining each cell's own anchor. -/
@[expose] def pairedSourceValues (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
  UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (parameter : InverseRootPolynomial.Coordinate) : PrimitivePoint := ⟨sourceValue source edge parameter,
      CellPrimitive.sourceValue otherSource otherEdge parameter⟩

/-- Pair the retained cap pullback values at the common parameter with their separate original anchors. -/
@[expose] def pairedCapValues (left : ArcSamples.Sample comparison sample) (right : ArcSamples.Sample otherComparison
  otherSample)
    (parameter : InverseRootPolynomial.Coordinate) : PrimitivePoint := ⟨capValue left parameter, ArcArea.Sample.capValue
      right parameter⟩

/-- The interval is contained in both actual cells; their anchoring points need not coincide. No endpoint correction has
been discarded. -/
theorem paired_ribbon_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
  UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : ArcSamples.Sample comparison sample) (right : ArcSamples.Sample otherComparison otherSample)
    {lower upper : InverseRootPolynomial.Coordinate}
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicDifference
      (pairedSourceValues (edge := edge)
      (otherEdge := otherEdge) source otherSource)
      (pairedCapValues left right) depth
        lower upper) ≤
      Geometric.Basic.quarterRadius (8 * max comparison.scale otherComparison.scale *
        (8 * max data.sourceSlope otherData.sourceSlope + 9 * max comparison.scale otherComparison.scale)) index *
        (upper - lower)^2 := by
  let scale := max comparison.scale otherComparison.scale
  let slope := max data.sourceSlope otherData.sourceSlope
  let error := Geometric.Basic.quarterRadius scale index
  have scaleNonnegative : 0 ≤ scale := comparison.scale_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)
  have errorNonnegative : 0 ≤ error := Geometric.Basic.quarterRadius_nonneg scaleNonnegative index
  have leftError : Geometric.Basic.quarterRadius comparison.scale index ≤ error :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.quarter_mono (Fraction.Order.Basic.le_max_left _ _)
    index
  have rightError : Geometric.Basic.quarterRadius otherComparison.scale index ≤ error :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.quarter_mono (Fraction.Order.Basic.le_max_right _
    _) index
  have leftInside (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter := ⟨leftLower.trans inside.1, inside.2.trans
        leftUpper⟩
  have rightInside (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      otherEdge.left.parameter ≤ parameter ∧ parameter ≤ otherEdge.right.parameter := ⟨rightLower.trans inside.1,
        inside.2.trans rightUpper⟩
  have points (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      PrimitivePoint.Bounded
        ((pairedSourceValues (edge :=
          edge) (otherEdge := otherEdge) source otherSource parameter).sub
          (pairedCapValues left right
          parameter)) error := by
    constructor
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (ArcArea.Sample.point_error_bound source left (leftInside parameter inside)).trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.edge_width_le_one edge cell.ordered.le)
          (Geometric.Basic.quarterRadius_nonneg comparison.scale_nonnegative index)).trans
          ((mul_one _).trans_le leftError))
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (ArcArea.Sample.point_error_bound otherSource right (rightInside parameter inside)).trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.edge_width_le_one otherEdge
          otherCell.ordered.le)
          (Geometric.Basic.quarterRadius_nonneg otherComparison.scale_nonnegative index)).trans
          ((mul_one _).trans_le rightError))
  have movement (first last : InverseRootPolynomial.Coordinate) (firstInside : lower ≤ first ∧ first ≤ upper)
      (lastInside : lower ≤ last ∧ last ≤ upper) :
      PrimitivePoint.Bounded
        ((pairedCapValues left right
          last).sub (pairedCapValues
          left right first)) (2 * (slope + error) * (last - first)^2) := by
    constructor
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (ArcArea.Sample.cap_increment_bound source left (leftInside first firstInside) (leftInside last
        lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_max_left _ _) leftError) (by decide)) (Fraction.Order.Arithmetic.sq_nonneg_direct
            _))
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (ArcArea.Sample.cap_increment_bound otherSource right (rightInside first firstInside) (rightInside last
        lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_max_right _ _) rightError) (by decide)) (Fraction.Order.Arithmetic.sq_nonneg_direct
            _))
  have drift (first last : InverseRootPolynomial.Coordinate) (firstInside : lower ≤ first ∧ first ≤ upper)
      (lastInside : lower ≤ last ∧ last ≤ upper) :
      PrimitivePoint.Bounded
      (((pairedSourceValues (edge :=
        edge) (otherEdge := otherEdge) source otherSource last).sub
        (pairedCapValues left right
        last)).sub
        ((pairedSourceValues (edge :=
          edge) (otherEdge := otherEdge) source otherSource first).sub
          (pairedCapValues left right
          first))) (error * (last - first)^2) := by
    constructor
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (ArcArea.Sample.drift_bound source left (leftInside first firstInside) (leftInside last lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct leftError
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (ArcArea.Sample.drift_bound otherSource right (rightInside first firstInside) (rightInside last
        lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rightError
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have estimate := DyadicBilinearBoundaryRibbon.dyadicDifference_bound _ _ points movement drift depth
    ⟨le_rfl, ordered⟩ ⟨ordered, le_rfl⟩ ordered
  have errorLe : error ≤ scale := Geometric.Basic.quarterRadius_le_scale scaleNonnegative index
  have enlarged : 8 * error * (8 * slope + 9 * error) * (upper - lower)^2 ≤
      8 * error * (8 * slope + 9 * scale) * (upper - lower)^2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (8 * slope))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) errorNonnegative))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (upper - lower))
  apply estimate.trans
  calc
    _ = 8 * error * (8 * slope + 9 * error) * (upper - lower)^2 := by ring1
    _ ≤ 8 * error * (8 * slope + 9 * scale) * (upper - lower)^2 := enlarged
    _ = _ := by
      dsimp only [error, scale, slope, -eq_self, -iff_self]
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
      ring1

end PairedPullback

/-- The squared distance from the original covered edge's left endpoint to an internal parameter is at most one. -/
private theorem parameter_width {parameter : InverseRootPolynomial.Coordinate}
    (inside : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
    (parameter - edge.left.parameter)^2 ≤ 1 := by
  have bound := Fraction.Order.Arithmetic.sub_le_sub_direct (inside.2.trans edge.right.inside.2) edge.left.inside.1
  rw [(show ∀ x : Fraction.Rational, x - 0 = x by intro x; ring1)] at bound
  exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct inside.1) bound
    2).trans_eq (by decide)

/-- The retained cap value and original source-to-cap error satisfy their separate fixed point ceilings. -/
private theorem sample_point_bounds (source : UniformReciprocalPrimitives.SourcePrimitive data index) (retained :
  ArcSamples.Sample comparison sample)
    {parameter : InverseRootPolynomial.Coordinate} (inside : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq (ArcArea.Sample.capValue retained parameter) ≤ 2 * (data.sourceSlope +
      Geometric.Basic.quarterRadius comparison.scale index) ∧
      Data.Gaussian.Norm.Basic.normSq (CellPrimitive.sourceValue source edge parameter -
        ArcArea.Sample.capValue retained parameter) ≤ Geometric.Basic.quarterRadius comparison.scale index := by
  have capBound := ArcArea.Sample.cap_increment_bound source retained ⟨le_rfl, cell.ordered.le⟩ inside
  rw [ArcArea.Sample.capValue_left retained, Data.Gaussian.Basic.sub_zero] at capBound
  have errorNonnegative := Geometric.Basic.quarterRadius_nonneg comparison.scale_nonnegative index
  have capNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg data.sourceSlope_nonnegative errorNonnegative)
  exact ⟨capBound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (parameter_width inside) capNonnegative).trans_eq
    (mul_one _)),
    (ArcArea.Sample.point_error_bound source retained inside).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (edge_width_le_one edge cell.ordered.le)
        errorNonnegative).trans_eq (mul_one _))⟩

/-- Both original open endpoint wedge corrections satisfy the retained paired ribbon's geometric scale. -/
theorem PairedPullback.endpoint_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
  UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : ArcSamples.Sample comparison sample) (right : ArcSamples.Sample otherComparison otherSample)
    {lower upper : InverseRootPolynomial.Coordinate}
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right upper)
      ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues (edge :=
        edge) (otherEdge := otherEdge) source otherSource upper).sub
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right
          upper)) -
      Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues
        left right lower)
        ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues (edge :=
          edge) (otherEdge := otherEdge) source otherSource lower).sub
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right
            lower))) ≤
      Geometric.Basic.quarterRadius (8 * max comparison.scale otherComparison.scale *
        (8 * max data.sourceSlope otherData.sourceSlope + 9 * max comparison.scale otherComparison.scale)) index := by
  let scale := max comparison.scale otherComparison.scale
  let slope := max data.sourceSlope otherData.sourceSlope
  let error := Geometric.Basic.quarterRadius scale index
  have scaleNonnegative : 0 ≤ scale := comparison.scale_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)
  have slopeNonnegative : 0 ≤ slope := data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)
  have errorNonnegative : 0 ≤ error := Geometric.Basic.quarterRadius_nonneg scaleNonnegative index
  have errorLe : error ≤ scale := Geometric.Basic.quarterRadius_le_scale scaleNonnegative index
  have pointBound (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      Data.Gaussian.Norm.Basic.normSq (Stokes.edgeArea
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right
        parameter)
        ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues (edge :=
          edge) (otherEdge := otherEdge) source otherSource parameter).sub
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right
            parameter))) ≤ 4 * (2 * (slope + error)) * error := by
    have first := sample_point_bounds source left
      ⟨leftLower.trans inside.1, inside.2.trans leftUpper⟩
    have second := sample_point_bounds otherSource
      right ⟨rightLower.trans inside.1, inside.2.trans rightUpper⟩
    have firstError : Geometric.Basic.quarterRadius comparison.scale index ≤ error :=
      quarter_mono (Fraction.Order.Basic.le_max_left _
      _) index
    have secondError : Geometric.Basic.quarterRadius otherComparison.scale index ≤ error :=
      quarter_mono (Fraction.Order.Basic.le_max_right _
      _) index
    have firstValue := first.1
    have secondValue := second.1
    have firstDifference := first.2
    have secondDifference := second.2
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstValue secondValue firstDifference secondDifference
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    apply PrimitivePoint.area_bound
    · exact ⟨firstValue.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_max_left _ _) firstError) (by decide)),
        secondValue.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_max_right _ _) secondError) (by
          decide))⟩
    · exact ⟨firstDifference.trans firstError, secondDifference.trans secondError⟩
  have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (pointBound
      upper ⟨ordered, le_rfl⟩)
      (pointBound lower ⟨le_rfl, ordered⟩)) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have enlarged : 32 * (slope + error) * error ≤ 32 * (slope + scale) * error :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        errorLe) (by decide +kernel)) errorNonnegative
  have slack : 0 ≤ (32 * slope + 40 * scale) * error := Fraction.Order.Arithmetic.mul_nonneg_direct
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) slopeNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) scaleNonnegative)) errorNonnegative
  calc
    _ ≤ 2 * (4 * (2 * (slope + error)) * error + 4 * (2 * (slope + error)) * error) := bound
    _ = 32 * (slope + error) * error := by ring1
    _ ≤ 32 * (slope + scale) * error := enlarged
    _ ≤ 32 * (slope + scale) * error + (32 * slope + 40 * scale) * error := le_add_of_nonneg_right slack
    _ = _ := by
      dsimp only [error, scale, slope, -eq_self, -iff_self]
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
      ring1

set_option genInjectivity false in
/-- A shared finite model-stage request for two original source-to-cap pullback comparisons.

The independent covered cells retain their original slopes and anchors; the same paid scale controls the ribbon and its
explicit endpoint correction. -/
structure PairedPullbackRequest (comparison : ArcSamples.Data regular cell) (otherComparison : ArcSamples.Data regular
  otherCell)
    (target : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The cached common paired ribbon and endpoint discrepancy scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The scale uses the maxima of the two original cell comparison scales and source slopes. -/ scale_eq : scale = 8 *
    max comparison.scale otherComparison.scale *
    (8 * max data.sourceSlope otherData.sourceSlope + 9 * max comparison.scale otherComparison.scale)
  /-- The retained common paired discrepancy scale is nonnegative. -/ scale_nonnegative : 0 ≤ scale
  /-- The cached common polynomial stage paying the original paired target. -/ index : Nat
  /-- The stage is the first original quarter-radius search result at or above the caller's minimum. -/ index_eq : index
    = Search.firstQuarterBelow scale minimum target
  /-- The retained common stage respects the original minimum stage. -/ minimum_le : minimum ≤ index
  /-- The cached geometric discrepancy at the retained common stage. -/ error : InverseRootPolynomial.Coordinate
  /-- The discrepancy is exactly the original common scale's quarter-radius. -/ error_eq : error =
    Geometric.Basic.quarterRadius scale index
  /-- The retained geometric discrepancy or actual ribbon remainder is strictly below the original target. -/ accurate :
    error < target

constructive_injectivity PairedPullbackRequest

namespace PairedPullbackRequest

/-- Retain the two original comparison ceilings and select one model stage paying the paired ribbon and endpoint target.
-/
@[expose] def build (comparison : ArcSamples.Data regular cell) (otherComparison : ArcSamples.Data regular otherCell)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest comparison otherComparison
      target minimum := by
  let scale := max comparison.scale otherComparison.scale
  let slope := max data.sourceSlope otherData.sourceSlope
  let total := 8 * scale * (8 * slope + 9 * scale)
  have scaleNonnegative : 0 ≤ scale := comparison.scale_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)
  have slopeNonnegative : 0 ≤ slope := data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)
  have totalNonnegative : 0 ≤ total := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) scaleNonnegative)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) slopeNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) scaleNonnegative))
  let index := Search.firstQuarterBelow total minimum target
  exact ⟨total, rfl, totalNonnegative, index, rfl, Search.firstQuarterBelow_ge total minimum target,
    Geometric.Basic.quarterRadius total index, rfl, Search.firstQuarterBelow_accurate total totalNonnegative minimum
      target positive⟩

variable {target : Coordinate} {minimum : Nat}

/-- One computed model stage pays every spatial depth on every common subinterval. This controls the ribbon remainder,
with its endpoint correction still explicitly present in `dyadicDifference`. -/
theorem accurate_at (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest
  comparison otherComparison target minimum)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : ArcSamples.Sample comparison sample) (right : ArcSamples.Sample otherComparison otherSample)
    (later : request.index ≤ index) {lower upper : InverseRootPolynomial.Coordinate}
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicDifference
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues (edge := edge)
        (otherEdge := otherEdge) source otherSource)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right) depth
        lower upper) < target := by
  have bound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.paired_ribbon_bound
    source otherSource left right leftLower leftUpper rightLower rightUpper ordered depth
  rw [← request.scale_eq] at bound
  have width : (upper - lower)^2 ≤ 1 := by
    have interval := Fraction.Order.Arithmetic.sub_le_sub_direct (leftUpper.trans edge.right.inside.2)
      (edge.left.inside.1.trans leftLower)
    rw [(show ∀ x : Fraction.Rational, x - 0 = x by intro x; ring1)] at interval
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) interval
      2).trans_eq (by decide)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width (Geometric.Basic.quarterRadius_nonneg
    request.scale_nonnegative index)
  rw [mul_one] at paid
  exact bound.trans_lt (paid.trans_lt ((quarterRadius_antitone request.scale_nonnegative later).trans_lt
    (request.error_eq ▸ request.accurate)))

set_option genInjectivity false in
/-- The cached actual paired source area, cap area and open endpoint correction.

Both original covered intervals and the common model floor remain explicit, and the retained remainder is certified
against the requested target. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest
  comparison otherComparison target minimum)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : ArcSamples.Sample comparison sample) (right : ArcSamples.Sample otherComparison otherSample)
    (lower upper : InverseRootPolynomial.Coordinate) (depth : Nat) where
  /-- The actual paired polynomial samples meet the original common request stage. -/ later : request.index ≤ index
  /-- The common lower parameter lies after the original first cell's left endpoint. -/ leftLower : edge.left.parameter
    ≤ lower
  /-- The common upper parameter lies before the original first cell's right endpoint. -/ leftUpper : upper ≤
    edge.right.parameter
  /-- The common lower parameter lies after the original second cell's left endpoint. -/ rightLower :
    otherEdge.left.parameter ≤ lower
  /-- The common upper parameter lies before the original second cell's right endpoint. -/ rightUpper : upper ≤
    otherEdge.right.parameter
  /-- The retained common parameter interval is ordered. -/ ordered : lower ≤ upper
  /-- The cached actual bilinear dyadic area of the original paired source primitives. -/ sourceArea :
    Data.Gaussian.Basic.Canonical
  /-- The cached source area uses the original source value pair on the exact common interval and depth. -/
    sourceArea_eq : sourceArea = DyadicBilinearBoundaryRibbon.dyadicArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues (edge := edge)
      (otherEdge := otherEdge) source otherSource) depth lower upper
  /-- The cached actual bilinear dyadic area of the retained cap pullbacks. -/ capArea : Data.Gaussian.Basic.Canonical
  /-- The cached cap area uses the original retained cap pair on the exact common interval and depth. -/ capArea_eq :
    capArea = DyadicBilinearBoundaryRibbon.dyadicArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right) depth
    lower upper
  /-- The cached open endpoint wedge correction for the original paired paths. -/ endpoint :
    Data.Gaussian.Basic.Canonical
  /-- The endpoint correction is exactly the upper endpoint wedge minus the lower endpoint wedge. -/ endpoint_eq :
    endpoint =
    Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues
      left right upper)
      ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues (edge :=
        edge) (otherEdge := otherEdge) source otherSource upper).sub
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right
          upper)) -
    Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues
      left right lower)
      ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues (edge :=
        edge) (otherEdge := otherEdge) source otherSource lower).sub
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left right
          lower))
  /-- The cached original source-minus-cap area after retaining the explicit endpoint correction. -/ remainder :
    Data.Gaussian.Basic.Canonical
  /-- The cached remainder is exactly source area minus cap area minus the original endpoint term. -/ remainder_eq :
    remainder = sourceArea - capArea - endpoint
  /-- The retained geometric discrepancy or actual ribbon remainder is strictly below the original target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq remainder < target

constructive_injectivity Evaluation

/-- The retained original endpoint correction separately satisfies the requested squared-norm target. -/
theorem Evaluation.endpoint_accurate {request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest comparison otherComparison
  target minimum}
    {source : UniformReciprocalPrimitives.SourcePrimitive data index} {otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index}
    {left : ArcSamples.Sample comparison sample} {right : ArcSamples.Sample otherComparison otherSample}
    {lower upper : InverseRootPolynomial.Coordinate} {depth : Nat} (evaluated :
      Evaluation request source
      otherSource left right lower upper depth) :
    Data.Gaussian.Norm.Basic.normSq evaluated.endpoint < target := by
  rw [evaluated.endpoint_eq]
  have bound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.endpoint_bound source
    otherSource left right
    evaluated.leftLower evaluated.leftUpper evaluated.rightLower evaluated.rightUpper evaluated.ordered
  rw [← request.scale_eq] at bound
  exact bound.trans_lt ((quarterRadius_antitone request.scale_nonnegative evaluated.later).trans_lt
    (request.error_eq ▸ request.accurate))

/-- The complete original paired source and cap areas differ by less than four targets after paying the retained
endpoint term. -/
theorem Evaluation.full_accurate {request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest comparison otherComparison
  target minimum}
    {source : UniformReciprocalPrimitives.SourcePrimitive data index} {otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index}
    {left : ArcSamples.Sample comparison sample} {right : ArcSamples.Sample otherComparison otherSample}
    {lower upper : InverseRootPolynomial.Coordinate} {depth : Nat} (evaluated :
      Evaluation request source
      otherSource left right lower upper depth) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.capArea) < 4 * target := by
  have identity : evaluated.sourceArea - evaluated.capArea = evaluated.remainder + evaluated.endpoint := by
    rw [evaluated.remainder_eq]; ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct evaluated.accurate evaluated.endpoint_accurate)).trans_eq (by ring1))

/-- Materialize the complete paired ribbon exactly once. In particular the open endpoint contribution is retained as
data, not hidden in an error flag. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest
  comparison otherComparison target minimum)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : ArcSamples.Sample comparison sample) (right : ArcSamples.Sample otherComparison otherSample)
    (later : request.index ≤ index) (lower upper : InverseRootPolynomial.Coordinate)
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
      Evaluation request source
      otherSource left right lower upper depth := by
  let sourceValues := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedSourceValues
    (edge := edge) (otherEdge := otherEdge) source otherSource
  let capValues := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullback.pairedCapValues left
    right
  let sourceArea := DyadicBilinearBoundaryRibbon.dyadicArea sourceValues depth lower upper
  let capArea := DyadicBilinearBoundaryRibbon.dyadicArea capValues depth lower upper
  let endpoint := Stokes.edgeArea (capValues upper) ((sourceValues upper).sub (capValues upper)) -
    Stokes.edgeArea (capValues lower) ((sourceValues lower).sub (capValues lower))
  exact ⟨later, leftLower, leftUpper, rightLower, rightUpper, ordered,
    sourceArea, rfl, capArea, rfl, endpoint, rfl, sourceArea - capArea - endpoint, rfl,
    request.accurate_at source otherSource left right later leftLower leftUpper rightLower rightUpper ordered depth⟩

end PairedPullbackRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon
