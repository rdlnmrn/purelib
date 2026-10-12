module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
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
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Rat
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon

/-! Two actual source/cap comparisons on a common parameter interval.
Reciprocal covers may differ. The bilinear ribbon keeps both endpoint terms
and bounds all intermediate excursions independently of spatial depth. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment (RegularAlignment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive (sourceValue)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Cell data edge} {otherCell :
    Cell otherData otherEdge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {comparison :
    Data regular cell} {otherComparison :
    Data regular otherCell}
  {index : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  {retained : Sample comparison sample} {otherRetained :
    Sample otherComparison otherSample}

/-- Increasing the retained geometric scale increases its quarter-radius at every original stage. -/
private theorem quarter_mono {left right : InverseRootPolynomial.Coordinate} (order : left ≤ right) (index : Nat) :
    Geometric.Basic.quarterRadius left index ≤ Geometric.Basic.quarterRadius right index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide) index)

/-- The squared width of an original ordered covered parameter edge is at most one. -/
private theorem edge_width_le_one (edge : ClearSheetContinuation.Subdivision.ParameterEdge) (ordered :
  edge.left.parameter ≤ edge.right.parameter) :
    (edge.right.parameter - edge.left.parameter)^2 ≤ 1 := by
  have zeroDifference (value : Purelib.Data.Rat.Fraction.Rational) : value - 0 = value := by ring1
  have width := Fraction.Order.Arithmetic.sub_le_sub_direct edge.right.inside.2 edge.left.inside.1
  rw [zeroDifference] at width
  exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) width
    2).trans_eq (by decide)

namespace RegularAlignment

/-- Pair the two original source primitives at one parameter while retaining their separate cell anchors. -/
@[expose] def pairedSourceValues (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
  UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (parameter : InverseRootPolynomial.Coordinate) : PrimitivePoint := ⟨sourceValue source edge parameter,
      CellPrimitive.sourceValue otherSource otherEdge parameter⟩

/-- Pair the two retained signed cap primitive values at their original common parameter. -/
@[expose] def pairedCapValues (left : SheetAlignment.RegularAlignment retained) (right : SheetAlignment.RegularAlignment
  otherRetained)
    (parameter : InverseRootPolynomial.Coordinate) : PrimitivePoint := ⟨RegularAlignment.capValue left parameter,
      RegularAlignment.capValue right parameter⟩

/-- The interval is contained in both actual cells; their anchoring points need not coincide. No endpoint correction has
been discarded. -/
theorem paired_ribbon_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
  UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : SheetAlignment.RegularAlignment retained) (right : SheetAlignment.RegularAlignment otherRetained)
    {lower upper : InverseRootPolynomial.Coordinate}
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicDifference
      (pairedSourceValues (edge := edge)
      (otherEdge := otherEdge) source otherSource)
      (pairedCapValues left right) depth lower
        upper) ≤
      Geometric.Basic.quarterRadius (8 * max (RegularComparison.Data.regularScale comparison)
        (RegularComparison.Data.regularScale otherComparison) *
        (8 * max data.sourceSlope otherData.sourceSlope + 9 * max (RegularComparison.Data.regularScale comparison)
          (RegularComparison.Data.regularScale otherComparison))) index *
        (upper - lower)^2 := by
  let scale := max (RegularComparison.Data.regularScale comparison) (RegularComparison.Data.regularScale
    otherComparison)
  let slope := max data.sourceSlope otherData.sourceSlope
  let error := Geometric.Basic.quarterRadius scale index
  have scaleNonnegative : 0 ≤ scale := (RegularComparison.Data.regularScale_nonnegative comparison).trans
    (Fraction.Order.Basic.le_max_left _ _)
  have errorNonnegative : 0 ≤ error := Geometric.Basic.quarterRadius_nonneg scaleNonnegative index
  have leftError : Geometric.Basic.quarterRadius (RegularComparison.Data.regularScale comparison) index ≤ error :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.quarter_mono (Fraction.Order.Basic.le_max_left _ _) index
  have rightError : Geometric.Basic.quarterRadius (RegularComparison.Data.regularScale otherComparison) index ≤ error :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.quarter_mono (Fraction.Order.Basic.le_max_right _ _) index
  have leftInside (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter := ⟨leftLower.trans inside.1, inside.2.trans
        leftUpper⟩
  have rightInside (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      otherEdge.left.parameter ≤ parameter ∧ parameter ≤ otherEdge.right.parameter := ⟨rightLower.trans inside.1,
        inside.2.trans rightUpper⟩
  have points (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      PrimitivePoint.Bounded
        ((pairedSourceValues (edge := edge)
        (otherEdge := otherEdge) source otherSource parameter).sub
        (pairedCapValues left right
        parameter)) error := by
    constructor
    · have scalar := RegularAlignment.point_error_bound source left (leftInside parameter inside)
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.edge_width_le_one edge cell.ordered.le)
          (Geometric.Basic.quarterRadius_nonneg (RegularComparison.Data.regularScale_nonnegative comparison)
            index)).trans
          ((mul_one _).trans_le leftError))
    · have scalar := RegularAlignment.point_error_bound otherSource right (rightInside parameter inside)
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.edge_width_le_one otherEdge otherCell.ordered.le)
          (Geometric.Basic.quarterRadius_nonneg (RegularComparison.Data.regularScale_nonnegative otherComparison)
            index)).trans
          ((mul_one _).trans_le rightError))
  have movement (first last : InverseRootPolynomial.Coordinate) (firstInside : lower ≤ first ∧ first ≤ upper)
      (lastInside : lower ≤ last ∧ last ≤ upper) :
      PrimitivePoint.Bounded ((pairedCapValues
        left right last).sub (pairedCapValues
        left right first)) (2 * (slope + error) * (last - first)^2) := by
    constructor
    · have scalar := RegularAlignment.cap_increment_bound source left (leftInside first firstInside) (leftInside last
        lastInside)
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_max_left data.sourceSlope otherData.sourceSlope) leftError) (by decide))
            (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    · have scalar := RegularAlignment.cap_increment_bound otherSource right (rightInside first firstInside) (rightInside
        last lastInside)
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_max_right data.sourceSlope otherData.sourceSlope) rightError) (by decide))
            (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have drift (first last : InverseRootPolynomial.Coordinate) (firstInside : lower ≤ first ∧ first ≤ upper)
      (lastInside : lower ≤ last ∧ last ≤ upper) :
      PrimitivePoint.Bounded
        (((pairedSourceValues (edge := edge)
        (otherEdge := otherEdge) source otherSource last).sub
        (pairedCapValues left right last)).sub
        ((pairedSourceValues (edge := edge)
          (otherEdge := otherEdge) source otherSource first).sub
          (pairedCapValues left right first)))
          (error * (last - first)^2) := by
    constructor
    · have scalar := RegularAlignment.drift_bound source left (leftInside first firstInside) (leftInside last
        lastInside)
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct leftError
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    · have scalar := RegularAlignment.drift_bound otherSource right (rightInside first firstInside) (rightInside last
        lastInside)
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
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
      dsimp only [error, scale, slope]
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
      ring1

end RegularAlignment

set_option genInjectivity false in
/-- A common polynomial-stage request for the original paired source-to-cap ribbon.

The scale retains both cell comparison bounds and source slopes; it pays every finite subdivision depth while keeping
the open endpoint correction explicit. -/
structure PairedRibbonRequest (comparison : ArcSamples.Data regular cell) (otherComparison : ArcSamples.Data regular
  otherCell)
    (target : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The cached common paired ribbon discrepancy scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The scale uses the maxima of both original regular comparison ceilings and source slopes. -/ scale_eq : scale = 8
    * max (RegularComparison.Data.regularScale comparison) (RegularComparison.Data.regularScale otherComparison) *
    (8 * max data.sourceSlope otherData.sourceSlope + 9 * max (RegularComparison.Data.regularScale comparison)
      (RegularComparison.Data.regularScale otherComparison))
  /-- The retained paired discrepancy scale is nonnegative. -/ scale_nonnegative : 0 ≤ scale
  /-- The cached common polynomial stage paying the original target. -/ index : Nat
  /-- The stage is the first quarter-radius search result at or above the original minimum. -/ index_eq : index =
    Search.firstQuarterBelow scale minimum target
  /-- The retained common stage respects the original minimum stage. -/ minimum_le : minimum ≤ index
  /-- The cached geometric discrepancy at the retained common stage. -/ error : InverseRootPolynomial.Coordinate
  /-- The discrepancy is exactly the retained scale's quarter-radius. -/ error_eq : error =
    Geometric.Basic.quarterRadius scale index
  /-- The retained geometric discrepancy or actual ribbon remainder is strictly below the original target. -/ accurate :
    error < target

constructive_injectivity PairedRibbonRequest

namespace PairedRibbonRequest

/-- Cache the original paired discrepancy scale and select one common stage paying the retained target. -/
@[expose] def build (comparison : ArcSamples.Data regular cell) (otherComparison : ArcSamples.Data regular otherCell)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.PairedRibbonRequest comparison otherComparison target
      minimum := by
  let scale := max (RegularComparison.Data.regularScale comparison) (RegularComparison.Data.regularScale
    otherComparison)
  let slope := max data.sourceSlope otherData.sourceSlope
  let total := 8 * scale * (8 * slope + 9 * scale)
  have scaleNonnegative : 0 ≤ scale := (RegularComparison.Data.regularScale_nonnegative comparison).trans
    (Fraction.Order.Basic.le_max_left _ _)
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
theorem accurate_at (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.PairedRibbonRequest comparison
  otherComparison target minimum)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : SheetAlignment.RegularAlignment retained) (right : SheetAlignment.RegularAlignment otherRetained)
    (later : request.index ≤ index) {lower upper : InverseRootPolynomial.Coordinate}
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicDifference
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedSourceValues (edge := edge)
        (otherEdge := otherEdge) source otherSource)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedCapValues left right) depth lower
        upper) < target := by
  have zeroDifference (value : Purelib.Data.Rat.Fraction.Rational) : value - 0 = value := by ring1
  have bound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.paired_ribbon_bound source
    otherSource left right leftLower leftUpper rightLower rightUpper ordered depth
  rw [← request.scale_eq] at bound
  have width : (upper - lower)^2 ≤ 1 := by
    have interval := Fraction.Order.Arithmetic.sub_le_sub_direct (leftUpper.trans edge.right.inside.2)
      (edge.left.inside.1.trans leftLower)
    rw [zeroDifference] at interval
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) interval
      2).trans_eq (by decide)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width (Geometric.Basic.quarterRadius_nonneg
    request.scale_nonnegative index)
  rw [mul_one] at paid
  exact bound.trans_lt (paid.trans_lt ((quarterRadius_antitone request.scale_nonnegative later).trans_lt
    (request.error_eq ▸ request.accurate)))

set_option genInjectivity false in
/-- The original paired source and cap areas with their actual open endpoint correction.

The common interval retains containment in both original cells, and the cached remainder is certified against the paid
target. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.PairedRibbonRequest comparison
  otherComparison target minimum)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : SheetAlignment.RegularAlignment retained) (right : SheetAlignment.RegularAlignment otherRetained)
    (lower upper : InverseRootPolynomial.Coordinate) (depth : Nat) where
  /-- Both original paired polynomial samples meet the retained common stage. -/ later : request.index ≤ index
  /-- The common lower parameter is after the original first cell's left endpoint. -/ leftLower : edge.left.parameter ≤
    lower
  /-- The common upper parameter is before the original first cell's right endpoint. -/ leftUpper : upper ≤
    edge.right.parameter
  /-- The common lower parameter is after the original second cell's left endpoint. -/ rightLower :
    otherEdge.left.parameter ≤ lower
  /-- The common upper parameter is before the original second cell's right endpoint. -/ rightUpper : upper ≤
    otherEdge.right.parameter
  /-- The retained common parameter interval is ordered. -/ ordered : lower ≤ upper
  /-- The cached actual bilinear dyadic area of the original paired source primitives. -/ sourceArea :
    InverseRootPolynomial.Gaussian
  /-- The cached source area uses the original value pair on the exact common interval and depth. -/ sourceArea_eq :
    sourceArea = DyadicBilinearBoundaryRibbon.dyadicArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedSourceValues (edge := edge)
      (otherEdge := otherEdge) source otherSource) depth lower upper
  /-- The cached actual bilinear dyadic area of the retained signed cap pair. -/ capArea :
    InverseRootPolynomial.Gaussian
  /-- The cached cap area uses the original retained cap pair on the exact common interval and depth. -/ capArea_eq :
    capArea = DyadicBilinearBoundaryRibbon.dyadicArea
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedCapValues left right) depth lower
    upper
  /-- The cached open endpoint wedge correction of the original paired paths. -/ endpoint :
    InverseRootPolynomial.Gaussian
  /-- The retained endpoint correction is the original upper wedge minus the lower wedge. -/ endpoint_eq : endpoint =
    Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedCapValues left
      right upper)
      ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedSourceValues (edge := edge)
        (otherEdge := otherEdge) source otherSource upper).sub
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedCapValues left right upper)) -
    Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedCapValues left
      right lower)
      ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedSourceValues (edge := edge)
        (otherEdge := otherEdge) source otherSource lower).sub
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedCapValues left right lower))
  /-- The cached source-minus-cap area after retaining the original endpoint correction. -/ remainder :
    InverseRootPolynomial.Gaussian
  /-- The cached remainder is exactly source area minus cap area minus the original endpoint term. -/ remainder_eq :
    remainder = sourceArea - capArea - endpoint
  /-- The retained geometric discrepancy or actual ribbon remainder is strictly below the original target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq remainder < target

constructive_injectivity Evaluation

/-- Materialize the complete paired ribbon exactly once. In particular the open endpoint contribution is retained as
data, not hidden in an error flag. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.PairedRibbonRequest
  comparison otherComparison target minimum)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : SheetAlignment.RegularAlignment retained) (right : SheetAlignment.RegularAlignment otherRetained)
    (later : request.index ≤ index) (lower upper : InverseRootPolynomial.Coordinate)
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
      Evaluation request source otherSource
      left right lower upper depth := by
  let sourceValues := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedSourceValues (edge
    := edge) (otherEdge := otherEdge) source otherSource
  let capValues := Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment.pairedCapValues left right
  let sourceArea := DyadicBilinearBoundaryRibbon.dyadicArea sourceValues depth lower upper
  let capArea := DyadicBilinearBoundaryRibbon.dyadicArea capValues depth lower upper
  let endpoint := Stokes.edgeArea (capValues upper) ((sourceValues upper).sub (capValues upper)) -
    Stokes.edgeArea (capValues lower) ((sourceValues lower).sub (capValues lower))
  exact ⟨later, leftLower, leftUpper, rightLower, rightUpper, ordered,
    sourceArea, rfl, capArea, rfl, endpoint, rfl, sourceArea - capArea - endpoint, rfl,
    request.accurate_at source otherSource left right later leftLower leftUpper rightLower rightUpper ordered depth⟩

end PairedRibbonRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
