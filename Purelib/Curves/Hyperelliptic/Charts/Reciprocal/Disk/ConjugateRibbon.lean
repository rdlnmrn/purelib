module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Conjugate source-to-cap ribbons reuse the retained scalar models and the
computed paired request. The complete open endpoint correction remains in
`dyadicDifference`; no holomorphic area-vanishing assertion is used. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon
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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon.RegularAlignment (pairedSourceValues
  pairedCapValues)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedRibbon (PairedRibbonRequest)
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

/-- Increasing the original retained scale increases its quarter-radius at every stage. -/
private theorem quarter_mono {left right : InverseRootPolynomial.Coordinate} (order : left ≤ right) (index : Nat) :
    Geometric.Basic.quarterRadius left index ≤ Geometric.Basic.quarterRadius right index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide) index)

/-- The squared width of an original ordered covered parameter edge is at most one. -/
private theorem edge_width_le_one (edge : ClearSheetContinuation.Subdivision.ParameterEdge) (ordered :
  edge.left.parameter ≤ edge.right.parameter) :
    (edge.right.parameter - edge.left.parameter) ^ 2 ≤ 1 := by
  have width := Fraction.Order.Arithmetic.sub_le_sub_direct edge.right.inside.2 edge.left.inside.1
  rw [(show (1 : Fraction.Rational) - 0 = 1 from by decide)] at width
  exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) width
    2).trans_eq (by decide)

/-- Conjugating the first coordinate commutes with subtraction of the original paired primitive points. -/
private theorem conjugate_sub (first last : Stokes.PrimitivePoint) :
    ConjugateIncrementComparison.conjugateFirst (first.sub last) =
      (ConjugateIncrementComparison.conjugateFirst first).sub (ConjugateIncrementComparison.conjugateFirst last) := by
  apply congrArg₂ PrimitivePoint.mk
  · apply Data.Gaussian.Basic.ext
    · rfl
    · simp only [ConjugateIncrementComparison.conjugateFirst, PrimitivePoint.sub, Data.Gaussian.Basic.conj,
        Data.Gaussian.Basic.sub_im]; ring1
  · rfl

/-- Conjugating the first paired coordinate preserves the original point, movement and drift ceilings for the finite
ribbon remainder. -/
private theorem conjugate_ribbon_bound (left right : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint)
    {lower upper error slope drift : InverseRootPolynomial.Coordinate}
    (points : ∀ parameter, lower ≤ parameter ∧ parameter ≤ upper →
      PrimitivePoint.Bounded ((left parameter).sub (right parameter)) error)
    (movement : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitivePoint.Bounded ((right last).sub (right first)) (slope * (last - first) ^ 2))
    (difference : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitivePoint.Bounded (((left last).sub (right last)).sub ((left first).sub (right first))) (drift * (last -
        first) ^ 2))
    (depth : Nat) (ordered : lower ≤ upper) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicDifference
      (fun parameter => ConjugateIncrementComparison.conjugateFirst (left parameter))
      (fun parameter => ConjugateIncrementComparison.conjugateFirst (right parameter)) depth lower upper) ≤
      8 * error * (4 * slope + drift) * (upper - lower) ^ 2 := by
  apply DyadicBilinearBoundaryRibbon.dyadicDifference_bound
    (fun parameter => ConjugateIncrementComparison.conjugateFirst (left parameter))
    (fun parameter => ConjugateIncrementComparison.conjugateFirst (right parameter))
    (errorLe := fun parameter inside => ConjugateIncrementComparison.conjugateFirst_error (points parameter inside))
    (rightLe := fun first last firstInside lastInside =>
      ConjugateIncrementComparison.conjugateFirst_error (movement first last firstInside lastInside))
    (driftLe := ?_) depth ⟨le_rfl, ordered⟩ ⟨ordered, le_rfl⟩ ordered
  intro first last firstInside lastInside
  rw [← conjugate_sub, ←
    conjugate_sub]
  exact ConjugateIncrementComparison.conjugateFirst_error (difference first last firstInside lastInside)

namespace RegularAlignment

/-- The interval is contained in both actual cells; their anchoring points need not coincide. No endpoint correction has
been discarded. -/
theorem conjugate_paired_ribbon_bound (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
  UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : SheetAlignment.RegularAlignment retained) (right : SheetAlignment.RegularAlignment otherRetained)
    {lower upper : InverseRootPolynomial.Coordinate}
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicDifference (fun parameter =>
      ConjugateIncrementComparison.conjugateFirst
        (RegularAlignment.pairedSourceValues (edge := edge) (otherEdge := otherEdge) source otherSource parameter))
      (fun parameter => ConjugateIncrementComparison.conjugateFirst (RegularAlignment.pairedCapValues left right
        parameter)) depth lower upper) ≤
      Geometric.Basic.quarterRadius (8 * max (RegularComparison.Data.regularScale comparison)
        (RegularComparison.Data.regularScale otherComparison) *
        (8 * max data.sourceSlope otherData.sourceSlope + 9 * max (RegularComparison.Data.regularScale comparison)
          (RegularComparison.Data.regularScale otherComparison))) index *
        (upper - lower) ^ 2 := by
  let scale := max (RegularComparison.Data.regularScale comparison) (RegularComparison.Data.regularScale
    otherComparison)
  let slope := max data.sourceSlope otherData.sourceSlope
  let error := Geometric.Basic.quarterRadius scale index
  have scaleNonnegative : 0 ≤ scale := (RegularComparison.Data.regularScale_nonnegative comparison).trans
    (Fraction.Order.Basic.le_max_left _ _)
  have errorNonnegative : 0 ≤ error := Geometric.Basic.quarterRadius_nonneg scaleNonnegative index
  have leftError : Geometric.Basic.quarterRadius (RegularComparison.Data.regularScale comparison) index ≤ error :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon.quarter_mono (Fraction.Order.Basic.le_max_left _ _)
    index
  have rightError : Geometric.Basic.quarterRadius (RegularComparison.Data.regularScale otherComparison) index ≤ error :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon.quarter_mono (Fraction.Order.Basic.le_max_right _ _)
    index
  have leftInside (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter := ⟨leftLower.trans inside.1, inside.2.trans
        leftUpper⟩
  have rightInside (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      otherEdge.left.parameter ≤ parameter ∧ parameter ≤ otherEdge.right.parameter := ⟨rightLower.trans inside.1,
        inside.2.trans rightUpper⟩
  have points (parameter : InverseRootPolynomial.Coordinate) (inside : lower ≤ parameter ∧ parameter ≤ upper) :
      PrimitivePoint.Bounded ((RegularAlignment.pairedSourceValues (edge := edge) (otherEdge := otherEdge) source
        otherSource parameter).sub (RegularAlignment.pairedCapValues left right parameter)) error := by
    constructor <;> rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    · exact (RegularAlignment.point_error_bound source left (leftInside parameter inside)).trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon.edge_width_le_one edge cell.ordered.le)
          (Geometric.Basic.quarterRadius_nonneg (RegularComparison.Data.regularScale_nonnegative comparison)
            index)).trans
          ((mul_one _).trans_le leftError))
    · exact (RegularAlignment.point_error_bound otherSource right (rightInside parameter inside)).trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon.edge_width_le_one otherEdge otherCell.ordered.le)
          (Geometric.Basic.quarterRadius_nonneg (RegularComparison.Data.regularScale_nonnegative otherComparison)
            index)).trans
          ((mul_one _).trans_le rightError))
  have movement (first last : InverseRootPolynomial.Coordinate) (firstInside : lower ≤ first ∧ first ≤ upper)
      (lastInside : lower ≤ last ∧ last ≤ upper) :
      PrimitivePoint.Bounded ((RegularAlignment.pairedCapValues left right last).sub (RegularAlignment.pairedCapValues
        left right first)) (2 * (slope + error) * (last - first) ^ 2) := by
    constructor <;> rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    · exact (RegularAlignment.cap_increment_bound source left (leftInside first firstInside) (leftInside last
        lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_max_left _ _) leftError) (by decide)) (Fraction.Order.Arithmetic.sq_nonneg_direct
            _))
    · exact (RegularAlignment.cap_increment_bound otherSource right (rightInside first firstInside) (rightInside last
        lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_max_right _ _) rightError) (by decide)) (Fraction.Order.Arithmetic.sq_nonneg_direct
            _))
  have drift (first last : InverseRootPolynomial.Coordinate) (firstInside : lower ≤ first ∧ first ≤ upper)
      (lastInside : lower ≤ last ∧ last ≤ upper) :
      PrimitivePoint.Bounded (((RegularAlignment.pairedSourceValues (edge := edge) (otherEdge := otherEdge) source
        otherSource last).sub (RegularAlignment.pairedCapValues left right last)).sub
        ((RegularAlignment.pairedSourceValues (edge := edge) (otherEdge := otherEdge) source otherSource first).sub
          (RegularAlignment.pairedCapValues left right first))) (error * (last - first) ^ 2) := by
    constructor <;> rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    · exact (RegularAlignment.drift_bound source left (leftInside first firstInside) (leftInside last lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct leftError
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    · exact (RegularAlignment.drift_bound otherSource right (rightInside first firstInside) (rightInside last
        lastInside)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rightError
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have estimate := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon.conjugate_ribbon_bound _ _ points
    movement drift depth ordered
  have errorLe : error ≤ scale := Geometric.Basic.quarterRadius_le_scale scaleNonnegative index
  have enlarged : 8 * error * (8 * slope + 9 * error) * (upper - lower) ^ 2 ≤
      8 * error * (8 * slope + 9 * scale) * (upper - lower) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (8 * slope))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) errorNonnegative))
        (Fraction.Order.Arithmetic.sq_nonneg_direct (upper - lower))
  apply estimate.trans
  calc
    _ = 8 * error * (8 * slope + 9 * error) * (upper - lower) ^ 2 := by ring1
    _ ≤ 8 * error * (8 * slope + 9 * scale) * (upper - lower) ^ 2 := enlarged
    _ = _ := by
      dsimp only [error, scale, slope]
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

end RegularAlignment

namespace PairedRibbonRequest
variable {target : Coordinate} {minimum : Nat}

/-- One computed model stage pays every spatial depth on every common subinterval. This controls the ribbon remainder,
with its endpoint correction still explicitly present in `dyadicDifference`. -/
theorem conjugate_accurate_at (request : PairedRibbon.PairedRibbonRequest comparison otherComparison target minimum)
    (source : UniformReciprocalPrimitives.SourcePrimitive data index) (otherSource :
      UniformReciprocalPrimitives.SourcePrimitive otherData index)
    (left : SheetAlignment.RegularAlignment retained) (right : SheetAlignment.RegularAlignment otherRetained)
    (later : request.index ≤ index) {lower upper : InverseRootPolynomial.Coordinate}
    (leftLower : edge.left.parameter ≤ lower) (leftUpper : upper ≤ edge.right.parameter)
    (rightLower : otherEdge.left.parameter ≤ lower) (rightUpper : upper ≤ otherEdge.right.parameter)
    (ordered : lower ≤ upper) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicDifference
      (fun parameter => ConjugateIncrementComparison.conjugateFirst
        (RegularAlignment.pairedSourceValues (edge := edge) (otherEdge := otherEdge) source otherSource parameter))
      (fun parameter => ConjugateIncrementComparison.conjugateFirst (RegularAlignment.pairedCapValues left right
        parameter)) depth lower upper) < target := by
  have bound :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon.RegularAlignment.conjugate_paired_ribbon_bound source
    otherSource left right leftLower leftUpper rightLower rightUpper ordered depth
  rw [← request.scale_eq] at bound
  have width : (upper - lower) ^ 2 ≤ 1 := by
    have interval := Fraction.Order.Arithmetic.sub_le_sub_direct (leftUpper.trans edge.right.inside.2)
      (edge.left.inside.1.trans leftLower)
    rw [(show (1 : Fraction.Rational) - 0 = 1 from by decide)] at interval
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) interval
      2).trans_eq (by decide)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width (Geometric.Basic.quarterRadius_nonneg
    request.scale_nonnegative index)
  rw [mul_one] at paid
  exact bound.trans_lt (paid.trans_lt ((quarterRadius_antitone request.scale_nonnegative later).trans_lt
    (request.error_eq ▸ request.accurate)))

end PairedRibbonRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateRibbon
