module
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Periods.BilinearBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Tactic.Ring

@[expose] public section

/-! Paired primitive ribbons on the actual dyadically subdivided sides.
Every split pays both child terms and their exact half-widths. -/

namespace Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon

open Purelib.Topology.Polygon.Stokes.PrimitivePoint (sub)
open Purelib.Riemann.Periods.BilinearBoundaryRibbon.Bilinear (area_difference correction_bound)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (midpoint_affine)

section
open Purelib.Data
/-- The rational scalar type for dyadic ribbon parameters and bounds. -/
private abbrev Coordinate := Rat.Fraction.Rational
/-- The executable Gaussian rational area-value type. -/
private abbrev Gaussian := Gaussian.Basic.Canonical

end

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (midpoint midpoint_between)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data in
open Purelib.Geometry in
/-- Compute paired primitive area along a dyadically subdivided rational parameter interval. -/
def dyadicArea (values : Rat.Fraction.Rational → PrimitivePoint) (depth : Nat) (first last : Rat.Fraction.Rational) :
  Gaussian.Basic.Canonical :=
  Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary (fun point => values point.re) depth first last 0

open Purelib.Data in
/-- At depth zero the dyadic area is the single endpoint pairing. -/
theorem dyadicArea_zero (values : Rat.Fraction.Rational → PrimitivePoint) (first last : Rat.Fraction.Rational) :
    dyadicArea values 0 first last = edgeArea (values first) (values last) := rfl

section
open Purelib.Data
open Purelib.Geometry
/-- A dyadic area at successor depth is the sum of its two midpoint-child areas. -/
theorem dyadicArea_succ (values : Rat.Fraction.Rational → PrimitivePoint) (depth : Nat) (first last :
  Rat.Fraction.Rational) :
    dyadicArea values (depth + 1) first last = dyadicArea values depth first
      (Rectangle.Partition.PreparedBoxPartitions.midpoint first last) +
      dyadicArea values depth (Rectangle.Partition.PreparedBoxPartitions.midpoint first last) last := rfl

/-- Read a horizontal boundary area through its rational coordinate parameter. -/
theorem horizontalBoundary_eq_dyadicArea (values : Gaussian.Basic.Canonical → PrimitivePoint)
    (depth : Nat) (first last height : Rat.Fraction.Rational) :
    Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary values depth first last height =
      dyadicArea (fun coordinate => values ⟨coordinate, height⟩) depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary, dyadicArea_succ, ih, ih]

/-- Read a vertical boundary area through its rational coordinate parameter. -/
theorem verticalBoundary_eq_dyadicArea (values : Gaussian.Basic.Canonical → PrimitivePoint)
    (depth : Nat) (first last horizontal : Rat.Fraction.Rational) :
    Rectangle.Partition.PreparedBoxBoundary.verticalBoundary values depth first last horizontal =
      dyadicArea (fun coordinate => values ⟨horizontal, coordinate⟩) depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [Rectangle.Partition.PreparedBoxBoundary.verticalBoundary, dyadicArea_succ, ih, ih]

end

open Purelib.Data in
/-- Pointwise equal primitive readings give equal dyadic areas. -/
theorem dyadicArea_congr {left right : Rat.Fraction.Rational → PrimitivePoint} (equal : ∀ parameter, left parameter =
  right parameter)
    (depth : Nat) (first last : Rat.Fraction.Rational) : dyadicArea left depth first last = dyadicArea right depth first
      last := by
  induction depth generalizing first last with
  | zero => rw [dyadicArea_zero, dyadicArea_zero, equal, equal]
  | succ depth ih => rw [dyadicArea_succ, dyadicArea_succ, ih, ih]

open Purelib.Integration in
open Purelib.Data in
/-- Affine parameter change preserves the dyadic area with transformed endpoints. -/
theorem dyadicArea_affine (values : Rat.Fraction.Rational → PrimitivePoint) (origin slope : Rat.Fraction.Rational)
    (depth : Nat) (first last : Rat.Fraction.Rational) :
    dyadicArea (fun parameter => values (origin + slope * parameter)) depth first last =
      dyadicArea values depth (origin + slope * first) (origin + slope * last) := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [dyadicArea_succ, dyadicArea_succ, ih, ih, Path.Dyadic.DyadicBoundaryRibbon.midpoint_affine]

section
open Purelib.Data
open Purelib.Geometry
/-- A horizontal boundary reads as the same dyadic area on its unit-interval affine segment. -/
theorem horizontalBoundary_eq_lineArea (values : Gaussian.Basic.Canonical → PrimitivePoint)
    (depth : Nat) (first last height : Rat.Fraction.Rational) :
    Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary values depth first last height =
      dyadicArea (fun parameter => values (Rational.Affine.line ⟨first, height⟩
        (⟨last, height⟩ - ⟨first, height⟩) parameter)) depth 0 1 := by
  have lineEq (parameter : Rat.Fraction.Rational) :
      Rational.Affine.line ⟨first, height⟩ (⟨last, height⟩ - ⟨first, height⟩) parameter =
        ⟨first + (last - first) * parameter, height⟩ := by
    apply Gaussian.Basic.ext <;>
      simp only [Rational.Affine.line, Gaussian.Cast.Path.ofCoordinate,
        Gaussian.Basic.add_re, Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
        Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
  have affine := dyadicArea_affine (fun coordinate => values ⟨coordinate, height⟩) first (last - first) depth 0 1
  rw [Rat.Fraction.Field.mul_zero_direct, _root_.add_zero,
    Rat.Fraction.Field.mul_one_direct, show first + (last - first) = last by ring1] at affine
  exact (horizontalBoundary_eq_dyadicArea values depth first last height).trans
    (affine.symm.trans (dyadicArea_congr (fun parameter => congrArg values (lineEq parameter).symm) depth 0 1))

/-- A vertical boundary reads as the same dyadic area on its unit-interval affine segment. -/
theorem verticalBoundary_eq_lineArea (values : Gaussian.Basic.Canonical → PrimitivePoint)
    (depth : Nat) (first last horizontal : Rat.Fraction.Rational) :
    Rectangle.Partition.PreparedBoxBoundary.verticalBoundary values depth first last horizontal =
      dyadicArea (fun parameter => values (Rational.Affine.line ⟨horizontal, first⟩
        (⟨horizontal, last⟩ - ⟨horizontal, first⟩) parameter)) depth 0 1 := by
  have lineEq (parameter : Rat.Fraction.Rational) :
      Rational.Affine.line ⟨horizontal, first⟩ (⟨horizontal, last⟩ - ⟨horizontal, first⟩) parameter =
        ⟨horizontal, first + (last - first) * parameter⟩ := by
    apply Gaussian.Basic.ext <;>
      simp only [Rational.Affine.line, Gaussian.Cast.Path.ofCoordinate,
        Gaussian.Basic.add_re, Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
        Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
  have affine := dyadicArea_affine (fun coordinate => values ⟨horizontal, coordinate⟩) first (last - first) depth 0 1
  rw [Rat.Fraction.Field.mul_zero_direct, _root_.add_zero,
    Rat.Fraction.Field.mul_one_direct, show first + (last - first) = last by ring1] at affine
  exact (verticalBoundary_eq_dyadicArea values depth first last horizontal).trans
    (affine.symm.trans (dyadicArea_congr (fun parameter => congrArg values (lineEq parameter).symm) depth 0 1))

end

open Purelib.Topology in
open Purelib.Data in
/-- Subtract the two dyadic areas and their exact endpoint error contribution. -/
def dyadicDifference (left right : Rat.Fraction.Rational → PrimitivePoint) (depth : Nat) (first last :
  Rat.Fraction.Rational) : Gaussian.Basic.Canonical :=
  dyadicArea left depth first last - dyadicArea right depth first last -
    (edgeArea (right last) (Polygon.Stokes.PrimitivePoint.sub (left last) (right last)) - edgeArea (right first)
      (Polygon.Stokes.PrimitivePoint.sub (left first) (right first)))

open Purelib.Data in
open Purelib.Geometry in
/-- The corrected dyadic difference is the sum of its two midpoint-child differences. -/
theorem dyadicDifference_succ (left right : Rat.Fraction.Rational → PrimitivePoint) (depth : Nat) (first last :
  Rat.Fraction.Rational) :
    dyadicDifference left right (depth + 1) first last =
      dyadicDifference left right depth first (Rectangle.Partition.PreparedBoxPartitions.midpoint first last) +
        dyadicDifference left right depth (Rectangle.Partition.PreparedBoxPartitions.midpoint first last) last := by
  simp only [dyadicDifference, dyadicArea_succ]
  ring1

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.Geometry in
/-- The corrected dyadic ribbon difference has a depth-independent squared-length bound.

Pointwise errors, right-reading increments and error drift satisfy their common interval bounds. Every split retains
both child terms and exact half widths, giving eight times error times the slope-and-drift factor times interval length
squared. -/
theorem dyadicDifference_bound (left right : Rat.Fraction.Rational → PrimitivePoint) {lower upper error slope drift :
  Rat.Fraction.Rational}
    (errorLe : ∀ parameter, lower ≤ parameter ∧ parameter ≤ upper → Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Polygon.Stokes.PrimitivePoint.sub (left parameter) (right parameter)) error)
    (rightLe : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Polygon.Stokes.PrimitivePoint.sub (right last) (right first))
        (slope * (last - first) ^ 2))
    (driftLe : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Polygon.Stokes.PrimitivePoint.sub
        (Polygon.Stokes.PrimitivePoint.sub (left last) (right last)) (Polygon.Stokes.PrimitivePoint.sub (left first)
        (right first))) (drift * (last - first) ^ 2))
    (depth : Nat) {first last : Rat.Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (dyadicDifference left right depth first last) ≤ 8 * error * (4 * slope + drift)
      * (last - first) ^ 2 := by
  induction depth generalizing first last with
  | zero =>
      rw [dyadicDifference, dyadicArea_zero, dyadicArea_zero, area_difference, add_sub_cancel_right]
      exact correction_bound (errorLe first firstInside) (errorLe last lastInside)
        (rightLe first last firstInside lastInside) (driftLe first last firstInside lastInside)
  | succ depth ih =>
      have between := Rectangle.Partition.PreparedBoxPartitions.midpoint_between ordered
      have middleInside := And.intro (firstInside.1.trans between.1) (between.2.trans lastInside.2)
      have firstBound := ih firstInside middleInside between.1
      have lastBound := ih middleInside lastInside between.2
      have twiceHalf : ((last - first) / 2) * 2 = last - first :=
        Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      have leftHalf : Rectangle.Partition.PreparedBoxPartitions.midpoint first last - first = (last - first) / 2 := by
        unfold Rectangle.Partition.PreparedBoxPartitions.midpoint; ring1
      have rightHalf : last - Rectangle.Partition.PreparedBoxPartitions.midpoint first last = (last - first) / 2 := by
        calc
          _ = (last - first) - (last - first) / 2 := by unfold Rectangle.Partition.PreparedBoxPartitions.midpoint; ring1
          _ = ((last - first) / 2) * 2 - (last - first) / 2 := by rw [twiceHalf]
          _ = _ := by ring1
      rw [dyadicDifference_succ]
      calc
        _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (dyadicDifference left right depth first
          (Rectangle.Partition.PreparedBoxPartitions.midpoint first last)) +
            Data.Gaussian.Norm.Basic.normSq (dyadicDifference left right depth
              (Rectangle.Partition.PreparedBoxPartitions.midpoint first last) last)) :=
              Gaussian.Norm.Bounds.normSq_add_le_two _ _
        _ ≤ 2 * (8 * error * (4 * slope + drift) * (Rectangle.Partition.PreparedBoxPartitions.midpoint first last -
          first) ^ 2 +
            8 * error * (4 * slope + drift) * (last - Rectangle.Partition.PreparedBoxPartitions.midpoint first last) ^
              2) :=
          Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstBound lastBound) (by decide)
        _ = 8 * error * (4 * slope + drift) * (((last - first) / 2) * 2) ^ 2 := by rw [leftHalf, rightHalf]; ring1
        _ = _ := by rw [twiceHalf]

end Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
