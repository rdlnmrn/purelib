module

import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Vector.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Finite boundary ribbons with the endpoint term retained

Discrete summation by parts compares the areas traced by two nearby finite
primitive paths.  The mismatch is multiplied by path increments, not by
absolute primitive values at every fine segment.  Cauchy then pays the square
of the segment count, which cancels the squared step size on uniform traces.
The endpoint correction is explicit; it is not silently discarded on open
paths.  All trace values and aggregate calculations are cached.
-/

namespace Purelib.Integration.Path.BoundaryRibbon

open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Gaussian in
/-- The canonical rational Gaussian carrier for boundary area calculations. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat in
/-- The rational coordinate carrier for boundary ribbon bounds. -/
abbrev Coordinate := Fraction.Rational
/-- The retained fixed-length vector carrier used for ribbon vertices and edge corrections. -/
abbrev Vector := Data.Vector

section
open Purelib
open Purelib.Algebra
open Purelib.Data.Gaussian
/-- The sum of consecutive decreasing differences telescopes to the first value minus the last.

The original successor-indexed values supply each consecutive difference.
Structural induction cancels the shared internal endpoint and retains the first
and final values, including the empty edge sequence. -/
theorem sum_decreasing {count : Nat} (values : Fin (count + 1) → Integration.Path.BoundaryRibbon.Gaussian) :
    FiniteSum.Fin.sumFin (fun index : Fin count => values index.castSucc - values index.succ) = values 0 - values
      (Fin.last count) := by
  induction count with
  | zero =>
      change (0 : Gaussian) = values 0 - values 0
      exact (Basic.sub_self (values 0)).symm
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      have tail := ih (fun index => values index.succ)
      simp only [Fin.castSucc_succ]
      rw [tail]
      change (values 0 - values (Fin.succ 0)) + (values (Fin.succ 0) - values (Fin.last (count + 1))) = _
      ring1

/-- The sum of consecutive increasing differences telescopes to the last value minus the first.

Negating the same retained values reverses each scalar difference. The
decreasing-difference certificate then identifies exactly the original final
value minus its first value, without changing the finite index order. -/
theorem sum_increasing {count : Nat} (values : Fin (count + 1) → Integration.Path.BoundaryRibbon.Gaussian) :
    FiniteSum.Fin.sumFin (fun index : Fin count => values index.succ - values index.castSucc) = values (Fin.last count)
      - values 0 := by
  have reverseDifference (first last : Gaussian) : -first - -last = last - first := by
    apply Basic.ext
    · simp only [Basic.sub_re, Basic.neg_re, -eq_self, -iff_self]
      ring1
    · simp only [Basic.sub_im, Basic.neg_im, -eq_self, -iff_self]
      ring1
  have reversed := Integration.Path.BoundaryRibbon.sum_decreasing (fun index => -values index)
  have terms : FiniteSum.Fin.sumFin (fun index : Fin count => values index.succ - values index.castSucc) =
      FiniteSum.Fin.sumFin (fun index : Fin count => -values index.castSucc - -values index.succ) :=
    FiniteSum.Fin.sumFin_congr (fun index => (reverseDifference (values index.castSucc) (values index.succ)).symm)
  exact terms.trans (reversed.trans (reverseDifference _ _))

end

section
open Purelib
open Purelib.Data.Gaussian
/-- The skew conjugate product associated with two Gaussian vertices. -/
def area (first last : Integration.Path.BoundaryRibbon.Gaussian) : Gaussian := Data.Gaussian.Basic.conj first * last -
  Data.Gaussian.Basic.conj last * first

/-- Subtracting the first vertex from the second leaves their skew area unchanged. -/
theorem area_sub_self_right (first last : Integration.Path.BoundaryRibbon.Gaussian) :
  Integration.Path.BoundaryRibbon.area first (last - first) = Integration.Path.BoundaryRibbon.area first last := by
  apply Basic.ext <;> simp only [Integration.Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.sub_re,
    Basic.sub_im,
    Basic.mul_re, Basic.mul_im] <;> ring1

/-- The squared norm of the skew area is at most four times the two squared vertex norms. -/
theorem area_bound (first last : Integration.Path.BoundaryRibbon.Gaussian) : Data.Gaussian.Norm.Basic.normSq
  (Integration.Path.BoundaryRibbon.area first last) ≤ 4 * Data.Gaussian.Norm.Basic.normSq first *
    Data.Gaussian.Norm.Basic.normSq
  last := by
  have estimate := Norm.Bounds.normSq_sub_le_two (Data.Gaussian.Basic.conj first * last) (Data.Gaussian.Basic.conj last
    * first)
  simp only [Norm.Basic.normSq_mul, Norm.Basic.normSq_conj] at estimate
  exact estimate.trans_eq (by ring1)

end

open Purelib in
/-- The sum of three skew-area terms comparing a left edge with its retained right edge and endpoint errors.

The first two terms use the right increment; the third uses the error increment, preserving their distinct roles. -/
def correction (firstRight lastRight firstError lastError : Integration.Path.BoundaryRibbon.Gaussian) : Gaussian :=
  Integration.Path.BoundaryRibbon.area firstError (lastRight - firstRight) + Integration.Path.BoundaryRibbon.area
    lastError (lastRight - firstRight) +
    Integration.Path.BoundaryRibbon.area firstError (lastError - firstError)

open Purelib in
open Purelib.Data.Gaussian in
/-- The difference of left and right edge areas splits into the exact correction and endpoint area difference. -/
theorem area_difference (firstLeft lastLeft firstRight lastRight : Integration.Path.BoundaryRibbon.Gaussian) :
    Integration.Path.BoundaryRibbon.area firstLeft lastLeft - Integration.Path.BoundaryRibbon.area firstRight lastRight
      =
      Integration.Path.BoundaryRibbon.correction firstRight lastRight (firstLeft - firstRight) (lastLeft - lastRight) +
        (Integration.Path.BoundaryRibbon.area lastRight (lastLeft - lastRight) - Integration.Path.BoundaryRibbon.area
          firstRight (firstLeft - firstRight)) := by
  apply Basic.ext
  · simp only [Integration.Path.BoundaryRibbon.area, Integration.Path.BoundaryRibbon.correction,
      Data.Gaussian.Basic.conj,
      Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.mul_re]
    ring1
  · simp only [Integration.Path.BoundaryRibbon.area, Integration.Path.BoundaryRibbon.correction,
      Data.Gaussian.Basic.conj,
      Basic.sub_re, Basic.sub_im, Basic.add_im, Basic.mul_im]
    ring1

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Uniform endpoint-error and increment bounds control the squared norm of the edge correction.

For nonnegative endpoint error, the bound is eight times that error times the combined slope and drift factor times the
squared step. -/
theorem correction_bound {firstRight lastRight firstError lastError : Integration.Path.BoundaryRibbon.Gaussian}
    {error slope drift step : Integration.Path.BoundaryRibbon.Coordinate} (errorNonnegative : 0 ≤ error)
    (firstLe : Data.Gaussian.Norm.Basic.normSq firstError ≤ error) (lastLe : Data.Gaussian.Norm.Basic.normSq lastError
      ≤ error)
    (rightLe : Data.Gaussian.Norm.Basic.normSq (lastRight - firstRight) ≤ slope * step ^ 2)
    (driftLe : Data.Gaussian.Norm.Basic.normSq (lastError - firstError) ≤ drift * step ^ 2) :
    Data.Gaussian.Norm.Basic.normSq (Integration.Path.BoundaryRibbon.correction firstRight lastRight firstError
      lastError) ≤
      8 * error * (4 * slope + drift) * step ^ 2 := by
  have product {left right : Integration.Path.BoundaryRibbon.Gaussian} {bound :
    Integration.Path.BoundaryRibbon.Coordinate} (leftLe : Data.Gaussian.Norm.Basic.normSq left ≤ error)
      (rightLe : Data.Gaussian.Norm.Basic.normSq right ≤ bound * step ^ 2) : Data.Gaussian.Norm.Basic.normSq
        (Integration.Path.BoundaryRibbon.area left right) ≤ 4 * error * bound * step ^ 2 := by
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct leftLe rightLe (Norm.Basic.normSq_nonneg right)
      errorNonnegative
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct multiplied (show (0 :
      Integration.Path.BoundaryRibbon.Coordinate) ≤ 4 by decide)
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq left * Data.Gaussian.Norm.Basic.normSq right :=
        Integration.Path.BoundaryRibbon.area_bound left right
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq left * Data.Gaussian.Norm.Basic.normSq right) := by ring1
      _ ≤ 4 * (error * (bound * step ^ 2)) := scaled
      _ = _ := by ring1
  have first := product firstLe rightLe
  have last := product lastLe rightLe
  have changing := product firstLe driftLe
  have pair := (Norm.Bounds.normSq_add_le_two (Integration.Path.BoundaryRibbon.area firstError (lastRight - firstRight))
    (Integration.Path.BoundaryRibbon.area lastError (lastRight - firstRight))).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add first last) (by decide))
  exact (Norm.Bounds.normSq_add_le_two _ (Integration.Path.BoundaryRibbon.area firstError (lastError -
    firstError))).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add pair changing) (by decide)).trans_eq (by
      ring1))

open Purelib in
open Purelib.Algebra in
set_option genInjectivity false in
/-- Two retained Gaussian vertex vectors with cached pointwise errors, edge corrections and area difference.

Every cache has an exact defining equality. The difference subtracts the retained endpoint correction from the two
original area totals. -/
structure Ribbon (count : Nat) where
  /-- The original left vertex vector. -/ left : Integration.Path.BoundaryRibbon.Vector
    Integration.Path.BoundaryRibbon.Gaussian (count + 1)
  /-- The original right vertex vector. -/ right : Integration.Path.BoundaryRibbon.Vector
    Integration.Path.BoundaryRibbon.Gaussian (count + 1)
  /-- The retained pointwise left-minus-right error vector. -/ errors : Integration.Path.BoundaryRibbon.Vector
    Integration.Path.BoundaryRibbon.Gaussian (count + 1)
  /-- Each retained error equals its original left vertex minus its right vertex. -/ errors_eq : ∀ vertex, errors vertex
    = left vertex - right vertex
  /-- The retained edge correction vector. -/ corrections : Integration.Path.BoundaryRibbon.Vector
    Integration.Path.BoundaryRibbon.Gaussian count
  /-- Each retained correction equals the exact formula for its right edge and endpoint errors. -/ corrections_eq : ∀
    edge, corrections edge = Integration.Path.BoundaryRibbon.correction (right edge.castSucc) (right edge.succ)
    (errors edge.castSucc) (errors edge.succ)
  /-- The cached sum of the original left edge areas. -/ leftArea : Integration.Path.BoundaryRibbon.Gaussian
  /-- The left area cache equals the original left edge sum. -/ leftArea_eq : leftArea = FiniteSum.Fin.sumFin (fun edge
    : Fin count => Integration.Path.BoundaryRibbon.area (left edge.castSucc) (left edge.succ))
  /-- The cached sum of the original right edge areas. -/ rightArea : Integration.Path.BoundaryRibbon.Gaussian
  /-- The right area cache equals the original right edge sum. -/ rightArea_eq : rightArea = FiniteSum.Fin.sumFin (fun
    edge : Fin count => Integration.Path.BoundaryRibbon.area (right edge.castSucc) (right edge.succ))
  /-- The cached difference of the terminal and initial right-error areas. -/ endpointCorrection :
    Integration.Path.BoundaryRibbon.Gaussian
  /-- The endpoint correction equals its exact original endpoint formula. -/ endpointCorrection_eq : endpointCorrection
    = Integration.Path.BoundaryRibbon.area (right (Fin.last count)) (errors (Fin.last count)) -
    Integration.Path.BoundaryRibbon.area (right 0) (errors 0)
  /-- The cached area difference after subtracting the endpoint correction. -/ difference :
    Integration.Path.BoundaryRibbon.Gaussian
  /-- The difference equals left area minus right area minus endpoint correction. -/ difference_eq : difference =
    leftArea - rightArea - endpointCorrection

constructive_injectivity Ribbon

namespace Ribbon

variable {count : Nat}

open Purelib in
open Purelib.Algebra in
open Purelib.Data in
/-- Compute and retain a ribbon's pointwise errors, edge corrections and exact area totals from its two original
vectors. -/
def build (left right : Integration.Path.BoundaryRibbon.Vector Integration.Path.BoundaryRibbon.Gaussian (count + 1)) :
  Integration.Path.BoundaryRibbon.Ribbon count :=
  let errors := Vector.Basic.vectorOfFn fun vertex => left vertex - right vertex
  let corrections := Vector.Basic.vectorOfFn fun edge : Fin count => Integration.Path.BoundaryRibbon.correction (right
    edge.castSucc) (right edge.succ)
    (errors edge.castSucc) (errors edge.succ)
  let leftArea := FiniteSum.Fin.sumFin fun edge : Fin count => Integration.Path.BoundaryRibbon.area (left edge.castSucc)
    (left edge.succ)
  let rightArea := FiniteSum.Fin.sumFin fun edge : Fin count => Integration.Path.BoundaryRibbon.area (right
    edge.castSucc) (right edge.succ)
  let endpointCorrection := Integration.Path.BoundaryRibbon.area (right (Fin.last count)) (errors (Fin.last count)) -
    Integration.Path.BoundaryRibbon.area (right 0) (errors 0)
  { left := left
    right := right
    errors := errors
    errors_eq := fun vertex => Vector.Basic.vectorOfFn_apply _ vertex
    corrections := corrections
    corrections_eq := fun edge => Vector.Basic.vectorOfFn_apply _ edge
    leftArea := leftArea
    leftArea_eq := rfl
    rightArea := rightArea
    rightArea_eq := rfl
    endpointCorrection := endpointCorrection
    endpointCorrection_eq := rfl
    difference := leftArea - rightArea - endpointCorrection
    difference_eq := rfl }

open Purelib in
open Purelib.Algebra in
/-- The cached corrected area difference equals the exact sum of retained edge corrections. -/
theorem difference_eq_sum (ribbon : Integration.Path.BoundaryRibbon.Ribbon count) : ribbon.difference =
  FiniteSum.Fin.sumFin (fun edge => ribbon.corrections edge) := by
  rw [ribbon.difference_eq, ribbon.leftArea_eq, ribbon.rightArea_eq, ← FiniteSum.Fin.sumFin_sub]
  have edges : FiniteSum.Fin.sumFin (fun edge : Fin count => Integration.Path.BoundaryRibbon.area (ribbon.left
    edge.castSucc) (ribbon.left edge.succ) -
      Integration.Path.BoundaryRibbon.area (ribbon.right edge.castSucc) (ribbon.right edge.succ)) =
      FiniteSum.Fin.sumFin (fun edge : Fin count => ribbon.corrections edge +
        (Integration.Path.BoundaryRibbon.area (ribbon.right edge.succ) (ribbon.errors edge.succ) -
          Integration.Path.BoundaryRibbon.area (ribbon.right edge.castSucc) (ribbon.errors edge.castSucc))) := by
    apply FiniteSum.Fin.sumFin_congr
    intro edge
    rw [ribbon.corrections_eq, ribbon.errors_eq, ribbon.errors_eq]
    exact Integration.Path.BoundaryRibbon.area_difference ..
  rw [edges, FiniteSum.Fin.sumFin_add, Integration.Path.BoundaryRibbon.sum_increasing (fun vertex =>
    Integration.Path.BoundaryRibbon.area (ribbon.right vertex) (ribbon.errors vertex)),
    ribbon.endpointCorrection_eq]
  ring1

open Purelib
open Purelib.Data.Gaussian
/-- Uniform error, slope and drift bounds control the ribbon difference using the squared total step length. -/
theorem difference_bound (ribbon : Integration.Path.BoundaryRibbon.Ribbon count) {error slope drift step :
  Integration.Path.BoundaryRibbon.Coordinate}
    (errorNonnegative : 0 ≤ error)
    (errorLe : ∀ vertex, Data.Gaussian.Norm.Basic.normSq (ribbon.errors vertex) ≤ error)
    (rightLe : ∀ edge : Fin count, Data.Gaussian.Norm.Basic.normSq (ribbon.right edge.succ - ribbon.right
      edge.castSucc) ≤
      slope * step ^ 2)
    (driftLe : ∀ edge : Fin count, Data.Gaussian.Norm.Basic.normSq (ribbon.errors edge.succ - ribbon.errors
      edge.castSucc) ≤
      drift * step ^ 2) :
    Data.Gaussian.Norm.Basic.normSq ribbon.difference ≤ 8 * error * (4 * slope + drift) * ((count :
      Integration.Path.BoundaryRibbon.Coordinate) * step) ^ 2 := by
  rw [ribbon.difference_eq_sum]
  have bound := Norm.Sum.Indexed.normSq_sumFin_le (fun edge => ribbon.corrections edge)
    (8 * error * (4 * slope + drift) * step ^ 2) (fun edge => by
      rw [ribbon.corrections_eq]
      exact Integration.Path.BoundaryRibbon.correction_bound errorNonnegative (errorLe edge.castSucc) (errorLe
        edge.succ) (rightLe edge) (driftLe edge))
  exact bound.trans_eq (by ring1)

/-- When both original vertex sequences close, the retained endpoint correction vanishes. -/
theorem endpointCorrection_eq_zero_of_closed (ribbon : Integration.Path.BoundaryRibbon.Ribbon count)
    (leftClosed : ribbon.left (Fin.last count) = ribbon.left 0)
    (rightClosed : ribbon.right (Fin.last count) = ribbon.right 0) : ribbon.endpointCorrection = 0 := by
  rw [ribbon.endpointCorrection_eq, ribbon.errors_eq, ribbon.errors_eq, leftClosed, rightClosed, Basic.sub_self]

/-- For two closed vertex sequences, the same ribbon estimate bounds their original area difference. -/
theorem closed_difference_bound (ribbon : Integration.Path.BoundaryRibbon.Ribbon count) {error slope drift step :
  Integration.Path.BoundaryRibbon.Coordinate}
    (leftClosed : ribbon.left (Fin.last count) = ribbon.left 0)
    (rightClosed : ribbon.right (Fin.last count) = ribbon.right 0)
    (errorNonnegative : 0 ≤ error)
    (errorLe : ∀ vertex, Data.Gaussian.Norm.Basic.normSq (ribbon.errors vertex) ≤ error)
    (rightLe : ∀ edge : Fin count, Data.Gaussian.Norm.Basic.normSq (ribbon.right edge.succ - ribbon.right
      edge.castSucc) ≤
      slope * step ^ 2)
    (driftLe : ∀ edge : Fin count, Data.Gaussian.Norm.Basic.normSq (ribbon.errors edge.succ - ribbon.errors
      edge.castSucc) ≤
      drift * step ^ 2) :
    Data.Gaussian.Norm.Basic.normSq (ribbon.leftArea - ribbon.rightArea) ≤ 8 * error * (4 * slope + drift) * ((count :
      Integration.Path.BoundaryRibbon.Coordinate) * step) ^ 2 := by
  have estimate := ribbon.difference_bound errorNonnegative errorLe rightLe driftLe
  rw [ribbon.difference_eq, ribbon.endpointCorrection_eq_zero_of_closed leftClosed rightClosed,
    Basic.sub_zero] at estimate
  exact estimate

end Ribbon

end Purelib.Integration.Path.BoundaryRibbon
