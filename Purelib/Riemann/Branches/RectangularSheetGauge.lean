module
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Cached, consistently oriented models on a regular grid patch

Apply the computed gauge once to each cached polynomial.  Negation retains
the original residual cache and error budget.  On every shared edge, the
oriented models satisfy the shrinking overlap bound with no further sign
selection.  The same bound is homogeneous in any numerator value.
-/

@[expose] public section

namespace Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Apply the selected Boolean sign to the original Gaussian value. -/
def signedValue (flip : Bool) (value : Gaussian) : Gaussian := if flip then -value else value

open Purelib.Data.Gaussian in
/-- Applying either retained sign preserves the original squared norm.

The Boolean sign retains the original value or its negation, both of which have the same exact rational squared norm. -/
theorem normSq_signedValue (flip : Bool) (value : Gaussian) : normSq (signedValue flip value) = normSq value := by
  cases flip with
  | false => rfl
  | true => exact Basic.Canonical.normSq_neg value

section
open Purelib.Polynomial
/-- Apply the selected sign to an original inverse-root model without changing its residual or bound.

Negation changes only the retained polynomial value; the exact residual identity and all original error certificates
remain attached to the same polynomial and box. -/
def signedModel {polynomial : Polynomial} {box : Box} (model : Model polynomial box) (flip : Bool) : Model polynomial
  box :=
  if flip then
    { value := -model.value
      residual := model.residual
      residual_eq := fun point => by
        rw [Dense.Basic.DensePolynomial.eval_neg, model.residual_eq]
        congr 1
        ring1
      bound := model.bound
      bound_nonnegative := model.bound_nonnegative
      bound_small := model.bound_small
      residualBound := model.residualBound }
  else model

/-- The signed model evaluates to the selected sign of its original value.

The original residual cache and box stay fixed, while evaluation reads either the retained polynomial or its negation.
-/
theorem signedModel_value {polynomial : Polynomial} {box : Box} (model : Model polynomial box) (flip : Bool) (point :
  Gaussian) :
    (signedModel model flip).value.eval point = signedValue flip (model.value.eval point) := by
  cases flip with
  | false => rfl
  | true => exact Dense.Basic.DensePolynomial.eval_neg model.value point

end

/-- Signing the original model preserves its exact retained error bound. -/
theorem signedModel_bound {polynomial : Polynomial} {box : Box} (model : Model polynomial box) (flip : Bool) :
    (signedModel model flip).bound = model.bound := by
  cases flip <;> rfl

/-- Apply the selected sign while retaining the original model's overlap-readiness bound. -/
def signedReady {polynomial : Polynomial} {box : Box} (ready : OverlapReady polynomial box) (flip : Bool) : OverlapReady
  polynomial box :=
  ⟨signedModel ready.model flip, (signedModel_bound ready.model flip).trans_le ready.small⟩

namespace Bank

variable {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}

open Purelib.Data in
/-- Apply the retained finite sign vector to the exact indexed original inverse-root models. -/
def orient (bank : Bank polynomial geometry) (signs : Data.Vector (Data.Vector Bool (rows + 1)) (columns
  + 1)) : Bank polynomial geometry :=
  .ofFn fun column row => signedReady (bank.ready column row) (signs column row)

open Purelib.Data
open Purelib.Riemann.Normalization
/-- An oriented cell evaluates to the retained sign applied to its original model value. -/
theorem orient_value (bank : Bank polynomial geometry) (signs : Data.Vector (Data.Vector Bool (rows +
  1)) (columns + 1))
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point : Gaussian) :
    ((Bank.orient bank signs).ready column row).model.value.eval point =
      signedValue (signs column row) ((bank.ready column row).model.value.eval point) := by
  rw [orient, RectangularInverseModels.Bank.ready_ofFn]
  exact signedModel_value _ _ _

/-- Orienting a cell preserves its original model's exact error bound. -/
theorem orient_bound (bank : Bank polynomial geometry) (signs : Data.Vector (Data.Vector Bool (rows +
  1)) (columns + 1))
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    ((Bank.orient bank signs).ready column row).model.bound = (bank.ready column row).model.bound := by
  rw [orient, RectangularInverseModels.Bank.ready_ofFn]
  exact signedModel_bound _ _

end Bank

open Purelib.Data.Gaussian in
/-- Signs differing by the original alignment flip preserve the exact aligned squared distance.

The supplied Boolean parity identifies the original aligned value, and the four sign cases preserve its scalar squared
distance. -/
private theorem signed_distance {reference candidate : Gaussian} (alignment : SignAlignment reference candidate)
    (left right : Bool) (same : (left ^^ right) = alignment.flip) :
    normSq (signedValue left reference - signedValue right candidate) = normSq (reference - alignment.value) := by
  rw [alignment.value_eq, ← same]
  cases left with
  | false =>
      cases right <;> rfl
  | true =>
      cases right with
      | false =>
          change normSq (-reference - candidate) = normSq (reference - -candidate)
          simp only [normSq, Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im,
            -eq_self, -iff_self]
          ring1
      | true =>
          change normSq (-reference - -candidate) = normSq (reference - candidate)
          simp only [normSq, Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im,
            -eq_self, -iff_self]
          ring1

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- Consistent endpoint signs satisfy the original edge's coefficient-distance estimate.

The same retained transition controls every point on its original segment, with the original numerator and model error
bounds unchanged. -/
private theorem signed_edge_bound {polynomial : Polynomial} {leftBox rightBox : Purelib.Geometry.Rational.Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    (edge : EdgeTransition left right start finish) (leftSign rightSign : Bool)
    (same : (leftSign ^^ rightSign) = edge.sample.alignment.flip)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) (numerator : Gaussian) :
    let point := Affine.line start (finish - start) parameter
    normSq (numerator * (signedValue leftSign (left.value.eval point) - signedValue rightSign (right.value.eval point)))
      ≤
      6 * (left.bound + right.bound) * normSq (numerator * signedValue leftSign (left.value.eval point)) := by
  let sample := edge.sampleAt parameter inside
  have signs : (leftSign ^^ rightSign) = sample.alignment.flip := same
  have equality := signed_distance sample.alignment leftSign rightSign signs
  change normSq (signedValue leftSign (left.value.eval _) - signedValue rightSign (right.value.eval _)) =
    normSq (sample.leftValue - sample.alignment.value) at equality
  dsimp only
  rw [Basic.Canonical.normSq_mul, equality, Basic.Canonical.normSq_mul, normSq_signedValue]
  have bound := sample.coefficient_distance_le (edge.left_contains_at inside) (edge.right_contains_at inside) numerator
  rw [show numerator * sample.leftValue - numerator * sample.alignment.value =
    numerator * (sample.leftValue - sample.alignment.value) by ring1] at bound
  simpa only [Basic.Canonical.normSq_mul, sample.leftValue_eq] using bound

namespace Transitions

variable {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {bank : Bank polynomial geometry}

open Purelib in
/-- The original inverse-root bank oriented by the retained gauge of its transition grid. -/
def oriented (transitions : Transitions bank) (gauge : Topology.Grid.Signs.Gauge transitions.flatGrid) : Bank polynomial
  geometry :=
  Bank.orient bank gauge.values

open Purelib
open Purelib.Geometry.Rational
/-- Gauge-oriented neighboring columns satisfy the original coefficient-distance bound along their common edge. -/
theorem horizontal_distance_le (transitions : Transitions bank) (gauge : Topology.Grid.Signs.Gauge transitions.flatGrid)
    (column : Fin columns) (row : Fin (rows + 1)) {parameter : Coordinate}
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) (numerator : Gaussian) :
    let point := Affine.line (geometry.vertex column.castSucc.succ row.castSucc)
      (geometry.vertex column.castSucc.succ row.succ - geometry.vertex column.castSucc.succ row.castSucc) parameter
    let left := ((Riemann.Branches.RectangularSheetGauge.Transitions.oriented transitions gauge).ready column.castSucc
      row).model
    let right := ((Riemann.Branches.RectangularSheetGauge.Transitions.oriented transitions gauge).ready column.succ
      row).model
    normSq (numerator * (left.value.eval point - right.value.eval point)) ≤
      6 * (left.bound + right.bound) * normSq (numerator * left.value.eval point) := by
  dsimp only
  simp only [oriented, Bank.orient_value, Bank.orient_bound]
  exact signed_edge_bound (bank.horizontalEdge column row) _ _
    ((gauge.horizontal_difference column row).trans (transitions.horizontal_eq column row)) inside numerator

/-- Gauge-oriented neighboring rows satisfy the original coefficient-distance bound along their common edge. -/
theorem vertical_distance_le (transitions : Transitions bank) (gauge : Topology.Grid.Signs.Gauge transitions.flatGrid)
    (column : Fin (columns + 1)) (row : Fin rows) {parameter : Coordinate}
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) (numerator : Gaussian) :
    let point := Affine.line (geometry.vertex column.castSucc row.castSucc.succ)
      (geometry.vertex column.succ row.castSucc.succ - geometry.vertex column.castSucc row.castSucc.succ) parameter
    let left := ((Riemann.Branches.RectangularSheetGauge.Transitions.oriented transitions gauge).ready column
      row.castSucc).model
    let right := ((Riemann.Branches.RectangularSheetGauge.Transitions.oriented transitions gauge).ready column
      row.succ).model
    normSq (numerator * (left.value.eval point - right.value.eval point)) ≤
      6 * (left.bound + right.bound) * normSq (numerator * left.value.eval point) := by
  dsimp only
  simp only [oriented, Bank.orient_value, Bank.orient_bound]
  exact signed_edge_bound (bank.verticalEdge column row) _ _
    ((gauge.vertical_difference column row).trans (transitions.vertical_eq column row)) inside numerator

end Transitions

end Purelib.Riemann.Branches.RectangularSheetGauge
