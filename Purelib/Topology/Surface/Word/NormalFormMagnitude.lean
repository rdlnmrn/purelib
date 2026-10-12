module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic
import Purelib.LinearAlgebra.Vector.Update
import Purelib.LinearAlgebra.Vector.Weighted

import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Boundary.DualCoordinateBounds
public import Purelib.Topology.Surface.Boundary.NormalFormArea
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Dual

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra.Vector

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary

@[expose] public section

/-!
# Fixed magnitudes and conjugacy of computed handle coordinates

Integer dual shears preserve conjugacy exactly. A cached amplification
factor bounds both coordinates uniformly over all later primitive samples.
-/

namespace Purelib.Topology.Surface.Word.NormalFormMagnitude

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_succ)
open Purelib.LinearAlgebra.Matrix (IntegralMatrix)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (Reduction)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)
open Purelib.LinearAlgebra.Matrix.Integral (Shear)
open Purelib.LinearAlgebra.Vector.Weighted (weighted)
open Purelib.LinearAlgebra.Vector.Update (bump)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Surface.Boundary.DualCoordinateBounds (DualMagnitude)
open _root_.Purelib.Topology.Surface.Boundary (NormalFormArea)
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)

/-- Gaussian conjugation commutes with negation. -/
private theorem conj_neg (value : Gaussian.Basic.Canonical) : Data.Gaussian.Basic.conj (-value) =
  -Data.Gaussian.Basic.conj value := rfl

/-- Gaussian conjugation fixes every integer cast. -/
private theorem conj_integer (value : Int) : Data.Gaussian.Basic.conj (value : Gaussian.Basic.Canonical) = (value :
  Gaussian.Basic.Canonical) := by
  rw [← WeightedPeriods.integer_eq]
  rfl

/-- Gaussian conjugation commutes with finite indexed summation. -/
private theorem conj_sum {count : Nat} (values : Fin count → Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (Purelib.Algebra.FiniteSum.Fin.sumFin values) = Purelib.Algebra.FiniteSum.Fin.sumFin
      fun index => Data.Gaussian.Basic.conj (values index) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, Gaussian.Basic.conj_add, ih]

/-- Integer-weighted readings preserve pointwise conjugacy. -/
private theorem weighted_conjugate {count : Nat} (weights : Fin count → Int)
    (first last : Data.Vector Gaussian.Basic.Canonical count)
    (related : ∀ index, first index = Data.Gaussian.Basic.conj (last index)) :
    Purelib.LinearAlgebra.Vector.Weighted.weighted (fun index => (weights index : Gaussian.Basic.Canonical)) first =
      Data.Gaussian.Basic.conj (Purelib.LinearAlgebra.Vector.Weighted.weighted (fun index => (weights index :
      Gaussian.Basic.Canonical)) last) := by
  rw [Weighted.weighted, Weighted.weighted, conj_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [Gaussian.Basic.conj_mul, conj_integer, related index]

/-- Updating conjugate vectors at one coordinate by conjugate amounts preserves conjugacy. -/
private theorem bump_conjugate {count : Nat}
    (first last : Data.Vector Gaussian.Basic.Canonical count) (index : Fin count)
    {firstAmount lastAmount : Gaussian.Basic.Canonical} (amountEq : firstAmount = Data.Gaussian.Basic.conj
      lastAmount)
    (related : ∀ position, first position = Data.Gaussian.Basic.conj (last position)) (position : Fin count) :
    Purelib.LinearAlgebra.Vector.Update.bump first index firstAmount position = Data.Gaussian.Basic.conj
      (Purelib.LinearAlgebra.Vector.Update.bump last index lastAmount position) := by
  rw [Update.bump_apply, Update.bump_apply,
    Gaussian.Basic.conj_add, related position]
  by_cases same : position = index
  · rw [if_pos same, if_pos same, amountEq]
  · rw [if_neg same, if_neg same, Gaussian.Basic.conj_zero]

/-- An integral dual shear preserves pointwise conjugacy of Gaussian vectors. -/
private theorem shear_conjugate {count : Nat} {first last : Fin count} (shear :
  Purelib.LinearAlgebra.Matrix.Integral.Shear first last)
    (left right : Data.Vector Gaussian.Basic.Canonical count)
    (related : ∀ index, left index = Data.Gaussian.Basic.conj (right index)) (index : Fin count) :
    shear.dual left index = Data.Gaussian.Basic.conj (shear.dual right index) := by
  have leftEq := (congrArg Neg.neg (weighted_conjugate shear.left left right related)).trans
    (conj_neg _).symm
  have rightEq := (congrArg Neg.neg (weighted_conjugate shear.right left right related)).trans
    (conj_neg _).symm
  exact bump_conjugate _ _ last rightEq (bump_conjugate left right first leftEq
    related) index

/-- Every step of an integral reduction preserves conjugacy in its dual-forward readings. -/
theorem dualForward_conjugate {count : Nat} {matrix : LinearAlgebra.Matrix.IntegralMatrix
  count} {raw : List (Handle.Basic.PivotIndices count)}
    (reduction : LinearAlgebra.Alternating.Reduction matrix raw) (left right : Data.Vector Gaussian.Basic.Canonical
      count)
    (related : ∀ index, left index = Data.Gaussian.Basic.conj (right index)) (index : Fin count) :
    reduction.dualForward left index = Data.Gaussian.Basic.conj (reduction.dualForward right index) := by
  induction reduction generalizing left right with
  | nil => exact related index
  | cons step tail ih => exact ih _ _ (shear_conjugate step.change left right related)

namespace NormalFormArea

variable {count : Nat} {matrix : LinearAlgebra.Matrix.IntegralMatrix count} {raw : List
  (Handle.Basic.PivotIndices count)}
  {normal : LinearAlgebra.Alternating.NormalForm matrix raw} {values : Data.Vector Stokes.PrimitivePoint count}

/-- The cached normal-form points retain the conjugacy of their original input coordinates. -/
theorem conjugate (sample : Boundary.NormalFormArea normal values) (related : ∀ index, (PrimitivePoint.Conjugate
  (values index))) (index : Fin count) :
    (PrimitivePoint.Conjugate (sample.points index)) := by
  rw [sample.points_eq, Data.Vector.Basic.vectorOfFn_apply]
  change sample.left index = Data.Gaussian.Basic.conj (sample.right index)
  rw [sample.left_eq, sample.right_eq]
  exact dualForward_conjugate normal.reduction _ _ (fun position => by
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
    exact related position) index

/-- A retained dual amplification bounds both coordinates of each normal-form point.

The bound uses the fixed reduction profile and a common nonnegative input magnitude. -/
theorem bounded (sample : Boundary.NormalFormArea normal values) (profile : DualCoordinateBounds.DualMagnitude
  normal.reduction)
    {bound : PrimitiveAreaBounds.AreaCoordinate} (nonnegative : 0 ≤ bound) (input : ∀ index, (PrimitivePoint.Bounded
      (values index)) bound) (index : Fin count) :
    (PrimitivePoint.Bounded (sample.points index)) (profile.factor * bound) := by
  rw [sample.points_eq, Data.Vector.Basic.vectorOfFn_apply]
  constructor
  · change Gaussian.Basic.Canonical.normSq (sample.left index) ≤ _
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical (sample.left index), sample.left_eq]
    exact profile.bounded _ nonnegative (fun position => by
      rw [Data.Vector.Basic.vectorOfFn_apply, Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (input position).1) index
  · change Gaussian.Basic.Canonical.normSq (sample.right index) ≤ _
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical (sample.right index), sample.right_eq]
    exact profile.bounded _ nonnegative (fun position => by
      rw [Data.Vector.Basic.vectorOfFn_apply, Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (input position).2) index

end NormalFormArea
end Purelib.Topology.Surface.Word.NormalFormMagnitude
