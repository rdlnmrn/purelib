module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.LinearAlgebra.Alternating.Reduction.Dual
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Dual
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic
import Purelib.LinearAlgebra.Vector.Update
import Purelib.LinearAlgebra.Vector.Weighted

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.LinearAlgebra.Alternating.UnitPivot
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Vector

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.WeightedPeriods

@[expose] public section

/-!
# Cached magnitude amplification of the actual dual coordinate change

Each shear retains its two exact coefficient banks. Their finite norm
charges give one magnitude factor, fixed independently of sampled values.
The complete factor is cached once; no normal-form search is repeated.
-/

namespace Purelib.Topology.Surface.Boundary.DualCoordinateBounds

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra.Matrix (IntegralMatrix)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (Reduction)
open _root_.Purelib.LinearAlgebra.Alternating.Reduction.Basic (Step)
open Purelib.LinearAlgebra.Matrix.Integral (Shear)
open Purelib.LinearAlgebra.Vector.Weighted (weighted)
open Purelib.LinearAlgebra.Vector.Update (bump)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Periods.WeightedPeriods (Coefficients Coordinate Gaussian)

variable {count : Nat}

/-- Retain both coefficient banks at every shear of an integral reduction.

The dependent recursive shape follows the exact stored reduction, ending in the empty bank at its terminal matrix. -/
def DualCoefficients : {matrix : IntegralMatrix count} → {raw : List
  (PivotIndices count)} → Reduction matrix raw → Type
  | _, _, .nil _ => PUnit
  | _, _, .cons step tail => Coefficients step.change.left × Coefficients
    step.change.right × DualCoordinateBounds.DualCoefficients tail

namespace DualCoefficients

section
open Purelib.Topology.Surface.Boundary
/-- Construct the two finite coefficient profiles for each retained reduction shear. -/
def build : {matrix : IntegralMatrix count} → {raw : List
  (PivotIndices count)} →
    (reduction : Reduction matrix raw) → DualCoefficients reduction
  | _, _, .nil _ => ⟨⟩
  | _, _, .cons step tail => ⟨Coefficients.build step.change.left, Coefficients.build step.change.right,
    build tail⟩

/-- Multiply the per-shear magnitude amplifications along the retained reduction. -/
def factor : {matrix : IntegralMatrix count} → {raw : List
  (PivotIndices count)} →
    (reduction : Reduction matrix raw) → DualCoefficients reduction →
      Coordinate
  | _, _, .nil _, _ => 1
  | _, _, .cons _ tail, banks => (4 * (1 + banks.1.mass + banks.2.1.mass)) *
    DualCoefficients.factor tail banks.2.2

end

/-- The magnitude factor from two nonnegative coefficient masses is strictly positive. -/
private theorem shearFactor_positive {first last : Fin count} {shear : Shear first last}
    (left : Coefficients shear.left) (right : Coefficients shear.right) :
    0 < 4 * (1 + left.mass + right.mass) := by
  have bound : (1 : Coordinate) ≤ 1 + left.mass + right.mass := by
    simpa only [add_assoc] using le_add_of_nonneg_right (add_nonneg left.mass_nonnegative right.mass_nonnegative)
  exact Arithmetic.mul_pos_direct (by decide) ((by
      decide : (0 : Coordinate) < 1).trans_le bound)

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.DualCoordinateBounds in
/-- The complete dual-coordinate amplification is strictly positive. -/
theorem factor_positive {matrix : IntegralMatrix count} {raw : List
  (PivotIndices count)}
    (reduction : Reduction matrix raw) (banks : DualCoefficients
      reduction) : 0 <
      factor reduction banks := by
  induction reduction with
  | nil => exact (by decide : (0 : Coordinate) < 1)
  | cons step tail ih =>
      exact Arithmetic.mul_pos_direct
        (shearFactor_positive banks.1 banks.2.1) (ih banks.2.2)

section
open Purelib.Topology.Surface.Boundary.DualCoordinateBounds.DualCoefficients
/-- Updating one vector coordinate costs at most twice the old bound plus update charge. -/
private theorem bump_bounded (values : Data.Vector Gaussian count) (index : Fin count)
  (amount : Gaussian)
    {bound charge : Coordinate} (bounded : ∀ position, normSq (values
      position) ≤ bound)
    (charged : normSq amount ≤ charge) (position : Fin count) :
    normSq (bump values index amount position) ≤ 2 *
      (bound + charge) := by
  rw [Update.bump_apply]
  have changed : normSq (if position = index then amount else 0) ≤ charge := by
    by_cases same : position = index
    · rw [if_pos same]; exact charged
    · rw [if_neg same, Gaussian.Norm.Basic.normSq_zero]
      exact (Gaussian.Norm.Basic.normSq_nonneg _).trans charged
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (bounded position) changed) (by decide))

/-- A retained coefficient mass bounds its weighted Gaussian combination under a uniform input bound. -/
private theorem weighted_bound {weights : Data.Vector Int count} (coefficients :
  Coefficients weights)
    (values : Data.Vector Gaussian count) {bound : Coordinate} (bounded : ∀
      index, normSq (values index) ≤ bound) :
    normSq (weighted (fun index => (weights index :
      Gaussian)) values) ≤ coefficients.mass * bound := by
  have boundedCanonical : ∀ index,
      Gaussian.Basic.Canonical.normSq (values index) ≤ bound := by
    intro index
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact bounded index
  have estimate := coefficients.normSq_combine_le values (fun _ => bound) boundedCanonical
  rw [coefficients.combine_eq, coefficients.charge_constant] at estimate
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate

end

open Purelib.Topology.Surface.Boundary.DualCoordinateBounds.DualCoefficients in
open Purelib.Topology.Surface.Boundary.DualCoordinateBounds in
/-- Both retained coefficient banks bound the dual action of one integral shear. -/
theorem shear_bounded {first last : Fin count} (shear : Shear first last)
    (left : Coefficients shear.left) (right : Coefficients shear.right)
    (values : Data.Vector Gaussian count) {bound : Coordinate} (nonnegative
      : 0 ≤ bound)
    (bounded : ∀ index, normSq (values index) ≤ bound) (index : Fin count) :
    normSq (shear.dual values index) ≤ (4 * (1 + left.mass + right.mass)) * bound := by
  have leftBound : normSq (-weighted (fun index => (shear.left index :
    Gaussian))
    values) ≤ left.mass * bound := by
    rw [Gaussian.Norm.Basic.normSq_neg]
    exact weighted_bound left values bounded
  have rightBound : normSq (-weighted (fun index => (shear.right index :
    Gaussian))
    values) ≤ right.mass * bound := by
    rw [Gaussian.Norm.Basic.normSq_neg]
    exact weighted_bound right values bounded
  have estimate := bump_bounded _ last _ (bump_bounded values first _ bounded
    leftBound) rightBound index
  have slack : 0 ≤ 2 * right.mass * bound := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide) right.mass_nonnegative) nonnegative
  calc
    _ ≤ 2 * (2 * (bound + left.mass * bound) + right.mass * bound) := estimate
    _ ≤ 2 * (2 * (bound + left.mass * bound) + right.mass * bound) + 2 * right.mass * bound := le_add_of_nonneg_right
      slack
    _ = _ := by ring1

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.DualCoordinateBounds in
/-- The product amplification bounds every transformed coordinate of the complete dual reduction. -/
theorem bounded {matrix : IntegralMatrix count} {raw : List
  (PivotIndices count)}
    (reduction : Reduction matrix raw) (banks : DualCoefficients
      reduction)
    (values : Data.Vector Gaussian count) {bound : Coordinate} (nonnegative
      : 0 ≤ bound)
    (input : ∀ index, normSq (values index) ≤ bound) (index : Fin count) :
    normSq (reduction.dualForward values index) ≤ factor reduction banks *
      bound := by
  induction reduction generalizing values bound with
  | nil => exact (input index).trans_eq (one_mul _).symm
  | cons step tail ih =>
      have estimate := ih banks.2.2 (step.change.dual values)
        (Arithmetic.mul_nonneg_direct (shearFactor_positive banks.1 banks.2.1).le
          nonnegative)
        (shear_bounded step.change banks.1 banks.2.1 values nonnegative input)
      exact estimate.trans_eq (by simp only [factor]; ring1)

end DualCoefficients

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.DualCoordinateBounds in
set_option genInjectivity false in
/-- Cached coefficient evidence and total magnitude amplification for one exact reduction.

The factor equation binds the retained scalar to the same per-shear coefficient banks used by its bound. -/
structure DualMagnitude {matrix : IntegralMatrix count} {raw : List
  (PivotIndices count)} (reduction : Reduction matrix raw) where
  /-- Dependent coefficient banks for every shear of the retained reduction. -/ coefficients :
    DualCoefficients reduction
  /-- Cached complete magnitude amplification of the dual coordinate change. -/ factor : Coordinate
  /-- The cached scalar equals the product computed from the retained coefficient banks. -/ factor_eq : factor =
    DualCoefficients.factor reduction coefficients

constructive_injectivity DualMagnitude

namespace DualMagnitude

variable {matrix : IntegralMatrix count} {raw : List
  (PivotIndices count)} {reduction : Reduction matrix raw}

open Purelib.Topology.Surface.Boundary
open Purelib.Topology.Surface.Boundary.DualCoordinateBounds
/-- Cache the coefficient banks and their complete dual-coordinate amplification once. -/
def build (reduction : Reduction matrix raw) : DualMagnitude reduction :=
  let coefficients := DualCoefficients.build reduction
  ⟨coefficients, DualCoefficients.factor reduction coefficients, rfl⟩

/-- The cached total dual-coordinate amplification is positive. -/
theorem positive (profile : DualMagnitude reduction) : 0 < profile.factor := by
  rw [profile.factor_eq]
  exact DualCoefficients.factor_positive reduction profile.coefficients

/-- Apply the cached amplification to a nonnegative uniform input-coordinate bound. -/
theorem bounded (profile : DualMagnitude reduction) (values : Data.Vector
  Gaussian count) {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (input : ∀ index, normSq (values index) ≤ bound) (index : Fin
      count) :
    normSq (reduction.dualForward values index) ≤ profile.factor * bound := by
  rw [profile.factor_eq]
  exact DualCoefficients.bounded reduction profile.coefficients values nonnegative input index

end DualMagnitude
end Purelib.Topology.Surface.Boundary.DualCoordinateBounds
