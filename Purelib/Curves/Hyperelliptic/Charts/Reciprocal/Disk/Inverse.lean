module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

public section

/-!
# The retained cap inverse polynomial on the whole reciprocal disk

The same seven Newton steps used by the inner cap are valid throughout the
coefficient-certified disk, including every inverse outer-boundary point.
The larger-domain view reuses the cached value and residual polynomials.
It does not extend clearance to a bounding square or change the period ambient.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Seed)
open Purelib.Riemann.Normalization.InverseModelRootSamples (refineValue)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Box Model correction_residual)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (residual_step_bound)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar (Data)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus}

/-- One sixty-fourth is exactly the square of one eighth. -/
private theorem eighth_square : (1 / 64 : InverseRootPolynomial.Coordinate) = (1 / 8) ^ 2 := by decide +kernel

/-- A fourfold rational bound of 81 over 64 gives the corresponding quartered bound. -/
private theorem quarter_bound {value : InverseRootPolynomial.Coordinate} (scaled : 4 * value ≤ 81 / 64) : value ≤ 81 /
  256 := by
  have divided : value ≤ (81 / 64 : InverseRootPolynomial.Coordinate) / 4 :=
    (Fraction.Order.Field.le_div_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)).mpr
      ((show value * 4 = 4 * value by ring1).trans_le scaled)
  exact divided.trans_eq (by decide +kernel)

/-- The retained leading-coefficient inverse-root seed has normalized squared norm at most 81 over 64. -/
private theorem seed_normalized (seed : OwnerSeededInverseRoot.Seed curve.polynomial.leadingCoeff) :
    Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff * Data.Gaussian.Norm.Basic.normSq
      seed.value ^ 2 ≤ 81 / 64 := by
  let residual := 1 - curve.polynomial.leadingCoeff * seed.value ^ 2
  have seedScalar := seed.residual_small
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at seedScalar
  have seedSquare := seedScalar.trans_eq eighth_square
  change residual.re ^ 2 + residual.im ^ 2 ≤ (1 / 8 : InverseRootPolynomial.Coordinate) ^ 2 at seedSquare
  have square : residual.re ^ 2 ≤ (1 / 8 : InverseRootPolynomial.Coordinate) ^ 2 :=
    (le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct residual.im)).trans
      seedSquare
  have negative : -residual.re ≤ 1 / 8 := by
    have lower := Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 8) square
    simpa only [_root_.neg_neg] using Fraction.Order.Arithmetic.neg_le_neg_direct lower
  have linear : 2 * -residual.re ≤ 1 / 4 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct negative (by decide)).trans_eq (by decide)
  calc
    _ = Data.Gaussian.Norm.Basic.normSq (1 - residual) := by
      rw [show 1 - residual = curve.polynomial.leadingCoeff * seed.value ^ 2 by dsimp only [residual]; ring1,
        Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
    _ = 1 + 2 * -residual.re + Data.Gaussian.Norm.Basic.normSq residual := by
      simp only [Data.Gaussian.Norm.Basic.normSq, Basic.sub_re, Basic.sub_im, Basic.one_re, Basic.one_im]
      ring1
    _ ≤ 1 + 1 / 4 + 1 / 64 := add_le_add (add_le_add (le_refl _) linear) seedScalar
    _ = _ := by decide +kernel

/-- The retained seed residual is bounded by two thirds throughout the full coefficient-certified reciprocal disk. -/
private theorem disk_initial (seed : OwnerSeededInverseRoot.Seed curve.polynomial.leadingCoeff) {point :
  InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (1 - (Reciprocal.reversed curve.polynomial).eval point * seed.value ^ 2) ≤
      2 / 3 := by
  let value := (Reciprocal.reversed curve.polynomial).eval point
  have seedScalar := seed.residual_small
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at seedScalar
  have perturbation : Data.Gaussian.Norm.Basic.normSq ((curve.polynomial.leadingCoeff - value) * seed.value ^
    2) ≤ 81 / 256 := by
    have scaled : 4 * Data.Gaussian.Norm.Basic.normSq ((curve.polynomial.leadingCoeff - value) * seed.value ^
      2) ≤ 81 / 64 := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow, show curve.polynomial.leadingCoeff - value = -(value -
        curve.polynomial.leadingCoeff) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
      calc
        _ = (4 * Data.Gaussian.Norm.Basic.normSq (value - curve.polynomial.leadingCoeff)) *
          Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 := by
          ring1
        _ ≤ Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff *
          Data.Gaussian.Norm.Basic.normSq seed.value ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Reciprocal.Bounds.disk_tail_bound curve.polynomial (BranchIsolation.degreePositive curve) point inside)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        _ ≤ _ := seed_normalized seed
    exact quarter_bound scaled
  rw [show 1 - value * seed.value ^ 2 = (1 - curve.polynomial.leadingCoeff * seed.value ^ 2) +
    (curve.polynomial.leadingCoeff - value) * seed.value ^ 2 by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add seedScalar perturbation) (by decide)).trans
      (by decide +kernel))

/-- One retained scalar Newton correction satisfies any next bound paying five quarters of the previous bound squared.
-/
private theorem next_residual {parameter seed : InverseRootPolynomial.Gaussian} {steps : Nat} {bound next :
  InverseRootPolynomial.Coordinate}
    (bounded : Data.Gaussian.Norm.Basic.normSq (1 - parameter * InverseModelRootSamples.refineValue parameter
      seed steps ^ 2) ≤ bound)
    (small : bound ≤ 1) (paid : (5 / 4) * bound ^ 2 ≤ next) :
    Data.Gaussian.Norm.Basic.normSq (1 - parameter * InverseModelRootSamples.refineValue parameter seed (steps
      + 1) ^ 2) ≤ next := by
  rw [InverseModelRootSamples.refineValue, InverseRootPolynomial.correction_residual _ _ _ rfl]
  exact (ReciprocalInnerInverse.residual_step_bound bounded small).trans paid

/-- Seven scalar Newton corrections reduce an initial two-thirds residual bound to one over 256. -/
private theorem seven_residual {parameter seed : InverseRootPolynomial.Gaussian}
    (bounded : Data.Gaussian.Norm.Basic.normSq (1 - parameter * seed ^ 2) ≤ 2 / 3) :
    Data.Gaussian.Norm.Basic.normSq (1 - parameter * InverseModelRootSamples.refineValue parameter seed 7 ^ 2)
      ≤ 1 / 256 := by
  have first := next_residual (steps := 0) bounded (by decide) (by
    decide +kernel : (5 / 4 : InverseRootPolynomial.Coordinate) * (2 / 3) ^ 2 ≤ 3 / 5)
  have second := next_residual first (by decide) (by
      decide +kernel : (5 / 4 : InverseRootPolynomial.Coordinate) * (3 / 5) ^ 2 ≤ 1 / 2)
  have third := next_residual second (by decide) (by
      decide +kernel : (5 / 4 : InverseRootPolynomial.Coordinate) * (1 / 2) ^ 2 ≤ 1 / 3)
  have fourth := next_residual third (by decide) (by
      decide +kernel : (5 / 4 : InverseRootPolynomial.Coordinate) * (1 / 3) ^ 2 ≤ 1 / 6)
  have fifth := next_residual fourth (by decide) (by
      decide +kernel : (5 / 4 : InverseRootPolynomial.Coordinate) * (1 / 6) ^ 2 ≤ 1 / 16)
  have sixth := next_residual fifth (by decide) (by
      decide +kernel : (5 / 4 : InverseRootPolynomial.Coordinate) * (1 / 16) ^ 2 ≤ 1 / 64)
  exact next_residual sixth (by decide +kernel) (by decide +kernel)

namespace Data

variable {collar : Data curve}

/-- The original cached model residual satisfies the one-over-256 bound throughout the full reciprocal disk. -/
theorem disk_residual (data : ReciprocalInnerInverse.Data curve collar) {point : InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (data.model.residual.eval point) ≤ 1 / 256 := by
  rw [data.model.residual_eq, data.model_eq]
  apply Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse.seven_residual
  rw [data.polynomial_eq]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse.disk_initial data.seed inside

/-- Retain the same finite polynomials on any explicitly certified box in this disk. Only the domain certificate and
residual bound change. -/
@[expose] def diskModel (data : ReciprocalInnerInverse.Data curve collar) (box : InverseRootPolynomial.Box)
    (inside : ∀ point, box.Contains point → Reciprocal.Bounds.InDisk curve.polynomial point) :
      InverseRootPolynomial.Model data.polynomial box where
  value := data.model.value
  residual := data.model.residual
  residual_eq := data.model.residual_eq
  bound := 1 / 256
  bound_nonnegative := by decide +kernel
  bound_small := by decide +kernel
  residualBound := fun point contained => by
    have scalar := disk_residual data (inside point contained)
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar

/-- The degenerate rational box containing exactly the displayed Gaussian point. -/
@[expose] def pointBox (point : InverseRootPolynomial.Gaussian) : Box := ⟨point.re, point.re, point.im, point.im,
  le_rfl, le_rfl⟩

/-- The displayed point belongs to its degenerate coordinate box. -/
theorem pointBox_contains (point : InverseRootPolynomial.Gaussian) :
  (pointBox point).Contains point := ⟨le_rfl, le_rfl, le_rfl,
  le_rfl⟩

/-- Every point in the degenerate coordinate box equals its original displayed point. -/
theorem eq_of_pointBox_contains {point other : InverseRootPolynomial.Gaussian} (inside :
  (pointBox point).Contains other) : other = point :=
  Data.Gaussian.Basic.ext (le_antisymm inside.2.1 inside.1) (le_antisymm inside.2.2.2 inside.2.2.1)

/-- A pointwise view is enough to name the global polynomial's root at an actual inverse boundary point; no larger
rectangle is assumed clear. -/
@[expose] def diskPointModel (data : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian)
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) : InverseRootPolynomial.Model data.polynomial
      (pointBox point) :=
  diskModel data
    (pointBox point)
    (fun _ contained => (eq_of_pointBox_contains
      contained).symm ▸ inside)

/-- Reboxing preserves both cached polynomial sequences at every finite stage.

This equality is proof data; consumers retain the original sample. -/
theorem diskModel_refine (data : ReciprocalInnerInverse.Data curve collar) (box : InverseRootPolynomial.Box)
    (inside : ∀ point, box.Contains point → Reciprocal.Bounds.InDisk curve.polynomial point) (index : Nat) :
    ((diskModel data box inside).refine index).value =
      (data.model.refine index).value ∧
      ((diskModel data box inside).refine index).residual =
        (data.model.refine index).residual := by
  induction index with
  | zero => exact ⟨rfl, rfl⟩
  | succ index previous =>
      change
        ((diskModel data box inside).refine index).value *
            (DensePolynomial.constant 1 + ((diskModel data box
              inside).refine index).residual.scale InverseRootPolynomial.half) = _ ∧
          _ = _
      dsimp only [Model.refine, InverseRootPolynomial.Model.step]
      rw [previous.1, previous.2]
      exact ⟨rfl, rfl⟩

/-- Every retained model refinement satisfies the geometric residual bound throughout the original reciprocal disk. -/
theorem disk_refine_residual (data : ReciprocalInnerInverse.Data curve collar) (index : Nat) {point :
  InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq ((data.model.refine index).residual.eval point) ≤
      Geometric.Basic.quarterRadius (1 / 256) index := by
  let model := diskPointModel data point inside
  have bounded := (model.refine index).residualBound point
    (pointBox_contains point)
  rw [model.refine_bound] at bounded
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at bounded
  rw [← (diskModel_refine data _ _ index).2]
  exact bounded

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
