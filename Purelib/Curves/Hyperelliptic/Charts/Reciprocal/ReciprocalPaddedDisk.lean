module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

public section

/-!
# A fixed certified neighborhood of the reciprocal disk

The initial inverse polynomial has a strict residual margin on the disk.
A finite Lipschitz bound extends that same cached polynomial to a computed
slightly larger disk. The padding is independent of all later Newton stages.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Square

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale normSq_scale)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

/-- The fixed rational square of radius two used for the original cap polynomial majorants. -/
@[expose] def box : Rational.Box := BoxTransport.centeredBox 0 2 (by decide)

set_option genInjectivity false in
/-- A cached positive padding of the original reciprocal disk for the retained cap polynomial.

The initial-value ceiling, residual Lipschitz bound and exact padding payment are independent of later Newton stages. -/
structure Data (cap : ReciprocalInnerInverse.Data curve collar) where
  /-- The cached ceiling for the original cap inverse polynomial on the fixed square. -/ initialUpper :
    InverseRootPolynomial.Coordinate
  /-- The cached inverse ceiling is exactly the original polynomial's computed box majorant. -/ initialUpper_eq :
    initialUpper = Dense.Gaussian.Bounds.Box.denseEvalNormMajorant cap.model.value
    box
  /-- The retained inverse-polynomial ceiling is strictly positive. -/ initial_positive : 0 < initialUpper
  /-- The cached squared-norm Lipschitz bound for the original residual polynomial. -/ lipschitz :
    InverseRootPolynomial.Coordinate
  /-- The cached Lipschitz bound is exactly the original residual's computed bound on the fixed square. -/ lipschitz_eq
    : lipschitz = Dense.Gaussian.Bounds.Box.denseLipschitzBound cap.model.residual
    box
  /-- The retained residual Lipschitz bound is strictly positive. -/ lipschitz_positive : 0 < lipschitz
  /-- The retained positive enlargement of the original reciprocal disk radius. -/ padding :
    InverseRootPolynomial.Coordinate
  /-- The padding is exactly the reciprocal of 1024 times one plus the retained Lipschitz bound. -/ padding_eq : padding
    = 1 / (1024 * (lipschitz + 1))
  /-- The retained disk padding is strictly positive. -/ positive : 0 < padding
  /-- The retained disk padding is at most one. -/ small : padding ≤ 1
  /-- The retained Lipschitz bound pays the squared padding movement within one over 256. -/ paid : 4 * lipschitz *
    padding ^ 2 ≤ 1 / 256

constructive_injectivity Data

namespace Data

variable {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}

/-- Cache a fixed inverse-polynomial ceiling and residual Lipschitz bound, then compute and certify the exact positive
disk padding.

The retained positive denominator determines the cached padding, its upper bound and the squared movement payment. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap := by
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound cap.model.residual
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.box
  have lipschitzPositive : 0 < lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos _ _
  have sumPositive : 0 < lipschitz + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct lipschitzPositive.le
    (by decide)
  have denominatorPositive : 0 < 1024 * (lipschitz + 1) := Fraction.Order.Arithmetic.mul_pos_direct
    (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 1024) sumPositive
  let padding := 1 / (1024 * (lipschitz + 1))
  have positive : 0 < padding := Fraction.Order.Field.div_pos_direct (by decide) denominatorPositive
  have oneLe : 1 ≤ 1024 * (lipschitz + 1) := by
    have sum : 1 ≤ lipschitz + 1 := (_root_.zero_add (1 : InverseRootPolynomial.Coordinate)).symm.trans_le (add_le_add
      lipschitzPositive.le le_rfl)
    exact (show (1 : InverseRootPolynomial.Coordinate) = 1 * 1 by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_direct (by decide +kernel : (1 : InverseRootPolynomial.Coordinate) ≤ 1024)
        sum (by decide) (by decide +kernel))
  have small : padding ≤ 1 := (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr
    (oneLe.trans_eq (by ring1))
  have cancel : padding * (1024 * (lipschitz + 1)) = 1 :=
    Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  have allowance : padding * (lipschitz + 1) = 1 / 1024 := by
    apply Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : (1024 : InverseRootPolynomial.Coordinate) ≠ 0)
    exact (by ring1 : padding * (lipschitz + 1) * 1024 = padding * (1024 * (lipschitz + 1))).trans
      (cancel.trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)).symm)
  have linear : lipschitz * padding ≤ 1 / 1024 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_right (by decide))
      positive.le).trans_eq
      ((Fraction.Field.mul_comm _ _).trans allowance)
  have square : padding ^ 2 ≤ padding := by
    exact (show padding ^ 2 = padding * padding by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small positive.le).trans_eq (by ring1))
  have paid : 4 * lipschitz * padding ^ 2 ≤ 1 / 256 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) lipschitzPositive.le)).trans
      ((by ring1 : 4 * lipschitz * padding = 4 * (lipschitz * padding)).trans_le
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct linear (by decide)).trans_eq (by decide +kernel)))
  exact ⟨Dense.Gaussian.Bounds.Box.denseEvalNormMajorant cap.model.value
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.box, rfl,
    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos _ _, lipschitz, rfl, lipschitzPositive, padding, rfl, positive,
      small, paid⟩

/-- The original radius-weighted squared norm lies within the retained padded disk. -/
@[expose] def Contains (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) (point :
  InverseRootPolynomial.Gaussian) : Prop :=
  ReciprocalExteriorCollar.radius curve ^ 2 * Data.Gaussian.Norm.Basic.normSq point ≤ (1 + data.padding) ^ 2

/-- Every point of the original reciprocal disk belongs to its retained padded enlargement. -/
theorem contains_disk (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) {point :
  InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) : data.Contains point := by
  have factor : 1 ≤ 1 + data.padding := le_add_of_nonneg_right data.positive.le
  exact inside.trans ((show (1 : InverseRootPolynomial.Coordinate) = 1 ^ 2 by decide).trans_le
    (Fraction.Order.Arithmetic.pow_le_pow_direct (by decide) factor 2))

/-- Every retained padded-disk point has squared norm at most four. -/
theorem norm_le (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) {point :
  InverseRootPolynomial.Gaussian} (inside : data.Contains point) : Data.Gaussian.Norm.Basic.normSq point ≤ 4 :=
  by
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct
    (add_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) data.positive.le) (add_le_add le_rfl
      data.small) 2
  exact ((show Data.Gaussian.Norm.Basic.normSq point = 1 * Data.Gaussian.Norm.Basic.normSq point by
    ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Reciprocal.Bounds.radius_square_one_le
      curve.polynomial)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _))).trans (inside.trans (square.trans_eq (by decide)))

/-- Every retained padded-disk point lies in the fixed majorant square. -/
theorem box_contains (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) {point :
  InverseRootPolynomial.Gaussian} (inside : data.Contains point) :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.box.Contains point := by
  apply Centered.centeredBox_contains_of_normSq_sub_le
  rw [Data.Gaussian.Basic.sub_zero]
  exact (data.norm_le inside).trans_eq (by decide)

/-- Contract the original point by the reciprocal of one plus the retained disk padding. -/
@[expose] def contract (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) (point :
  InverseRootPolynomial.Gaussian) : Gaussian := Scale.scale (1 + data.padding)⁻¹ point

/-- The squared contraction factor recovers the original point's squared norm exactly.

The positive padding gives a nonzero contraction denominator and retains the same displayed point and disk-radius
bounds. -/
private theorem contract_identity (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) (point :
  InverseRootPolynomial.Gaussian) :
    (1 + data.padding) ^ 2 * Data.Gaussian.Norm.Basic.normSq (data.contract point) =
      Data.Gaussian.Norm.Basic.normSq point := by
  have cancel := Fraction.Field.mul_inv_cancel (1 + data.padding)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
      data.positive).ne'
  rw [contract, Scale.normSq_scale]
  calc
    _ = ((1 + data.padding) * (1 + data.padding)⁻¹) ^ 2 * Data.Gaussian.Norm.Basic.normSq point := by ring1
    _ = _ := by rw [cancel]; ring1

/-- Contracting a padded-disk point puts it inside the original coefficient-certified disk.

The positive padding gives a nonzero contraction denominator and retains the same displayed point and disk-radius
bounds. -/
theorem contract_inside (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) {point :
  InverseRootPolynomial.Gaussian} (inside : data.Contains point) :
    Reciprocal.Bounds.InDisk curve.polynomial (data.contract point) := by
  have factorPositive : 0 < (1 + data.padding) ^ 2 := Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (by decide) data.positive) 2
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := (1 + data.padding) ^ 2) _ factorPositive
  exact (show ReciprocalExteriorCollar.radius curve ^ 2 * Data.Gaussian.Norm.Basic.normSq (data.contract point)
    * (1 + data.padding) ^ 2 =
    ReciprocalExteriorCollar.radius curve ^ 2 * ((1 + data.padding) ^ 2 * Data.Gaussian.Norm.Basic.normSq
      (data.contract point)) by ring1).trans_le
      (by rw [data.contract_identity]; exact inside.trans_eq (by ring1))

/-- The contraction movement squared norm is bounded by four times the retained padding squared.

The positive padding gives a nonzero contraction denominator and retains the same displayed point and disk-radius
bounds. -/
theorem contract_distance (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) {point :
  InverseRootPolynomial.Gaussian} (inside : data.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (point - data.contract point) ≤ 4 * data.padding ^ 2 := by
  have cancel := Fraction.Field.mul_inv_cancel (1 + data.padding)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
      data.positive).ne'
  have scalar : 1 - (1 + data.padding)⁻¹ = data.padding * (1 + data.padding)⁻¹ := by
    calc
      _ = (1 + data.padding) * (1 + data.padding)⁻¹ - (1 + data.padding)⁻¹ := by rw [cancel]
      _ = _ := by ring1
  have identity : point - data.contract point = Scale.scale data.padding (data.contract point) := by
    apply Data.Gaussian.Basic.ext
    · simp only [contract, Basic.sub_re,
        Scale.scale_re]
      exact (by ring1 : point.re - (1 + data.padding)⁻¹ * point.re = (1 - (1 + data.padding)⁻¹) * point.re).trans
        ((congrArg (fun factor => factor * point.re) scalar).trans (by ring1))
    · simp only [contract, Basic.sub_im,
        Scale.scale_im]
      exact (by ring1 : point.im - (1 + data.padding)⁻¹ * point.im = (1 - (1 + data.padding)⁻¹) * point.im).trans
        ((congrArg (fun factor => factor * point.im) scalar).trans (by ring1))
  rw [identity, Scale.normSq_scale]
  have bounded := Reciprocal.Bounds.disk_unit_bound (data.contract_inside inside)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded.trans (by
      decide : (1 : InverseRootPolynomial.Coordinate) ≤ 4))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1)

/-- The original cached cap residual remains bounded by one over 64 throughout the retained padded disk. -/
theorem residual_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data cap) {point :
  InverseRootPolynomial.Gaussian} (inside : data.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (cap.model.residual.eval point) ≤ 1 / 64 := by
  have original := Data.disk_residual cap (data.contract_inside inside)
  have difference := (Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound cap.model.residual
    (data.box_contains inside) (data.box_contains (data.contains_disk (data.contract_inside inside)))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (data.contract_distance inside)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos _ _).le)
  rw [← data.lipschitz_eq] at difference
  have tiny := difference.trans ((by
      ring1 : data.lipschitz * (4 * data.padding ^ 2) = 4 * data.lipschitz * data.padding ^ 2).trans_le data.paid)
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (cap.model.residual.eval point - cap.model.residual.eval
    (data.contract point))
    (cap.model.residual.eval (data.contract point))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add tiny original) (by decide))
  rw [show cap.model.residual.eval point - cap.model.residual.eval (data.contract point) +
    cap.model.residual.eval (data.contract point) = cap.model.residual.eval point by ring1] at estimate
  exact estimate.trans_eq (by decide +kernel)

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
