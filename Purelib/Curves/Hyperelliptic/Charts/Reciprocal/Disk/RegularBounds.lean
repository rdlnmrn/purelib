module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Radial.Bounds
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
public import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Riemann.Normalization.InverseRootComparison
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Uniform cap polynomial bounds on the reciprocal disk

One initial differential-residual polynomial and its finite norm ceiling
are retained for all later cap samples. A containing square is used only
to bound this fixed polynomial; model validity is proved on the disk.
The factor ceiling follows by finite radial integration within that disk.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Square

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelDifferentialResidual

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual DifferentialResidualBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Model)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Cast.Path (ofCoordinate)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  ReciprocalExteriorCollar.Data curve}
  {cap : ReciprocalInnerInverse.Data curve collar}

/-- A checked inverse at a contained point needs only the displayed radicand lower bound for this uniform numerical
ceiling. -/
theorem inverse_le {polynomial : Polynomial} {box : Rational.Box} (model :
  Model polynomial box)
    {point : Gaussian} (inside : box.Contains point) {lower : Coordinate}
    (positive : 0 < lower) (bounded : lower ≤ Norm.Basic.normSq (polynomial.eval point)) :
    Norm.Basic.normSq (model.value.eval point) ≤ 1 + 4 / lower := by
  have residual : Norm.Basic.normSq (1 - polynomial.eval point * (model.value.eval point) ^ 2) ≤
    1 / 16 := by
    rw [← model.residual_eq, Norm.Basic.normSq_eq_canonical]
    exact (model.residualBound point inside).trans model.bound_small
  have squared : Norm.Basic.normSq (model.value.eval point) ^ 2 ≤ 4 / lower := by
    apply (Field.le_div_iff_pos positive).mpr
    calc
      _ = lower * Norm.Basic.normSq (model.value.eval point) ^ 2 := by ring1
      _ ≤ Norm.Basic.normSq (polynomial.eval point) * Norm.Basic.normSq
        (model.value.eval point) ^ 2 :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct bounded (Arithmetic.sq_nonneg_direct
          _)
      _ ≤ 4 := InverseRootComparison.normalized_value_bound residual
  have elementary : Norm.Basic.normSq (model.value.eval point) ≤ 1 +
    Norm.Basic.normSq (model.value.eval point) ^ 2 := by
    apply Arithmetic.le_of_sub_nonneg_direct
    exact (add_nonneg (Arithmetic.sq_nonneg_direct (Norm.Basic.normSq
      (model.value.eval point) - 1))
      (Norm.Basic.normSq_nonneg (model.value.eval point))).trans_eq (by ring1)
  exact elementary.trans (add_le_add le_rfl squared)

/-- The fixed unit square used to bound the original differential-residual polynomial. -/
@[expose] def boundingBox : Rational.Box := BoxTransport.centeredBox 0 1 (by decide)

/-- The coefficient-certified reciprocal disk lies in the fixed unit square. -/
theorem boundingBox_contains {point : Gaussian} (inside : Reciprocal.Bounds.InDisk
  curve.polynomial point) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox.Contains point := by
  apply centeredBox_contains_of_normSq_sub_le
  simpa only [Basic.sub_zero, _root_.one_pow] using Reciprocal.Bounds.disk_unit_bound inside

/-- Multiplication by any power of a real unit-interval parameter preserves the original reciprocal disk. -/
theorem radial_inside {point : Gaussian} (inside : Reciprocal.Bounds.InDisk curve.polynomial
  point)
    {parameter : Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) (exponent : Nat) :
    Reciprocal.Bounds.InDisk curve.polynomial (point * (ofCoordinate parameter) ^ exponent) := by
  have norm : Norm.Basic.normSq (ofCoordinate parameter) ≤ 1 := by
    rw [Norm.Basic.normSq, ofCoordinate_re, ofCoordinate_im,
      show (0 : Coordinate) ^ 2 = 0 by decide, _root_.add_zero]
    exact (Arithmetic.pow_le_pow_direct unit.1 unit.2 2).trans_eq (_root_.one_pow _)
  have powered := Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg (ofCoordinate
    parameter)) norm exponent
  have movement : Norm.Basic.normSq (point * (ofCoordinate parameter) ^ exponent) ≤
    Norm.Basic.normSq point := by
    rw [Norm.Basic.normSq_mul, Power.normSq_pow]
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct powered (Norm.Basic.normSq_nonneg
      point)).trans_eq
      (by rw [_root_.one_pow, Fraction.Field.mul_one_direct])
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct movement
    (Arithmetic.sq_nonneg_direct _)).trans inside

/-- The parity-selected radial integration degree equals the cap primitive degree.

The certified origin order is zero or one, so each selected finite branch has the corresponding displayed degree. -/
private theorem radial_degree :
    Parity.degree (decide (HyperellipticReciprocal.originOrder curve = 1)) =
      Primitives.degree curve := by
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rw [Parity.degree, Primitives.degree, regular]
    decide
  · rw [Parity.degree, Primitives.degree, branch]
    decide

/-- The squared norm of the original cap primitive degree is at most four. -/
private theorem degree_norm : Norm.Basic.normSq (Primitives.degree curve :
  Gaussian) ≤ 4 := by
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rw [Primitives.degree, regular]
    decide
  · rw [Primitives.degree, branch]
    decide

set_option genInjectivity false in
/-- Uniform bounds for the original cap inverse and differential residual over the reciprocal disk.

The padded disk and initial residual polynomial are retained once, together with exact leading-coefficient and
polynomial norm ceilings. -/
structure Data (cap : ReciprocalInnerInverse.Data curve collar) where
  /-- The retained padded reciprocal disk geometry of the original cap. -/ padded : ReciprocalPaddedDisk.Data cap
  /-- The original cap model's cached differential-residual polynomial and its exact defining identity. -/ initial :
    DifferentialResidualBounds cap.model
  /-- The cached squared-norm ceiling for the initial differential residual on the fixed unit square. -/
    differentialUpper : Coordinate
  /-- The cached residual ceiling is the finite polynomial evaluation bound on the original fixed square. -/
    differentialUpper_eq : differentialUpper = Bounds.Box.denseEvalNormBound initial.value
    boundingBox
  /-- The cached positive radicand lower bound throughout the reciprocal disk. -/ lower :
    Coordinate
  /-- The cached lower bound is one quarter of the original leading coefficient's squared norm. -/ lower_eq : lower =
    Norm.Basic.normSq curve.polynomial.leadingCoeff / 4
  /-- The cached uniform squared-norm ceiling for original cap inverse-polynomial samples. -/ inverseUpper :
    Coordinate
  /-- The cached inverse ceiling is one plus four divided by the retained radicand lower bound. -/ inverseUpper_eq :
    inverseUpper = 1 + 4 / lower

constructive_injectivity Data

namespace Data

/-- Cache the padded disk, original differential residual and numerical ceilings shared by every later cap sample. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) :
  Data cap :=
  let initial := DifferentialResidualBounds.build cap.model
  let lower := Norm.Basic.normSq curve.polynomial.leadingCoeff / 4
  ⟨ReciprocalPaddedDisk.Data.build cap, initial, Bounds.Box.denseEvalNormBound initial.value
    boundingBox, rfl,
    lower, rfl, 1 + 4 / lower, rfl⟩

/-- The retained radicand lower bound is positive because the original leading coefficient is nonzero. -/
theorem lower_positive (data : Data cap) : 0 < data.lower :=
  by
  rw [data.lower_eq]
  exact Field.div_pos_direct
    (Norm.Basic.normSq_pos (DensePolynomial.leadingCoeff_ne_zero curve.nonzero)) (by decide)

/-- The retained inverse-polynomial squared-norm ceiling is strictly positive. -/
theorem inverseUpper_positive (data : Data cap) : 0 <
  data.inverseUpper := by
  rw [data.inverseUpper_eq]
  exact (show (0 : Coordinate) < 1 by decide).trans_le
    (le_add_of_nonneg_right (Field.div_nonneg_direct (by decide) data.lower_positive.le))

/-- The retained initial differential-residual ceiling is nonnegative. -/
theorem differentialUpper_nonnegative (data : Data cap) : 0 ≤
  data.differentialUpper := by
  rw [data.differentialUpper_eq]
  exact (Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- Every original cap inverse-polynomial refinement satisfies the retained ceiling throughout the reciprocal disk. -/
theorem inverse_bound (data : Data cap) (index : Nat) {point :
  Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Norm.Basic.normSq ((cap.model.refine index).value.eval point) ≤ data.inverseUpper := by
  let model := Data.diskPointModel cap point inside
  have same : (model.refine index).value = (cap.model.refine index).value := (Data.diskModel_refine cap _ _ index).1
  rw [data.inverseUpper_eq, ← same]
  apply inverse_le (model.refine index)
    (Data.pointBox_contains point) data.lower_positive
  rw [data.lower_eq, cap.polynomial_eq]
  exact Reciprocal.Bounds.disk_lower curve.polynomial (BranchIsolation.degreePositive curve) point inside

/-- The differential residual satisfies its retained geometric quarter-radius bound at every reciprocal disk point.

Each finite refinement reuses the cached cap model and the initial coefficient ceiling; the same disk containment
witness pays every later stage. -/
theorem differential_bound (data : Data cap) (index : Nat)
  {point : Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Norm.Basic.normSq (differentialResidual cap.polynomial
      (cap.model.refine index).value point) ≤
      quarterRadius data.differentialUpper index := by
  induction index with
  | zero =>
      change Norm.Basic.normSq (differentialResidual
        cap.polynomial cap.model.value point) ≤ _
      rw [← data.initial.value_eq, quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct,
        data.differentialUpper_eq]
      exact Bounds.Box.normSq_eval_le_denseEvalNormBound _
        (boundingBox_contains inside)
  | succ index previous =>
      let model := Data.diskPointModel cap point inside
      have same (stage : Nat) : (model.refine stage).value = (cap.model.refine stage).value :=
        (Data.diskModel_refine cap _ _ stage).1
      have step := (Model.step_differentialResidual_bound (model.refine index)) (Data.pointBox_contains point)
      simp only [← Norm.Basic.normSq_eq_canonical] at step
      change Norm.Basic.normSq (differentialResidual
        cap.polynomial (model.refine (index + 1)).value point) ≤ _ at step
      rw [same (index + 1), same index] at step
      apply step.trans
      calc
        _ = Norm.Basic.normSq (differentialResidual
          cap.polynomial (cap.model.refine index).value point) * (1 / 4) := by
          rw [Fraction.Field.div_eq_mul_inv_direct, show (1 / 4 : Coordinate) = 4⁻¹ by decide]
        _ ≤ quarterRadius data.differentialUpper index * (1 / 4) :=
          Arithmetic.mul_le_mul_of_nonneg_right_direct previous (by decide)
        _ = _ := by
          rw [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow, pow_succ];
          ring1

/-- The uniform primitive-factor ceiling is eight times the retained inverse-polynomial ceiling. -/
@[expose] def factorUpper (data : Data cap) : Coordinate := 8
  * data.inverseUpper

/-- The uniform primitive-factor ceiling is nonnegative. -/
theorem factorUpper_nonnegative (data : Data cap) : 0 ≤
  data.factorUpper :=
  Arithmetic.mul_nonneg_direct (by decide) data.inverseUpper_positive.le

/-- The cap factor's bound is independent of the refinement index and holds at every disk point, including the origin,
in both degree parities. -/
theorem factor_bound (data : Data cap) {differential :
  Differential genus} {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) {point : Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Norm.Basic.normSq (sample.factor.eval point) ≤ data.factorUpper := by
  have estimate := Radial.Bounds.factor_bound sample.factor point
    (decide (HyperellipticReciprocal.originOrder curve = 1)) (4 * data.inverseUpper) (by
      intro parameter unit
      rw [radial_degree]
      let coordinate := point * (ofCoordinate parameter) ^ Primitives.degree curve
      have contained := radial_inside inside unit
        (Primitives.degree curve)
      change Norm.Basic.normSq (sample.factor.eval coordinate + (Primitives.degree curve :
        Gaussian) * coordinate *
        (GCD.derivative sample.factor).eval coordinate) ≤ _
      rw [sample.factor_derivative, sample.inverse_eq, Norm.Basic.normSq_mul,
        Norm.Basic.normSq_mul, Norm.Basic.normSq_neg, Power.normSq_pow]
      have numerator := Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg coordinate)
        (Reciprocal.Bounds.disk_unit_bound contained) (HyperellipticReciprocal.reversedDifferential
          differential).exponent
      have factors := Arithmetic.mul_le_mul_direct
        (degree_norm (curve := curve)) numerator
        (Arithmetic.pow_nonneg_direct (Norm.Basic.normSq_nonneg coordinate) _) (by decide)
      have bounded := Arithmetic.mul_le_mul_direct factors (data.inverse_bound index contained)
        (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct (by decide)
          (Arithmetic.pow_nonneg_direct (by decide : (0 : Coordinate) ≤ 1) _))
      simpa only [_root_.one_pow, Fraction.Field.mul_one_direct] using bounded)
  exact estimate.trans_eq (by unfold factorUpper; ring1)

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
