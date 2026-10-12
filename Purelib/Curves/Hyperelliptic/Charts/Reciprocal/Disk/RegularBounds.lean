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
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}

/-- A checked inverse at a contained point needs only the displayed radicand lower bound for this uniform numerical
ceiling. -/
theorem inverse_le {polynomial : InverseRootPolynomial.Polynomial} {box : Rational.Box} (model :
  InverseRootPolynomial.Model polynomial box)
    {point : InverseRootPolynomial.Gaussian} (inside : box.Contains point) {lower : InverseRootPolynomial.Coordinate}
    (positive : 0 < lower) (bounded : lower ≤ Data.Gaussian.Norm.Basic.normSq (polynomial.eval point)) :
    Data.Gaussian.Norm.Basic.normSq (model.value.eval point) ≤ 1 + 4 / lower := by
  have residual : Data.Gaussian.Norm.Basic.normSq (1 - polynomial.eval point * (model.value.eval point) ^ 2) ≤
    1 / 16 := by
    rw [← model.residual_eq, Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (model.residualBound point inside).trans model.bound_small
  have squared : Data.Gaussian.Norm.Basic.normSq (model.value.eval point) ^ 2 ≤ 4 / lower := by
    apply (Fraction.Order.Field.le_div_iff_pos positive).mpr
    calc
      _ = lower * Data.Gaussian.Norm.Basic.normSq (model.value.eval point) ^ 2 := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) * Data.Gaussian.Norm.Basic.normSq
        (model.value.eval point) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bounded (Fraction.Order.Arithmetic.sq_nonneg_direct
          _)
      _ ≤ 4 := InverseRootComparison.normalized_value_bound residual
  have elementary : Data.Gaussian.Norm.Basic.normSq (model.value.eval point) ≤ 1 +
    Data.Gaussian.Norm.Basic.normSq (model.value.eval point) ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    exact (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct (Data.Gaussian.Norm.Basic.normSq
      (model.value.eval point) - 1))
      (Data.Gaussian.Norm.Basic.normSq_nonneg (model.value.eval point))).trans_eq (by ring1)
  exact elementary.trans (add_le_add le_rfl squared)

/-- The fixed unit square used to bound the original differential-residual polynomial. -/
@[expose] def boundingBox : Rational.Box := BoxTransport.centeredBox 0 1 (by decide)

/-- The coefficient-certified reciprocal disk lies in the fixed unit square. -/
theorem boundingBox_contains {point : InverseRootPolynomial.Gaussian} (inside : Reciprocal.Bounds.InDisk
  curve.polynomial point) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox.Contains point := by
  apply Centered.centeredBox_contains_of_normSq_sub_le
  simpa only [Data.Gaussian.Basic.sub_zero, _root_.one_pow] using Reciprocal.Bounds.disk_unit_bound inside

/-- Multiplication by any power of a real unit-interval parameter preserves the original reciprocal disk. -/
theorem radial_inside {point : InverseRootPolynomial.Gaussian} (inside : Reciprocal.Bounds.InDisk curve.polynomial
  point)
    {parameter : InverseRootPolynomial.Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) (exponent : Nat) :
    Reciprocal.Bounds.InDisk curve.polynomial (point * (Path.ofCoordinate parameter) ^ exponent) := by
  have norm : Data.Gaussian.Norm.Basic.normSq (Path.ofCoordinate parameter) ≤ 1 := by
    rw [Data.Gaussian.Norm.Basic.normSq, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      show (0 : InverseRootPolynomial.Coordinate) ^ 2 = 0 by decide, _root_.add_zero]
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct unit.1 unit.2 2).trans_eq (_root_.one_pow _)
  have powered := Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg (Path.ofCoordinate
    parameter)) norm exponent
  have movement : Data.Gaussian.Norm.Basic.normSq (point * (Path.ofCoordinate parameter) ^ exponent) ≤
    Data.Gaussian.Norm.Basic.normSq point := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powered (Data.Gaussian.Norm.Basic.normSq_nonneg
      point)).trans_eq
      (by rw [_root_.one_pow, Fraction.Field.mul_one_direct])
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans inside

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
private theorem degree_norm : Data.Gaussian.Norm.Basic.normSq (Primitives.degree curve :
  InverseRootPolynomial.Gaussian) ≤ 4 := by
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
    InverseModelDifferentialResidual.DifferentialResidualBounds cap.model
  /-- The cached squared-norm ceiling for the initial differential residual on the fixed unit square. -/
    differentialUpper : InverseRootPolynomial.Coordinate
  /-- The cached residual ceiling is the finite polynomial evaluation bound on the original fixed square. -/
    differentialUpper_eq : differentialUpper = Dense.Gaussian.Bounds.Box.denseEvalNormBound initial.value
    boundingBox
  /-- The cached positive radicand lower bound throughout the reciprocal disk. -/ lower :
    InverseRootPolynomial.Coordinate
  /-- The cached lower bound is one quarter of the original leading coefficient's squared norm. -/ lower_eq : lower =
    Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff / 4
  /-- The cached uniform squared-norm ceiling for original cap inverse-polynomial samples. -/ inverseUpper :
    InverseRootPolynomial.Coordinate
  /-- The cached inverse ceiling is one plus four divided by the retained radicand lower bound. -/ inverseUpper_eq :
    inverseUpper = 1 + 4 / lower

constructive_injectivity Data

namespace Data

/-- Cache the padded disk, original differential residual and numerical ceilings shared by every later cap sample. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap :=
  let initial := DifferentialResidualBounds.build cap.model
  let lower := Data.Gaussian.Norm.Basic.normSq curve.polynomial.leadingCoeff / 4
  ⟨ReciprocalPaddedDisk.Data.build cap, initial, Dense.Gaussian.Bounds.Box.denseEvalNormBound initial.value
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox, rfl,
    lower, rfl, 1 + 4 / lower, rfl⟩

/-- The retained radicand lower bound is positive because the original leading coefficient is nonzero. -/
theorem lower_positive (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) : 0 < data.lower :=
  by
  rw [data.lower_eq]
  exact Fraction.Order.Field.div_pos_direct
    (Data.Gaussian.Norm.Basic.normSq_pos (DensePolynomial.leadingCoeff_ne_zero curve.nonzero)) (by decide)

/-- The retained inverse-polynomial squared-norm ceiling is strictly positive. -/
theorem inverseUpper_positive (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) : 0 <
  data.inverseUpper := by
  rw [data.inverseUpper_eq]
  exact (show (0 : InverseRootPolynomial.Coordinate) < 1 by decide).trans_le
    (le_add_of_nonneg_right (Fraction.Order.Field.div_nonneg_direct (by decide) data.lower_positive.le))

/-- The retained initial differential-residual ceiling is nonnegative. -/
theorem differentialUpper_nonnegative (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) : 0 ≤
  data.differentialUpper := by
  rw [data.differentialUpper_eq]
  exact (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- Every original cap inverse-polynomial refinement satisfies the retained ceiling throughout the reciprocal disk. -/
theorem inverse_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (index : Nat) {point :
  InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq ((cap.model.refine index).value.eval point) ≤ data.inverseUpper := by
  let model := Data.diskPointModel cap point inside
  have same : (model.refine index).value = (cap.model.refine index).value := (Data.diskModel_refine cap _ _ index).1
  rw [data.inverseUpper_eq, ← same]
  apply Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.inverse_le (model.refine index)
    (Data.pointBox_contains point) data.lower_positive
  rw [data.lower_eq, cap.polynomial_eq]
  exact Reciprocal.Bounds.disk_lower curve.polynomial (BranchIsolation.degreePositive curve) point inside

/-- The differential residual satisfies its retained geometric quarter-radius bound at every reciprocal disk point.

Each finite refinement reuses the cached cap model and the initial coefficient ceiling; the same disk containment
witness pays every later stage. -/
theorem differential_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (index : Nat)
  {point : InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual cap.polynomial
      (cap.model.refine index).value point) ≤
      Geometric.Basic.quarterRadius data.differentialUpper index := by
  induction index with
  | zero =>
      change Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual
        cap.polynomial cap.model.value point) ≤ _
      rw [← data.initial.value_eq, Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct,
        data.differentialUpper_eq]
      exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains inside)
  | succ index previous =>
      let model := Data.diskPointModel cap point inside
      have same (stage : Nat) : (model.refine stage).value = (cap.model.refine stage).value :=
        (Data.diskModel_refine cap _ _ stage).1
      have step := (Model.step_differentialResidual_bound (model.refine index)) (Data.pointBox_contains point)
      simp only [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at step
      change Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual
        cap.polynomial (model.refine (index + 1)).value point) ≤ _ at step
      rw [same (index + 1), same index] at step
      apply step.trans
      calc
        _ = Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual
          cap.polynomial (cap.model.refine index).value point) * (1 / 4) := by
          rw [Fraction.Field.div_eq_mul_inv_direct, show (1 / 4 : Coordinate) = 4⁻¹ by decide]
        _ ≤ Geometric.Basic.quarterRadius data.differentialUpper index * (1 / 4) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct previous (by decide)
        _ = _ := by
          rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ];
          ring1

/-- The uniform primitive-factor ceiling is eight times the retained inverse-polynomial ceiling. -/
@[expose] def factorUpper (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) : Coordinate := 8
  * data.inverseUpper

/-- The uniform primitive-factor ceiling is nonnegative. -/
theorem factorUpper_nonnegative (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) : 0 ≤
  data.factorUpper :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.inverseUpper_positive.le

/-- The cap factor's bound is independent of the refinement index and holds at every disk point, including the origin,
in both degree parities. -/
theorem factor_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) {differential :
  Differentials.Basic.Differential genus} {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) {point : InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (sample.factor.eval point) ≤ data.factorUpper := by
  have estimate := Radial.Bounds.factor_bound sample.factor point
    (decide (HyperellipticReciprocal.originOrder curve = 1)) (4 * data.inverseUpper) (by
      intro parameter unit
      rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.radial_degree]
      let coordinate := point * (Path.ofCoordinate parameter) ^ Primitives.degree curve
      have contained := Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.radial_inside inside unit
        (Primitives.degree curve)
      change Data.Gaussian.Norm.Basic.normSq (sample.factor.eval coordinate + (Primitives.degree curve :
        InverseRootPolynomial.Gaussian) * coordinate *
        (GCD.derivative sample.factor).eval coordinate) ≤ _
      rw [sample.factor_derivative, sample.inverse_eq, Data.Gaussian.Norm.Basic.normSq_mul,
        Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_neg, Power.normSq_pow]
      have numerator := Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg coordinate)
        (Reciprocal.Bounds.disk_unit_bound contained) (HyperellipticReciprocal.reversedDifferential
          differential).exponent
      have factors := Fraction.Order.Arithmetic.mul_le_mul_direct
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.degree_norm (curve := curve)) numerator
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg coordinate) _) (by decide)
      have bounded := Fraction.Order.Arithmetic.mul_le_mul_direct factors (data.inverse_bound index contained)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) _))
      simpa only [_root_.one_pow, Fraction.Field.mul_one_direct] using bounded)
  exact estimate.trans_eq (by unfold Disk.RegularBounds.Data.factorUpper; ring1)

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
