module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
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
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-!
# Uniform inverse bounds on the certified padded disk

Reboxing retains the initial value and residual polynomials. A cached norm
bound for that fixed initial value supplies a positive radicand margin and
hence a uniform ceiling for every later Newton inverse polynomial.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Model)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk (Data)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}

section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

/-- Rebox the original cap inverse and residual polynomials at a point of the retained padded disk.

The original cap value and residual caches remain fixed; only the point box and certified residual bound are retained
anew. -/
@[expose] def pointModel
    (data : Data cap) (point : Gaussian) (inside : data.Contains point) :
    Model cap.polynomial (Inverse.Data.pointBox point) where
  value := cap.model.value
  residual := cap.model.residual
  residual_eq := cap.model.residual_eq
  bound := 1 / 64
  bound_nonnegative := by decide +kernel
  bound_small := by decide +kernel
  residualBound := fun other contained => by
    have scalar := data.residual_bound inside
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact (Inverse.Data.eq_of_pointBox_contains contained).symm ▸ scalar

/-- Every pointwise reboxed refinement preserves the exact original cap value and residual polynomials.

Both updates consume the same retained value and residual polynomials at every original refinement index. -/
theorem pointModel_refine
    (data : Data cap) (point : Gaussian) (inside : data.Contains point)
      (index : Nat) :
    ((data.pointModel point inside).refine index).value = (cap.model.refine index).value ∧
      ((data.pointModel point inside).refine index).residual = (cap.model.refine index).residual := by
  induction index with
  | zero => exact ⟨rfl, rfl⟩
  | succ index previous =>
      constructor
      · change
          ((data.pointModel point inside).refine index).value *
            (DensePolynomial.constant 1 +
              ((data.pointModel point inside).refine index).residual.scale half) = _
        rw [previous.1, previous.2]
        rfl
      · dsimp only [Model.refine, Model.step]
        rw [previous.2]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

end

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse

set_option genInjectivity false in
/-- Cached positive radicand and inverse-polynomial ceilings on the original padded disk.

The bounds derive from the retained initial polynomial ceiling and preserve their exact scalar formulas. -/
structure UniformBounds (data : Data cap) where
  /-- The cached original cap initial inverse-polynomial squared-norm ceiling. -/ initialUpper :
    Coordinate
  /-- The cached initial ceiling is exactly the retained padded-disk bound. -/ initialUpper_eq : initialUpper =
    data.initialUpper
  /-- The original initial inverse-polynomial ceiling is strictly positive. -/ positive : 0 < initialUpper
  /-- The cached radicand squared-norm lower bound throughout the padded disk. -/ lower :
    Coordinate
  /-- The retained radicand lower bound is one divided by four times the squared initial ceiling. -/ lower_eq : lower =
    1 / (4 * initialUpper ^ 2)
  /-- The cached radicand lower bound is strictly positive. -/ lower_positive : 0 < lower
  /-- The cached common squared-norm ceiling for all original inverse-polynomial refinements. -/ inverseUpper :
    Coordinate
  /-- The inverse ceiling is one plus four divided by the retained radicand lower bound. -/ inverseUpper_eq :
    inverseUpper = 1 + 4 / lower
  /-- The cached common inverse-polynomial ceiling is strictly positive. -/ inverse_positive : 0 < inverseUpper

constructive_injectivity UniformBounds

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse

section

variable {data : Data cap}

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds

/-- Cache the original initial ceiling, positive radicand margin and uniform inverse-polynomial ceiling.

All three scalar bounds keep their original formulas and derive positivity from the retained initial polynomial ceiling.
-/
@[expose] def build (data : Data cap) :
  UniformBounds data := by
  let initialUpper := data.initialUpper
  have positive : 0 < initialUpper := data.initial_positive
  let lower := 1 / (4 * initialUpper ^ 2)
  have lowerPositive : 0 < lower := Field.div_pos_direct (by decide)
    (Arithmetic.mul_pos_direct (by decide) (Arithmetic.pow_pos_direct positive 2))
  let inverseUpper := 1 + 4 / lower
  have inversePositive : 0 < inverseUpper :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (by decide)
    (Field.div_pos_direct (by decide) lowerPositive)
  exact ⟨initialUpper, rfl, positive, lower, rfl, lowerPositive, inverseUpper, rfl, inversePositive⟩

/-- The original cap radicand satisfies the retained positive lower bound throughout the padded disk. -/
theorem radicand_lower (bounds : UniformBounds data)
  {point : Gaussian} (inside : data.Contains point) :
    bounds.lower ≤ Norm.Basic.normSq (cap.polynomial.eval point) := by
  have residual := data.residual_bound inside
  rw [cap.model.residual_eq] at residual
  let value := cap.polynomial.eval point * cap.model.value.eval point ^ 2
  have triangle := Norm.Bounds.normSq_add_le_two value (1 - value)
  rw [show value + (1 - value) = 1 by ring1, Norm.Basic.normSq_one] at triangle
  have oneLe : 1 ≤ 2 * (Norm.Basic.normSq value + 1 / 16) := triangle.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl (residual.trans (by decide +kernel : (1 / 64 : Coordinate) ≤ 1 / 16)))
        (by decide))
  have quarterLe : 1 / 4 ≤ Norm.Basic.normSq value := by
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide)
    exact (show (1 / 4 : Coordinate) * 2 ≤ 1 - 1 / 8 by decide).trans
      ((Arithmetic.sub_le_sub_direct oneLe le_rfl).trans_eq (by
        rw [show 2 * (Norm.Basic.normSq value + 1 / 16) - 1 / 8 = 2 *
          Norm.Basic.normSq value + (2 * (1 / 16) - 1 / 8) by ring1,
          show (2 * (1 / 16) - 1 / 8 : Coordinate) = 0 by decide]; ring1))
  have initial : Norm.Basic.normSq (cap.model.value.eval point) ≤ bounds.initialUpper := by
    rw [bounds.initialUpper_eq, data.initialUpper_eq]
    exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant _ (data.box_contains inside)
  have normalized : 1 / 4 ≤ Norm.Basic.normSq (cap.polynomial.eval point) * bounds.initialUpper ^
    2 := by
    dsimp only [value] at quarterLe
    rw [Norm.Basic.normSq_mul, Power.normSq_pow] at quarterLe
    exact quarterLe.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) initial 2)
        (Norm.Basic.normSq_nonneg _))
  rw [bounds.lower_eq]
  apply (Field.div_le_iff_pos
    (Arithmetic.mul_pos_direct (by decide : (0 : Coordinate) < 4)
      (Arithmetic.pow_pos_direct bounds.positive 2))).mpr
  exact (show (1 : Coordinate) = 4 * (1 / 4) by decide).trans_le
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct normalized (by decide)).trans_eq (by ring1))

/-- Every original cap inverse refinement satisfies the retained padded-disk ceiling. -/
theorem inverse_bound (bounds : UniformBounds data)
  (index : Nat) {point : Gaussian} (inside : data.Contains point) :
    Norm.Basic.normSq ((cap.model.refine index).value.eval point) ≤ bounds.inverseUpper := by
  rw [bounds.inverseUpper_eq, ← (data.pointModel_refine point inside index).1]
  exact RegularBounds.inverse_le ((data.pointModel point inside).refine index)
    (Inverse.Data.pointBox_contains point) bounds.lower_positive (bounds.radicand_lower inside)

/-- The odd-chart differential ceiling is fixed before the shared cap polynomial's Newton index is selected.

The bound uses the original reversed differential exponent and the cached common inverse-polynomial ceiling. -/
@[expose] def coefficientUpper (bounds : UniformBounds
  data) (differential : Differential genus) : Coordinate :=
  4 * 4 ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * bounds.inverseUpper

/-- The odd-chart differential coefficient ceiling is nonnegative. -/
theorem coefficientUpper_nonnegative (bounds :
  UniformBounds data) (differential :
  Differential genus) :
    0 ≤ bounds.coefficientUpper differential := Arithmetic.mul_nonneg_direct
  (Arithmetic.mul_nonneg_direct (by decide)
    (Arithmetic.pow_nonneg_direct (by decide) _)) bounds.inverse_positive.le

/-- The original odd-chart cap coefficient satisfies its retained ceiling when the squared coordinate lies in the padded
disk.

The original odd-chart coefficient factors and retained inverse-polynomial ceiling bound the same cached sample on the
padded disk. -/
theorem coefficient_bound (bounds : UniformBounds data)
  {differential : Differential genus}
    {index : Nat} {box : Rational.Box} (sample : Primitives.Sample cap differential index box)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {point : Gaussian}
    (inside : data.Contains (point * point)) : Norm.Basic.normSq (sample.coefficient.eval point)
      ≤ bounds.coefficientUpper differential := by
  have inverse := bounds.inverse_bound index inside
  rw [← sample.inverse_eq] at inverse
  have numerator := Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg (point * point))
    (data.norm_le inside) (HyperellipticReciprocal.reversedDifferential differential).exponent
  rw [Norm.Basic.normSq_mul] at numerator
  have identity : Norm.Basic.normSq (sample.coefficient.eval point) =
      4 * (Norm.Basic.normSq point * Norm.Basic.normSq point) ^
        (HyperellipticReciprocal.reversedDifferential differential).exponent *
        Norm.Basic.normSq (sample.inverse.value.eval (point * point)) := by
    rw [sample.coefficient_eq, sample.pulledInverse_eq]
    simp only [Primitives.coefficient, Primitives.point, Primitives.degree,
      branch, show (1 + 1 : Nat) = 2 by rfl, Norm.Basic.normSq_mul, Norm.Basic.normSq_neg,
        Power.normSq_pow,
      show Norm.Basic.normSq ((2 : Nat) : Gaussian) = 4 by decide,
        -eq_self, -iff_self]
    rw [pow_mul, pow_two, pow_two]
  rw [identity, coefficientUpper]
  exact Arithmetic.mul_le_mul_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct numerator (by decide)) inverse
    (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.pow_nonneg_direct (by decide) _))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds

end
end
