module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Derivative
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Init.Prelude
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PrimitiveSamples

section

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelDifferentialResidual

@[expose] public section

/-!
# Cap derivative comparison on the actual exterior overlap

The global regular-factor bounds are shared by all reciprocal cells. Each
cell prepares its own initial reciprocal differential residual once. The
resulting geometric estimate uses the displayed disk and radicand margins,
so it applies along the actual inverted outer arc outside the inner square.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Model half)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback (Preparation Sample)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {box :
    Purelib.Geometry.Rational.Box}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {initial : Model
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) box}

set_option genInjectivity false in
/-- A local reciprocal derivative-comparison preparation sharing the original regular cap bounds.

The local residual polynomial and inverse ceiling are cached before refinement, with an exact common geometric error
scale. -/
structure Data (regular : RegularBounds.Data cap)
    (initial : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) box) where
  /-- The original local reciprocal differential residual paired with the retained regular residual. -/ preparation :
    Preparation cap initial
  /-- The preparation reuses exactly the original regular cap residual. -/ regular_eq : preparation.regular =
    regular.initial
  /-- The cached local reciprocal inverse-polynomial squared-norm ceiling. -/ inverseUpper :
    InverseRootPolynomial.Coordinate
  /-- The local inverse ceiling is one plus four divided by the original collar radicand margin. -/ inverseUpper_eq :
    inverseUpper = 1 + 4 / collar.radicandBound
  /-- The cached common geometric derivative-error scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The scale is the exact sum of the inverse-residual and two differential-residual allocations. -/ scale_eq : scale
    = 2 * inverseUpper * (1 / 256) + 4 * regular.factorUpper *
    (regular.inverseUpper * preparation.reciprocal.bound + inverseUpper * regular.differentialUpper)

constructive_injectivity Data

namespace Data

/-- Cache the local reciprocal residual once, reuse the original regular residual, and retain their
derivative-comparison scale. -/
def build (regular : RegularBounds.Data cap)
    (initial : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) box) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular initial :=
  let preparation : Preparation cap initial := ⟨DifferentialResidualBounds.build initial, regular.initial⟩
  let inverseUpper := 1 + 4 / collar.radicandBound
  ⟨preparation, rfl, inverseUpper, rfl, 2 * inverseUpper * (1 / 256) + 4 * regular.factorUpper *
    (regular.inverseUpper * preparation.reciprocal.bound + inverseUpper * regular.differentialUpper), rfl⟩

/-- The local reciprocal inverse-polynomial ceiling is strictly positive. -/
theorem inverseUpper_positive (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular initial)
  : 0 < data.inverseUpper := by
  rw [data.inverseUpper_eq]
  exact (show (0 : InverseRootPolynomial.Coordinate) < 1 by decide).trans_le
    (le_add_of_nonneg_right (Fraction.Order.Field.div_nonneg_direct (by decide) collar.radicandBound_positive.le))

/-- The cached derivative-comparison error scale is nonnegative. -/
theorem scale_nonnegative (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular initial) : 0
  ≤ data.scale := by
  have residualNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 256 := by decide +kernel
  rw [data.scale_eq]
  exact add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.inverseUpper_positive.le) residualNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) regular.factorUpper_nonnegative)
      (add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct regular.inverseUpper_positive.le
          data.preparation.reciprocal.bound_nonnegative)
        (Fraction.Order.Arithmetic.mul_nonneg_direct data.inverseUpper_positive.le
          regular.differentialUpper_nonnegative)))

/-- Every natural power of a point in the original reciprocal disk has squared norm at most one. -/
private theorem power_bound {point : InverseRootPolynomial.Gaussian} (inside : Reciprocal.Bounds.InDisk curve.polynomial
  point) (exponent : Nat) :
    Data.Gaussian.Norm.Basic.normSq (point ^ exponent) ≤ 1 := by
  rw [Power.normSq_pow]
  exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg point)
    (Reciprocal.Bounds.disk_unit_bound inside) exponent).trans_eq (_root_.one_pow _)

/-- A triple product with first squared norm at most one is bounded by the other two squared-norm ceilings. -/
private theorem product_bound {first second third : InverseRootPolynomial.Gaussian} {secondUpper thirdUpper :
  InverseRootPolynomial.Coordinate}
    (firstBound : Data.Gaussian.Norm.Basic.normSq first ≤ 1) (secondBound :
      Data.Gaussian.Norm.Basic.normSq second ≤ secondUpper)
    (thirdBound : Data.Gaussian.Norm.Basic.normSq third ≤ thirdUpper) :
      Data.Gaussian.Norm.Basic.normSq (first * second * third) ≤ secondUpper * thirdUpper := by
  rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
  have firstTwo := Fraction.Order.Arithmetic.mul_le_mul_direct firstBound secondBound
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
  rw [Fraction.Field.one_mul] at firstTwo
  exact Fraction.Order.Arithmetic.mul_le_mul_direct firstTwo thirdBound (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    ((Data.Gaussian.Norm.Basic.normSq_nonneg second).trans secondBound)

variable {differential : Differential genus} {index : Nat} {capBox :
  Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index capBox}

/-- The retained reciprocal polynomial sample satisfies the local inverse ceiling under the original radicand margin. -/
private theorem reciprocal_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular
  initial) (sample : Sample data.preparation capSample)
    {point : InverseRootPolynomial.Gaussian} (localInside : box.Contains point)
    (lower : collar.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial
      curve).eval point)) :
    Data.Gaussian.Norm.Basic.normSq (sample.reciprocal.value.eval point) ≤ data.inverseUpper := by
  rw [data.inverseUpper_eq]
  exact RegularBounds.inverse_le sample.reciprocal localInside collar.radicandBound_positive lower

/-- The regular inverse residual term satisfies its retained geometric derivative-error allocation. -/
private theorem first_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular initial)
  (sample : Sample data.preparation capSample)
    {point : InverseRootPolynomial.Gaussian} (localInside : box.Contains point) (inside : Reciprocal.Bounds.InDisk
      curve.polynomial point)
    (lower : collar.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial
      curve).eval point)) :
    Data.Gaussian.Norm.Basic.normSq (point ^ (HyperellipticReciprocal.reversedDifferential
      differential).exponent * sample.reciprocal.value.eval point *
      capSample.inverse.residual.eval point) ≤ Geometric.Basic.quarterRadius (data.inverseUpper * (1 / 256)) index :=
  (product_bound
    (power_bound inside _) (data.reciprocal_bound
    sample localInside lower)
    (capSample.disk_residual_bound inside)).trans_eq
      (by rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)

/-- The reciprocal differential residual term satisfies its retained geometric allocation on the original overlap. -/
private theorem second_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular initial)
  (sample : Sample data.preparation capSample)
    {point : InverseRootPolynomial.Gaussian} (localInside : box.Contains point) (inside : Reciprocal.Bounds.InDisk
      curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (point ^ (1 - HyperellipticReciprocal.originOrder curve) *
      capSample.inverse.value.eval point *
      InverseModelDifferentialResidual.differentialResidual (HyperellipticReciprocal.polynomial curve)
        sample.reciprocal.value point) ≤
      Geometric.Basic.quarterRadius (regular.inverseUpper * data.preparation.reciprocal.bound) index := by
  have regularBound : Data.Gaussian.Norm.Basic.normSq (capSample.inverse.value.eval point) ≤
    regular.inverseUpper := by
    rw [capSample.inverse_eq]
    exact regular.inverse_bound index inside
  exact (product_bound
    (power_bound inside _) regularBound
    (sample.reciprocal_differential_bound localInside)).trans_eq
    (by rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)

/-- The regular differential residual term satisfies its retained geometric allocation on the original overlap. -/
private theorem third_bound (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular initial)
  (sample : Sample data.preparation capSample)
    {point : InverseRootPolynomial.Gaussian} (localInside : box.Contains point) (inside : Reciprocal.Bounds.InDisk
      curve.polynomial point)
    (lower : collar.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial
      curve).eval point)) :
    Data.Gaussian.Norm.Basic.normSq (point * sample.reciprocal.value.eval point *
      InverseModelDifferentialResidual.differentialResidual cap.polynomial capSample.inverse.value point) ≤
      Geometric.Basic.quarterRadius (data.inverseUpper * regular.differentialUpper) index := by
  have differentialBound : Data.Gaussian.Norm.Basic.normSq
    (InverseModelDifferentialResidual.differentialResidual cap.polynomial capSample.inverse.value point) ≤
      Geometric.Basic.quarterRadius regular.differentialUpper index := by
    rw [capSample.inverse_eq]
    exact regular.differential_bound index inside
  exact (product_bound
    (Reciprocal.Bounds.disk_unit_bound inside)
    (data.reciprocal_bound sample localInside lower) differentialBound).trans_eq
      (by rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)

/-- The original half-scaled cap factor satisfies the retained uniform factor ceiling throughout the reciprocal disk. -/
private theorem factor_bound (regular : RegularBounds.Data cap)
    (capSample : Primitives.Sample cap differential index capBox)
    {point : InverseRootPolynomial.Gaussian} (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (InverseRootPolynomial.half * capSample.factor.eval point) ≤
      regular.factorUpper := by
  rw [Data.Gaussian.Norm.Basic.normSq_mul]
  exact (Fraction.Order.Arithmetic.mul_le_mul_direct (show Data.Gaussian.Norm.Basic.normSq
    InverseRootPolynomial.half ≤ 1 by decide)
    (regular.factor_bound capSample inside) (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)).trans_eq
      (Fraction.Field.one_mul _)

/-- Three retained squared-norm estimates and a factor ceiling bound the full derivative-error expression. -/
private theorem combine {first second third factor : InverseRootPolynomial.Gaussian} {a b c f :
  InverseRootPolynomial.Coordinate}
    (firstBound : Data.Gaussian.Norm.Basic.normSq first ≤ a) (secondBound :
      Data.Gaussian.Norm.Basic.normSq second ≤ b) (thirdBound : Data.Gaussian.Norm.Basic.normSq third
      ≤ c)
    (factorBound : Data.Gaussian.Norm.Basic.normSq factor ≤ f) : Data.Gaussian.Norm.Basic.normSq
      (first + factor * (second + third)) ≤ 2 * a + 4 * f * (b + c) := by
  have sumBound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two second third).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add secondBound thirdBound) (by decide))
  have tailBound := Fraction.Order.Arithmetic.mul_le_mul_direct factorBound sumBound
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    ((Data.Gaussian.Norm.Basic.normSq_nonneg factor).trans factorBound)
  apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
  rw [Data.Gaussian.Norm.Basic.normSq_mul]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstBound tailBound) (by
    decide)).trans_eq (by ring1)

/-- A geometric derivative error on the whole certified overlap, with all scales fixed before the common polynomial
refinement index. -/
theorem derivative_error_le (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds.Data regular initial)
  (sample : Sample data.preparation capSample)
    {point : InverseRootPolynomial.Gaussian} (localInside : box.Contains point) (inside : Reciprocal.Bounds.InDisk
      curve.polynomial point)
    (lower : collar.radicandBound ≤ Data.Gaussian.Norm.Basic.normSq ((HyperellipticReciprocal.polynomial
      curve).eval point)) :
    Data.Gaussian.Norm.Basic.normSq ((Derivative.derivative sample.value).eval point - sample.coefficient.eval
      point) ≤
      Geometric.Basic.quarterRadius data.scale index := by
  rw [sample.derivative_error]
  exact (combine (data.first_bound sample localInside
    inside lower) (data.second_bound sample localInside inside)
    (data.third_bound sample localInside inside lower)
      (factor_bound regular capSample
      inside)).trans_eq
      (by simp only [Geometric.Basic.quarterRadius_eq_mul_pow, data.scale_eq]; ring1)

end Data
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds

end
