module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Riemann.Periods.PrimitiveTriangleBilinear
import Purelib.Tactic.Ring

public section

/-! Both reciprocal primitives use the same coordinate increments. Their
affine determinant is exactly zero; the remaining wedge has cubic squared
diameter decay, sufficient to pay the refined triangle count. -/
namespace Purelib.Riemann.Periods.ReciprocalCapBilinearBounds

open Purelib.Data.Rat

open Purelib.Data in
/-- The exact Gaussian rational carrier of the reciprocal primitive samples. -/
private abbrev Gaussian := Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (Sample)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_mul)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Topology.Polygon.Stokes (PrimitivePoint triangleWedgeArea)
variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential other :
    Differential genus}
  {domain : Purelib.Geometry.Rational.Box}
  {index otherIndex : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Sample cap differential index box}
    {otherSample : Sample cap other otherIndex otherBox}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap in
open Purelib.Data in
/-- Pair the two retained reciprocal primitive values at the same coordinate. -/
@[expose] def pairedValue (sample : Primitives.Sample cap differential index box) (otherSample : Primitives.Sample cap
  other otherIndex otherBox)
    (point : Gaussian.Basic.Canonical) : PrimitivePoint := ⟨sample.primitive.value.eval point,
      otherSample.primitive.value.eval point⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap in
/-- The rational cubic-error scale from the maxima of two retained coefficient and remainder bounds. -/
@[expose] def bilinearScale (left : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample domain) (right :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
  otherSample domain) : Coordinate :=
  16 * (2 * max left.coefficient right.coefficient * max left.remainder right.remainder +
    64 * (max left.remainder right.remainder)^2)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap in
open Purelib.Data.Rat.Fraction.Order in
/-- Nonnegative retained coefficient and remainder bounds give a nonnegative bilinear scale. -/
theorem bilinearScale_nonnegative (left : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample domain) (right
    : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
  otherSample domain) :
    0 ≤ bilinearScale left right := by
  have coefficient : 0 ≤ max left.coefficient right.coefficient := left.coefficient_nonnegative.trans
    (Fraction.Order.Basic.le_max_left _ _)
  have remainder : 0 ≤ max left.remainder right.remainder := left.remainder_nonnegative.trans
    (Fraction.Order.Basic.le_max_left _ _)
  have first : 0 ≤ 2 * max left.coefficient right.coefficient * max left.remainder right.remainder :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide) coefficient) remainder
  have sixtyFour : (0 : Coordinate) ≤ 64 := by decide +kernel
  have last : 0 ≤ 64 * (max left.remainder right.remainder)^2 := Arithmetic.mul_nonneg_direct sixtyFour
    (Arithmetic.sq_nonneg_direct _)
  exact Arithmetic.mul_nonneg_direct (by decide) (add_nonneg first last)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Geometry.Rational (Box) in
open Purelib.Riemann in
/-- Bound the paired reciprocal primitive wedge by cubic squared-diameter decay.

All three vertices lie in the common certified domain, both squared edge distances are at most a nonnegative diameter
bound of at most sixty-four, and the two affine parts use the same coordinate increments. -/
theorem bilinear_triangle_bound (left : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample domain) (right :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
  otherSample domain)
    {first second third : Gaussian.Basic.Canonical}
    (firstInside : domain.Contains first)
    (secondInside : domain.Contains second)
    (thirdInside : domain.Contains third)
    {diameter : Coordinate} (nonnegative : 0 ≤ diameter) (small : diameter ≤ 64)
    (secondDistance : Data.Gaussian.Norm.Basic.normSq (second - first) ≤ diameter) (thirdDistance :
      Data.Gaussian.Norm.Basic.normSq (third -
      first) ≤ diameter) :
    Data.Gaussian.Norm.Basic.normSq (triangleWedgeArea (pairedValue sample otherSample first) (pairedValue sample
      otherSample
      second)
      (pairedValue sample otherSample third)) ≤ bilinearScale left right * diameter^3 := by
  let coefficient := max left.coefficient right.coefficient
  let remainder := max left.remainder right.remainder
  have coefficientNonnegative : 0 ≤ coefficient := left.coefficient_nonnegative.trans (Fraction.Order.Basic.le_max_left
    _ _)
  have remainderNonnegative : 0 ≤ remainder := left.remainder_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)
  have affine {d : Basic.Differential genus} {i : Nat} {b : Box} {s : Primitives.Sample cap d i b}
      (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds s domain) (boundLe : bounds.coefficient ≤
          coefficient)
      {point : Gaussian.Basic.Canonical} (distance : Data.Gaussian.Norm.Basic.normSq (point - first) ≤ diameter) :
      Basic.Canonical.normSq (s.coefficient.eval first * (point - first)) ≤ 1 * (coefficient * diameter) := by
    rw [← Basic.normSq_eq_canonical, Basic.normSq_mul, Fraction.Field.one_mul]
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((bounds.coefficient_box_le firstInside).trans boundLe)
      (Basic.normSq_nonneg _)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct distance coefficientNonnegative)
  have error {d : Basic.Differential genus} {i : Nat} {b : Box} {s : Primitives.Sample cap d i b}
      (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds s domain) (boundLe : bounds.remainder ≤
          remainder)
      {point : Gaussian.Basic.Canonical} (inside : domain.Contains point)
      (distance : Data.Gaussian.Norm.Basic.normSq (point - first) ≤ diameter) :
      Basic.Canonical.normSq (s.primitive.value.eval point - s.primitive.value.eval first - s.coefficient.eval first *
        (point - first)) ≤
        1 * (remainder * diameter^2) := by
    rw [← Basic.normSq_eq_canonical, Fraction.Field.one_mul]
    exact (bounds.increment_box_le firstInside
      inside).trans
      ((Arithmetic.mul_le_mul_of_nonneg_right_direct boundLe (Arithmetic.sq_nonneg_direct _)).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.pow_le_pow_direct
          (Basic.normSq_nonneg _) distance 2) remainderNonnegative))
  have estimate := Periods.PrimitiveTriangleBilinear.bilinearDeterminant_bound
    (sample.coefficient.eval first) (otherSample.coefficient.eval first) (second - first) (third - first)
    (sample.primitive.value.eval second - sample.primitive.value.eval first)
    (sample.primitive.value.eval third - sample.primitive.value.eval first)
    (otherSample.primitive.value.eval second - otherSample.primitive.value.eval first)
    (otherSample.primitive.value.eval third - otherSample.primitive.value.eval first)
    1 1 (coefficient * diameter) (coefficient * diameter) (remainder * diameter^2) (remainder * diameter^2)
    (affine left (Fraction.Order.Basic.le_max_left _ _) secondDistance) (affine left (Fraction.Order.Basic.le_max_left _
      _) thirdDistance)
    (affine right (Fraction.Order.Basic.le_max_right _ _) secondDistance) (affine right
      (Fraction.Order.Basic.le_max_right _ _) thirdDistance)
    (error left (Fraction.Order.Basic.le_max_left _ _) secondInside secondDistance) (error left
      (Fraction.Order.Basic.le_max_left _ _) thirdInside thirdDistance)
    (error right (Fraction.Order.Basic.le_max_right _ _) secondInside secondDistance) (error right
      (Fraction.Order.Basic.le_max_right _ _) thirdInside thirdDistance)
  rw [← Basic.normSq_eq_canonical] at estimate
  have fourth : remainder^2 * diameter^4 ≤ 64 * remainder^2 * diameter^3 := by
    have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct small
      (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct remainder) (Arithmetic.pow_nonneg_direct nonnegative
        3))
    exact (by ring1 : remainder^2 * diameter^4 = (remainder^2 * diameter^3) * diameter).trans_le
      (bounded.trans_eq (by ring1))
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (le_refl (2 * coefficient * remainder * diameter^3)) fourth) (by
        decide : (0 : Coordinate) ≤ 16)
  change Data.Gaussian.Norm.Basic.normSq (triangleWedgeArea (pairedValue sample otherSample first) (pairedValue sample
    otherSample
    second)
    (pairedValue sample otherSample third)) ≤ _ at estimate
  exact estimate.trans ((by ring1 :
    1 * 1 * (16 * (coefficient * diameter * (remainder * diameter^2) + coefficient * diameter * (remainder * diameter^2)
      +
      remainder * diameter^2 * (remainder * diameter^2))) =
      16 * (2 * coefficient * remainder * diameter^3 + remainder^2 * diameter^4)).trans_le
        (paid.trans_eq (by unfold bilinearScale; dsimp only [-eq_self, -iff_self, coefficient, remainder] at *; ring1)))

end Purelib.Riemann.Periods.ReciprocalCapBilinearBounds

end
