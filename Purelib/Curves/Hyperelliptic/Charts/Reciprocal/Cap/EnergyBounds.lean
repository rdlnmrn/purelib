module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
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
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Energy

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Riemann.Normalization

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Taylor budgets for the retained cap polynomial

The containing square covers the whole reciprocal disk. Its finite Horner
and Taylor ceilings are cached for the existing polynomial; neither the
inverse approximation nor the primitive is constructed again.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Energy.AffineTriangle (affinePrimitiveIncrement affinePrimitiveIncrementError)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (crossErrorSquare computedAffineTriangleError
  computedAffineTriangleError_totalBudget_le)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (Sample)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- Cached coefficient and Taylor-remainder ceilings for one original cap primitive on a fixed rectangle.

The default rectangle contains the reciprocal disk; both bounds retain the exact existing polynomial sample without
refinement. -/
structure EnergyBounds (sample : Primitives.Sample cap differential index box)
    (domain : Rational.Box := RegularBounds.boundingBox) where
  /-- The cached finite squared-norm ceiling of the original coefficient polynomial. -/ coefficient :
    InverseRootPolynomial.Coordinate
  /-- The coefficient ceiling is the exact finite polynomial evaluation bound on the retained rectangle. -/
    coefficient_eq : coefficient = Dense.Gaussian.Bounds.Box.denseEvalNormBound sample.coefficient domain
  /-- The cached finite Taylor-remainder ceiling of the original primitive polynomial. -/ remainder :
    InverseRootPolynomial.Coordinate
  /-- The remainder ceiling is the exact finite Taylor bound on the same retained rectangle. -/ remainder_eq : remainder
    = Taylor.denseTaylorRemainderBound sample.primitive.value domain

constructive_injectivity EnergyBounds

namespace EnergyBounds

variable {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {domain : Purelib.Geometry.Rational.Box}

/-- Compute finite coefficient and Taylor ceilings for the supplied original cap sample and retained rectangle. -/
def build (sample : Primitives.Sample cap differential index box)
    (domain : Rational.Box := RegularBounds.boundingBox) :
      EnergyBounds sample domain :=
  ⟨Dense.Gaussian.Bounds.Box.denseEvalNormBound sample.coefficient domain, rfl,
    Taylor.denseTaylorRemainderBound sample.primitive.value domain, rfl⟩

/-- The cached coefficient squared-norm ceiling is nonnegative. -/
theorem coefficient_nonnegative (bounds : EnergyBounds sample
  domain) : 0 ≤ bounds.coefficient := by
  rw [bounds.coefficient_eq]
  exact (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- The cached Taylor-remainder ceiling is nonnegative. -/
theorem remainder_nonnegative (bounds : EnergyBounds sample
  domain) : 0 ≤ bounds.remainder := by
  rw [bounds.remainder_eq]
  exact (Taylor.denseTaylorRemainderBound_pos _ _).le

/-- The original cap coefficient satisfies its cached ceiling throughout the retained rectangle. -/
theorem coefficient_box_le (bounds : EnergyBounds sample domain)
  {point : InverseRootPolynomial.Gaussian}
    (inside : domain.Contains point) : Data.Gaussian.Norm.Basic.normSq (sample.coefficient.eval point) ≤
      bounds.coefficient := by
  rw [bounds.coefficient_eq]
  exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _ inside

/-- The original primitive's linearization error is bounded by the cached Taylor ceiling times squared displacement norm
squared. -/
theorem increment_box_le (bounds : EnergyBounds sample domain)
  {first last : InverseRootPolynomial.Gaussian}
    (firstInside : domain.Contains first)
    (lastInside : domain.Contains last) :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval last - sample.primitive.value.eval first -
      sample.coefficient.eval first * (last - first)) ≤
      bounds.remainder * Data.Gaussian.Norm.Basic.normSq (last - first) ^ 2 := by
  rw [bounds.remainder_eq]
  have estimate := Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
    sample.primitive.value lastInside
      firstInside
  rw [sample.primitive.derivative_eq] at estimate
  exact estimate

/-- The normalized cross-error square is bounded by the product of the two supplied squared-norm ceilings. -/
private theorem cross_le {first second : InverseRootPolynomial.Gaussian} {firstBound secondBound :
  InverseRootPolynomial.Coordinate}
    (firstLe : Data.Gaussian.Norm.Basic.normSq first ≤ firstBound) (secondLe :
      Data.Gaussian.Norm.Basic.normSq second ≤ secondBound) :
    PreparedSurfaceCoercivity.crossErrorSquare first second ≤ firstBound * secondBound := by
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct firstLe secondLe (Data.Gaussian.Norm.Basic.normSq_nonneg
    second)
    ((Data.Gaussian.Norm.Basic.normSq_nonneg first).trans firstLe)
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    ((Data.Gaussian.Norm.Basic.normSq_nonneg first).trans firstLe) ((Data.Gaussian.Norm.Basic.normSq_nonneg
      second).trans secondLe)
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)).2
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by
      decide : (1 : InverseRootPolynomial.Coordinate) ≤ 4) nonnegative
  rw [Fraction.Field.mul_one_direct] at scaled
  exact product.trans scaled

/-- The computed face budget is linear in the squared diameter after the Taylor error meets the selected local
tolerance. -/
theorem triangle_budget_le (bounds : EnergyBounds sample domain)
  (first second third : InverseRootPolynomial.Gaussian)
    (firstInside : domain.Contains first)
    (secondInside : domain.Contains second)
    (thirdInside : domain.Contains third)
    (epsilon distance radius : InverseRootPolynomial.Coordinate) (epsilonPositive : 0 < epsilon) (epsilonLe : epsilon ≤
      1)
    (distancePositive : 0 < distance) (radiusPositive : 0 < radius) (radiusEq : radius = epsilon * distance)
    (secondDistance : Data.Gaussian.Norm.Basic.normSq (second - first) ≤ distance) (thirdDistance :
      Data.Gaussian.Norm.Basic.normSq (third - first) ≤ distance)
    (taylor : bounds.remainder * distance ≤ epsilon ^ 2) :
    (PreparedSurfaceCoercivity.computedAffineTriangleError (sample.coefficient.eval first) first second third
      (sample.primitive.value.eval first) (sample.primitive.value.eval second) (sample.primitive.value.eval third)
      radius radiusPositive).totalBudget ≤ (2 * bounds.coefficient + 4) * radius := by
  have affine {last : InverseRootPolynomial.Gaussian} (close : Data.Gaussian.Norm.Basic.normSq (last - first) ≤
    distance) :
      Data.Gaussian.Norm.Basic.normSq (AffineTriangle.affinePrimitiveIncrement (sample.coefficient.eval first)
        first last) ≤ bounds.coefficient * distance := by
    rw [AffineTriangle.affinePrimitiveIncrement, ← mul_sub, Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct (bounds.coefficient_box_le firstInside) close
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) bounds.coefficient_nonnegative
  have error {last : InverseRootPolynomial.Gaussian} (inside : domain.Contains last)
      (close : Data.Gaussian.Norm.Basic.normSq (last - first) ≤ distance) :
      Data.Gaussian.Norm.Basic.normSq (AffineTriangle.affinePrimitiveIncrementError (sample.coefficient.eval
        first) first last
        (sample.primitive.value.eval first) (sample.primitive.value.eval last)) ≤ epsilon ^ 2 * distance := by
    have same : AffineTriangle.affinePrimitiveIncrementError (sample.coefficient.eval first) first last
        (sample.primitive.value.eval first) (sample.primitive.value.eval last) =
        sample.primitive.value.eval last - sample.primitive.value.eval first - sample.coefficient.eval first * (last -
          first) := by
      unfold AffineTriangle.affinePrimitiveIncrementError AffineTriangle.affinePrimitiveIncrement
      ring1
    rw [same]
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) close 2
    have estimate := (bounds.increment_box_le firstInside inside).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square bounds.remainder_nonnegative)
    calc
      _ ≤ bounds.remainder * distance ^ 2 := estimate
      _ = (bounds.remainder * distance) * distance := by ring1
      _ ≤ epsilon ^ 2 * distance := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct taylor
        distancePositive.le
  have firstCross := cross_le (error secondInside
    secondDistance) (affine thirdDistance)
  have secondCross := cross_le (affine
    secondDistance) (error thirdInside thirdDistance)
  have mixedCross := cross_le (error secondInside
    secondDistance) (error thirdInside thirdDistance)
  have firstBound : PreparedSurfaceCoercivity.crossErrorSquare
      (AffineTriangle.affinePrimitiveIncrementError (sample.coefficient.eval first) first second
        (sample.primitive.value.eval first) (sample.primitive.value.eval second))
      (AffineTriangle.affinePrimitiveIncrement (sample.coefficient.eval first) first third) ≤ bounds.coefficient *
        radius ^ 2 :=
    firstCross.trans_eq (by rw [radiusEq]; ring1)
  have secondBound : PreparedSurfaceCoercivity.crossErrorSquare
      (AffineTriangle.affinePrimitiveIncrement (sample.coefficient.eval first) first second)
      (AffineTriangle.affinePrimitiveIncrementError (sample.coefficient.eval first) first third
        (sample.primitive.value.eval first) (sample.primitive.value.eval third)) ≤
      bounds.coefficient * radius ^ 2 := secondCross.trans_eq (by rw [radiusEq]; ring1)
  have mixedBound : PreparedSurfaceCoercivity.crossErrorSquare
      (AffineTriangle.affinePrimitiveIncrementError (sample.coefficient.eval first) first second
        (sample.primitive.value.eval first) (sample.primitive.value.eval second))
      (AffineTriangle.affinePrimitiveIncrementError (sample.coefficient.eval first) first third
        (sample.primitive.value.eval first) (sample.primitive.value.eval third)) ≤ 1 * radius ^ 2 := by
    have squareLe : epsilon ^ 2 ≤ 1 := (Fraction.Order.Arithmetic.pow_le_pow_direct epsilonPositive.le epsilonLe
      2).trans_eq (by decide)
    exact mixedCross.trans ((by
        rw [radiusEq];
        ring1 : (epsilon ^ 2 * distance) * (epsilon ^ 2 * distance) = epsilon ^ 2 * radius ^ 2).trans_le
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squareLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct radius)))
  exact (PreparedSurfaceCoercivity.computedAffineTriangleError_totalBudget_le _ _ _ _ _ _ _ radius radiusPositive
    bounds.coefficient bounds.coefficient 1 firstBound secondBound mixedBound).trans_eq (by ring1)

/-- The regular reciprocal disk remains a certified specialization of the same box-based Taylor calculation used for
sampled root-coordinate caps. -/
theorem coefficient_le (bounds : EnergyBounds sample) {point :
  InverseRootPolynomial.Gaussian}
    (inside : Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (sample.coefficient.eval point) ≤ bounds.coefficient :=
  bounds.coefficient_box_le (RegularBounds.boundingBox_contains inside)

/-- The same cached Taylor remainder bound controls original primitive increments at any two reciprocal disk points. -/
theorem increment_le (bounds : EnergyBounds sample) {first last
  : InverseRootPolynomial.Gaussian}
    (firstInside : Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Reciprocal.Bounds.InDisk curve.polynomial last) :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval last - sample.primitive.value.eval first -
      sample.coefficient.eval first * (last - first)) ≤
      bounds.remainder * Data.Gaussian.Norm.Basic.normSq (last - first) ^ 2 :=
  bounds.increment_box_le (RegularBounds.boundingBox_contains firstInside)
    (RegularBounds.boundingBox_contains lastInside)

end EnergyBounds
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
