module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRadialRibbon
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedArcArea

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-! Paired radial connectors retain their endpoint wedge. The estimate is
uniform in the polynomial stage and in the radial subdivision depth. -/
namespace Purelib.Riemann.RootContinuation.RootRadialGeometry.Bilinear
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

/-- The finite bilinear dyadic area of the supplied original paired values along one radial root-coordinate path. -/
@[expose] def radialArea (values : Gaussian → PrimitivePoint) (depth : Nat) (point : Gaussian) : Gaussian :=
  DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => values (Scale.scale parameter point)) depth 0 1

end Purelib.Riemann.RootContinuation.RootRadialGeometry.Bilinear

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Riemann.Normalization
open Purelib.Data.Gaussian.Scale (scale normSq_scale)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {data : Data cap} {differential other :
    Differential genus}
  {index otherIndex : Nat} {box otherBox : Purelib.Geometry.Rational.Box}

/-- A zero rational scale sends the original Gaussian point to zero. -/
private theorem scale_zero (point : InverseRootPolynomial.Gaussian) : Scale.scale 0 point = 0 := by
  apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Scale.scale_re, Scale.scale_im, Basic.zero_re,
    Basic.zero_im] <;> ring1

/-- A unit rational scale preserves the original Gaussian point. -/
private theorem scale_one (point : InverseRootPolynomial.Gaussian) : Scale.scale 1 point = point := by
  apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Scale.scale_re, Scale.scale_im] <;> ring1

/-- A common rational scale preserves the difference of the original Gaussian endpoints. -/
private theorem scale_sub (first last : InverseRootPolynomial.Gaussian) (parameter : InverseRootPolynomial.Coordinate) :
    Scale.scale parameter last - Scale.scale parameter first = Scale.scale parameter (last - first) := by
  apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Scale.scale_re, Scale.scale_im, Basic.sub_re,
    Basic.sub_im] <;> ring1

/-- The difference of two radial readings is the original Gaussian point scaled by the parameter difference. -/
private theorem radial_sub (point : InverseRootPolynomial.Gaussian) (first last : InverseRootPolynomial.Coordinate) :
    Scale.scale last point - Scale.scale first point = Scale.scale (last - first) point := by
  apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Scale.scale_re, Scale.scale_im, Basic.sub_re,
    Basic.sub_im] <;> ring1

/-- The original paired radial areas, with their endpoint wedge retained, satisfy a fixed padded coefficient bound.

The bound applies to both supplied differential polynomials at all original polynomial stages and every finite radial
subdivision depth. -/
theorem paired_radial_connector_bound (bounds : ReciprocalPaddedInverse.UniformBounds data)
    (sample : Primitives.Sample cap differential index box)
    (otherSample : Primitives.Sample cap other otherIndex otherBox)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last : InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) (depth : Nat) :
    let values := fun point => (⟨sample.primitive.value.eval point, otherSample.primitive.value.eval point⟩ :
      Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (Riemann.RootContinuation.RootRadialGeometry.Bilinear.radialArea values
      depth last -
      Riemann.RootContinuation.RootRadialGeometry.Bilinear.radialArea values depth first - Stokes.edgeArea (values
        first) (values last)) ≤
        512 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)) ^ 2 *
          Data.Gaussian.Norm.Basic.normSq (last - first) := by
  intro values
  let coefficient := max (bounds.coefficientUpper differential) (bounds.coefficientUpper other)
  have coefficientNonnegative : 0 ≤ coefficient := (bounds.coefficientUpper_nonnegative differential).trans
    (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _)
  have increment {d : Differentials.Basic.Differential genus} {n : Nat} {b : Rational.Box}
      (s : Primitives.Sample cap d n b) (coefficientLe : bounds.coefficientUpper d ≤ coefficient)
      {a b : InverseRootPolynomial.Gaussian} (aInside : data.Contains (a * a)) (bInside : data.Contains (b * b)) :
      Data.Gaussian.Norm.Basic.normSq (s.primitive.value.eval b - s.primitive.value.eval a) ≤ 2 * coefficient *
        Data.Gaussian.Norm.Basic.normSq (b - a) := by
    have bound := bounds.chord_increment s branch aInside bInside (left := 0) (right := 1) (by decide) (by decide)
    have zero : RootRadialGeometry.chord a b 0 = a := by
      rw [RootRadialGeometry.chord, show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 by decide,
        scale_zero,
        scale_one,
        Data.Gaussian.Basic.add_zero]
    have one : RootRadialGeometry.chord a b 1 = b := by
      rw [RootRadialGeometry.chord, show (1 : InverseRootPolynomial.Coordinate) - 1 = 0 by decide,
        scale_zero,
        scale_one,
        Data.Gaussian.Basic.zero_add]
    rw [zero, one, show ((1 : InverseRootPolynomial.Coordinate) - 0) ^ 2 = 1 by decide, _root_.mul_one] at bound
    exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientLe (by decide))
        (Data.Gaussian.Norm.Basic.normSq_nonneg _))
  have points {d : Differentials.Basic.Differential genus} {n : Nat} {b : Rational.Box}
      (s : Primitives.Sample cap d n b) (coefficientLe : bounds.coefficientUpper d ≤ coefficient)
      (parameter : InverseRootPolynomial.Coordinate) (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq (s.primitive.value.eval (Scale.scale parameter last) -
        s.primitive.value.eval (Scale.scale parameter first)) ≤
        2 * coefficient * Data.Gaussian.Norm.Basic.normSq (last - first) := by
    have bound := increment s coefficientLe (data.radial_square firstInside unit) (data.radial_square lastInside unit)
    rw [scale_sub, Scale.normSq_scale] at bound
    have factor := (Fraction.Order.Arithmetic.pow_le_pow_direct unit.1 unit.2 2).trans_eq (by
        decide : (1 : InverseRootPolynomial.Coordinate)^2 = 1)
    exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factor (Data.Gaussian.Norm.Basic.normSq_nonneg _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)).trans_eq (by ring1))
  have radial {d : Differentials.Basic.Differential genus} {n : Nat} {b : Rational.Box}
      (s : Primitives.Sample cap d n b) (coefficientLe : bounds.coefficientUpper d ≤ coefficient)
      {point : InverseRootPolynomial.Gaussian} (inside : data.Contains (point * point)) (lower upper :
        InverseRootPolynomial.Coordinate)
      (lowerUnit : 0 ≤ lower ∧ lower ≤ 1) (upperUnit : 0 ≤ upper ∧ upper ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq (s.primitive.value.eval (Scale.scale upper point) -
        s.primitive.value.eval (Scale.scale lower point)) ≤
        (4 * coefficient) * (upper - lower)^2 := by
    have bound := increment s coefficientLe (data.radial_square inside lowerUnit) (data.radial_square inside upperUnit)
    rw [radial_sub, Scale.normSq_scale] at bound
    have rootScalar := data.root_norm_le inside
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at rootScalar
    exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootScalar (Fraction.Order.Arithmetic.sq_nonneg_direct
        _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)).trans_eq (by ring1))
  have drift {d : Differentials.Basic.Differential genus} {n : Nat} {b : Rational.Box}
      (s : Primitives.Sample cap d n b) (coefficientLe : bounds.coefficientUpper d ≤ coefficient)
      (lower upper : InverseRootPolynomial.Coordinate) (lowerUnit : 0 ≤ lower ∧ lower ≤ 1) (upperUnit : 0 ≤ upper ∧
        upper ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq ((s.primitive.value.eval (Scale.scale upper last) -
        s.primitive.value.eval (Scale.scale upper first)) -
        (s.primitive.value.eval (Scale.scale lower last) - s.primitive.value.eval (Scale.scale lower first))) ≤
          (16 * coefficient) * (upper - lower)^2 := by
    have bound := Data.Gaussian.Norm.Bounds.normSq_sub_le_two
      (s.primitive.value.eval (Scale.scale upper last) - s.primitive.value.eval (Scale.scale lower last))
      (s.primitive.value.eval (Scale.scale upper first) - s.primitive.value.eval (Scale.scale lower first))
    have identity : (s.primitive.value.eval (Scale.scale upper last) - s.primitive.value.eval (Scale.scale upper first))
      -
        (s.primitive.value.eval (Scale.scale lower last) - s.primitive.value.eval (Scale.scale lower first)) =
      (s.primitive.value.eval (Scale.scale upper last) - s.primitive.value.eval (Scale.scale lower last)) -
        (s.primitive.value.eval (Scale.scale upper first) - s.primitive.value.eval (Scale.scale lower first)) := by
          ring1
    rw [identity]
    exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (radial s coefficientLe lastInside lower upper lowerUnit upperUnit)
        (radial s coefficientLe firstInside lower upper lowerUnit upperUnit)) (by decide)).trans_eq (by ring1))
  let left := fun parameter => values (Scale.scale parameter last)
  let right := fun parameter => values (Scale.scale parameter first)
  have bound := DyadicBilinearBoundaryRibbon.dyadicDifference_bound left right
    (fun parameter unit => by
      have firstScalar := points sample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _) parameter unit
      have secondScalar := points otherSample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _) parameter unit
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
      exact ⟨firstScalar, secondScalar⟩)
    (fun lower upper lowerUnit upperUnit => by
      have firstScalar := radial sample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _) firstInside lower upper
        lowerUnit upperUnit
      have secondScalar := radial otherSample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _) firstInside lower
        upper lowerUnit upperUnit
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
      exact ⟨firstScalar, secondScalar⟩)
    (fun lower upper lowerUnit upperUnit => by
      have firstScalar := drift sample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _) lower upper lowerUnit
        upperUnit
      have secondScalar := drift otherSample (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _) lower upper
        lowerUnit upperUnit
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
      exact ⟨firstScalar, secondScalar⟩)
    depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have zero : left 0 = ⟨0, 0⟩ ∧ right 0 = ⟨0, 0⟩ := by
    dsimp only [-eq_self, -iff_self, left, right, values]
    rw [scale_zero,
      scale_zero, sample.primitive_zero,
      otherSample.primitive_zero]
    exact ⟨rfl, rfl⟩
  have one : left 1 = values last ∧ right 1 = values first := by
    dsimp only [-eq_self, -iff_self, left, right]; rw
      [scale_one,
      scale_one]; exact ⟨rfl, rfl⟩
  have endpoint : DyadicBilinearBoundaryRibbon.dyadicDifference left right depth 0 1 =
      Riemann.RootContinuation.RootRadialGeometry.Bilinear.radialArea values depth last -
        Riemann.RootContinuation.RootRadialGeometry.Bilinear.radialArea values depth first -
        Stokes.edgeArea (values first) (values last) := by
    rw [DyadicBilinearBoundaryRibbon.dyadicDifference, zero.1, zero.2, one.1, one.2]
    dsimp only [-eq_self, -iff_self, Stokes.edgeArea, PrimitivePoint.sub]
    dsimp only [-eq_self, -iff_self, Riemann.RootContinuation.RootRadialGeometry.Bilinear.radialArea, left, right]
    ring1
  rw [endpoint] at bound
  exact bound.trans_eq (by rw [show ((1 : InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide]; dsimp only [-eq_self,
    -iff_self, coefficient]; ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds
