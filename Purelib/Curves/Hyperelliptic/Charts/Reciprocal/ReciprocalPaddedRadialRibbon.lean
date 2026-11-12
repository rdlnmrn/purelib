module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedArcArea
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Uniform radial connector bounds between retained cap roots

The open ribbon retains the endpoint edge joining the two root readings.
Its bound is independent of both polynomial stage and radial subdivision
depth. No orientation assumption is needed on a cell or parent join.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale normSq_scale)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicDifference dyadicArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk (Data)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {data : Data cap} {differential :
    Differential genus} {index : Nat} {box :
    Geometry.Rational.Box}

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse

/-- Scaling an original Gaussian point by zero gives zero. -/
private theorem scale_zero (point : Gaussian) : scale 0 point = 0 := by
  apply Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im, Basic.zero_re, Basic.zero_im] <;> ring1

/-- Scaling an original Gaussian point by one preserves that point. -/
private theorem scale_one (point : Gaussian) : scale 1 point = point := by
  apply Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im] <;> ring1

/-- A common rational scale transports the difference of the two original Gaussian endpoints. -/
private theorem scale_difference (first last : Gaussian) (parameter :
  Coordinate) :
    scale parameter last - scale parameter first = scale parameter (last - first) := by
  apply Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im, Basic.sub_re, Basic.sub_im] <;> ring1

/-- The difference of two radial points is the original Gaussian point scaled by the parameter difference. -/
private theorem radial_difference (point : Gaussian) (first last :
  Coordinate) :
    scale last point - scale first point = scale (last - first) point := by
  apply Basic.ext <;> simp only [Scale.scale_re, Scale.scale_im, Basic.sub_re, Basic.sub_im] <;> ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

/-- Every unit-interval radial contraction of an original root remains squared inside the retained padded disk. -/
theorem radial_square (data :
  Data cap) {point : Gaussian} (inside : data.Contains (point * point))
    {parameter : Coordinate} (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
    data.Contains (scale parameter point * scale parameter point) := by
  have factor : parameter ^ 4 ≤ 1 := (Arithmetic.pow_le_pow_direct unit.1 unit.2 4).trans_eq (by decide)
  have identity : ReciprocalExteriorCollar.radius curve ^ 2 * Norm.Basic.normSq (scale
    parameter point * scale parameter point) =
      parameter ^ 4 * (ReciprocalExteriorCollar.radius curve ^ 2 * Norm.Basic.normSq (point *
        point)) := by
    rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, normSq_scale]
    ring1
  exact identity.trans_le ((Arithmetic.mul_le_mul_of_nonneg_right_direct factor
    (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _)
      (Norm.Basic.normSq_nonneg _))).trans_eq
      (Fraction.Field.one_mul _)) |>.trans inside

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk.Data

section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds

/-- The original primitive endpoint increment satisfies the fixed padded coefficient bound times squared root
separation. -/
private theorem increment (bounds : UniformBounds data) (sample : Primitives.Sample cap
  differential index box)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last : Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) :
    Norm.Basic.normSq (sample.primitive.value.eval last - sample.primitive.value.eval first) ≤
      2 * bounds.coefficientUpper differential * Norm.Basic.normSq (last - first) := by
  have estimate := bounds.chord_increment sample branch firstInside lastInside
    (left := 0) (right := 1) (by decide) (by decide)
  have atZero : RootRadialGeometry.chord first last 0 = first := by
    rw [RootRadialGeometry.chord, show (1 : Coordinate) - 0 = 1 by decide,
      scale_zero,
      scale_one, Basic.add_zero]
  have atOne : RootRadialGeometry.chord first last 1 = last := by
    rw [RootRadialGeometry.chord, show (1 : Coordinate) - 1 = 0 by decide,
      scale_zero,
      scale_one, Basic.zero_add]
  rw [atZero, atOne] at estimate
  exact estimate.trans_eq (by rw [show ((1 : Coordinate) - 0) ^ 2 = 1 by decide]; ring1)

/-- All depths share the same squared connector bound. The final edge term is essential: neither radial path is
individually negligible. -/
theorem radial_connector_bound (bounds : UniformBounds data)
    (sample : Primitives.Sample cap differential index box)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last : Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) (depth : Nat) :
    Norm.Basic.normSq (RootRadialGeometry.radialArea sample.primitive.value.eval depth last -
      RootRadialGeometry.radialArea sample.primitive.value.eval depth first -
      area (sample.primitive.value.eval first) (sample.primitive.value.eval last)) ≤
        512 * bounds.coefficientUpper differential ^ 2 * Norm.Basic.normSq (last - first) := by
  let left := fun parameter => sample.primitive.value.eval (scale parameter last)
  let right := fun parameter => sample.primitive.value.eval (scale parameter first)
  let coefficient := bounds.coefficientUpper differential
  have coefficientNonnegative : 0 ≤ coefficient := bounds.coefficientUpper_nonnegative differential
  have errorNonnegative : 0 ≤ 2 * coefficient * Norm.Basic.normSq (last - first) :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide)
      coefficientNonnegative) (Norm.Basic.normSq_nonneg _)
  have errorLe (parameter : Coordinate) (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
      Norm.Basic.normSq (left parameter - right parameter) ≤ 2 * coefficient *
        Norm.Basic.normSq (last - first) := by
    have estimate := bounds.increment sample branch (data.radial_square firstInside unit) (data.radial_square lastInside
      unit)
    rw [scale_difference, normSq_scale] at estimate
    have factor := Arithmetic.pow_le_pow_direct unit.1 unit.2 2
    rw [one_pow] at factor
    exact estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_right_direct factor (Norm.Basic.normSq_nonneg _))
      (Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)).trans_eq (by ring1))
  have radial {point : Gaussian} (inside : data.Contains (point * point)) (lower upper :
    Coordinate)
      (lowerUnit : 0 ≤ lower ∧ lower ≤ 1) (upperUnit : 0 ≤ upper ∧ upper ≤ 1) :
      Norm.Basic.normSq (sample.primitive.value.eval (scale upper point) -
        sample.primitive.value.eval (scale lower point)) ≤
        (4 * coefficient) * (upper - lower) ^ 2 := by
    have estimate := bounds.increment sample branch (data.radial_square inside lowerUnit) (data.radial_square inside
      upperUnit)
    rw [radial_difference, normSq_scale] at estimate
    have rootScalar := data.root_norm_le inside
    rw [← Norm.Basic.normSq_eq_canonical] at rootScalar
    exact estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct rootScalar
        (Arithmetic.sq_nonneg_direct _))
      (Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)).trans_eq (by ring1))
  have drift (lower upper : Coordinate) (lowerUnit : 0 ≤ lower ∧ lower ≤ 1) (upperUnit : 0 ≤ upper
    ∧ upper ≤ 1) :
      Norm.Basic.normSq ((left upper - right upper) - (left lower - right lower)) ≤ (16 *
        coefficient) * (upper - lower) ^ 2 := by
    rw [show (left upper - right upper) - (left lower - right lower) = (left upper - left lower) - (right upper - right
      lower) by ring1]
    exact (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (radial lastInside lower upper lowerUnit upperUnit) (radial firstInside lower upper lowerUnit
        upperUnit)) (by decide)).trans_eq (by ring1))
  have estimate := DyadicBoundaryRibbon.dyadicDifference_bound left right errorNonnegative errorLe
    (radial firstInside) drift depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have atZero : left 0 = 0 ∧ right 0 = 0 := by
    dsimp only [left, right]
    rw [scale_zero,
      scale_zero, sample.primitive_zero]
    exact ⟨rfl, rfl⟩
  have atOne : left 1 = sample.primitive.value.eval last ∧ right 1 = sample.primitive.value.eval first := by
    dsimp only [left, right]
    rw [scale_one,
      scale_one]
    exact ⟨rfl, rfl⟩
  rw [dyadicDifference, atZero.1, atZero.2, atOne.1, atOne.2, BoundaryRibbon.area_sub_self_right,
    IncrementArea.area_zero_left, Basic.sub_zero] at estimate
  exact estimate.trans_eq (by
    rw [show ((1 : Coordinate) - 0) ^ 2 = 1 by decide];
    dsimp only [coefficient];
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds

end
end
