module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRadialRibbon
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Homogeneous radial connector bounds retain the actual joining edge. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisRadialRibbon

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.RootContinuation

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {data : ReciprocalPaddedDisk.Data cap} {bounds :
    ReciprocalPaddedInverse.UniformBounds data} {index : Nat} {box :
    Rational.Box}

/-- Scaling a Gaussian point by zero gives zero. -/
private theorem scale_zero (point : Normalization.InverseRootPolynomial.Gaussian) : Gaussian.Scale.scale 0
  point = 0 := by
  apply Gaussian.Basic.ext <;> simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.zero_re,
    Gaussian.Basic.zero_im] <;> ring1

/-- Scaling a Gaussian point by one preserves the point. -/
private theorem scale_one (point : Normalization.InverseRootPolynomial.Gaussian) : Gaussian.Scale.scale 1
  point = point := by
  apply Gaussian.Basic.ext <;> simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1

/-- A common rational scale preserves the difference of two Gaussian points. -/
private theorem scale_difference (first last : Normalization.InverseRootPolynomial.Gaussian) (parameter :
  Normalization.InverseRootPolynomial.Coordinate) :
    Gaussian.Scale.scale parameter last - Gaussian.Scale.scale parameter first =
      Gaussian.Scale.scale parameter (last - first) := by
  apply Gaussian.Basic.ext <;> simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im] <;> ring1

/-- The difference of two radial points is the original point scaled by the parameter difference. -/
private theorem radial_difference (point : Normalization.InverseRootPolynomial.Gaussian) (first last :
  Normalization.InverseRootPolynomial.Coordinate) :
    Gaussian.Scale.scale last point - Gaussian.Scale.scale first point =
      Gaussian.Scale.scale (last - first) point := by
  apply Gaussian.Basic.ext <;> simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im] <;> ring1

/-- The retained odd-degree basis polynomial combination satisfies the homogeneous squared-increment ceiling on the
original padded root domain. -/
private theorem increment (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last :
      Normalization.InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) :
    Gaussian.Norm.Basic.normSq ((polynomials.value coefficients) last - (polynomials.value coefficients) first)
      ≤
      2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * basis.coefficient) *
        Gaussian.Norm.Basic.normSq (last - first) := by
  have estimate := ReciprocalPaddedBasisArcs.BasisBounds.chord_increment basis
    polynomials coefficients branch firstInside lastInside
    (left := 0) (right := 1) (by decide) (by decide)
  have atZero : RootRadialGeometry.chord first last 0 = first := by
    rw [RootRadialGeometry.chord, show (1 : Normalization.InverseRootPolynomial.Coordinate) - 0 = 1 by
      decide, scale_zero,
      scale_one, Gaussian.Basic.add_zero]
  have atOne : RootRadialGeometry.chord first last 1 = last := by
    rw [RootRadialGeometry.chord, show (1 : Normalization.InverseRootPolynomial.Coordinate) - 1 = 0 by
      decide, scale_zero,
      scale_one, Gaussian.Basic.zero_add]
  rw [atZero, atOne] at estimate
  exact estimate.trans_eq (by
    rw [
      show ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0) ^ 2 = 1 by decide];
    ring1)

/-- All depths share the same squared connector bound. The final edge
term is essential: neither radial path is individually negligible. -/
theorem radial_connector_bound (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {first last :
      Normalization.InverseRootPolynomial.Gaussian}
    (firstInside : data.Contains (first * first)) (lastInside : data.Contains (last * last)) (depth : Nat) :
    Gaussian.Norm.Basic.normSq (RootRadialGeometry.radialArea (polynomials.value coefficients)
      depth last -
      RootRadialGeometry.radialArea (polynomials.value coefficients) depth first -
      Path.BoundaryRibbon.area ((polynomials.value coefficients) first) ((polynomials.value coefficients) last)) ≤
        512 * basis.coefficient^2 * Gaussian.Norm.Basic.normSq (last - first) *
          (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Purelib.Algebra in open
          Purelib.Data.Rat in by
  let left := fun parameter => (polynomials.value coefficients) (Gaussian.Scale.scale parameter last)
  let right := fun parameter => (polynomials.value coefficients) (Gaussian.Scale.scale parameter first)
  let coefficient := (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * basis.coefficient)
  have coefficientNonnegative : 0 ≤ coefficient := Arithmetic.mul_nonneg_direct
    (FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
        Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => normSq_nonneg
        (coefficients row)))) basis.coefficient_nonnegative
  have errorNonnegative : 0 ≤ 2 * coefficient * Gaussian.Norm.Basic.normSq (last - first) :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide)
      coefficientNonnegative) (Gaussian.Norm.Basic.normSq_nonneg _)
  have errorLe (parameter : Normalization.InverseRootPolynomial.Coordinate) (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
      Gaussian.Norm.Basic.normSq (left parameter - right parameter) ≤ 2 * coefficient *
        Gaussian.Norm.Basic.normSq (last - first) := by
    have estimate := increment basis polynomials
      coefficients branch (data.radial_square firstInside unit) (data.radial_square lastInside unit)
    rw [scale_difference, Gaussian.Scale.normSq_scale]
      at estimate
    have factor := Arithmetic.pow_le_pow_direct unit.1 unit.2 2
    rw [one_pow] at factor
    exact estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_right_direct factor (Gaussian.Norm.Basic.normSq_nonneg _))
      (Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)).trans_eq (by ring1))
  have radial {point : Normalization.InverseRootPolynomial.Gaussian} (inside : data.Contains (point * point)) (lower
    upper : Normalization.InverseRootPolynomial.Coordinate)
      (lowerUnit : 0 ≤ lower ∧ lower ≤ 1) (upperUnit : 0 ≤ upper ∧ upper ≤ 1) :
      Gaussian.Norm.Basic.normSq ((polynomials.value coefficients) (Gaussian.Scale.scale upper point) -
        (polynomials.value coefficients) (Gaussian.Scale.scale lower point)) ≤
        (4 * coefficient) * (upper - lower) ^ 2 := by
    have estimate := increment basis polynomials
      coefficients branch (data.radial_square inside lowerUnit) (data.radial_square inside upperUnit)
    rw [radial_difference,
      Gaussian.Scale.normSq_scale] at estimate
    have rootBound := data.root_norm_le inside
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at rootBound
    exact estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct rootBound
        (Arithmetic.sq_nonneg_direct _))
      (Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)).trans_eq (by ring1))
  have drift (lower upper : Normalization.InverseRootPolynomial.Coordinate) (lowerUnit : 0 ≤ lower ∧ lower ≤ 1)
    (upperUnit : 0 ≤ upper ∧ upper ≤ 1) :
      Gaussian.Norm.Basic.normSq ((left upper - right upper) - (left lower - right lower)) ≤ (16 * coefficient)
        * (upper - lower) ^ 2 := by
    rw [show (left upper - right upper) - (left lower - right lower) = (left upper - left lower) - (right upper - right
      lower) by ring1]
    exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (radial lastInside lower upper lowerUnit upperUnit) (radial firstInside lower upper lowerUnit
        upperUnit)) (by decide)).trans_eq (by ring1))
  have estimate := Path.Dyadic.DyadicBoundaryRibbon.dyadicDifference_bound left right errorNonnegative errorLe
    (radial firstInside) drift depth (first := 0) (last := 1) (by decide) (by decide) (by decide)
  have atZero : left 0 = 0 ∧ right 0 = 0 := by
    dsimp only [left, right]
    have valueZero : polynomials.value coefficients 0 = 0 := by
      unfold Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials.value
      exact (FiniteSum.Fin.sumFin_congr (fun row => by
        rw [(polynomials.get row).primitive_zero, Gaussian.Basic.mul_zero])).trans FiniteSum.Fin.sumFin_zero
    rw [scale_zero,
      scale_zero, valueZero]
    exact ⟨rfl, rfl⟩
  have atOne : left 1 = (polynomials.value coefficients) last ∧ right 1 = (polynomials.value coefficients) first := by
    dsimp only [left, right]
    rw [scale_one,
      scale_one]
    exact ⟨rfl, rfl⟩
  rw [Path.Dyadic.DyadicBoundaryRibbon.dyadicDifference, atZero.1, atZero.2, atOne.1, atOne.2,
    Path.BoundaryRibbon.area_sub_self_right,
    Path.IncrementArea.area_zero_left, Gaussian.Basic.sub_zero] at estimate
  exact estimate.trans_eq (by
    rw [
      show ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0) ^ 2 = 1 by decide];
    dsimp only [coefficient];
    ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisRadialRibbon
