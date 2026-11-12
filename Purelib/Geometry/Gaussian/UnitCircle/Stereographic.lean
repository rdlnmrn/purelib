module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The real Gaussian denominator `t² + 1` of the stereographic chart. -/
def unitCircleDenominator (parameter : Fraction.Rational) :
  Basic.Canonical :=
  ⟨parameter ^ 2 + 1, 0⟩
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The stereographic denominator has squared norm `(t² + 1)²`. -/
private theorem unitCircleDenominator_normSq (parameter :
  Fraction.Rational) :
    Norm.Basic.normSq (unitCircleDenominator
      parameter) =
      (parameter ^ 2 + 1) ^ 2 := by
  dsimp only [unitCircleDenominator,
    Norm.Basic.normSq]
  ring1
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-! ## An explicit rational unit-circle circuit -/

/-- The Gaussian stereographic numerator `(1 - t²) + 2ti`. -/
def unitCircleDirection (parameter : Fraction.Rational) :
  Basic.Canonical :=
  ⟨1 - parameter ^ 2, 2 * parameter⟩
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The cleared difference of two stereographic numerators has squared norm `4(s-t)²(s²+1)(t²+1)`. -/
private theorem unitCircleCrossDifference_normSq
    (source target : Fraction.Rational) :
    Norm.Basic.normSq (unitCircleDirection source *
      unitCircleDenominator target -
      unitCircleDirection target *
        unitCircleDenominator source) =
      4 * (source - target) ^ 2 *
        ((source ^ 2 + 1) * (target ^ 2 + 1)) := by
  dsimp only [unitCircleDirection,
    unitCircleDenominator, Norm.Basic.normSq,
    Basic.mul_re,
    Basic.mul_im, Basic.sub_re, Basic.sub_im]
  ring1
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The stereographic numerator has squared norm `(t² + 1)²`. -/
private theorem unitCircleDirection_normSq (parameter :
  Fraction.Rational) :
    Norm.Basic.normSq (unitCircleDirection parameter)
      =
      (parameter ^ 2 + 1) ^ 2 := by
  dsimp only [unitCircleDirection, Norm.Basic.normSq]
  ring1
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The rational stereographic scalar denominator `t² + 1` is positive. -/
theorem unitCircleScalar_pos (parameter :
  Fraction.Rational) :
    0 < parameter ^ 2 + 1 := by
  exact lt_of_le_of_lt
    (Arithmetic.sq_nonneg_direct parameter)
    (by
      have shifted := Arithmetic.add_lt_add_left_direct
        (show (0 : Fraction.Rational) < 1 by decide) (parameter ^ 2)
      calc
        parameter ^ 2 = parameter ^ 2 + 0 := by ring1
        _ < parameter ^ 2 + 1 := shifted)
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The Gaussian stereographic denominator never vanishes. -/
private theorem unitCircleDenominator_nonzero (parameter :
  Fraction.Rational) :
    unitCircleDenominator parameter ≠ 0 := by
  intro zero
  have realZero := congrArg Basic.re zero
  change parameter ^ 2 + 1 = 0 at realZero
  have positive := unitCircleScalar_pos parameter
  rw [realZero] at positive
  exact (lt_irrefl 0 positive).elim
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Primary rational stereographic quarter-circle chart, from `1` at parameter zero to `i` at parameter one. -/
def unitQuarterPoint (parameter : Fraction.Rational) :
  Basic.Canonical :=
  unitCircleDirection parameter *
    Field.inv (unitCircleDenominator parameter)
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Clearing the two denominators expresses the chart-point difference as a cross difference. -/
public theorem unitQuarterPoint_cross_difference
    (source target : Fraction.Rational) :
    (unitQuarterPoint source -
      unitQuarterPoint target) *
        (unitCircleDenominator source *
          unitCircleDenominator target) =
      unitCircleDirection source *
        unitCircleDenominator target -
        unitCircleDirection target *
          unitCircleDenominator source := by
  unfold unitQuarterPoint
  rw [_root_.sub_mul]
  congr 1
  · calc
      (unitCircleDirection source *
            Field.inv
              (unitCircleDenominator source)) *
          (unitCircleDenominator source *
            unitCircleDenominator target) =
        unitCircleDirection source *
          (Field.inv
              (unitCircleDenominator source) *
            (unitCircleDenominator source *
              unitCircleDenominator target)) :=
          Basic.mul_assoc _ _ _
      _ = unitCircleDirection source *
          ((Field.inv
              (unitCircleDenominator source) *
            unitCircleDenominator source) *
              unitCircleDenominator target) := by
          rw [Basic.mul_assoc]
      _ =
        unitCircleDirection source *
          (Field.inv
              (unitCircleDenominator source) *
            unitCircleDenominator source) *
              unitCircleDenominator target := by
          exact (Basic.mul_assoc
            (unitCircleDirection source)
            (Field.inv
              (unitCircleDenominator source) *
                unitCircleDenominator source)
            (unitCircleDenominator target)).symm
      _ = unitCircleDirection source *
        unitCircleDenominator target := by
        rw [Field.inv_mul
            (unitCircleDenominator source)
            (unitCircleDenominator_nonzero source),
          Basic.mul_one]
  · calc
      (unitCircleDirection target *
            Field.inv
              (unitCircleDenominator target)) *
          (unitCircleDenominator source *
            unitCircleDenominator target) =
        unitCircleDirection target *
          (Field.inv
              (unitCircleDenominator target) *
            (unitCircleDenominator target *
              unitCircleDenominator source)) := by
          rw [Basic.mul_comm
              (unitCircleDenominator source)
                (unitCircleDenominator target),
            Basic.mul_assoc]
      _ = unitCircleDirection target *
          ((Field.inv
              (unitCircleDenominator target) *
            unitCircleDenominator target) *
              unitCircleDenominator source) := by
          rw [Basic.mul_assoc]
      _ = unitCircleDirection target *
        unitCircleDenominator source := by
        rw [Field.inv_mul
            (unitCircleDenominator target)
            (unitCircleDenominator_nonzero target),
          Basic.one_mul]

end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Coarse rational Lipschitz estimate for the stereographic chart. It is obtained by an exact cross-product identity
and cancellation of the positive displayed denominator product. -/
theorem unitQuarterPoint_distance_le (source target :
  Fraction.Rational) :
    Norm.Basic.normSq (unitQuarterPoint source -
      unitQuarterPoint target) ≤
      4 * (source - target) ^ 2 := by
  let sourceScalar := source ^ 2 + 1
  let targetScalar := target ^ 2 + 1
  let product := sourceScalar * targetScalar
  have productPositive : 0 < product :=
    Arithmetic.mul_pos_direct
      (unitCircleScalar_pos source)
        (unitCircleScalar_pos target)
  have cross := congrArg Norm.Basic.normSq
    (unitQuarterPoint_cross_difference source target)
  have productEquation :
      Norm.Basic.normSq (unitQuarterPoint source -
        unitQuarterPoint target) * product ^ 2 =
        (4 * (source - target) ^ 2) * product := by
    rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul,
      unitCircleDenominator_normSq source,
      unitCircleDenominator_normSq target,
      unitCircleCrossDifference_normSq source target] at cross
    simpa only [sourceScalar, targetScalar, product] using (by
      calc
        Norm.Basic.normSq (unitQuarterPoint source -
          unitQuarterPoint target) *
            product ^ 2 =
          Norm.Basic.normSq (unitQuarterPoint source -
            unitQuarterPoint target) *
            (sourceScalar ^ 2 * targetScalar ^ 2) := by ring1
        _ = 4 * (source - target) ^ 2 * product := cross)
  have canceled :
      Norm.Basic.normSq (unitQuarterPoint source -
        unitQuarterPoint target) * product =
        4 * (source - target) ^ 2 := by
    apply Fraction.mul_left_cancel_of_nonzero
      productPositive.ne'
    calc
      product *
          (Norm.Basic.normSq (unitQuarterPoint source
            - unitQuarterPoint target) *
            product) =
        Norm.Basic.normSq (unitQuarterPoint source -
          unitQuarterPoint target) *
          product ^ 2 := by ring1
      _ = (4 * (source - target) ^ 2) * product := productEquation
      _ = product * (4 * (source - target) ^ 2) := by ring1
  have oneLeProduct : (1 : Fraction.Rational) ≤ product := by
    have sourceOne : (1 : Fraction.Rational) ≤ sourceScalar := by
      dsimp only [sourceScalar]
      exact le_add_of_nonneg_left
        (Arithmetic.sq_nonneg_direct source)
    have targetOne : (1 : Fraction.Rational) ≤ targetScalar := by
      dsimp only [targetScalar]
      exact le_add_of_nonneg_left
        (Arithmetic.sq_nonneg_direct target)
    exact (show (1 : Fraction.Rational) = 1 * 1 by ring1) ▸
      Arithmetic.mul_le_mul_direct sourceOne targetOne
        (by decide) (unitCircleScalar_pos source).le
  calc
    Norm.Basic.normSq (unitQuarterPoint source -
      unitQuarterPoint target) =
        Norm.Basic.normSq (unitQuarterPoint source -
          unitQuarterPoint target) * 1 := by
      ring1
    _ ≤ Norm.Basic.normSq (unitQuarterPoint source -
      unitQuarterPoint target) * product :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct oneLeProduct
        (Norm.Basic.normSq_nonneg _)
    _ = 4 * (source - target) ^ 2 := canceled
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Multiplying a stereographic point by its retained denominator recovers its numerator. -/
public theorem unitQuarterPoint_mul_denominator
    (parameter : Fraction.Rational) :
    unitQuarterPoint parameter *
      unitCircleDenominator parameter =
      unitCircleDirection parameter := by
  unfold unitQuarterPoint
  rw [Basic.mul_assoc,
    Field.inv_mul
      (unitCircleDenominator parameter)
      (unitCircleDenominator_nonzero parameter),
    Basic.mul_one]

end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The stereographic point has imaginary coordinate `2t/(t²+1)`. -/
@[simp] theorem unitQuarterPoint_im (parameter :
  Fraction.Rational) :
    (unitQuarterPoint parameter).im =
      (2 * parameter) * (parameter ^ 2 + 1)⁻¹ := by
  let scalar := parameter ^ 2 + 1
  have scalarNonzero : scalar ≠ 0 := (unitCircleScalar_pos parameter).ne'
  have imaginaryProduct := congrArg Basic.im
    (unitQuarterPoint_mul_denominator parameter)
  simp only [Basic.mul_im] at imaginaryProduct
  change (unitQuarterPoint parameter).re * 0 +
      (unitQuarterPoint parameter).im * (parameter ^ 2 + 1) =
        2 * parameter at imaginaryProduct
  have imaginaryProduct' : (unitQuarterPoint parameter).im * scalar =
      2 * parameter := by
    dsimp only [scalar]
    calc
      (unitQuarterPoint parameter).im * (parameter ^ 2 + 1) =
          (unitQuarterPoint parameter).re * 0 +
            (unitQuarterPoint parameter).im * (parameter ^ 2 + 1) := by ring1
      _ = 2 * parameter := imaginaryProduct
  apply Fraction.Field.mul_right_cancel_of_ne scalarNonzero
  calc
    (unitQuarterPoint parameter).im * scalar =
        2 * parameter := imaginaryProduct'
    _ = ((2 * parameter) * scalar⁻¹) * scalar := by
      rw [Fraction.Field.mul_assoc,
        Fraction.Field.inv_mul_cancel scalar scalarNonzero]
      ring1
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The stereographic point at parameter one is the imaginary unit. -/
theorem unitQuarterPoint_one :
  unitQuarterPoint 1 = ⟨0, 1⟩ := by
  decide
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The stereographic point has real coordinate `(1-t²)/(t²+1)`. -/
@[simp] theorem unitQuarterPoint_re (parameter :
  Fraction.Rational) :
    (unitQuarterPoint parameter).re =
      (1 - parameter ^ 2) * (parameter ^ 2 + 1)⁻¹ := by
  let scalar := parameter ^ 2 + 1
  have scalarNonzero : scalar ≠ 0 := (unitCircleScalar_pos parameter).ne'
  have realProduct := congrArg Basic.re
    (unitQuarterPoint_mul_denominator parameter)
  simp only [Basic.mul_re] at realProduct
  change (unitQuarterPoint parameter).re * (parameter ^ 2 + 1) -
      (unitQuarterPoint parameter).im * 0 = 1 - parameter ^ 2 at realProduct
  have realProduct' : (unitQuarterPoint parameter).re * scalar =
      1 - parameter ^ 2 := by
    dsimp only [scalar]
    calc
      (unitQuarterPoint parameter).re * (parameter ^ 2 + 1) =
          (unitQuarterPoint parameter).re * (parameter ^ 2 + 1) -
            (unitQuarterPoint parameter).im * 0 := by ring1
      _ = 1 - parameter ^ 2 := realProduct
  apply Fraction.Field.mul_right_cancel_of_ne scalarNonzero
  calc
    (unitQuarterPoint parameter).re * scalar =
        1 - parameter ^ 2 := realProduct'
    _ = ((1 - parameter ^ 2) * scalar⁻¹) * scalar := by
      rw [Fraction.Field.mul_assoc,
        Fraction.Field.inv_mul_cancel scalar scalarNonzero]
      ring1
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The fixed diagonal coordinate of the primary stereographic quarter is at least one throughout its displayed
parameter interval. -/
theorem unitQuarterPoint_re_add_im_ge_one
    {parameter : Fraction.Rational} (nonnegative : 0 ≤ parameter)
    (atMostOne : parameter ≤ 1) :
    1 ≤ (unitQuarterPoint parameter).re +
      (unitQuarterPoint parameter).im := by
  let scalar := parameter ^ 2 + 1
  have scalarPositive : 0 < scalar := unitCircleScalar_pos parameter
  have oneMinusNonnegative : 0 ≤ 1 - parameter :=
    Arithmetic.sub_nonneg_direct atMostOne
  have extraNonnegative : 0 ≤ 2 * parameter * (1 - parameter) :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) nonnegative)
      oneMinusNonnegative
  have numeratorBound : scalar ≤
      1 - parameter ^ 2 + 2 * parameter := by
    calc
      scalar = 0 + scalar := by ring1
      _ ≤ 2 * parameter * (1 - parameter) + scalar :=
        Arithmetic.add_le_add_right_direct
          extraNonnegative scalar
      _ = scalar + 2 * parameter * (1 - parameter) := by ring1
      _ = 1 - parameter ^ 2 + 2 * parameter := by
        dsimp only [scalar]
        ring1
  rw [unitQuarterPoint_re,
    unitQuarterPoint_im]
  have combined :
      (1 - parameter ^ 2) * scalar⁻¹ +
          (2 * parameter) * scalar⁻¹ =
        (1 - parameter ^ 2 + 2 * parameter) / scalar := by
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  rw [combined]
  apply (Field.le_div_iff_pos scalarPositive).2
  simpa only [Fraction.Field.one_mul] using numeratorBound
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- Every rational stereographic point has squared norm one. -/
theorem unitQuarterPoint_unit (parameter : Fraction.Rational)
  :
    Norm.Basic.normSq (unitQuarterPoint parameter) = 1
      := by
  unfold unitQuarterPoint
  rw [Norm.Basic.normSq_mul,
    Field.normSq_inv _ (unitCircleDenominator_nonzero
      parameter),
    unitCircleDirection_normSq,
      unitCircleDenominator_normSq]
  exact Fraction.Field.mul_inv_cancel _
    (Arithmetic.pow_pos_direct
      (unitCircleScalar_pos parameter) 2).ne'
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The stereographic point at parameter zero is one. -/
theorem unitQuarterPoint_zero :
  unitQuarterPoint 0 = 1 := by
  decide
end Purelib.Geometry.Gaussian.UnitCircle.Stereographic

end
