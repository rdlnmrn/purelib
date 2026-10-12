module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Power.Bounds
public import Purelib.RootIsolation.Power.Unit.Newton
import Purelib.RootIsolation.Power.Unit.Radius
import Purelib.RootIsolation.Power.Unit.Source
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Power.Unit.Box

open Purelib.Data.Gaussian

/-- The fixed-radius Newton square attached to one degree-indexed owner. -/
def unitRobustBox
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) : Box :=
  Box.Square.Centered.Affine.centeredSquare
    (Power.Unit.Newton.unitRobustNewton parameterNonzero parameterUnit degree degreeAtLeastTwo
      index).point
    (Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo)
    (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
end Purelib.RootIsolation.Power.Unit.Box

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

namespace Purelib.RootIsolation.Power.Unit.Box

open Purelib.Data.Gaussian

/-- The robust box is definitionally the separated Newton square after
replacing the certificate's recorded point by its proved formula. -/
theorem unitRobustBox_eq_centeredNewtonSquare
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo index =
      Box.Square.Centered.Affine.centeredSquare
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
          (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).box)
        (Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo)
        (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le := by
  unfold unitRobustBox
  rw [(Power.Unit.Newton.unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index).point_eq]
end Purelib.RootIsolation.Power.Unit.Box

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

namespace Purelib.RootIsolation.Power.Unit.Box

open Purelib.Data.Gaussian

/-- The retained positive robust radius makes the centered Newton square proper. -/
theorem unitRobustBox_proper
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      index).Proper :=
  Box.Square.Centered.centeredSquare_proper _
    (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Box

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

namespace Purelib.RootIsolation.Power.Unit.Box

open Purelib.Data.Gaussian

/-- Every robust Newton square lies directly in the common global square.
This is a finite coordinate calculation; it does not consume the original
owner's boundary clearance. -/
theorem unitRobustBox_refinesAmbient
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      index).Refines
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          degree)) := by
  let center := (Power.Unit.Newton.unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index).point
  let source := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let q := r / 4
  have anchorNorm := Power.Unit.Newton.unitRobustSourceState_anchor_normSq_le parameterNonzero
    parameterUnit degree degreeAtLeastTwo index
  have anchorBounds := Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le
    (show (0 : Fraction.Rational) ≤ 2 by decide)
    (anchorNorm.trans (show (5 / 2 : Fraction.Rational) ≤ 2 ^ 2 by decide))
  have correctionBounds := Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le
    (Fraction.Order.Field.div_nonneg_direct
      (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
      (by decide))
    (Power.Unit.Newton.unitRobustNewton_displacement_le_quarterRadius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)
  have qLe : q ≤ (1 / 4 : Fraction.Rational) :=
    Power.Unit.Newton.unitRobustQuarterRadius_le_quarter parameterUnit degree degreeAtLeastTwo
  have centerRealLower : -(9 / 4 : Fraction.Rational) ≤ center.re := by
    calc
      -(9 / 4 : Fraction.Rational) = -(1 / 4 : Fraction.Rational) + -2 := by decide
      _ ≤ -q + -2 := add_le_add
        (Fraction.Order.Arithmetic.neg_le_neg_direct qLe) (le_refl _)
      _ ≤ (center - source.box.anchor).re + source.box.anchor.re :=
        add_le_add correctionBounds.1 anchorBounds.1
      _ = center.re := by simp only [Gaussian.Basic.sub_re]; ring1
  have centerRealUpper : center.re ≤ (9 / 4 : Fraction.Rational) := by
    calc
      center.re = (center - source.box.anchor).re + source.box.anchor.re := by
        simp only [Gaussian.Basic.sub_re]; ring1
      _ ≤ q + 2 := add_le_add correctionBounds.2.1 anchorBounds.2.1
      _ ≤ (1 / 4 : Fraction.Rational) + 2 := add_le_add qLe (le_refl _)
      _ = 9 / 4 := by decide
  have centerImagLower : -(9 / 4 : Fraction.Rational) ≤ center.im := by
    calc
      -(9 / 4 : Fraction.Rational) = -(1 / 4 : Fraction.Rational) + -2 := by decide
      _ ≤ -q + -2 := add_le_add
        (Fraction.Order.Arithmetic.neg_le_neg_direct qLe) (le_refl _)
      _ ≤ (center - source.box.anchor).im + source.box.anchor.im :=
        add_le_add correctionBounds.2.2.1 anchorBounds.2.2.1
      _ = center.im := by simp only [Gaussian.Basic.sub_im]; ring1
  have centerImagUpper : center.im ≤ (9 / 4 : Fraction.Rational) := by
    calc
      center.im = (center - source.box.anchor).im + source.box.anchor.im := by
        simp only [Gaussian.Basic.sub_im]; ring1
      _ ≤ q + 2 := add_le_add correctionBounds.2.2.2 anchorBounds.2.2.2
      _ ≤ (1 / 4 : Fraction.Rational) + 2 := add_le_add qLe (le_refl _)
      _ = 9 / 4 := by decide
  have radiusLe : r ≤ (1 / 8 : Fraction.Rational) :=
    Power.Unit.Radius.unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo
  have threeLeGlobal : (3 : Fraction.Rational) ≤ (degree.value : Fraction.Rational) + 1 := by
    have degreeTwo : (2 : Fraction.Rational) ≤ (degree.value : Fraction.Rational) :=
      Fraction.Cast.Order.natCast_le_direct degreeAtLeastTwo
    calc
      (3 : Fraction.Rational) = 2 + 1 := by decide
      _ ≤ (degree.value : Fraction.Rational) + 1 :=
        add_le_add degreeTwo (le_refl 1)
  change
    -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) ≤ center.re - r ∧
      center.re + r ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) ∧
      -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) ≤ center.im - r ∧
      center.im + r ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
  constructor
  · calc
      -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) =
          -((degree.value : Fraction.Rational) + 1) := by
        rw [Power.Bounds.denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]
      _ ≤ -(3 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.neg_le_neg_direct threeLeGlobal
      _ ≤ -(9 / 4 : Fraction.Rational) - 1 / 8 := by decide
      _ ≤ center.re - r :=
        Fraction.Order.Arithmetic.sub_le_sub_direct centerRealLower radiusLe
  constructor
  · calc
      center.re + r ≤ (9 / 4 : Fraction.Rational) + 1 / 8 :=
        add_le_add centerRealUpper radiusLe
      _ ≤ 3 := by decide
      _ ≤ (degree.value : Fraction.Rational) + 1 := threeLeGlobal
      _ = Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) := by
        rw [Power.Bounds.denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]
  constructor
  · calc
      -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) =
          -((degree.value : Fraction.Rational) + 1) := by
        rw [Power.Bounds.denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]
      _ ≤ -(3 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.neg_le_neg_direct threeLeGlobal
      _ ≤ -(9 / 4 : Fraction.Rational) - 1 / 8 := by decide
      _ ≤ center.im - r :=
        Fraction.Order.Arithmetic.sub_le_sub_direct centerImagLower radiusLe
  · calc
      center.im + r ≤ (9 / 4 : Fraction.Rational) + 1 / 8 :=
        add_le_add centerImagUpper radiusLe
      _ ≤ 3 := by decide
      _ ≤ (degree.value : Fraction.Rational) + 1 := threeLeGlobal
      _ = Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) := by
        rw [Power.Bounds.denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]
end Purelib.RootIsolation.Power.Unit.Box

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

namespace Purelib.RootIsolation.Power.Unit.Box

open Purelib.Data.Gaussian

/-- The quarter-radius Newton correction is, in particular, within the full
robust radius required by the winding transfer theorem. -/
theorem unitRobustNewton_displacement_le_radius_sq
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Data.Gaussian.Norm.Basic.normSq
        ((Power.Unit.Newton.unitRobustNewton parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).point -
          (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).box.anchor) ≤
      Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo ^ 2 := by
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have quarterLe : r / 4 ≤ r :=
    (Fraction.Order.Field.div_le_iff_pos
      (show (0 : Fraction.Rational) < 4 by
        exact Fraction.Cast.Order.natCast_pos_direct (by decide))).mpr (by
      calc
        r = r * 1 := by ring1
        _ ≤ r * 4 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (by decide) (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree
              degreeAtLeastTwo).le)
  exact (Power.Unit.Newton.unitRobustNewton_displacement_le_quarterRadius_sq parameterNonzero
    parameterUnit degree degreeAtLeastTwo index).trans
      (Fraction.Order.Arithmetic.pow_le_pow_direct
        (Fraction.Order.Field.div_nonneg_direct
          (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
          (by decide)) quarterLe 2)
end Purelib.RootIsolation.Power.Unit.Box

end
