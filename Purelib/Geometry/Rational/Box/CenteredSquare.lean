module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Square.Centered

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

namespace Purelib.Geometry.Rational.Box.CenteredSquare
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- A small source box and a nearby proposed centre fit in the corresponding centred square. The proof checks the two
displayed corners after a finite quadrance estimate. -/
private theorem box_refines_centeredSquare_of_anchor_near
    {source : Rational.Box} {center : Data.Gaussian.Basic.Canonical} {q r : Fraction.Rational}
    (qNonnegative : 0 ≤ q) (rNonnegative : 0 ≤ r)
    (sourceSmall : source.diagonalSq ≤ q ^ 2)
    (centerNear : Data.Gaussian.Norm.Basic.normSq (center - source.anchor) ≤ q ^ 2)
    (twiceQLe : 2 * q ≤ r) :
    source.Refines (Affine.centeredSquare center r rNonnegative) := by
  have fourQSquareLe : 4 * q ^ 2 ≤ r ^ 2 := by
    have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) qNonnegative)
      twiceQLe 2
    calc
      4 * q ^ 2 = (2 * q) ^ 2 := by ring1
      _ ≤ r ^ 2 := powered
  have included : ∀ z : Data.Gaussian.Basic.Canonical, source.Contains z →
      (Affine.centeredSquare center r rNonnegative).Contains z := by
    intro z inside
    have pointNearAnchor := (source.normSq_sub_anchor_le inside).trans sourceSmall
    have reverseCenter : Data.Gaussian.Norm.Basic.normSq (source.anchor - center) ≤ q ^ 2 := by
      calc
        Data.Gaussian.Norm.Basic.normSq (source.anchor - center) = Data.Gaussian.Norm.Basic.normSq
          (center - source.anchor) := by
          simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im]
          ring1
        _ ≤ q ^ 2 := centerNear
    have pointIdentity : z - center =
        (z - source.anchor) + (source.anchor - center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
          Data.Gaussian.Basic.add_im] <;> ring1
    have pointNearCenter : Data.Gaussian.Norm.Basic.normSq (z - center) ≤ r ^ 2 := by
      rw [pointIdentity]
      calc
        Data.Gaussian.Norm.Basic.normSq ((z - source.anchor) + (source.anchor - center)) ≤
            2 * (Data.Gaussian.Norm.Basic.normSq (z - source.anchor) +
              Data.Gaussian.Norm.Basic.normSq (source.anchor - center)) :=
                Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
        _ ≤ 2 * (q ^ 2 + q ^ 2) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add pointNearAnchor reverseCenter) (by decide)
        _ = 4 * q ^ 2 := by ring1
        _ ≤ r ^ 2 := fourQSquareLe
    have bounds := Data.Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le
      rNonnegative pointNearCenter
    change center.re - r ≤ z.re ∧ z.re ≤ center.re + r ∧
      center.im - r ≤ z.im ∧ z.im ≤ center.im + r
    exact
      ⟨by
        calc
          center.re - r = -r + center.re := by ring1
          _ ≤ (z - center).re + center.re :=
            add_le_add bounds.1 (le_refl center.re)
          _ = z.re := by simp only [Data.Gaussian.Basic.sub_re]; ring1,
       by
        calc
          z.re = (z - center).re + center.re := by
            simp only [Data.Gaussian.Basic.sub_re]; ring1
          _ ≤ r + center.re := add_le_add bounds.2.1 (le_refl center.re)
          _ = center.re + r := by ring1,
       by
        calc
          center.im - r = -r + center.im := by ring1
          _ ≤ (z - center).im + center.im :=
            add_le_add bounds.2.2.1 (le_refl center.im)
          _ = z.im := by simp only [Data.Gaussian.Basic.sub_im]; ring1,
       by
        calc
          z.im = (z - center).im + center.im := by
            simp only [Data.Gaussian.Basic.sub_im]; ring1
          _ ≤ r + center.im := add_le_add bounds.2.2.2 (le_refl center.im)
          _ = center.im + r := by ring1⟩
  let upperRight : Data.Gaussian.Basic.Canonical := ⟨source.xUpper, source.yUpper⟩
  have anchorInside := included source.anchor source.contains_anchor
  have upperRightInside := included upperRight
    (show source.Contains upperRight from
      ⟨source.x_valid, le_rfl, source.y_valid, le_rfl⟩)
  exact ⟨anchorInside.1, upperRightInside.2.1,
    anchorInside.2.2.1, upperRightInside.2.2.2⟩
end Purelib.Geometry.Rational.Box.CenteredSquare

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

namespace Purelib.Geometry.Rational.Box.CenteredSquare
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- A radius-`r` square containing a displayed point lies in the radius-`2r` square centred at that point. -/
private theorem centeredSquare_refines_double_at_member
    {center point : Data.Gaussian.Basic.Canonical} {r : Fraction.Rational} (rNonnegative : 0 ≤ r)
    (inside :
      (Affine.centeredSquare center r rNonnegative).Contains point) :
    (Affine.centeredSquare center r rNonnegative).Refines
      (Affine.centeredSquare point (2 * r)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          rNonnegative)) := by
  change point.re - 2 * r ≤ center.re - r ∧
    center.re + r ≤ point.re + 2 * r ∧
    point.im - 2 * r ≤ center.im - r ∧
    center.im + r ≤ point.im + 2 * r
  exact
    ⟨by
      calc
        point.re - 2 * r ≤ center.re + r - 2 * r :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.1 (2 * r)
        _ = center.re - r := by ring1,
     by
      calc
        center.re + r = center.re - r + 2 * r := by ring1
        _ ≤ point.re + 2 * r := add_le_add inside.1 (le_refl (2 * r)),
     by
      calc
        point.im - 2 * r ≤ center.im + r - 2 * r :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2.2.2 (2 * r)
        _ = center.im - r := by ring1,
     by
      calc
        center.im + r = center.im - r + 2 * r := by ring1
        _ ≤ point.im + 2 * r :=
          add_le_add inside.2.2.1 (le_refl (2 * r))⟩
end Purelib.Geometry.Rational.Box.CenteredSquare

end
