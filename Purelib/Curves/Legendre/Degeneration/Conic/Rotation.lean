module

public import Purelib.Curves.Legendre.Degeneration.Conic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Unit rotations of the original product conic

Multiplying the first coordinate by a certified unit and the second by its
conjugate preserves the SAME conic product. Both coordinate norms remain
unchanged; conjugate rotation gives an exact inverse on the whole Point.
No cubic root, parameter transport or homology action is constructed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Point

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

variable {site : Fin 2} {parameter : Canonical}

/-- A unit scalar times its conjugate is exactly one in the original Gaussian multiplication. -/
private theorem unit_product (factor : Canonical) (unit : Norm.Basic.normSq factor = 1) :
    factor * Basic.conj factor = 1 := by
  have product := Basic.Canonical.mul_conj factor
  rewrite [← Norm.Basic.normSq_eq_canonical, unit] at product
  exact product

/-- Rotate the two original conic coordinates by a certified unit and its conjugate.

The original parameter and collision site remain unchanged. The exact
product certificate follows from the supplied unit norm; no square-root
or sheet owner is substituted for either coordinate.
-/
def rotate (point : Point site parameter) (factor : Canonical) (unit : Norm.Basic.normSq factor = 1) :
    Point site parameter :=
  { plus := point.plus * factor
    minus := point.minus * Basic.conj factor
    equation := by
      calc
        _ = (point.plus * point.minus) * (factor * Basic.conj factor) := by ring1
        _ = smoothing site parameter := by
          rewrite [point.equation, unit_product factor unit, Basic.mul_one]
          rfl }

/-- Read the retained first conic coordinate and actual unit factor of the same rotation. -/
theorem rotate_plus (point : Point site parameter) (factor : Canonical) (unit : Norm.Basic.normSq factor = 1) :
    (point.rotate factor unit).plus = point.plus * factor := by unfold rotate; rfl

/-- Read the retained second conic coordinate and the conjugate of that same unit factor. -/
theorem rotate_minus (point : Point site parameter) (factor : Canonical) (unit : Norm.Basic.normSq factor = 1) :
    (point.rotate factor unit).minus = point.minus * Basic.conj factor := by unfold rotate; rfl

/-- Unit rotation preserves the exact squared radius of the original first conic coordinate. -/
theorem rotate_plus_normSq (point : Point site parameter) (factor : Canonical)
    (unit : Norm.Basic.normSq factor = 1) :
    Norm.Basic.normSq (point.rotate factor unit).plus = Norm.Basic.normSq point.plus := by
  rewrite [rotate_plus, Norm.Basic.normSq_mul, unit]
  exact Data.Rat.Fraction.Field.mul_one_direct _

/-- The same rotation preserves the original second coordinate's exact squared radius. -/
theorem rotate_minus_normSq (point : Point site parameter) (factor : Canonical)
    (unit : Norm.Basic.normSq factor = 1) :
    Norm.Basic.normSq (point.rotate factor unit).minus = Norm.Basic.normSq point.minus := by
  rewrite [rotate_minus, Norm.Basic.normSq_mul, Norm.Basic.normSq_conj, unit]
  exact Data.Rat.Fraction.Field.mul_one_direct _

/-- A conjugate rotation undoes the SAME given unit rotation on the complete original conic Point. -/
theorem rotate_conj (point : Point site parameter) (factor : Canonical) (unit : Norm.Basic.normSq factor = 1) :
    (point.rotate factor unit).rotate (Basic.conj factor) ((Norm.Basic.normSq_conj factor).trans unit) = point := by
  apply coordinates_eq
  · rewrite [rotate_plus, rotate_plus, Basic.mul_assoc, unit_product factor unit, Basic.mul_one]
    rfl
  · rewrite [rotate_minus, rotate_minus, Basic.conj_conj]
    have reverse : Basic.conj factor * factor = 1 :=
      (Basic.mul_comm _ _).trans (unit_product factor unit)
    rewrite [Basic.mul_assoc, reverse, Basic.mul_one]
    rfl

/-- Rotation undoes the conjugate rotation on the SAME complete original conic Point. -/
theorem conj_rotate (point : Point site parameter) (factor : Canonical) (unit : Norm.Basic.normSq factor = 1) :
    (point.rotate (Basic.conj factor) ((Norm.Basic.normSq_conj factor).trans unit)).rotate factor unit = point := by
  apply coordinates_eq
  · rewrite [rotate_plus, rotate_plus]
    have reverse : Basic.conj factor * factor = 1 :=
      (Basic.mul_comm _ _).trans (unit_product factor unit)
    rewrite [Basic.mul_assoc, reverse, Basic.mul_one]
    rfl
  · rewrite [rotate_minus, rotate_minus, Basic.conj_conj, Basic.mul_assoc, unit_product factor unit, Basic.mul_one]
    rfl

/-- An exactly trivial phase fixes the entire original Point; no coordinate quotient or root identification is used. -/
theorem rotate_eq_of_one (point : Point site parameter) (factor : Canonical)
    (unit : Norm.Basic.normSq factor = 1) (one : factor = 1) : point.rotate factor unit = point := by
  apply coordinates_eq
  · rewrite [rotate_plus, one, Basic.mul_one]
    rfl
  · rewrite [rotate_minus, one]
    change point.minus * (1 : Canonical) = point.minus
    exact Basic.mul_one _

/-- Reindex the SAME complete conic Point through an exact equality of the original fibre parameters. -/
def castParameter {source target : Canonical} (same : source = target) (point : Point site source) :
    Point site target := by
  cases same
  exact point

/-- Exact fibre-index transport preserves the original first conic coordinate unchanged. -/
theorem castParameter_plus {source target : Canonical} (same : source = target) (point : Point site source) :
    (point.castParameter same).plus = point.plus := by cases same; rfl

/-- The same exact transport preserves the independent original second conic coordinate unchanged. -/
theorem castParameter_minus {source target : Canonical} (same : source = target) (point : Point site source) :
    (point.castParameter same).minus = point.minus := by cases same; rfl

/-- Exact fibre-parameter transport preserves the recovered original cubic base coordinate. -/
theorem castParameter_base {source target : Canonical} (same : source = target) (point : Point site source) :
    (point.castParameter same).base = point.base := by cases same; rfl

/-- Exact fibre-parameter transport preserves the original normalized ordinate. -/
theorem castParameter_ordinate {source target : Canonical} (same : source = target) (point : Point site source) :
    (point.castParameter same).ordinate = point.ordinate := by cases same; rfl

/-- The whole original Point survives exact fibre-index transport heterogeneously; no root Owner is identified. -/
theorem castParameter_heq {source target : Canonical} (same : source = target) (point : Point site source) :
    HEq (point.castParameter same) point := by cases same; rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Point

end
