module

public import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Seed bounds from the original inverse-root residual

The original seed residual controls the seed quadrance from a positive
radicand floor. Neither the seed owner, its root sample nor its signed
continuation relation is replaced by a box or coordinate label.
-/

public section

namespace Purelib.Riemann.Normalization.OwnerSeededInverseRoot.Seed

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- The original seed residual bounds radicand quadrance times squared seed quadrance by three.

The actual retained residual is at most one sixty-fourth. The Gaussian
quadrance inequality applied to one minus that same residual bounds the
product without a seed-owner radius or an additional sampled root.
-/
theorem normSq_square_mul_le_three {parameter : Canonical} (seed : Seed parameter) :
    Canonical.normSq parameter * Canonical.normSq seed.value ^ 2 ≤ 3 := by
  have product : Canonical.normSq (parameter * seed.value ^ 2) =
      Canonical.normSq parameter * Canonical.normSq seed.value ^ 2 := by
    have power := Power.normSq_pow seed.value 2
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at power
    rewrite [Canonical.normSq_mul, power]
    rfl
  have triangle := Norm.Bounds.normSq_sub_le_two 1 (1 - parameter * seed.value ^ 2)
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
    Norm.Basic.normSq_eq_canonical, Canonical.normSq_one] at triangle
  have identity : 1 - (1 - parameter * seed.value ^ 2) = parameter * seed.value ^ 2 := by ring1
  rewrite [identity] at triangle
  calc
    _ = Canonical.normSq (parameter * seed.value ^ 2) := product.symm
    _ ≤ 2 * (1 + Canonical.normSq (1 - parameter * seed.value ^ 2)) := triangle
    _ ≤ 2 * (1 + 1 / 64) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) seed.residual_small)
        (by decide +kernel : (0 : Rational) ≤ 2)
    _ ≤ 3 := by decide +kernel

/-- A positive radicand quadrance floor bounds squared seed quadrance independently of the seed-owner box.

The floor multiplies the same nonnegative seed square. The original
residual estimate pays the resulting product before division by that
strictly positive scalar.
-/
theorem normSq_square_le {parameter : Canonical} (seed : Seed parameter) {floor : Rational}
    (positive : 0 < floor) (lower : floor ≤ Canonical.normSq parameter) :
    Canonical.normSq seed.value ^ 2 ≤ 3 / floor := by
  apply (Order.Field.le_div_iff_pos positive).mpr
  calc
    _ = floor * Canonical.normSq seed.value ^ 2 := Field.mul_comm _ _
    _ ≤ Canonical.normSq parameter * Canonical.normSq seed.value ^ 2 :=
      Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lower
        (Order.Arithmetic.sq_nonneg_direct _)
    _ ≤ 3 := seed.normSq_square_mul_le_three

/-- A positive radicand floor bounds the quadrance of the actual retained inverse-root seed.

For nonnegative seed quadrance, its square plus one dominates it. The
original residual therefore gives the explicit ceiling one plus three
divided by the same fixed radicand floor.
-/
theorem normSq_le {parameter : Canonical} (seed : Seed parameter) {floor : Rational}
    (positive : 0 < floor) (lower : floor ≤ Canonical.normSq parameter) :
    Canonical.normSq seed.value ≤ 1 + 3 / floor := by
  have quadratic : Canonical.normSq seed.value ≤ Canonical.normSq seed.value ^ 2 + 1 := by
    apply Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 = 0 + 0 := by ring1
      _ ≤ (Canonical.normSq seed.value - 1) ^ 2 + Canonical.normSq seed.value :=
        Order.Arithmetic.add_le_add_direct (Order.Arithmetic.sq_nonneg_direct _)
          (Canonical.normSq_nonneg _)
      _ = (Canonical.normSq seed.value ^ 2 + 1) - Canonical.normSq seed.value := by ring1
  calc
    _ ≤ Canonical.normSq seed.value ^ 2 + 1 := quadratic
    _ ≤ 3 / floor + 1 :=
      Order.Arithmetic.add_le_add_right_direct (seed.normSq_square_le positive lower) 1
    _ = 1 + 3 / floor := Field.add_comm _ _

end Purelib.Riemann.Normalization.OwnerSeededInverseRoot.Seed

end
