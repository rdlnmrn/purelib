module

import Purelib.Polynomial.Laurent.Toeplitz.Deformation
import TestPurelib.Polynomial.Laurent.Circle.Deformation
import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.System.IO

/-!
# Actual recurrence ledgers through collisions and changing support

A double and simple rational root meet in a triple zero. Their original
multiplicity contexts remain linear away from the collision. Changing-pole
and changing-degree paths reuse the original whole-boundary payments.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz.Deformation

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Polynomial.Laurent
open Path (Parameter)
open Circle.Deformation (Uniform)
open Data.Gaussian.Basic (Canonical)
open Data.Rat.Fraction (Rational)
open Data.Rat.Fraction.Order

/-- The fixed quarter-unit coefficient in the collision path. -/
private def quarter : Canonical := ⟨1 / 4, 0⟩

/-- A double and simple root merge at zero, changing the actual squarefree multiplicities. -/
private def collision : Path :=
  ⟨[⟨⟨[1]⟩, .nonnegative 3⟩,
    ⟨⟨[-quarter, 0]⟩, .nonnegative 2⟩,
    ⟨⟨[-(quarter * quarter), 0, 0]⟩, .nonnegative 1⟩,
    ⟨⟨[quarter * quarter * quarter, 0, 0, 0]⟩, .nonnegative 0⟩]⟩

/-- The displayed coefficient path is the original product of its double and simple moving factors. -/
private theorem collision_value (parameter : Rational) (point : Canonical) :
    (collision.symbol parameter).eval point =
      (point - quarter * Cast.Path.ofCoordinate parameter) *
      (point - quarter * Cast.Path.ofCoordinate parameter) *
      (point + quarter * Cast.Path.ofCoordinate parameter) := by
  let scalar := Cast.Path.ofCoordinate parameter
  change (0 * scalar + 1) * point ^ 3 +
    (((0 * scalar + -quarter) * scalar + 0) * point ^ 2 +
      ((((0 * scalar + -(quarter * quarter)) * scalar + 0) * scalar + 0) * point ^ 1 +
        (((((0 * scalar + quarter * quarter * quarter) * scalar + 0) * scalar + 0) * scalar + 0) *
          point ^ 0 + 0))) = _
  rewrite [pow_zero, pow_one]
  ring1

/-- Every original moving root has quadrance at most one quarter throughout the parameter cell. -/
private theorem root_bound {parameter : Rational} (inside : Parameter parameter) :
    Norm.Basic.normSq (quarter * Cast.Path.ofCoordinate parameter) ≤ 1 / 4 := by
  have scalar : quarter * Cast.Path.ofCoordinate parameter =
      Cast.Path.ofCoordinate (parameter / 4) := by
    apply Gaussian.Basic.ext
    · change (1 / 4) * parameter - 0 * 0 = parameter / 4
      rewrite [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.div_eq_mul_inv_direct]
      ring1
    · change (1 / 4) * 0 + 0 * parameter = 0
      ring1
  rewrite [scalar]
  change (parameter / 4) ^ 2 + 0 ^ 2 ≤ (1 : Rational) / 4
  rewrite [show (parameter / 4) ^ 2 + 0 ^ 2 = (parameter / 4) ^ 2 by ring1]
  exact (Arithmetic.pow_le_pow_direct (Field.div_nonneg_direct inside.1 (by decide))
    (Field.divide_mono inside.2 (by decide : (0 : Rational) < 4)) 2).trans (by decide)

/-- A unit point perturbed by this finite quadrance budget retains a quarter-unit lower bound. -/
private theorem quarter_margin (point value : Canonical) (unit : Norm.Basic.normSq point = 1)
    (close : Norm.Basic.normSq (point - value) ≤ 1 / 4) :
    (1 : Rational) / 4 ≤ Norm.Basic.normSq value := by
  have lower := Norm.Bounds.quarter_normSq_le_of_close point value (unit.symm ▸ close)
  rewrite [unit] at lower
  exact lower

/-- One finite lower bound covers the complete collision path, including its triple-root parameter. -/
private def collisionMargin : Uniform collision :=
  { bound := (1 / 4) * (1 / 4) * (1 / 4)
    positive := Arithmetic.mul_pos_direct
      (Arithmetic.mul_pos_direct (by decide) (by decide)) (by decide)
    lower := by
      intro parameter inside point unit
      let center := quarter * Cast.Path.ofCoordinate parameter
      have centerBound := root_bound inside
      have unitNorm : Norm.Basic.normSq point = 1 := (Norm.Basic.normSq_eq_canonical point).trans unit
      have first : (1 : Rational) / 4 ≤ Norm.Basic.normSq (point - center) := by
        apply quarter_margin point _ unitNorm
        rewrite [show point - (point - center) = center by ring1]
        exact centerBound
      have second : (1 : Rational) / 4 ≤ Norm.Basic.normSq (point + center) := by
        apply quarter_margin point _ unitNorm
        rewrite [show point - (point + center) = -center by ring1,
          Norm.Basic.normSq_neg]
        exact centerBound
      have nonnegative := Norm.Basic.normSq_nonneg (point - center)
      have square := Arithmetic.mul_le_mul_direct first first (by decide : (0 : Rational) ≤ 1 / 4)
        nonnegative
      have product := Arithmetic.mul_le_mul_direct square second (by decide : (0 : Rational) ≤ 1 / 4)
        (Arithmetic.mul_nonneg_direct nonnegative nonnegative)
      rewrite [collision_value, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
      exact product }

/-- Inspect actual endpoint and queried ledgers while the original minimal support changes. -/
private def check {path : Path} (uniform : Uniform path) (expected : Int)
    (initialPole finalPole initialDegree finalDegree : Nat) : IO Unit := do
  let comparison := Toeplitz.Deformation.Comparison.prepare uniform
  let first := comparison.initial
  let last := comparison.terminal
  let middle := comparison.evaluate (1 / 2) ⟨by decide, by decide⟩
  unless first.result.index == expected && last.result.index == expected && middle.result.index == expected &&
      first.circle.normalized.poleOrder == initialPole && last.circle.normalized.poleOrder == finalPole &&
      first.circle.normalized.polynomial.natDegree == initialDegree &&
      last.circle.normalized.polynomial.natDegree == finalDegree &&
      middle.circle.normalized.poleOrder == finalPole &&
      middle.circle.normalized.polynomial.natDegree == finalDegree &&
      first.circle.result.reading.winding == -expected && last.circle.result.reading.winding == -expected &&
      middle.circle.result.reading.winding == -expected && middle.circle.margin.bound == uniform.bound do
    throw (IO.userError "actual deformation recurrence ledgers lost their index, support or original margin")

/-- Run actual collision, changing-pole and changing-degree endpoint and interior recurrence ledgers. -/
public def run : IO Unit := do
  check collisionMargin (-3) 0 0 3 3
  check TestPurelib.Polynomial.Laurent.Circle.Deformation.supportMargin 0 0 1 0 1
  check TestPurelib.Polynomial.Laurent.Circle.Deformation.degreeMargin 0 0 0 0 1

end TestPurelib.Polynomial.Laurent.Toeplitz.Deformation
