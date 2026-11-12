module

public import Purelib.Polynomial.Laurent.Circle.Deformation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.System.IO

/-!
# Laurent deformations through collisions and changing support

The same positive margin covers every original rational parameter. Actual
constructor clients retain finite Horner payments, mesh data and original
phase readings. The support-change family keeps its original negative-power
guard even at the parameter where its coefficient vanishes.
-/

namespace TestPurelib.Polynomial.Laurent.Circle.Deformation

open Purelib
open Polynomial.Laurent
open Polynomial.Laurent.Circle.Deformation
open RationalFunctions.Curve.Canonical.Circle
open Data
open Data.Rat
open Data.Rat.Fraction.Order
open Data.Rat.Fraction (Rational)
open Data.Gaussian.Basic (Canonical)

/-- A quadratic coefficient path collides at the zero root without touching the unit boundary. -/
private def collision : Path :=
  ⟨[⟨⟨[1]⟩, .nonnegative 2⟩, ⟨⟨[⟨-1 / 4, 0⟩, 0]⟩, .nonnegative 0⟩]⟩

/-- A negative-power coefficient vanishes at the initial parameter, changing the actual minimal pole order. -/
public def support : Path :=
  ⟨[⟨⟨[1]⟩, .nonnegative 0⟩, ⟨⟨[⟨1 / 2, 0⟩, 0]⟩, .negative 0⟩]⟩

/-- A leading coefficient vanishes at the initial parameter, changing the actual polynomial degree. -/
public def degree : Path :=
  ⟨[⟨⟨[1]⟩, .nonnegative 0⟩, ⟨⟨[⟨1 / 2, 0⟩, 0]⟩, .nonnegative 1⟩]⟩

/-- The original quadratic path specializes to the displayed exact Gaussian polynomial value. -/
private theorem collision_value (parameter : Rational) (point : Canonical) :
    (collision.symbol parameter).eval point = point ^ 2 - Gaussian.Cast.Path.ofCoordinate (parameter / 4) := by
  change (0 * Gaussian.Cast.Path.ofCoordinate parameter + 1) * point ^ 2 +
    (((0 * Gaussian.Cast.Path.ofCoordinate parameter + (⟨-1 / 4, 0⟩ : Canonical)) *
      Gaussian.Cast.Path.ofCoordinate parameter + 0) * point ^ 0 + 0) = _
  rewrite [pow_zero]
  have scalar : (⟨-1 / 4, 0⟩ : Canonical) * Gaussian.Cast.Path.ofCoordinate parameter =
      -Gaussian.Cast.Path.ofCoordinate (parameter / 4) := by
    apply Gaussian.Basic.ext
    · change (-1 / 4) * parameter - 0 * 0 = -(parameter / 4)
      rewrite [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.div_eq_mul_inv_direct]
      ring1
    · change (-1 / 4) * 0 + 0 * parameter = -0
      ring1
  simp only [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add,
    Gaussian.Basic.mul_one, Gaussian.Basic.add_zero]
  rewrite [scalar]
  ring1

/-- The original support-changing path retains its actual reciprocal term value. -/
private theorem support_value (parameter : Rational) (point : Canonical) :
    (support.symbol parameter).eval point =
      1 + Gaussian.Cast.Path.ofCoordinate (parameter / 2) * point⁻¹ := by
  change (0 * Gaussian.Cast.Path.ofCoordinate parameter + 1) * point ^ 0 +
    (((0 * Gaussian.Cast.Path.ofCoordinate parameter + (⟨1 / 2, 0⟩ : Canonical)) *
      Gaussian.Cast.Path.ofCoordinate parameter + 0) * (point ^ 1)⁻¹ + 0) = _
  rewrite [pow_zero, pow_one]
  have scalar : (⟨1 / 2, 0⟩ : Canonical) * Gaussian.Cast.Path.ofCoordinate parameter =
      Gaussian.Cast.Path.ofCoordinate (parameter / 2) := by
    apply Gaussian.Basic.ext
    · change (1 / 2) * parameter - 0 * 0 = parameter / 2
      rewrite [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.div_eq_mul_inv_direct]
      ring1
    · change (1 / 2) * 0 + 0 * parameter = 0
      ring1
  simp only [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add,
    Gaussian.Basic.mul_one, Gaussian.Basic.add_zero]
  rewrite [scalar]
  ring1

/-- The degree-changing path retains its actual original linear value. -/
private theorem degree_value (parameter : Rational) (point : Canonical) :
    (degree.symbol parameter).eval point = 1 + Gaussian.Cast.Path.ofCoordinate (parameter / 2) * point := by
  change (0 * Gaussian.Cast.Path.ofCoordinate parameter + 1) * point ^ 0 +
    (((0 * Gaussian.Cast.Path.ofCoordinate parameter + (⟨1 / 2, 0⟩ : Canonical)) *
      Gaussian.Cast.Path.ofCoordinate parameter + 0) * point ^ 1 + 0) = _
  rewrite [pow_zero, pow_one]
  have scalar : (⟨1 / 2, 0⟩ : Canonical) * Gaussian.Cast.Path.ofCoordinate parameter =
      Gaussian.Cast.Path.ofCoordinate (parameter / 2) := by
    apply Gaussian.Basic.ext
    · change (1 / 2) * parameter - 0 * 0 = parameter / 2
      rewrite [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.div_eq_mul_inv_direct]
      ring1
    · change (1 / 2) * 0 + 0 * parameter = 0
      ring1
  simp only [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add,
    Gaussian.Basic.mul_one, Gaussian.Basic.add_zero]
  rewrite [scalar]
  ring1

/-- Half a unit-cell real parameter has quadrance at most one quarter. -/
private theorem half_norm {parameter : Rational} (inside : Path.Parameter parameter) :
    Gaussian.Norm.Basic.normSq (Gaussian.Cast.Path.ofCoordinate (parameter / 2)) ≤ 1 / 4 := by
  change (parameter / 2) ^ 2 + 0 ^ 2 ≤ _
  rewrite [show (parameter / 2) ^ 2 + 0 ^ 2 = (parameter / 2) ^ 2 by ring1]
  exact (Arithmetic.pow_le_pow_direct (Field.div_nonneg_direct inside.1 (by decide))
    (Field.divide_mono inside.2 (by decide : (0 : Rational) < 2)) 2).trans_eq (by decide)

/-- A unit Gaussian perturbed by at most one quarter of its quadrance retains that quarter margin. -/
private theorem quarter_margin (base value : Canonical) (unit : Gaussian.Norm.Basic.normSq base = 1)
    (close : Gaussian.Norm.Basic.normSq (base - value) ≤ 1 / 4) :
    (1 : Rational) / 4 ≤ Gaussian.Norm.Basic.normSq value := by
  have lower := Gaussian.Norm.Bounds.quarter_normSq_le_of_close base value
    (unit.symm ▸ close)
  rewrite [unit] at lower
  exact lower

/-- One explicit whole-boundary payment covers the full root-collision path. -/
private def collisionMargin : Uniform collision :=
  { bound := 1 / 4, positive := by decide
    lower := by
      intro parameter inside point unit
      rewrite [collision_value]
      apply quarter_margin (point ^ 2) _
      · rewrite [Gaussian.Power.normSq_pow, Gaussian.Norm.Basic.normSq_eq_canonical point, unit]
        decide
      · rewrite [show point ^ 2 - (point ^ 2 - Gaussian.Cast.Path.ofCoordinate (parameter / 4)) =
          Gaussian.Cast.Path.ofCoordinate (parameter / 4) by ring1]
        change (parameter / 4) ^ 2 + 0 ^ 2 ≤ (1 : Rational) / 4
        rewrite [show (parameter / 4) ^ 2 + 0 ^ 2 = (parameter / 4) ^ 2 by ring1]
        exact (Arithmetic.pow_le_pow_direct (Field.div_nonneg_direct inside.1 (by decide))
          (Field.divide_mono inside.2 (by decide : (0 : Rational) < 4)) 2).trans (by decide) }

/-- The same quarter margin covers a changing minimal pole order and preserved raw guards. -/
public def supportMargin : Uniform support :=
  { bound := 1 / 4, positive := by decide
    lower := by
      intro parameter inside point unit
      rewrite [support_value]
      apply quarter_margin 1 _ Gaussian.Norm.Basic.normSq_one
      rewrite [show (1 : Canonical) - (1 + Gaussian.Cast.Path.ofCoordinate (parameter / 2) * point⁻¹) =
        -(Gaussian.Cast.Path.ofCoordinate (parameter / 2) * point⁻¹) by ring1,
        Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_mul,
        Gaussian.Field.inv_eq point,
        Gaussian.Field.normSq_inv point (Circle.Substitutions.unit_ne_zero unit),
        Gaussian.Norm.Basic.normSq_eq_canonical point, unit]
      change Gaussian.Norm.Basic.normSq (Gaussian.Cast.Path.ofCoordinate (parameter / 2)) * 1 ≤ _
      rewrite [Rat.Fraction.Field.mul_one_direct]
      exact half_norm inside }

/-- The same quarter margin covers the changing normalized degree. -/
public def degreeMargin : Uniform degree :=
  { bound := 1 / 4, positive := by decide
    lower := by
      intro parameter inside point unit
      rewrite [degree_value]
      apply quarter_margin 1 _ Gaussian.Norm.Basic.normSq_one
      rewrite [show (1 : Canonical) - (1 + Gaussian.Cast.Path.ofCoordinate (parameter / 2) * point) =
        -(Gaussian.Cast.Path.ofCoordinate (parameter / 2) * point) by ring1,
        Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_mul,
        Gaussian.Norm.Basic.normSq_eq_canonical point, unit, Rat.Fraction.Field.mul_one_direct]
      exact half_norm inside }

/-- The collision family has invariant actual automatically constructed index at every original rational parameter. -/
private theorem collision_index {parameter : Rational} (inside : Path.Parameter parameter) :
    let first := Evaluation.prepare collisionMargin 0 ⟨by decide, by decide⟩
    let last := Evaluation.prepare collisionMargin parameter inside
    (last.normalized.poleOrder : Int) - (last.result.polynomial.inventory.insideCount : Int) =
      (first.normalized.poleOrder : Int) - (first.result.polynomial.inventory.insideCount : Int) :=
  Evaluation.index_eq (prepare collisionMargin) _ _

/-- A vanishing original negative-power coefficient retains the input's nonzero guard. -/
private theorem initial_support_guard : ¬(support.symbol 0).DefinedAt 0 := by
  intro defined
  exact defined ⟨0, .negative 0⟩ (by decide +kernel) (by decide) rfl

/-- Check cached mesh payments and the actual original independent readings at representative rational parameters. -/
private def checkReadings (path : Path) (uniform : Uniform path) (expected : Int) : IO Unit := do
  let schedule := prepare uniform
  unless schedule.intervals > 0 && schedule.side > 0 && schedule.side < schedule.width &&
      schedule.path.shift == path.shape.rawShift &&
      schedule.path.coefficient * schedule.side ^ 2 < uniform.bound / 16 do
    throw (IO.userError "deformation lost its actual finite Horner or sufficient mesh payment")
  for parameter in ([0, 1 / 2, 1] : List Rational) do
    let polynomial := (path.symbol parameter).polynomialize schedule.path.shift
    let paths := Boundary.Substitutions.prepare polynomial
    unless Polynomial.Winding.Circle.raw paths == 4 * (expected + (schedule.path.shift : Int)) do
      throw (IO.userError "deformation changed the independently computed original common-numerator winding")

/-- Check two actual automatic original parameter evaluations and their changing support data. -/
private def checkEndpoints (path : Path) (uniform : Uniform path)
    (initialPole finalPole initialDegree finalDegree : Nat) : IO Unit := do
  let comparison := Comparison.prepare uniform
  let first := comparison.initial
  let last := comparison.terminal
  let middle := comparison.evaluate (1 / 2) ⟨by decide, by decide⟩
  unless first.normalized.poleOrder == initialPole && last.normalized.poleOrder == finalPole &&
      first.normalized.polynomial.natDegree == initialDegree && last.normalized.polynomial.natDegree == finalDegree &&
      first.result.reading.winding == last.result.reading.winding &&
      middle.normalized.poleOrder == finalPole && middle.normalized.polynomial.natDegree == finalDegree &&
      middle.result.reading.winding == first.result.reading.winding && middle.margin.bound == uniform.bound &&
      (first.normalized.poleOrder : Int) - (first.result.polynomial.inventory.insideCount : Int) ==
        (last.normalized.poleOrder : Int) - (last.result.polynomial.inventory.insideCount : Int) do
    throw (IO.userError "actual deformation endpoints lost minimal support, complete inventory or independent winding")

/-- Run a collision, a changing minimal pole order and a changing normalized degree. -/
public def run : IO Unit := do
  match (collision.symbol 0).prepare, (collision.symbol 1).prepare with
  | .normalized first, .normalized last =>
      unless first.zeroMultiplicity == 2 && last.zeroMultiplicity == 0 &&
          first.polynomial.natDegree == 2 && last.polynomial.natDegree == 2 do
        throw (IO.userError "collision lost its actual repeated-zero versus split-zero coefficient data")
  | _, _ => throw (IO.userError "a uniformly clear collision path returned a zero-symbol obstruction")
  checkReadings collision collisionMargin 2
  checkReadings support supportMargin 0
  checkReadings degree degreeMargin 0
  checkEndpoints support supportMargin 0 1 0 1
  checkEndpoints degree degreeMargin 0 0 0 1

end TestPurelib.Polynomial.Laurent.Circle.Deformation
