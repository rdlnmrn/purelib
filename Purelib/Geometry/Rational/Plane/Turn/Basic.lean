module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Lattice
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Geometry.Rational.Plane.Turn.Basic

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Square-root-free quantitative small turn for two nonzero complex endpoint vectors.

Three times the retained rational absolute cross product is strictly
below the original endpoint dot product. Both comparisons use
the same four rational endpoint coordinates. -/
@[expose] public def NarrowComplexTurn
    (Aₗ Bₗ Aᵣ Bᵣ : Fraction.Rational) : Prop :=
  3 * Fraction.abs (Aₗ * Bᵣ - Bₗ * Aᵣ) < Aₗ * Aᵣ + Bₗ * Bᵣ

/-- The narrow-turn inequality forces the endpoint vectors to have positive dot product.

The retained rational absolute cross product is nonnegative. Its
positive scale and original strict narrow-turn inequality force
the same endpoint dot product to be positive. -/
public theorem complexDot_pos_of_narrowComplexTurn
    {Aₗ Bₗ Aᵣ Bᵣ : Fraction.Rational}
    (narrow : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ) :
    0 < Aₗ * Aᵣ + Bₗ * Bᵣ := by
  have nonnegative : 0 ≤ 3 * Fraction.abs (Aₗ * Bᵣ - Bₗ * Aᵣ) :=
    Arithmetic.mul_nonneg_direct (by decide) (Arithmetic.abs_nonneg_direct _)
  exact nonnegative.trans_lt narrow

end Purelib.Geometry.Rational.Plane.Turn.Basic
