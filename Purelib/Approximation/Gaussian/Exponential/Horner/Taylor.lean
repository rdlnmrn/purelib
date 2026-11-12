module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.NatCast
import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
public import Purelib.Data.Nat.Factorial.Consecutive
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Nat.Factorial.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Finite exponential Horner and Taylor identities

Consecutive-factor products identify the nested Gaussian Horner contributions
with the corresponding finite factorial-scaled monomials and truncations.
-/

public section
namespace Purelib.Approximation.Gaussian.Exponential.Horner.Taylor

open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Nat.Factorial
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Exponential

/-- A Horner contribution is a monomial scaled by consecutive factors.

The retained starting denominator and finite degree determine the entire
product. Coordinate identities compare the same Gaussian power and exact scale. -/
theorem hornerTerm_eq_scaled_power (x : Basic.Canonical) :
    ∀ (degree denominator : Nat),
      Taylor.Basic.hornerTerm x denominator degree =
        Scale.scale
          (1 / (Consecutive.consecutiveProduct denominator degree : Fraction.Rational))
          (x ^ degree)
  | 0, denominator => by
      rw [Taylor.Basic.hornerTerm_zero, Consecutive.consecutiveProduct_zero]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, pow_zero, Basic.one_re, Basic.one_im] <;>
        change _ = (1 / (1 : Fraction.Rational)) * _ <;>
        rw [show (1 / (1 : Fraction.Rational)) = 1 by decide,
          Fraction.Field.one_mul]
  | degree + 1, denominator => by
      rw [Taylor.Basic.hornerTerm_succ,
        Taylor.hornerTerm_eq_scaled_power x degree (denominator + 1),
        Consecutive.consecutiveProduct_succ_head, NatCast.mul, pow_succ]
      have coefficient :
          1 / ((denominator : Fraction.Rational) *
                (Consecutive.consecutiveProduct (denominator + 1) degree : Fraction.Rational)) =
            (1 / (denominator : Fraction.Rational)) *
              (1 / (Consecutive.consecutiveProduct (denominator + 1) degree : Fraction.Rational)) :=
        by rw [Fraction.Field.div_mul_div_direct,
          Fraction.Field.one_mul]
      rw [coefficient]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Starting a Horner monomial at one gives the factorial-scaled Taylor term.

The finite consecutive product starting at one equals the same degree factorial,
so both expressions retain the same exact Gaussian power and reciprocal scale. -/
theorem hornerTerm_one_eq_taylorTerm (x : Basic.Canonical) (degree : Nat) :
    Taylor.Basic.hornerTerm x 1 degree = Taylor.Basic.taylorTerm x degree := by
  rw [hornerTerm_eq_scaled_power, Taylor.Basic.taylorTerm,
    Consecutive.consecutiveProduct_one_eq_factorial]

/-- Increasing Horner depth adds its final displayed monomial.

Structural induction distributes the retained Gaussian multiplication and scale
over the lower-depth value and the next finite contribution. -/
theorem horner_succ_eq_add_hornerTerm (x : Basic.Canonical) :
    ∀ (degree denominator : Nat),
      Basic.horner x denominator (degree + 1) =
        Basic.horner x denominator degree +
          Taylor.Basic.hornerTerm x denominator (degree + 1)
  | 0, denominator => by
      rw [Basic.horner_succ,
        Basic.horner_zero,
        Basic.horner_zero,
        Basic.step_eq, Taylor.Basic.hornerTerm_succ, Taylor.Basic.hornerTerm_zero]
  | degree + 1, denominator => by
      calc
        Basic.horner x denominator (degree + 1 + 1) =
            Basic.step x denominator
              (Basic.horner x (denominator + 1)
                (degree + 1)) := rfl
        _ = Basic.step x denominator
              (Basic.horner x (denominator + 1) degree +
                Taylor.Basic.hornerTerm x (denominator + 1) (degree + 1)) := by
          rw [Taylor.horner_succ_eq_add_hornerTerm x degree
            (denominator + 1)]
        _ = Basic.step x denominator
              (Basic.horner x (denominator + 1) degree) +
            Taylor.Basic.hornerTerm x denominator (degree + 1 + 1) := by
          rw [Basic.step_eq,
            Basic.step_eq]
          change
            1 + Scale.scale
                (1 / (denominator : Fraction.Rational))
                (x * (Basic.horner x
                    (denominator + 1) degree +
                  Taylor.Basic.hornerTerm x (denominator + 1) (degree + 1))) =
              (1 + Scale.scale
                (1 / (denominator : Fraction.Rational))
                (x * Basic.horner x
                  (denominator + 1) degree)) +
                Scale.scale
                  (1 / (denominator : Fraction.Rational))
                  (x * Taylor.Basic.hornerTerm x (denominator + 1) (degree + 1))
          apply Basic.ext <;>
            simp only [Scale.scale_re,
              Scale.scale_im, Basic.add_re, Basic.add_im, Basic.mul_re,
              Basic.mul_im, Basic.one_re, Basic.one_im] <;> ring1
        _ = Basic.horner x denominator (degree + 1) +
            Taylor.Basic.hornerTerm x denominator (degree + 1 + 1) := rfl

/-- The finite Horner program equals the bounded Taylor polynomial.

The successor identity adds the same factorial-scaled monomial to both retained
finite recurrences, starting from their common constant value. -/
theorem horner_one_eq_truncatedExp (x : Basic.Canonical) : ∀ degree : Nat,
    Basic.horner x 1 degree = Taylor.Basic.truncatedExp x degree
  | 0 => rfl
  | degree + 1 => by
      rw [horner_succ_eq_add_hornerTerm,
        Taylor.horner_one_eq_truncatedExp x degree,
        hornerTerm_one_eq_taylorTerm, Taylor.Basic.truncatedExp_succ]

/-- An exponential Horner sample equals its finite Taylor truncation.

The sample uses depth plus one as its retained polynomial degree. The equality
identifies that finite Gaussian value with the same bounded factorial recurrence. -/
theorem sample_eq_truncatedExp (x : Basic.Canonical) (depth : Nat) :
    Sample.sample x depth = Taylor.Basic.truncatedExp x (depth + 1) := by
  change Basic.horner x 1 (depth + 1) = _
  exact horner_one_eq_truncatedExp x (depth + 1)
end Purelib.Approximation.Gaussian.Exponential.Horner.Taylor
end
