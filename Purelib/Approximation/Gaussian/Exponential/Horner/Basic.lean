module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Scale

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite exponential Horner approximation

This is a finite operational exponential on Gaussian rationals in the closed
unit disk.  `sample x n` evaluates exactly one finite Horner program.  The
pairwise theorem compares any two displayed truncations and supplies an
explicit rational squared-error sidecar.  Nothing in this module defines a
completed exponential value or invokes an infinite series or a limit.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Basic

/-- Compute one canonical exponential Horner stage: one plus the input times the retained tail divided by the displayed
natural denominator. -/
def step (x : Canonical) (denominator
  : Nat) (tail : Canonical) : Canonical :=
  Data.Gaussian.Basic.canonical (1 + Scale.scale (1 / (denominator : Fraction.Rational)) (x * tail))

/-- The canonical exponential Horner step equals its defining Gaussian scalar expression. -/
theorem step_eq (x : Canonical)
  (denominator : Nat) (tail : Canonical) :
    step x denominator tail =
      1 + Scale.scale (1 / (denominator : Fraction.Rational)) (x * tail) :=
  Data.Gaussian.Basic.canonical_eq _

/-- A displayed finite Horner program. At depth zero its tail is exactly the rational value one. -/
def horner (x : Canonical) :
  Nat → Nat → Canonical
  | _, 0 => 1
  | denominator, depth + 1 =>
      step x denominator
        (horner x (denominator + 1) depth)

/-- The zero-depth exponential Horner value is one. -/
@[simp] theorem horner_zero (x :
  Canonical) (denominator : Nat) :
    horner x denominator 0 = 1 := rfl

/-- A successor-depth exponential Horner value applies one step to the next-denominator tail. -/
@[simp] theorem horner_succ (x :
  Canonical) (denominator depth : Nat) :
    horner x denominator (depth + 1) =
      step x denominator
        (horner x (denominator + 1) depth) := rfl

/-- Every finite truncation at the displayed rational input zero is exactly one. This is the first analytic
normalization law, proved before introducing any completed exponential value. -/
theorem horner_zero_input :
    ∀ (depth denominator : Nat),
      horner (0 : Canonical) denominator depth = 1
  | 0, _ => rfl
  | depth + 1, denominator => by
      rw [horner_succ,
        step_eq,
        horner_zero_input depth (denominator + 1)]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
          Purelib.Data.Gaussian.Basic.one_re, Purelib.Data.Gaussian.Basic.one_im, Purelib.Data.Gaussian.Scale.scale_re,
          Purelib.Data.Gaussian.Scale.scale_im,
          Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im, Purelib.Data.Gaussian.Basic.zero_re,
            Purelib.Data.Gaussian.Basic.zero_im] <;> ring1

/-- The difference of exponential Horner steps is the denominator-scaled input times the original tail difference. -/
theorem step_sub_step (x : Canonical)
  (denominator : Nat)
    (left right : Canonical) :
    step x denominator left -
      step x denominator right =
      Scale.scale (1 / (denominator : Fraction.Rational)) (x * (left - right)) := by
  rw [step_eq, step_eq]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re, Scale.scale_im, Basic.add_re, Basic.add_im, Basic.sub_re,
      Basic.sub_im, Basic.one_re, Basic.one_im, Basic.mul_re, Basic.mul_im] <;> ring1
end Purelib.Approximation.Gaussian.Exponential.Horner.Basic

end
