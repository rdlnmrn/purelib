module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Nat.Factorial.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Scale

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Nat

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Basic

/-- One ordinary displayed Taylor monomial `x^degree / degree!`. -/
def taylorTerm (x : Data.Gaussian.Basic.Canonical)
  (degree : Nat) : Data.Gaussian.Basic.Canonical :=
  Scale.scale
    (1 / (Factorial.Basic.factorial degree : Fraction.Rational)) (x ^ degree)

/-- The bounded Taylor polynomial through the displayed degree. -/
def truncatedExp (x :
  Canonical) : Nat → Canonical
  | 0 => 1
  | degree + 1 => truncatedExp x degree +
    taylorTerm x (degree + 1)

/-- The degree-zero finite exponential Taylor polynomial is one. -/
@[simp] theorem truncatedExp_zero (x :
  Data.Gaussian.Basic.Canonical) : truncatedExp x 0 = 1 := rfl

/-- The successor-degree Taylor polynomial adds its final displayed Taylor monomial. -/
@[simp] theorem truncatedExp_succ (x :
  Data.Gaussian.Basic.Canonical) (degree : Nat) :
    truncatedExp x (degree + 1) =
      truncatedExp x degree +
        taylorTerm x (degree + 1) := rfl

/-- The final nested monomial contributed by a Horner program. -/
def hornerTerm (x :
  Canonical) : Nat → Nat → Canonical
  | _, 0 => 1
  | denominator, degree + 1 =>
      Purelib.Data.Gaussian.Scale.scale
        (1 / (denominator : Purelib.Data.Rat.Fraction.Rational))
        (x * hornerTerm x (denominator + 1) degree)

/-- The degree-zero nested Horner monomial is one. -/
@[simp] theorem hornerTerm_zero (x :
  Data.Gaussian.Basic.Canonical) (denominator : Nat) :
    hornerTerm x denominator 0 = 1 := rfl

/-- A successor-degree Horner monomial multiplies the next-denominator monomial by the input and reciprocal denominator.
-/
@[simp] theorem hornerTerm_succ (x :
  Data.Gaussian.Basic.Canonical)
    (denominator degree : Nat) :
    hornerTerm x denominator (degree + 1) =
      Scale.scale
        (1 / (denominator : Fraction.Rational))
        (x * hornerTerm x (denominator + 1) degree) := rfl
end Purelib.Approximation.Gaussian.Exponential.Taylor.Basic

end
