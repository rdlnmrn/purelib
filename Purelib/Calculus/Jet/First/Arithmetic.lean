module
public import Purelib.Calculus.Jet.First.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

section
@[expose] public section

/-!
# Executable first jets and forward differentiation

A `FirstJet` is just two displayed Gaussian rationals: a value and its
first-order coefficient.  It is not a function graph, germ, infinitesimal,
or equivalence class.  The operations below are finite programs implementing
the sum, product, chain, reciprocal, and quotient rules.

`JetExpression` is finite syntax.  Its evaluator computes the value and
first-order coefficient together.  Exponential and logarithm nodes call the
finite sample programs from the preceding calculus modules at the requested
natural depth.
-/

namespace Purelib.Calculus.Jet.First.Basic
namespace FirstJet

section
open Purelib.Data
open Purelib.Calculus.Jet.First
/-- Pair a Gaussian rational value with zero first-order coefficient. -/
def constant (value : Canonical) : Basic.FirstJet :=
  ⟨value, 0⟩

/-- Pair a Gaussian rational value with unit first-order coefficient. -/
def independent (value : Canonical) : Basic.FirstJet :=
  ⟨value, 1⟩

end

section
open Purelib.Calculus.Jet.First
/-- Add the values and first-order coefficients of two jets. -/
def add (left right : Basic.FirstJet) : Basic.FirstJet :=
  ⟨left.value + right.value, left.slope + right.slope⟩

/-- Negate the value and first-order coefficient of a jet. -/
def neg (jet : Basic.FirstJet) : Basic.FirstJet := ⟨-jet.value,
  -jet.slope⟩

/-- Subtract two jets componentwise using addition and negation. -/
def sub (left right : Basic.FirstJet) : Basic.FirstJet :=
  add left (neg right)

/-- Multiply jets using the finite product rule.

The value is the product of the displayed values. The coefficient adds the left coefficient times the right value and
the left value times the right coefficient. -/
def mul (left right : Basic.FirstJet) : Basic.FirstJet :=
  ⟨left.value * right.value,
    left.slope * right.value + left.value * right.slope⟩

/-- Compute the displayed reciprocal value and first-order coefficient.

Gaussian rational inversion is total, so this operation accepts zero values. Interpreting the coefficient as the
reciprocal rule requires a nonzero input value. -/
def reciprocal (jet : Basic.FirstJet) : Basic.FirstJet :=
  ⟨jet.value⁻¹, -(jet.slope * (jet.value⁻¹ * jet.value⁻¹))⟩

/-- Multiply the numerator jet by the displayed reciprocal of the denominator.

The computation is total. Interpreting its coefficient as the quotient rule requires a nonzero denominator value. -/
def div (numerator denominator : Basic.FirstJet) : Basic.FirstJet :=
  mul numerator (reciprocal denominator)

/-- Combine displayed first-order coefficients by the chain rule.

The outer jet is assumed already evaluated at the inner value. The result retains the outer value and multiplies the two
coefficients; it does not evaluate or check that assumption. -/
def compose (outer inner : Basic.FirstJet) : Basic.FirstJet :=
  ⟨outer.value, inner.slope * outer.slope⟩

end

section
open Purelib.Data
open Purelib.Calculus.Jet.First
/-- The constant jet retains the supplied value. -/
@[simp] theorem constant_value (value : Canonical) :
    (constant value).value = value := rfl

/-- The constant jet has zero first-order coefficient. -/
@[simp] theorem constant_slope (value : Canonical) :
    (constant value).slope = 0 := rfl

/-- The independent jet retains the supplied value. -/
@[simp] theorem independent_value (value : Canonical) :
    (independent value).value = value := rfl

/-- The independent jet has unit first-order coefficient. -/
@[simp] theorem independent_slope (value : Canonical) :
    (independent value).slope = 1 := rfl

end

section
open Purelib.Calculus.Jet.First
/-- The coefficient of a sum is the sum of the coefficients. -/
@[simp] theorem add_slope (left right : Basic.FirstJet) :
    (add left right).slope = left.slope + right.slope := rfl

/-- The coefficient of a negated jet is the negated coefficient. -/
@[simp] theorem neg_slope (jet : Basic.FirstJet) :
    (neg jet).slope = -jet.slope := rfl

/-- The product coefficient is the sum of the two first-order product terms. -/
@[simp] theorem mul_slope (left right : Basic.FirstJet) :
    (mul left right).slope =
      left.slope * right.value + left.value * right.slope := rfl

/-- The reciprocal coefficient is the negative input coefficient times the squared inverse value. -/
@[simp] theorem reciprocal_slope (jet : Basic.FirstJet) :
    jet.reciprocal.slope =
      -(jet.slope * (jet.value⁻¹ * jet.value⁻¹)) := rfl

/-- The coefficient of the displayed composition is the product of the two coefficients. -/
@[simp] theorem compose_slope (outer inner : Basic.FirstJet) :
    (compose outer inner).slope = inner.slope * outer.slope := rfl

end

open Purelib.Calculus.Jet.First in
open Purelib.Data in
/-- The reciprocal coefficient cancels against the squared input value.

For a nonzero displayed value, multiplying the reciprocal coefficient by that square gives the negative original
coefficient. -/
theorem reciprocal_slope_mul_square (jet : Basic.FirstJet)
    (nonzero : jet.value ≠ 0) :
    jet.reciprocal.slope * jet.value ^ 2 = -jet.slope := by
  have inverseCancel : jet.value⁻¹ * jet.value = 1 := by
    simpa only [Gaussian.Field.inv_eq] using
      Gaussian.Field.inv_mul jet.value nonzero
  rw [reciprocal_slope, pow_two]
  calc
    -(jet.slope * (jet.value⁻¹ * jet.value⁻¹)) *
          (jet.value * jet.value) =
        -jet.slope *
          ((jet.value⁻¹ * jet.value) *
            (jet.value⁻¹ * jet.value)) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
    _ = -jet.slope := by
      rw [inverseCancel, Gaussian.Basic.one_mul,
        Gaussian.Basic.mul_one]

end FirstJet

end Purelib.Calculus.Jet.First.Basic

end
