module

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite rational geometry of CCL comparisons

Every radial or coordinate comparison made after a finite decoder homography
pulls back to a four-coefficient Hermitian form

`a * (x² + y²) + b * x + c * y + d`.

The coefficients and the evaluated point are constructive rationals.  These
identities are the algebraic input for the finite x--y curve classifier used
by the persistent next-bit controller.
-/

namespace Purelib.Geometry.Projective.Hermitian

set_option genInjectivity false in
/-- A generalized rational circle or line in Hermitian normal form. -/
@[ext]
structure HermitianForm where
  /-- Coefficient of the squared Gaussian norm. -/ radial : Fraction.Rational
  /-- Coefficient of the real coordinate. -/ realLinear : Fraction.Rational
  /-- Coefficient of the imaginary coordinate. -/ imagLinear : Fraction.Rational
  /-- Constant term of the Hermitian form. -/ constant : Fraction.Rational
deriving DecidableEq

constructive_injectivity HermitianForm

namespace HermitianForm

/-- Evaluate the Hermitian form at a Gaussian rational.

The radial coefficient multiplies the squared norm, followed by the two linear coordinate terms and the constant. -/
def eval (form : HermitianForm)
  (value : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  form.radial * Data.Gaussian.Norm.Basic.normSq value + form.realLinear * value.re +
    form.imagLinear * value.im + form.constant

/-- Add Hermitian forms coefficientwise. -/
def add (left right :
  HermitianForm) : HermitianForm :=
  ⟨left.radial + right.radial,
    left.realLinear + right.realLinear,
    left.imagLinear + right.imagLinear,
    left.constant + right.constant⟩

/-- Negate every coefficient of a Hermitian form. -/
def neg (form : HermitianForm)
  : HermitianForm :=
  ⟨-form.radial, -form.realLinear, -form.imagLinear, -form.constant⟩

/-- Subtract Hermitian forms coefficientwise. -/
def sub (left right :
  HermitianForm) : HermitianForm := left.add right.neg

/-- Multiply every coefficient of a Hermitian form by a rational scalar. -/
def scale (factor : Fraction.Rational) (form :
  HermitianForm) : HermitianForm :=
  ⟨factor * form.radial, factor * form.realLinear,
    factor * form.imagLinear, factor * form.constant⟩

/-- Evaluation carries addition of forms to addition of their values. -/
@[simp] theorem eval_add (left right :
  HermitianForm) (value : Data.Gaussian.Basic.Canonical) :
    (left.add right).eval value = left.eval value + right.eval value := by
  simp only [eval, add]
  ring1

/-- Evaluation commutes with negation of a form. -/
@[simp] theorem eval_neg (form :
  HermitianForm) (value : Data.Gaussian.Basic.Canonical) :
    form.neg.eval value = -form.eval value := by
  simp only [eval, neg]
  ring1

/-- Evaluation carries subtraction of forms to subtraction of their values. -/
@[simp] theorem eval_sub (left right :
  HermitianForm) (value : Data.Gaussian.Basic.Canonical) :
    (left.sub right).eval value = left.eval value - right.eval value := by
  simp only [sub, eval_add,
    eval_neg]
  ring1

/-- Evaluation commutes with rational scaling of a form. -/
@[simp] theorem eval_scale
    (factor : Fraction.Rational) (form : HermitianForm) (value :
      Data.Gaussian.Basic.Canonical) :
    (form.scale factor).eval value = factor * form.eval value := by
  simp only [eval, scale]
  ring1

end HermitianForm
end Purelib.Geometry.Projective.Hermitian

end

public section

namespace Purelib.Geometry.Projective.Hermitian.HermitianForm

open Purelib.Data

/-- Require all four original Hermitian coefficients to vanish. -/
@[expose] def IsZero (form : HermitianForm) : Prop :=
  form.radial = 0 ∧ form.realLinear = 0 ∧ form.imagLinear = 0 ∧ form.constant = 0

/-- Decide coefficientwise vanishing using the four original rational equality procedures. -/
instance isZeroDecidable (form : HermitianForm) : Decidable form.IsZero := by
  unfold IsZero
  infer_instance

/-- A coefficientwise zero Hermitian form evaluates to zero at every Gaussian rational. -/
theorem eval_of_isZero (form : HermitianForm) (zero : form.IsZero) (value : Gaussian.Basic.Canonical) :
    form.eval value = 0 := by
  unfold eval
  rewrite [zero.1, zero.2.1, zero.2.2.1, zero.2.2.2]
  ring1

end Purelib.Geometry.Projective.Hermitian.HermitianForm
