module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

section
@[expose] public section

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Geometry.Projective.Hermitian

/-- The Hermitian form with the given constant value and zero other coefficients. -/
def constantForm (value : Fraction.Rational) : Hermitian.HermitianForm :=
  ⟨0, 0, 0, value⟩

/-- A constant Hermitian form evaluates to its stored constant. -/
@[simp] theorem eval_constantForm (constant : Fraction.Rational) (value :
  Data.Gaussian.Basic.Canonical) :
    (constantForm constant).eval value = constant := by
  simp only [constantForm, HermitianForm.eval]
  ring1

/-- Form evaluating to `N(z) - threshold`. -/
def affineNormComparisonForm (threshold : Fraction.Rational) :
  Hermitian.HermitianForm :=
  (Hermitian.affineNormForm 1 0).sub (constantForm threshold)

/-- The affine norm comparison evaluates to squared norm minus the threshold. -/
@[simp] theorem eval_affineNormComparisonForm
    (threshold : Fraction.Rational) (value : Data.Gaussian.Basic.Canonical) :
    (affineNormComparisonForm threshold).eval value =
      Data.Gaussian.Norm.Basic.normSq value - threshold := by
  rw [affineNormComparisonForm, HermitianForm.eval_sub,
    Hermitian.eval_affineNormForm, eval_constantForm,
    Data.Gaussian.Basic.one_mul,
    Data.Gaussian.Basic.add_zero]

/-- Form evaluating to `2^count * N(z) - threshold`. -/
def scaledNormComparisonForm (count : Nat) (threshold : Fraction.Rational)
  :
    Hermitian.HermitianForm :=
  (Hermitian.affineNormForm 1 0).scale ((2 : Fraction.Rational) ^ count) |>.sub
    (constantForm threshold)

/-- The scaled comparison evaluates to `2^count` times squared norm minus the threshold. -/
@[simp] theorem eval_scaledNormComparisonForm
    (count : Nat) (threshold : Fraction.Rational) (value : Data.Gaussian.Basic.Canonical) :
    (scaledNormComparisonForm count threshold).eval value =
      (2 : Fraction.Rational) ^ count * Data.Gaussian.Norm.Basic.normSq value - threshold := by
  rw [scaledNormComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, Hermitian.eval_affineNormForm, eval_constantForm,
    Data.Gaussian.Basic.one_mul,
    Data.Gaussian.Basic.add_zero]
end Purelib.Geometry.Projective.Hermitian

end
