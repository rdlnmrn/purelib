module

import Purelib.Data.Rat.Sign.Products
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Box.Variation
import Purelib.Geometry.Rational.Box.Basic
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Nat
meta import Purelib.Elab.ConstructiveInjectivity

public section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian.Box

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

namespace Purelib.Geometry.Projective.Hermitian.Box

set_option genInjectivity false in
/-- A proof-bearing finite certificate that one displayed sample is farther from zero than the form can vary across the
current box. -/
structure Certificate
    (form : Hermitian.HermitianForm) (bounding current : Rational.Box) where
  /-- The current box is contained in the retained bounding box. -/ refines : current.Refines bounding
  /-- The Gaussian rational used to test the form sign. -/ sample : Data.Gaussian.Basic.Canonical
  /-- The retained sample lies in the current box. -/ sampleInside : current.Contains sample
  /-- The squared sample value strictly exceeds the variation bound across the current box. -/ margin :
    Hermitian.Box.variationSqBound form bounding current < form.eval sample ^ 2

constructive_injectivity Certificate

namespace Certificate

/-- Every value in a certified box has the same strict sign as the retained sample.

Equivalently, its form value times the sample form value is strictly positive; the squared variation bound is smaller
than the sample squared value. -/
theorem eval_mul_sample_pos
    {form : Hermitian.HermitianForm} {bounding current : Rational.Box}
    (certificate : Certificate form bounding current)
    {value : Data.Gaussian.Basic.Canonical} (inside : current.Contains value) :
    0 < form.eval value * form.eval certificate.sample := by
  have difference := Hermitian.Box.eval_sub_sq_le form certificate.refines inside
    certificate.sampleInside
  exact Sign.Products.mul_pos_of_sub_sq_lt_sq
    (difference.trans_lt certificate.margin)

/-- A successful margin certificate produces one strict sign over the whole box. -/
inductive StrictSign (form : Hermitian.HermitianForm)
  (current : Rational.Box) where
  /-- The Hermitian form is strictly negative at every point in the current box. -/ | negative (holds : ∀ value,
    current.Contains value → form.eval value < 0)
  /-- The Hermitian form is strictly positive at every point in the current box. -/ | positive (holds : ∀ value,
    current.Contains value → 0 < form.eval value)

/-- Read the uniform strict sign from a successful box margin certificate.

An exact comparison at the retained sample selects the negative or positive result, with a proof applying to every point
in the current box. -/
@[expose] def strictSign
    {form : Hermitian.HermitianForm} {bounding current : Rational.Box}
    (certificate : Certificate form bounding current) :
    StrictSign form current := by
  if sampleNegative : form.eval certificate.sample < 0 then
    exact .negative (by
      intro value inside
      exact Purelib.Data.Rat.Fraction.Order.Arithmetic.negative_of_mul_pos_right_neg
        (certificate.eval_mul_sample_pos inside) sampleNegative)
  else
    have sampleNonzero : form.eval certificate.sample ≠ 0 := by
      intro sampleZero
      have impossible : Hermitian.Box.variationSqBound form bounding current < 0 := by
        have margin := certificate.margin
        rw [sampleZero] at margin
        have zeroSquare : (0 : Fraction.Rational) ^ 2 = 0 := by ring1
        rw [zeroSquare] at margin
        exact margin
      exact (not_lt_of_ge
        (Hermitian.Box.variationSqBound_nonneg form bounding current) impossible).elim
    have sampleNonnegative : 0 ≤ form.eval certificate.sample :=
      le_of_not_gt sampleNegative
    have samplePositive : 0 < form.eval certificate.sample :=
      lt_of_le_of_ne sampleNonnegative (Ne.symm sampleNonzero)
    exact .positive (by
      intro value inside
      exact Purelib.Data.Rat.Fraction.Order.Arithmetic.positive_of_mul_pos_right_pos
        (certificate.eval_mul_sample_pos inside) samplePositive)

end Certificate

/-- Execute the one rational margin comparison. -/
@[expose] def certificate?
    (form : Hermitian.HermitianForm) (bounding current : Rational.Box)
    (refines : current.Refines bounding) (sample : Data.Gaussian.Basic.Canonical)
    (sampleInside : current.Contains sample) :
    Option (Certificate form bounding current) :=
  if margin : Hermitian.Box.variationSqBound form bounding current < form.eval sample ^ 2 then
    some ⟨refines, sample, sampleInside, margin⟩
  else
    none

/-- The certificate constructor succeeds exactly when the strict squared-margin comparison holds. -/
theorem certificate?_isSome_iff
    (form : Hermitian.HermitianForm) (bounding current : Rational.Box)
    (refines : current.Refines bounding) (sample : Data.Gaussian.Basic.Canonical)
    (sampleInside : current.Contains sample) :
    (certificate? form bounding current refines sample sampleInside).isSome =
        true ↔
      Hermitian.Box.variationSqBound form bounding current < form.eval sample ^ 2 := by
  by_cases margin : Hermitian.Box.variationSqBound form bounding current < form.eval sample ^ 2
  · rewrite [certificate?, dif_pos margin]
    exact ⟨fun _ => margin, fun _ => rfl⟩
  · rewrite [certificate?, dif_neg margin]
    exact ⟨fun impossible => Bool.noConfusion impossible, fun impossible => (margin impossible).elim⟩

end Purelib.Geometry.Projective.Hermitian.Box

end
