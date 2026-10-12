module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Certificate.Raw
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Raw Gaussian certificate displays

The companion Python program performs only search and exact integer
arithmetic.  This module is the trust boundary: generated certificates store
displayed integer numerators and positive natural denominators, and the Lean
kernel checks the resulting cross-products before any fact is promoted to a
statement about constructive rationals.

Keeping the unreduced displayed fractions as data is deliberate.  It avoids
asking the elaborator to normalize a large expression in the canonical
rational implementation merely to check an inequality.
-/

public section

namespace Purelib.Data.Gaussian.Certificate.Raw

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Certificate.Raw (RationalData)

set_option genInjectivity false in
/-- Retain two displayed rational fractions as an exact Gaussian pair.

Each coordinate keeps its unreduced numerator and positive denominator. Coordinate
arithmetic constructs new displayed fractions, and soundness relates their
cross-product checks to canonical Gaussian equality. -/
structure GaussianData where
  /-- The retained displayed real rational coordinate. -/ re : RationalData
  /-- The retained displayed imaginary rational coordinate. -/ im : RationalData

constructive_injectivity GaussianData

namespace GaussianData

/-- Normalize the two retained rational displays into their canonical Gaussian pair.

Each coordinate uses its own retained positive denominator. The resulting
canonical pair reads those exact displays without changing the raw data. -/
@[expose] def toGaussian (value : GaussianData) : Canonical :=
  ⟨value.re.toRational, value.im.toRational⟩

/-- Negate both displayed coordinates of the Gaussian pair. -/
@[expose] def neg (value : GaussianData) : GaussianData :=
  ⟨value.re.neg, value.im.neg⟩

/-- Retain the displayed real coordinate and negate its imaginary coordinate. -/
@[expose] def conj (value : GaussianData) : GaussianData :=
  ⟨value.re, value.im.neg⟩

/-- Add displayed Gaussian pairs using coordinatewise rational fraction arithmetic. -/
@[expose] def add (left right : GaussianData) : GaussianData :=
  ⟨left.re.add right.re, left.im.add right.im⟩

/-- Subtract displayed Gaussian pairs using coordinatewise rational fraction arithmetic. -/
@[expose] def sub (left right : GaussianData) : GaussianData :=
  ⟨left.re.sub right.re, left.im.sub right.im⟩

/-- Multiply displayed Gaussian pairs using the exact real and imaginary product
formulas. -/
@[expose] def mul (left right : GaussianData) : GaussianData :=
  ⟨(left.re.mul right.re).sub (left.im.mul right.im),
    (left.re.mul right.im).add (left.im.mul right.re)⟩

/-- Compute the displayed rational sum of the squares of both coordinates. -/
@[expose] def normSq (value : GaussianData) : RationalData :=
  (value.re.mul value.re).add (value.im.mul value.im)

/-- Check equality of both displayed coordinates by their exact rational cross-products. -/
@[expose] def Eq (left right : GaussianData) : Prop :=
  RationalData.Eq left.re right.re ∧ RationalData.Eq left.im right.im

/-- Decide displayed Gaussian equality from the two rational cross-product decisions.

The decision conjoins the real and imaginary coordinate predicates on the exact
retained displays. It uses the same rational decisions and both original pairs
of numerator-denominator fields. -/
instance (left right : GaussianData) : Decidable (GaussianData.Eq left right) :=
  inferInstanceAs (Decidable
    (RationalData.Eq left.re right.re ∧
      RationalData.Eq left.im right.im))

/-- Normalizing displayed negation gives negation of the normalized Gaussian value.

Each displayed coordinate retains its original numerator and positive denominator.
The exact raw rational readback laws transport those same coordinate operations
to the canonical Gaussian pair. -/
theorem neg_toGaussian (value : GaussianData) :
    value.neg.toGaussian = -value.toGaussian := by
  apply Basic.ext
  · change value.re.neg.toRational = -value.re.toRational
    exact RationalData.neg_toRational value.re
  · change value.im.neg.toRational = -value.im.toRational
    exact RationalData.neg_toRational value.im

/-- Normalizing displayed conjugation gives conjugation of the normalized Gaussian value.

Each displayed coordinate retains its original numerator and positive denominator.
The exact raw rational readback laws transport those same coordinate operations
to the canonical Gaussian pair. -/
theorem conj_toGaussian (value : GaussianData) :
    value.conj.toGaussian = Basic.conj value.toGaussian := by
  apply Basic.ext
  · rfl
  · change value.im.neg.toRational = -value.im.toRational
    exact RationalData.neg_toRational value.im

/-- Normalizing displayed addition gives addition of the two normalized Gaussian values.

Each displayed coordinate retains its original numerator and positive denominator.
The exact raw rational readback laws transport those same coordinate operations
to the canonical Gaussian pair. -/
theorem add_toGaussian (left right : GaussianData) :
    (GaussianData.add left right).toGaussian =
      left.toGaussian + right.toGaussian := by
  apply Basic.ext
  · change (left.re.add right.re).toRational = left.re.toRational + right.re.toRational
    exact RationalData.add_toRational left.re right.re
  · change (left.im.add right.im).toRational = left.im.toRational + right.im.toRational
    exact RationalData.add_toRational left.im right.im

/-- Normalizing displayed subtraction gives subtraction of the two normalized Gaussian
values.

Each displayed coordinate retains its original numerator and positive denominator.
The exact raw rational readback laws transport those same coordinate operations
to the canonical Gaussian pair. -/
theorem sub_toGaussian (left right : GaussianData) :
    (GaussianData.sub left right).toGaussian =
      left.toGaussian - right.toGaussian := by
  apply Basic.ext
  · change (left.re.sub right.re).toRational = left.re.toRational - right.re.toRational
    exact RationalData.sub_toRational left.re right.re
  · change (left.im.sub right.im).toRational = left.im.toRational - right.im.toRational
    exact RationalData.sub_toRational left.im right.im

/-- Normalizing displayed multiplication gives multiplication of the two normalized
Gaussian values.

Each displayed coordinate retains its original numerator and positive denominator.
The exact raw rational readback laws transport those same coordinate operations
to the canonical Gaussian pair. -/
theorem mul_toGaussian (left right : GaussianData) :
    (GaussianData.mul left right).toGaussian =
      left.toGaussian * right.toGaussian := by
  apply Basic.ext
  · change ((left.re.mul right.re).sub (left.im.mul right.im)).toRational =
      left.re.toRational * right.re.toRational - left.im.toRational * right.im.toRational
    rewrite [RationalData.sub_toRational, RationalData.mul_toRational,
      RationalData.mul_toRational]
    exact Eq.refl _
  · change ((left.re.mul right.im).add (left.im.mul right.re)).toRational =
      left.re.toRational * right.im.toRational + left.im.toRational * right.re.toRational
    rewrite [RationalData.add_toRational, RationalData.mul_toRational,
      RationalData.mul_toRational]
    exact Eq.refl _

/-- Normalizing the displayed squared norm gives the squared norm of the normalized
Gaussian value.

Each displayed coordinate retains its original numerator and positive denominator.
The exact raw rational readback laws transport those same coordinate operations
to the canonical Gaussian pair. -/
theorem normSq_toRational (value : GaussianData) :
    value.normSq.toRational =
      Norm.Basic.normSq value.toGaussian := by
  change ((value.re.mul value.re).add (value.im.mul value.im)).toRational =
    value.re.toRational ^ 2 + value.im.toRational ^ 2
  rewrite [RationalData.add_toRational, RationalData.mul_toRational,
    RationalData.mul_toRational, pow_two, pow_two]
  exact Eq.refl _

/-- Checked equality of both rational coordinate cross-products implies equality of the
canonical Gaussian values. -/
theorem eq_sound {left right : GaussianData} (checked : GaussianData.Eq left right) :
    left.toGaussian = right.toGaussian := by
  apply Basic.ext
  · exact RationalData.eq_sound checked.1
  · exact RationalData.eq_sound checked.2

end GaussianData

end Purelib.Data.Gaussian.Certificate.Raw

end
