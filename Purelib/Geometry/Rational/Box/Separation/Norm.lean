module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation.Certificate
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Geometry.Rational.Box.Separation

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

/-!
# Squared-distance witnesses of box separation

A retained coordinate-separation certificate supplies a positive gap and
its uniform squared-distance bound for points in the original boxes.
-/

namespace Purelib.Geometry.Rational.Box.Separation.Norm

/-- Separated boxes retain a positive gap bounding every squared point distance.

The original finite coordinate certificate supplies the same gap and its
positivity. Its lower bound concerns every displayed point of those two boxes. -/
public theorem separated_normSq_lower
    {left right : Rational.Box} (separated : left.Separated right) :
    ∃ gap : Fraction.Rational, 0 < gap ∧
      ∀ {u v : Data.Gaussian.Basic.Canonical}, left.Contains u → right.Contains v →
        gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (u - v) := by
  let certificate := Rational.Box.separationCertificate separated
  exact ⟨certificate.gap, certificate.positive, certificate.lower⟩

end Purelib.Geometry.Rational.Box.Separation.Norm
