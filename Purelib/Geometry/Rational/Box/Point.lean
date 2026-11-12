module
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Separation.Certificate
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib

open Purelib.Geometry

@[expose] public section

/-!
# Finite rational content of RFAP boxes

Axis-aligned rational boxes have an exact executable area.  Finite covers and
effective nullity are request protocols returning only displayed box lists;
no outer-measure infimum or collection of all covers is formed.
-/

namespace Purelib.Geometry.Rational.Box.Point

/-- Degenerate rational box containing exactly the displayed rational point. -/
def pointBox (point : Data.Gaussian.Basic.Canonical) :
  Rational.Box where
  xLower := point.re
  xUpper := point.re
  yLower := point.im
  yUpper := point.im
  x_valid := le_rfl
  y_valid := le_rfl

/-- The degenerate point box contains its defining point. -/
theorem pointBox_contains (point : Data.Gaussian.Basic.Canonical) :
    (pointBox point).Contains point :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- A point outside the original closed box has a positive coordinate gap from its degenerate point box. -/
theorem separated_of_not_contains (box : Rational.Box) (point : Data.Gaussian.Basic.Canonical)
    (outside : ¬ box.Contains point) : box.Separated (pointBox point) := by
  by_cases leftOf : box.xUpper < point.re
  · exact Or.inl leftOf
  · by_cases rightOf : point.re < box.xLower
    · exact Or.inr (Or.inl rightOf)
    · by_cases below : box.yUpper < point.im
      · exact Or.inr (Or.inr (Or.inl below))
      · by_cases above : point.im < box.yLower
        · exact Or.inr (Or.inr (Or.inr above))
        · exact (outside
            ⟨Data.Rat.Fraction.Order.Arithmetic.le_of_not_gt_direct rightOf,
              Data.Rat.Fraction.Order.Arithmetic.le_of_not_gt_direct leftOf,
              Data.Rat.Fraction.Order.Arithmetic.le_of_not_gt_direct above,
              Data.Rat.Fraction.Order.Arithmetic.le_of_not_gt_direct below⟩).elim

/-- Compute a positive coordinate gap and uniform squared-distance bound from actual point exclusion. -/
def separationCertificateOfNotContains (box : Rational.Box) (point : Data.Gaussian.Basic.Canonical)
    (outside : ¬ box.Contains point) : Rational.Box.SeparationCertificate box (pointBox point) :=
  Rational.Box.separationCertificate (separated_of_not_contains box point outside)

end Purelib.Geometry.Rational.Box.Point

end
