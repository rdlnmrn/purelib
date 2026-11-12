module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Quadratic.Split
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Tactic.Ring

/-! # Injectivity of the regular parallel base ellipse

At radial scale two both ellipse axes are nonzero. Equality of base
coordinates therefore preserves the original unit-direction vertex and its
exact conic ordinate. This is a finite coordinate statement; it does not
identify any independently acquired continuation Owners.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)

/-- The scale-two ellipse direction is injective on the original Gaussian coordinate carrier. -/
theorem baseDirection_two_injective {first last : Canonical}
    (equal : baseDirection 2 first = baseDirection 2 last) : first = last := by
  have real := congrArg Canonical.re equal
  have imaginary := congrArg Canonical.im equal
  change longAxis 2 * first.re = longAxis 2 * last.re at real
  change shortAxis 2 * first.im = shortAxis 2 * last.im at imaginary
  apply Basic.ext
  · exact Fraction.mul_left_cancel_of_nonzero
      (by unfold longAxis; decide +kernel : longAxis 2 ≠ 0) real
  · exact Fraction.mul_left_cancel_of_nonzero
      (by unfold shortAxis; decide +kernel : shortAxis 2 ≠ 0) imaginary

/-- Equal regular scale-two base points retain the identical original unit-direction vertex.

The nonzero original half-gap cancels first. The two actual ellipse axes
then recover the same retained real and imaginary unit-direction readings;
no branch or square-root selection is introduced.
-/
theorem point_two_vertex_eq (site : Fin 2) (parameter : Canonical)
    (first last : UnitVertex) (positive : (0 : Fraction.Rational) < 2)
    (regular : parameter ≠ criticalValue site)
    (equal : (point site parameter 2 first positive).base = (point site parameter 2 last positive).base) :
    first = last := by
  have gapNonzero := Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm
  have bases := congrArg (fun value : Canonical => value - center site parameter) equal
  rewrite [point_base, point_base] at bases
  have cancel (value : Canonical) : center site parameter + halfGap site parameter * value -
      center site parameter = halfGap site parameter * value := by ring1
  rewrite [cancel, cancel] at bases
  have direction := Field.eq_of_mul_eq_mul_left gapNonzero bases
  exact UnitVertex.eq_of_value_eq (baseDirection_two_injective direction)

/-- Equal regular parallel base points preserve their exact original normalized ordinates. -/
theorem point_two_ordinate_eq (site : Fin 2) (parameter : Canonical)
    (first last : UnitVertex) (positive : (0 : Fraction.Rational) < 2)
    (regular : parameter ≠ criticalValue site)
    (equal : (point site parameter 2 first positive).base = (point site parameter 2 last positive).base) :
    (point site parameter 2 first positive).ordinate = (point site parameter 2 last positive).ordinate :=
  congrArg (fun vertex : UnitVertex => (point site parameter 2 vertex positive).ordinate)
    (point_two_vertex_eq site parameter first last positive regular equal)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
