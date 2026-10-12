module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Contraction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Sector.Eight.Safe
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Sector.Eight

section
@[expose] public section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

namespace Purelib.Geometry.Rational.Sector.Eight.Cell

/-- A strict axis-aligned unit cell centred at one sector representative. The strict inequalities are essential: a
closed cell corner has residual quadrance exactly `1/2`. -/
def InOpenCell (sector :
  Sector) (value :
  Data.Gaussian.Basic.Canonical) : Prop :=
  -1 / 2 < (value - sector.rep).re ∧
    (value - sector.rep).re < 1 / 2 ∧
    -1 / 2 < (value - sector.rep).im ∧
    (value - sector.rep).im < 1 / 2

/-- Decide strict sector-cell membership using the four rational coordinate comparisons. -/
instance inOpenCellDecidable (sector :
  Sector) (value :
  Data.Gaussian.Basic.Canonical) :
    Decidable (InOpenCell sector value) := by
  unfold InOpenCell
  infer_instance

/-- Strict containment in the displayed unit cell is a direct local contraction certificate; no annulus membership is
involved. -/
theorem safe_of_openCell {sector :
  Sector} {value :
  Data.Gaussian.Basic.Canonical}
    (inside : InOpenCell sector value) : Geometry.Rational.Sector.Eight.Safe sector
        value := by
  rcases inside with ⟨realLower, realUpper, imaginaryLower, imaginaryUpper⟩
  have realSquare := Bounds.Square.square_lt_quarter realLower realUpper
  have imaginarySquare := Bounds.Square.square_lt_quarter imaginaryLower imaginaryUpper
  unfold Geometry.Rational.Sector.Eight.Safe Data.Gaussian.Norm.Basic.normSq
  exact (Fraction.Order.Arithmetic.add_lt_add_direct
    realSquare imaginarySquare).trans_eq (by decide)

/-- Every canonical annulus-sector choice is also a redundant safe choice. This embeds the original bitstream semantics
into the stronger arithmetic layer without changing the original definitions. -/
theorem safe_of_canonical {sector :
  Sector} {value :
  Data.Gaussian.Basic.Canonical}
    (band : Sector.Band value) (holds : sector.Holds value) :
    Geometry.Rational.Sector.Eight.Safe sector value :=
  Sector.contraction band sector holds

end Purelib.Geometry.Rational.Sector.Eight.Cell

end

end
