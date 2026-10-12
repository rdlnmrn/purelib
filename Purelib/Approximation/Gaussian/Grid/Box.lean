module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Sample
public import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Geometry.Rational.Box.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

open Purelib.Geometry

section
@[expose] public section

/-!
# Checked shortcuts for winding-one refinement

Newton iteration supplies candidates, not a convergence assumption.  A
candidate is accepted only after exact finite checks of strict containment,
the requested diagonal bound and winding four.  Eliminant-safe sides supply
the same ambient and boundary clearances as the total extractor.  A bounded
unsuccessful search delegates to the original total track.
-/

namespace Purelib.Approximation.Gaussian.Grid.Box

/-- Keep speculative coordinates on a rational grid fine enough for both the request and the current box. The floor is
only a candidate generator; `checkCenter` certifies the rounded result. Explicit integer construction avoids a unary
cast of a large numerator. -/
def roundedCenter (box : Rational.Box) (epsilon :
  Fraction.Rational) (extraBits : Nat)
    (center : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  let grid := min epsilon (min box.widthX box.widthY) / (64 * 2 ^ extraBits)
  let rounded := fun value : Fraction.Rational =>
    Fraction.Cast.fromInt (Floor.floor (value / grid)) * grid
  ⟨rounded center.re, rounded center.im⟩
end Purelib.Approximation.Gaussian.Grid.Box

end

section
@[expose] public section

/-!
# Checked replay of bounded Newton proposal traces

Saved integer grid coordinates are checked by multiplication and inequalities;
saved Newton updates are checked by multiplication.  Replay does not call the
floor or Newton proposal generators.  The starting proposal is explicit, so
diameter preparation can supply its checked warm-up result while ordinary
refinement supplies the box midpoint.  The existing finite candidate acceptance
check is retained, including its safe-side selection and winding.
All imports are already audited finite dependencies of checked shrinking.
-/

namespace Purelib.Approximation.Gaussian.Grid.Box

/-- Compute the rational grid spacing constrained by the request and both box widths.

The denominator is sixty-four times the displayed binary refinement factor; grid construction itself does not certify a
proposal's acceptance. -/
def grid (box : Rational.Box) (epsilon :
  Fraction.Rational) (extraBits : Nat) : Fraction.Rational :=
  min epsilon (min box.widthX box.widthY) / (64 * 2 ^ extraBits)
end Purelib.Approximation.Gaussian.Grid.Box

end
