module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Grid.Box
public import Purelib.Approximation.Gaussian.Grid.Replay
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
public import Purelib.Data.Rat.Rounding.Floor.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Newton.Search.Replay.Input

set_option genInjectivity false in
/-- Evidence identifying a failed finite rounding or Newton replay condition.

Each case retains the actual scalar or Gaussian inputs and a proof of the violated comparison or update identity. -/
inductive Invalid where
  /-- The retained grid spacing fails strict positivity. -/ | nonpositiveGrid (value : Fraction.Rational) (failed : ¬ 0
    < value)
  /-- The proposed integer grid cell fails its lower endpoint comparison. -/ | lower (imaginary : Bool) (value grid :
    Fraction.Rational) (integer : Int)
      (failed : ¬ Fraction.Cast.fromInt integer * grid ≤ value)
  /-- The proposed integer grid cell fails its strict upper endpoint comparison. -/ | upper (imaginary : Bool) (value
    grid : Fraction.Rational) (integer : Int)
      (failed : ¬ value < Fraction.Cast.fromInt (integer + 1) * grid)
  /-- The proposed Newton update fails the retained multiplication identity. -/ | newton (center next derivative value :
    Gaussian.Basic.Canonical)
      (failed : (center - next) * derivative ≠ value)

constructive_injectivity Invalid

open Purelib.RootIsolation
/-- Check a saved integer cell by its two rational endpoint comparisons.

Success returns the rounded coordinate with equality to floor-based rounding; failure retains the violated bound and
coordinate tag. -/
def checkCoordinate (imaginary : Bool) (value grid : Fraction.Rational)
    (positive : 0 < grid) (integer : Int) :
    Except Newton.Search.Replay.Input.Invalid { rounded : Fraction.Rational //
      rounded = Fraction.Cast.fromInt
        (Data.Rat.Rounding.Floor.floor (value / grid)) * grid } :=
  if lower : Fraction.Cast.fromInt integer * grid ≤ value then
    if upper : value < Fraction.Cast.fromInt (integer + 1) * grid then
      have floorEq := Data.Rat.Rounding.Floor.Bounds.floor_eq_of_bounds integer (value / grid)
        ((Fraction.Order.Field.le_div_iff_pos positive).mpr lower)
        ((Fraction.Order.Field.div_lt_iff_pos positive).mpr upper)
      .ok ⟨Fraction.Cast.fromInt integer * grid, by rw [floorEq]⟩
    else .error (.upper imaginary value grid integer upper)
  else .error (.lower imaginary value grid integer lower)

/-- Check both saved grid coordinates for the displayed Gaussian proposal.

The exact box, tolerance and extra-bit count determine the spacing; success certifies equality to the original rounded
center without executing floor search. -/
def checkRounded (box : Box) (epsilon : Fraction.Rational) (extraBits : Nat)
    (proposal : Gaussian.Basic.Canonical) (witness : Grid.Replay.Witness) :
    Except Newton.Search.Replay.Input.Invalid { center : Gaussian.Basic.Canonical // center = Grid.Box.roundedCenter box
      epsilon extraBits proposal } := do
  let spacing := Grid.Box.grid box epsilon extraBits
  if positive : 0 < spacing then
    let real ← Newton.Search.Replay.Input.checkCoordinate false proposal.re spacing positive witness.realFloor
    let imaginary ← Newton.Search.Replay.Input.checkCoordinate true proposal.im spacing positive witness.imaginaryFloor
    return ⟨⟨real.val, imaginary.val⟩, by
      unfold Grid.Box.roundedCenter
      rw [real.property, imaginary.property]
      rfl⟩
  else .error (.nonpositiveGrid spacing positive)
end Purelib.RootIsolation.Newton.Search.Replay.Input

end

end
