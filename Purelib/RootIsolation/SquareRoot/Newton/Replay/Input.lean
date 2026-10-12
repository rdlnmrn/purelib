module

import Purelib.Approximation.Gaussian.Grid.Replay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Rounding.Floor
public import Purelib.RootIsolation.Newton.Search.Replay.Input

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Gaussian.Grid.Nearest.Replay
public import Purelib.Data.Gaussian.Inverse.Check
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Grid.Nearest.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.RootIsolation

public section

/-! Exact replay of the finite rounded sample search. Integer rounding
witnesses are checked by inequalities, and inverse witnesses by multiplication.
An exhausted trace certifies only this finite attempt. -/

namespace Purelib.RootIsolation.SquareRoot.Newton.Replay.Input

set_option genInjectivity false in
/-- A checked obstruction to replaying a rounded square-root Newton proposal.

The result retains the failed rounding check, a nonzero inverse proposed for zero, or a failed inverse multiplication
equation. -/
inductive Invalid where
  /-- A retained obstruction from the underlying coordinate-rounding checker. -/ | rounding (failure :
    Newton.Search.Replay.Input.Invalid)
  /-- The input was zero but its proposed inverse was nonzero, with that failure retained. -/ | zeroInverse (candidate :
    Gaussian.Basic.Canonical) (failed : candidate ≠ 0)
  /-- The proposed inverse fails the required multiplication equation for the retained input. -/ | inverse (point
    candidate : Gaussian.Basic.Canonical) (failed : candidate * point ≠ 1)

constructive_injectivity Invalid

/-- Check an integer rounding witness and return the exact rounded coordinate with its defining equation. -/
@[expose] def coordinate (imaginary : Bool) (value grid : Fraction.Rational) (integer : Int) :
    Except SquareRoot.Newton.Replay.Input.Invalid {result : Fraction.Rational // result = Fraction.Cast.fromInt
      (Data.Rat.Rounding.Floor.floor (value / grid + 1 / 2)) * grid} := open Purelib.Algebra.Field in do
  let checked ← (Newton.Search.Replay.Input.checkCoordinate imaginary (value / grid + 1 / 2)
    1 (by decide) integer).mapError SquareRoot.Newton.Replay.Input.Invalid.rounding
  return ⟨checked.val * grid, by
    rw [checked.property]
    simp only [ExplicitField.div_eq_mul_inv, show (1 : Fraction.Rational)⁻¹ = 1 from rfl, mul_one, -eq_self]
    rfl⟩

/-- Check both integer rounding witnesses and retain the resulting Gaussian grid point. -/
@[expose] def checkRounded (grid : Fraction.Rational) (proposal : Gaussian.Basic.Canonical) (witness :
  Grid.Replay.Witness) :
    Except SquareRoot.Newton.Replay.Input.Invalid (Grid.Nearest.Replay.Rounded grid proposal) := do
  let real ← SquareRoot.Newton.Replay.Input.coordinate false proposal.re grid witness.realFloor
  let imaginary ← SquareRoot.Newton.Replay.Input.coordinate true proposal.im grid witness.imaginaryFloor
  return ⟨⟨real.val, imaginary.val⟩, Gaussian.Basic.ext real.property imaginary.property⟩

/-- Check a proposed Gaussian inverse by its zero case or multiplication equation.

Success retains the supplied candidate with equality to the exact inverse; rejection records the equation that failed.
-/
@[expose] def checkInverse (point candidate : Gaussian.Basic.Canonical) : Except SquareRoot.Newton.Replay.Input.Invalid
  (Data.Gaussian.Basic.Canonical.Inverse.Certificate point) :=
  if zero : point = 0 then
    if valid : candidate = 0 then .ok ⟨candidate, by cases zero; exact valid⟩
    else .error (.zeroInverse candidate valid)
  else if product : candidate * point = 1 then
    .ok ⟨candidate, Gaussian.Basic.Canonical.mul_right_cancel_of_nonzero zero
      (product.trans (Gaussian.Basic.Canonical.inv_mul_cancel point zero).symm)⟩
  else .error (.inverse point candidate product)
end Purelib.RootIsolation.SquareRoot.Newton.Replay.Input

end
