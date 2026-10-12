module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
public import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! Imaginary separation from retained signed and unsigned acquisition evidence. -/

namespace Purelib.Approximation.Gaussian.Process.Imaginary.Separation

open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Approximation.Gaussian.Acquisition.Signed
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Rat
open Purelib.Data.Rat.Bounds

/-- Retain the squared imaginary gap certified by a negative acquisition result.

The original acquired state and threshold determine the separation magnitude.
Its negative coordinate bound supplies the square bound without selecting a new state. -/
@[expose] public def ofNegative {tau : CoherentNamed}
    {state : Acquisition.State tau} {delta : Fraction.Rational}
    (positive : 0 < delta)
    (certificate : Certificate.Negative tau state delta) : Separation tau :=
  { state := state.retained.source
    gap := delta / 4
    positive := Quarter.quarter_pos positive
    squared_lower := fun possible => Square.square_lower_of_negative
      (Quarter.quarter_pos positive) (certificate.upper possible) }

/-- Form imaginary separation from a retained unsigned coordinate gap.

The original state and positive magnitude stay unchanged. Each signed branch
of the supplied gap gives the same lower bound on the squared imaginary coordinate. -/
@[expose] public def ofGap {tau : CoherentNamed}
    (state : Acquisition.State tau) (delta : Fraction.Rational) (positive : 0 < delta)
    (gap : Acquisition.Signed.Gap tau state delta) : Separation tau :=
  { state := state.retained.source
    gap := delta
    positive := positive
    squared_lower := fun possible => (gap possible).elim
      (Square.square_lower_of_negative positive)
      (fun lower => Fraction.Order.Arithmetic.pow_le_pow_direct positive.le lower 2) }

end Purelib.Approximation.Gaussian.Process.Imaginary.Separation
