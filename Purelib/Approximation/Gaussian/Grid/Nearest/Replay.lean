module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Grid.Replay
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Grid.Nearest.Basic

open Purelib

open Purelib.Approximation.Gaussian.Grid

open Purelib.Data.Rat

section
@[expose] public section

/-! Exact replay of the finite rounded sample search. Integer rounding
witnesses are checked by inequalities, and inverse witnesses by multiplication.
An exhausted trace certifies only this finite attempt. -/

namespace Purelib.Approximation.Gaussian.Grid.Nearest.Replay

open Purelib.Approximation.Gaussian.Grid.Replay (Witness)

/-- A Gaussian rational point with an exact equality to the displayed grid rounding of the original proposal. -/
abbrev Rounded (grid : Fraction.Rational) (proposal :
  Data.Gaussian.Basic.Canonical) :=
  {point : Data.Gaussian.Basic.Canonical // point = Nearest.Basic.rounded grid proposal}
end Purelib.Approximation.Gaussian.Grid.Nearest.Replay

end
