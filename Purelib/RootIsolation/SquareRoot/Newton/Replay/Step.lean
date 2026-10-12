module
import Purelib.Data.Gaussian.Basic
public import Purelib.RootIsolation.SquareRoot.Newton.Basic

public import Purelib.Data.Gaussian.Inverse.Check
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Grid.Replay
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data

open Purelib.RootIsolation

section
@[expose] public section

/-! Exact replay of the finite rounded sample search. Integer rounding
witnesses are checked by inequalities, and inverse witnesses by multiplication.
An exhausted trace certifies only this finite attempt. -/

namespace Purelib.RootIsolation.SquareRoot.Newton.Replay.Step

/-- Compute one square-root Newton proposal using the supplied checked inverse. -/
def advance (parameter point : Canonical)
  (inverse : Gaussian.Basic.Canonical.Inverse.Certificate point) : Canonical :=
  let sum := point + parameter * inverse.val
  ⟨sum.re / 2, sum.im / 2⟩

/-- A replay step using a checked inverse is exactly the original square-root Newton step. -/
theorem advance_eq (parameter point :
  Canonical) (inverse : Gaussian.Basic.Canonical.Inverse.Certificate point) :
    advance parameter point inverse = SquareRoot.Newton.Basic.step parameter point := by
  rcases inverse with ⟨value, same⟩
  cases same
  rfl
end Purelib.RootIsolation.SquareRoot.Newton.Replay.Step

end
