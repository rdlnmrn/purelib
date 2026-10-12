module
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace Purelib.Approximation.Gaussian.Coherent.Additive.Multiple

/-! ## Explicit integral combinations -/

/-- Repeated operational addition by an explicitly supplied natural multiplicity. -/
def natMultiple : Nat ->
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed ->
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
  | 0, _ => Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0
  | count + 1, value => Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.add value
      (natMultiple count value)

/-- Integer multiplication represented constructively by a finite number of additions and, for a negative coefficient,
one stateful negation. -/
def intMultiple : Int -> Coherent.CoherentNamed ->
  Coherent.CoherentNamed
  | .ofNat count, value => natMultiple count value
  | .negSucc count, value =>
      CoherentNamed.neg
        (natMultiple (count + 1) value)
end Purelib.Approximation.Gaussian.Coherent.Additive.Multiple

end
