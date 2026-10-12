module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Computation.Arithmetic.Cost.Basic
public import Purelib.Computation.Arithmetic.Cost.Gaussian

import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-! Gaussian power computations with retained work charges. -/

namespace Purelib.Computation.Arithmetic.Cost.Gaussian.Power

open Purelib.Data.Gaussian
open Purelib.Computation.Arithmetic.Cost.Basic
open Purelib.Computation.Arithmetic.Cost

/-- Compute a natural Gaussian power together with its accumulated arithmetic work.

Starting at one with zero charge, each recursive step retains the previous power and charges its multiplication by the
input. The computed values follow the same recurrence as natural powers. -/
def powerWork (point : Basic.Canonical) : Nat → Work ×
  Basic.Canonical
  | 0 => (0, 1)
  | exponent + 1 =>
      let previous := Purelib.Computation.Arithmetic.Cost.Gaussian.Power.powerWork point exponent
      (previous.1 + Gaussian.gaussianMulWork previous.2 point,
        previous.2 * point)

/-- The value retained by powerWork is the requested natural power. -/
@[simp] theorem powerWork_value (point : Basic.Canonical) : ∀
  exponent,
    (Gaussian.Power.powerWork point exponent).2 = point ^ exponent
  | 0 => rfl
  | exponent + 1 => by
      rw [Gaussian.Power.powerWork, Purelib.Computation.Arithmetic.Cost.Gaussian.Power.powerWork_value, pow_succ]

/-- Charge a candidate power followed by comparison with the supplied input.

The comparison charge is added to core work, while normalization work remains exactly the charge retained by the power
computation. -/
def powerTestWork (input candidate : Basic.Canonical) (degree
  : Nat) : Work :=
  let powered := Gaussian.Power.powerWork candidate degree
  { core := powered.1.core + Gaussian.gaussianEqualityCost powered.2 input
    normalization := powered.1.normalization }
end Purelib.Computation.Arithmetic.Cost.Gaussian.Power

end
