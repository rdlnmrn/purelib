module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Scale
public import Purelib.Data.Rat.Alternating

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Data.Gaussian.Power.Alternating

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Negating a Gaussian before taking a natural power scales the original power by the rational alternating sign. -/
theorem negPower_eq_scaledPower (u : Basic.Canonical) : ∀ index,
    (-u) ^ index =
      Scale.scale (Alternating.alternatingSign index) (u ^ index)
  | 0 => by
      apply Basic.ext <;>
        simp only [pow_zero, Alternating.alternatingSign,
          Scale.scale_re,
          Scale.scale_im, Basic.one_re, Basic.one_im] <;> ring1
  | index + 1 => by
      rw [pow_succ, negPower_eq_scaledPower u index, pow_succ,
        Alternating.alternatingSign]
      apply Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.mul_re, Basic.mul_im, Basic.neg_re,
          Basic.neg_im] <;> ring1
end Purelib.Data.Gaussian.Power.Alternating

end
