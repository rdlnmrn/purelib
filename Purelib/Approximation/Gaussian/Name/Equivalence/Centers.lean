module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Equivalence.Centers
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite comparison of centres enclosing equivalent names

Uniform rational enclosures of operationally equivalent finite samplers
bound the separation of their centres.  The proof does not select a common
completed value: any proposed rational violation supplies one positive
comparison request which contradicts that violation.
-/

namespace Purelib.Approximation.Gaussian.Name.Equivalence.Centers

/-- Process-level form: the actual finite witnesses used by the operational sampler inherit the displayed all-candidate
bounds. -/
theorem named_separation_le {left right :
  Gaussian.Name.Basic.Named}
    (equivalent : Gaussian.Equivalence.NamedEquivalent left right)
    (leftCenter rightCenter : Data.Gaussian.Basic.Canonical) (leftAllowance rightAllowance : Fraction.Rational)
    (leftBound : ∀ state candidate, left.process.Possible state candidate →
      Data.Gaussian.Norm.Basic.normSq (candidate - leftCenter) ≤ leftAllowance)
    (rightBound : ∀ state candidate, right.process.Possible state candidate →
      Data.Gaussian.Norm.Basic.normSq (candidate - rightCenter) ≤ rightAllowance) :
    Data.Gaussian.Norm.Basic.normSq (leftCenter - rightCenter) ≤ 2 * (leftAllowance + rightAllowance) :=
  Equivalence.Centers.separation_le equivalent leftCenter rightCenter leftAllowance rightAllowance
    (fun index => leftBound _ _ (Gaussian.Process.Sampling.witnessAt_possible left.process left.state index))
    (fun index => rightBound _ _ (Gaussian.Process.Sampling.witnessAt_possible right.process right.state index))

end Purelib.Approximation.Gaussian.Name.Equivalence.Centers

end
