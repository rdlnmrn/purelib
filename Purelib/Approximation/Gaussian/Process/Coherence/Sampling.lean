module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite coherence certificates for progressive CCL processes

`Process` deliberately permits branching refinement strategies: it promises
that every requested branch becomes accurate, but does not by itself say that
two independently refined branches describe one operational value.  This
module adds exactly that missing, finite certificate.

A coherent process assigns a nonnegative rational squared allowance to every
finite state.  The current enclosure radius is no larger than that allowance,
every pair of explicitly possible Gaussian-rational readings is close at the
sum of their allowances, and one ordinary refinement makes the allowance
smaller than any requested positive rational target.  There is no completed
value, infinite carrier, limit, or choice of a value common to all states.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic
namespace Coherent

/-- Once the canonical rational process request is below a coherence certificate's computed request, that finite sample
state has the desired semantic allowance. -/
theorem stateAt_allowance_lt {process :
  Approximation.Gaussian.Process} (coherent : Gaussian.Process.Coherence.Basic.Coherent process)
    (start : process.State) (index : Nat) (target : Fraction.Rational)
    (positive : 0 < target)
    (requestSmall :
      Gaussian.Process.Sampling.refinementTarget index <
        coherent.accuracyRequest target) :
    coherent.allowance
        (Gaussian.Process.Sampling.stateAt process start index) <
      target := by
  cases index with
  | zero =>
      exact coherent.refine_accurate start target positive _ _ requestSmall
  | succ index =>
      exact coherent.refine_accurate
        (Gaussian.Process.Sampling.stateAt process start index)
        target positive _ _ requestSmall
end Coherent

end Purelib.Approximation.Gaussian.Process.Coherence.Basic

end
