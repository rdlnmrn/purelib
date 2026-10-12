module
public import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

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

/-- Restricting a coherent process to the refinement future of one explicit base state preserves coherence. The based
state remembers that every later candidate was already possible at the base; the numerical allowance remains the
allowance of its displayed source state. -/
def based {process :
  Approximation.Gaussian.Process} (coherent : Gaussian.Process.Coherence.Basic.Coherent process)
    (base : process.State) :
    Gaussian.Process.Coherence.Basic.Coherent (Gaussian.Process.Based.based process base) where
  allowance state := coherent.allowance state.source
  allowance_nonneg state := coherent.allowance_nonneg state.source
  ball_radius_le state := coherent.ball_radius_le state.source
  possible_close := by
    intro leftState rightState leftValue rightValue leftPossible rightPossible
    exact coherent.possible_close leftPossible rightPossible
  accuracyRequest := coherent.accuracyRequest
  accuracyRequest_pos := coherent.accuracyRequest_pos
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact coherent.refine_accurate state.source target positive request
      requestPositive requestSmall
end Coherent

end Purelib.Approximation.Gaussian.Process.Coherence.Basic

end
