module
import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Rational.Request.Common
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

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Rational.Request

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

/-- Preparing an explicitly candidate-apart process for whole-ball inversion preserves finite coherence. Each refinement
uses one finite common request; no limiting value or completed family of states is selected. -/
def apartify {process :
  Approximation.Gaussian.Process} (coherent : Gaussian.Process.Coherence.Basic.Coherent process)
    (apart : Possible.PossibleApart process) :
    Gaussian.Process.Coherence.Basic.Coherent (Preparation.apartify apart) where
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
    let apartTarget := apart.lowerSq / 12
    have apartTargetPositive : 0 < apartTarget := apart.twelfth_pos
    let inputTarget :=
      Common.commonTarget request apartTarget
    have inputPositive : 0 < inputTarget :=
      Common.commonTarget_pos requestPositive
        apartTargetPositive
    have inputSmallRequest : inputTarget < request :=
      Common.commonTarget_lt_left requestPositive
        apartTargetPositive
    change coherent.allowance
        (process.refine state.source inputTarget inputPositive) < target
    exact coherent.refine_accurate state.source target positive inputTarget
      inputPositive (inputSmallRequest.trans requestSmall)
end Coherent

end Purelib.Approximation.Gaussian.Process.Coherence.Basic

end
