module
public import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

import Purelib.Approximation.Gaussian.Division.Partial.ZeroObstruction
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

section
@[expose] public section

/-!
# Exact finite division decisions from a candidate gap

The extra invariant supplies a positive rational exclusion zone for nonzero
candidates, without supplying the result of the decision. Requested-precision
smallness then forces zero; the other branch constructs ordinary apartness.
This candidate invariant is intentionally not asserted for arbitrary
approximate readings of an algebraic or operationally zero channel.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial.GapObstruction

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Process.Apart.Possible (PossibleApart)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero (ZeroCandidates)
open Purelib.Data.Gaussian.Basic.Canonical
namespace Gap
end Gap

/-- An exact exclusion rules out any later manually or automatically supplied preparation on this branch, not just this
particular detector. -/
theorem excluded_no_ready {numerator denominator :
  Coherent.CoherentNamed}
    {first last : Approximation.Gaussian.Name.Coherent.Refinement.State denominator} (zero : Zero.ZeroCandidates
        denominator first)
    (path : State.Reachable first last) {output : Coherent.CoherentNamed}
    (ready : Approximation.Gaussian.Division.Partial.Ready numerator denominator last output) : False :=
  ZeroObstruction.ZeroCandidates.no_ready zero path ready

end Purelib.Approximation.Gaussian.Division.Partial.GapObstruction

end
