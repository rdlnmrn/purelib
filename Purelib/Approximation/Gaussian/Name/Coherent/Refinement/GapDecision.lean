module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Rational.Request.Sixth

public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Gap
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (State)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Gap

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Data.Rat

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement.GapDecision

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Process.Apart.Possible (PossibleApart)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero (ZeroCandidates)
open Purelib.Data.Gaussian.Basic.Canonical
namespace Gap
end Gap

set_option genInjectivity false in
/-- A prepared-or-zero decision at the exact retained denominator state.

The alternatives retain either apartness for its based process or evidence that every candidate at that source is
exactly zero. -/
inductive Outcome (denominator :
  Coherent.CoherentNamed) (state : State denominator) : Type
  /-- Retain candidate apartness for the process based at the exact source state. -/ | prepared (evidence :
    Possible.PossibleApart
      (Gaussian.Process.Based.based denominator.name.process state.source))
  /-- Retain exact-zero evidence for every candidate at the exact source state. -/ | excluded (zero :
    Zero.ZeroCandidates denominator state)

constructive_injectivity Outcome

/-- The cached requested inspection and its prepared-or-zero outcome indexed by the same retained state.

The requested squared precision is one sixth of the supplied positive gap. -/
def Report (denominator :
  Coherent.CoherentNamed) (start : State denominator)
    (gap : Fraction.Rational) (positive : 0 < gap) :=
  Sigma fun inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection denominator start (gap / 6)
    (Rational.Request.Sixth.requestTarget_positive positive) =>
    Outcome denominator inspection.retained

/-- Total preparation-or-exclusion from finite gap information. There is no small or exhausted branch, and the initial
gap does not encode a chosen answer. -/
def acquire {denominator :
  Coherent.CoherentNamed} (start : State denominator) (gap :
      Fraction.Rational)
    (positive : 0 < gap) (certificate : Approximation.Gaussian.Name.Coherent.Refinement.Gap denominator start gap) :
    Report denominator start gap positive :=
  let report := SmallOrApart.acquire start gap positive
  ⟨report.inspection, match report.outcome with
    | .inl evidence => .prepared evidence
    | .inr small => .excluded (Approximation.Gaussian.Name.Coherent.Refinement.Gap.zero_of_small
        (Approximation.Gaussian.Name.Coherent.Refinement.Gap.after certificate report.inspection.possible_at_start)
            small)⟩

/-- Return whether the certified gap decision carries the prepared alternative. -/
def Outcome.isPrepared {denominator :
  Coherent.CoherentNamed} {state : State denominator} :
    Outcome denominator state → Bool
  | .prepared _ => true
  | .excluded _ => false
end Purelib.Approximation.Gaussian.Name.Coherent.Refinement.GapDecision

end
