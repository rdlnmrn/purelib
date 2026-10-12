module

import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Newton.Check.Product
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Search.Center.Basic
public import Purelib.RootIsolation.Newton.Search.Iteration
public import Purelib.RootIsolation.Newton.Search.Replay.Input
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Checked replay of bounded Newton proposal traces

Saved integer grid coordinates are checked by multiplication and inequalities;
saved Newton updates are checked by multiplication.  Replay does not call the
floor or Newton proposal generators.  The starting proposal is explicit, so
diameter preparation can supply its checked warm-up result while ordinary
refinement supplies the box midpoint.  The existing finite candidate acceptance
check is retained, including its safe-side selection and winding.
All imports are already audited finite dependencies of checked shrinking.
-/

namespace Purelib.RootIsolation.Newton.Search.Trace

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
  (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
  (initialProposal : Gaussian.Basic.Canonical)

/-- A proof-only history of exactly the rejected, nonstationary proposals
preceding a saved cursor.  Thus `inspected` is not merely a bounded label. -/
inductive Prefix : Nat → Nat → Gaussian.Basic.Canonical → Nat → Prop where
  /-- The original six-proposal search before inspecting any center. -/ | first :
    Purelib.RootIsolation.Newton.Search.Trace.Prefix 6 0 initialProposal 0
  /-- Extend the exact history by one rejected rounded center with nonzero derivative and its original Newton update. -/
    | step {remaining bits proposal inspected}
      (previous : Purelib.RootIsolation.Newton.Search.Trace.Prefix (remaining + 1) bits proposal inspected)
      (center next : Gaussian.Basic.Canonical)
      (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
      (rejected : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = none)
      (nonzero : Gaussian.Basic.value
        (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) ≠ 0)
      (newton : next = Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center)) :
      Purelib.RootIsolation.Newton.Search.Trace.Prefix remaining (bits + 2) next (inspected + 1)

/-- The displayed count belongs to an actual terminal path of the original
bounded search.  The complete history is proof-only and erased at runtime. -/
inductive Execution : Nat → Option (Refinement current epsilon) → Prop where
  /-- The original search accepts the displayed refinement at this exact inspected count. -/ | accepted {remaining bits
    proposal inspected}
      (previous : Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal (remaining + 1) bits
        proposal inspected)
      (center : Gaussian.Basic.Canonical) (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
      (value : Refinement current epsilon)
      (found : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = some value) :
      Purelib.RootIsolation.Newton.Search.Trace.Execution (inspected + 1) (some value)
  /-- The exact retained search history exhausts its remaining proposals. -/ | exhausted {bits proposal inspected}
      (previous : Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal 0 bits proposal
        inspected) :
      Purelib.RootIsolation.Newton.Search.Trace.Execution inspected none
  /-- A rejected original center terminates the search with a displayed zero derivative. -/ | zeroDerivative {remaining
    bits proposal inspected}
      (previous : Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal (remaining + 1) bits
        proposal inspected)
      (center : Gaussian.Basic.Canonical) (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
      (rejected : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = none)
      (zero : Gaussian.Basic.value (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0) :
      Purelib.RootIsolation.Newton.Search.Trace.Execution (inspected + 1) none

set_option genInjectivity false in
/-- A checked prefix of the original six-proposal search from the displayed
seed.  The equation retains first-accepted semantics and every rejection. -/
structure Pending where
  /-- The original number of proposals still available in the saved cursor. -/ remaining : Nat
  /-- The actual number of proposals already inspected. -/ inspected : Nat
  /-- Remaining and inspected proposals sum to the original budget of six. -/ budget : remaining + inspected = 6
  /-- The retained additional rounding precision at the saved cursor. -/ extraBits : Nat
  /-- The exact current Newton proposal awaiting its rounded check. -/ proposal : Gaussian.Basic.Canonical
  /-- The original sequence of rejected nonstationary proposals leading to this saved cursor. -/ history :
    Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal remaining extraBits proposal
    inspected
  /-- The saved continuation equals the original six-proposal search exactly. -/ equation :
    Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances =
    Newton.Search.Iteration.search elimination current epsilon remaining extraBits proposal clearances

constructive_injectivity Pending

/-- Initialize the exact six-proposal search history at the original seed. -/
def first : Newton.Search.Trace.Pending elimination current epsilon clearances initialProposal where
  remaining := 6
  inspected := 0
  budget := rfl
  extraBits := 0
  proposal := initialProposal
  history := .first
  equation := rfl

set_option genInjectivity false in
/-- The exact stopping reason and the actual number of candidates inspected.
A zero derivative is distinguished from exhaustion of all six proposals. -/
inductive Finished where
  /-- The first accepted original refinement, its actual inspected count and complete certified execution. -/ | accepted
    (value : Refinement current epsilon) (inspected : Nat)
      (withinBudget : inspected ≤ 6)
      (equation : Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances = some
        value)
      (execution : Newton.Search.Trace.Execution elimination current epsilon clearances initialProposal inspected (some
        value))
  /-- The original search exhausted all six proposals, with its exact none result and execution. -/ | exhausted
    (inspected : Nat) (allInspected : inspected = 6)
      (equation : Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances = none)
      (execution : Newton.Search.Trace.Execution elimination current epsilon clearances initialProposal inspected none)
  /-- The original search stopped at the retained center's zero derivative, preserving its count, value and execution.
  -/
  | zeroDerivative (center derivative : Gaussian.Basic.Canonical) (inspected : Nat)
      (withinBudget : inspected ≤ 6)
      (derivative_eq : derivative =
        (Dense.Derivative.derivative p).eval center)
      (zero : derivative = 0)
      (equation : Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances = none)
      (execution : Newton.Search.Trace.Execution elimination current epsilon clearances initialProposal inspected none)

constructive_injectivity Finished

/-- Project the checked search result without losing the separately retained
execution history and stopping reason. -/
def Finished.value : Newton.Search.Trace.Finished elimination current epsilon clearances initialProposal →
    Option (Refinement current epsilon)
  | .accepted value _ _ _ _ => some value
  | .exhausted _ _ _ _ => none
  | .zeroDerivative _ _ _ _ _ _ _ _ => none

/-- The retained terminal result equals the original bounded-search result. -/
theorem Finished.equation (finished : Newton.Search.Trace.Finished elimination current epsilon clearances
  initialProposal) :
    Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances = finished.value := by
  cases finished with
  | accepted value inspected withinBudget equation execution => exact equation
  | exhausted inspected allInspected equation execution => exact equation
  | zeroDerivative center derivative inspected withinBudget derivativeEq zero equation execution => exact equation

set_option genInjectivity false in
/-- The candidate has already been rejected and its derivative checked.
Only a saved next Newton value remains to be supplied. -/
structure Rejected where
  /-- The number of original proposals available after this rejection. -/ remaining : Nat
  /-- The actual number of proposals inspected through this rejection. -/ inspected : Nat
  /-- The saved remaining and inspected counts still sum to six. -/ budget : remaining + inspected = 6
  /-- The rounding precision for the next saved proposal. -/ extraBits : Nat
  /-- The exact rejected rounded center. -/ center : Gaussian.Basic.Canonical
  /-- The cached derivative value at the original rejected center. -/ derivative : Gaussian.Basic.Canonical
  /-- The cached derivative equals evaluation of the original polynomial derivative. -/ derivative_eq : derivative =
    (Dense.Derivative.derivative p).eval center
  /-- The retained derivative is nonzero. -/ nonzero : derivative ≠ 0
  /-- Any checked original Newton update extends this exact rejection history. -/ history : ∀ next, next =
    Gaussian.Basic.value
      (Dense.Gaussian.Newton.Basic.newtonCenter p center) →
    Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal remaining extraBits next inspected
  /-- The checked next Newton value preserves equality with the original complete bounded search. -/ equation : ∀ next,
    next = Gaussian.Basic.value
      (Dense.Gaussian.Newton.Basic.newtonCenter p center) →
    Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances =
      Newton.Search.Iteration.search elimination current epsilon remaining extraBits next clearances

constructive_injectivity Rejected

set_option genInjectivity false in
/-- One finite search-history inspection either finishes or retains a rejected nonstationary candidate.

The latter still requires its checked next Newton value before the original search can continue. -/
inductive Inspection where
  /-- The original search has a retained exact terminal outcome. -/ | finished (result : Newton.Search.Trace.Finished
    elimination current epsilon clearances initialProposal)
  /-- The original candidate is rejected with nonzero derivative and awaits its next checked Newton value. -/ | rejected
    (result : Newton.Search.Trace.Rejected elimination current epsilon clearances initialProposal)

-- Symbolic proof steps stay at the finite algorithm boundary.

constructive_injectivity Inspection

attribute [local irreducible] Newton.Search.Center.Basic.checkCenter Grid.Box.roundedCenter
  Newton.Search.Iteration.search
  Gaussian.Basic.value Dense.Gaussian.Derivative.Evaluation.derivativeEval
  Dense.Gaussian.Newton.Basic.newtonCenter

/-- Consume a checked rounded centre and its restored original candidate
result. Candidate generation and disk restoration share this exact history
transition; neither can bypass an earlier rejection. -/
def inspect (pending : Newton.Search.Trace.Pending elimination current epsilon clearances initialProposal)
    (center : Gaussian.Basic.Canonical)
    (centerEq : center = Grid.Box.roundedCenter current.box epsilon pending.extraBits pending.proposal)
    (candidate : { result : Option (Refinement current epsilon) //
      result = Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances }) :
    Newton.Search.Trace.Inspection elimination current epsilon clearances initialProposal := Id.run do
  match count : pending.remaining with
  | 0 =>
      have terminal : Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal 0
          pending.extraBits pending.proposal pending.inspected := by
        simpa only [count] using pending.history
      return .finished (.exhausted pending.inspected (by have := pending.budget; omega) (by
        rw [pending.equation, count, Newton.Search.Iteration.search_zero])
        (.exhausted terminal))
  | remaining + 1 =>
      have unfoldSearch : Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances =
          (match Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances with
          | some accepted => some accepted
          | none => if Gaussian.Basic.value
              (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
            else Newton.Search.Iteration.search elimination current epsilon remaining (pending.extraBits + 2)
              (Gaussian.Basic.value
                (Dense.Gaussian.Newton.Basic.newtonCenter p center)) clearances) := by
        rw [pending.equation, count, Newton.Search.Iteration.search_succ, ← centerEq]
        rfl
      have budget : remaining + (pending.inspected + 1) = 6 := by
        have := pending.budget
        omega
      have history : Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal (remaining + 1)
          pending.extraBits pending.proposal pending.inspected := by
        simpa only [count] using pending.history
      match restored : candidate.val with
      | some value =>
          have accepted := candidate.property.symm.trans restored
          return .finished (.accepted value (pending.inspected + 1) (by omega) (by
            rw [unfoldSearch, accepted]) (.accepted history center centerEq value accepted))
      | none =>
          have accepted := candidate.property.symm.trans restored
          let derivative := Gaussian.Basic.value
            (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center)
          have derivativeEq : derivative = (Dense.Derivative.derivative p).eval center :=
            Dense.Gaussian.Derivative.Evaluation.value_derivativeEval _ _
          if zero : derivative = 0 then
            return .finished (.zeroDerivative center derivative (pending.inspected + 1)
              (by omega) derivativeEq zero (by
                rw [unfoldSearch, accepted]
                exact if_pos zero) (.zeroDerivative history center centerEq accepted zero))
          else
            if exhausted : remaining = 0 then
              return .finished (.exhausted (pending.inspected + 1) (by omega) (by
                rw [unfoldSearch, accepted, if_neg zero, exhausted, Newton.Search.Iteration.search_zero])
                (.exhausted (bits := pending.extraBits + 2)
                  (proposal := Gaussian.Basic.value
                    (Dense.Gaussian.Newton.Basic.newtonCenter p center)) (by
                  have terminal := Newton.Search.Trace.Prefix.step history center _ centerEq accepted zero rfl
                  simpa only [exhausted] using terminal)))
            else
              return .rejected
                { remaining := remaining
                  inspected := pending.inspected + 1
                  budget := budget
                  extraBits := pending.extraBits + 2
                  center := center
                  derivative := derivative
                  derivative_eq := derivativeEq
                  nonzero := zero
                  history := fun next nextEq =>
                    Newton.Search.Trace.Prefix.step history center next centerEq accepted zero nextEq
                  equation := fun next nextEq => by
                    rw [unfoldSearch, accepted, if_neg zero, nextEq] }

/-- Check a supplied next Newton value against the retained derivative and original polynomial value.

The product identity advances the exact saved history; a failed identity returns the original inputs and its explicit
invalidity witness. -/
def supplyNext (rejected : Newton.Search.Trace.Rejected elimination current epsilon clearances initialProposal) (next :
  Gaussian.Basic.Canonical) :
    Except Newton.Search.Replay.Input.Invalid (Newton.Search.Trace.Pending elimination current epsilon clearances
      initialProposal) :=
  let value := p.eval rejected.center
  if product : (rejected.center - next) * rejected.derivative = value then
    have nextEq := Dense.Gaussian.Newton.Check.Product.newton_eq_of_product p rejected.center next
      (by rw [← rejected.derivative_eq]; exact rejected.nonzero)
      (by rw [← rejected.derivative_eq]; exact product)
    .ok
      { remaining := rejected.remaining
        inspected := rejected.inspected
        budget := rejected.budget
        extraBits := rejected.extraBits
        proposal := next
        history := rejected.history next nextEq
        equation := rejected.equation next nextEq }
  else .error (.newton rejected.center next rejected.derivative value product)

end Purelib.RootIsolation.Newton.Search.Trace

end

end
