module

public import Purelib.RootIsolation.Newton.Search.Execution
public import Purelib.RootIsolation.Refinement.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.QuotientFreeOmega

/-! Exact rounded checks determine the retained numerical search history.
The original remaining proposal count also bounds the runtime history length. -/

public section

namespace Purelib.RootIsolation.Newton.Search.Trace.DataExecution

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {degreeBound : Nat}
    {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate polynomial degreeBound}
    {current : State.Raw.RawWindingState polynomial ambient} {epsilon : Fraction.Rational}
    {clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination}

/-- The original remaining proposal budget bounds the actual retained attempt list. -/
theorem length_le {remaining bits : Nat} {proposal : Basic.Canonical}
    {steps : List (Attempted current epsilon)} {result : Option (Refinement current epsilon)}
    (execution : DataExecution elimination current epsilon clearances remaining bits proposal steps result) :
    steps.length ≤ remaining := by
  induction execution with
  | exhausted => exact Nat.le_refl 0
  | accepted => exact Nat.succ_le_succ (Nat.zero_le _)
  | stationary => exact Nat.succ_le_succ (Nat.zero_le _)
  | exhaustedAfter => exact Nat.le_refl 1
  | rejected _ _ _ _ _ _ _ induction => exact Nat.succ_le_succ induction

/-- Two certified executions from the same cursor retain exactly the same numerical attempts.

Rounded centers, acceptance checks, derivatives and Newton updates determine
each branch. The conclusion compares the retained list itself, including its
original precisions, proposals, accepted owner and every continuation value. -/
theorem steps_unique {remaining bits : Nat} {proposal : Basic.Canonical}
    {stepsLeft stepsRight : List (Attempted current epsilon)}
    {resultLeft resultRight : Option (Refinement current epsilon)}
    (left : DataExecution elimination current epsilon clearances remaining bits proposal stepsLeft resultLeft)
    (right : DataExecution elimination current epsilon clearances remaining bits proposal stepsRight resultRight) :
    stepsLeft = stepsRight := by
  induction left generalizing stepsRight resultRight with
  | exhausted => cases right; rfl
  | @accepted remaining bits proposal center value rounded checked =>
    cases right with
    | @accepted _ _ _ centerRight valueRight roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have valueEq := Option.some.inj (checkedRight.symm.trans checked)
      subst valueRight
      rfl
    | @stationary _ _ _ centerRight _ roundedRight checkedRight _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @rejected _ _ _ centerRight _ _ _ _ _ roundedRight checkedRight _ _ _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @exhaustedAfter _ _ centerRight _ roundedRight checkedRight _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
  | @stationary remaining bits proposal center derivative rounded checked derivativeEq zero =>
    cases right with
    | @accepted _ _ _ centerRight _ roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @stationary _ _ _ centerRight derivativeRight roundedRight _ derivativeRightEq _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      cases derivativeSame
      rfl
    | @rejected _ _ _ centerRight derivativeRight _ _ _ _ roundedRight _ derivativeRightEq nonzero _ _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.trans zero))
    | @exhaustedAfter _ _ centerRight derivativeRight roundedRight _ derivativeRightEq nonzero =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.trans zero))
  | @exhaustedAfter bits proposal center derivative rounded checked derivativeEq nonzero =>
    cases right with
    | @accepted _ _ _ centerRight _ roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @stationary _ _ _ centerRight derivativeRight roundedRight _ derivativeRightEq zero =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.symm.trans zero))
    | @exhaustedAfter _ _ centerRight derivativeRight roundedRight _ derivativeRightEq _ =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      cases derivativeSame
      rfl
    | rejected remainingPositive _ _ _ _ _ _ =>
      exact False.elim (Nat.not_lt_zero _ remainingPositive)
  | @rejected remaining bits proposal center derivative next steps result remainingPositive rounded checked
      derivativeEq nonzero
      nextEq tail induction =>
    cases right with
    | @accepted _ _ _ centerRight _ roundedRight checkedRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      cases checkedRight.symm.trans checked
    | @stationary _ _ _ centerRight derivativeRight roundedRight _ derivativeRightEq zero =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      exact False.elim (nonzero (derivativeSame.symm.trans zero))
    | exhaustedAfter => exact False.elim (Nat.not_lt_zero _ remainingPositive)
    | @rejected _ _ _ centerRight derivativeRight nextRight stepsRight resultRight _ roundedRight _ derivativeRightEq _
        nextRightEq tailRight =>
      have centerEq := roundedRight.trans rounded.symm
      clear roundedRight
      subst centerRight
      have derivativeSame := derivativeRightEq.trans derivativeEq.symm
      clear derivativeRightEq
      subst derivativeRight
      have nextSame := nextRightEq.trans nextEq.symm
      clear nextRightEq
      subst nextRight
      have tailSame := induction tailRight
      cases tailSame
      rfl

end Purelib.RootIsolation.Newton.Search.Trace.DataExecution

namespace Purelib.RootIsolation.Newton.Search.Trace

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {degreeBound : Nat}
    {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational}
    {clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination}
    {initialProposal : Gaussian.Basic.Canonical}

set_option genInjectivity false in
/-- The numerical terminal fields of an original finite search. -/
private inductive Stop where
  | accepted (value : Refinement current epsilon) (inspected : Nat)
  | exhausted (inspected : Nat)
  | stationary (center derivative : Gaussian.Basic.Canonical) (inspected : Nat)

/-- Add an already inspected prefix to a terminal count. -/
private def Stop.add (count : Nat) :
    Stop (current := current) (epsilon := epsilon) → Stop (current := current) (epsilon := epsilon)
  | .accepted value inspected => .accepted value (inspected + count)
  | .exhausted inspected => .exhausted (inspected + count)
  | .stationary center derivative inspected => .stationary center derivative (inspected + count)

/-- Adding consecutive inspected prefixes preserves every terminal numerical field. -/
private theorem Stop.add_add (stop : Stop (current := current) (epsilon := epsilon)) (left right : Nat) :
    (stop.add left).add right = stop.add (left + right) := by
  cases stop with
  | accepted value inspected => exact congrArg (Stop.accepted value) (Nat.add_assoc inspected left right)
  | exhausted inspected => exact congrArg Stop.exhausted (Nat.add_assoc inspected left right)
  | stationary center derivative inspected =>
      exact congrArg (Stop.stationary center derivative) (Nat.add_assoc inspected left right)

/-- Read the terminal fields from the actual ordered numerical attempts. -/
private def attemptStop : List (Attempted current epsilon) → Stop (current := current) (epsilon := epsilon)
  | [] => .exhausted 0
  | .accepted _ _ _ value :: _ => .accepted value 1
  | .stationary _ _ center derivative :: _ => .stationary center derivative 1
  | .exhausted _ _ _ _ :: _ => .exhausted 1
  | .rejected _ _ _ _ _ :: tail => (attemptStop tail).add 1

/-- Read the same terminal fields from the certified original stopping outcome. -/
private def Finished.summary : Finished elimination current epsilon clearances initialProposal →
    Stop (current := current) (epsilon := epsilon)
  | .accepted value inspected _ _ _ => .accepted value inspected
  | .exhausted inspected _ _ _ _ => .exhausted inspected
  | .zeroDerivative center derivative inspected _ _ _ _ _ _ => .stationary center derivative inspected

/-- A checked rejected proposal prefixes the same original numerical execution. -/
private theorem DataExecution.prepend {remaining bits : Nat}
    {proposal center derivative next : Gaussian.Basic.Canonical}
    {steps : List (Attempted current epsilon)} {result : Option (Refinement current epsilon)}
    (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
    (checked : Center.Basic.checkCenter elimination current epsilon center clearances = none)
    (derivativeEq : derivative = Gaussian.Basic.value
      (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center))
    (nonzero : derivative ≠ 0)
    (nextEq : next = Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center))
    (tail : DataExecution elimination current epsilon clearances remaining (bits + 2) next steps result) :
    ∃ all, DataExecution elimination current epsilon clearances (remaining + 1) bits proposal all result ∧
      attemptStop all = (attemptStop steps).add 1 := by
  cases remaining with
  | zero =>
      cases tail
      exact ⟨[.exhausted bits proposal center derivative],
        .exhaustedAfter rounded checked derivativeEq nonzero, rfl⟩
  | succ remaining =>
      exact ⟨.rejected bits proposal center derivative next :: steps,
        .rejected (Nat.zero_lt_succ _) rounded checked derivativeEq nonzero nextEq tail, rfl⟩

/-- A certified rejected prefix extends a terminal execution without changing its terminal data. -/
private theorem Prefix.lift_stop {remaining bits inspected : Nat} {proposal : Gaussian.Basic.Canonical}
    (history : Prefix elimination current epsilon clearances initialProposal remaining bits proposal inspected)
    {steps : List (Attempted current epsilon)} {result : Option (Refinement current epsilon)}
    (tail : DataExecution elimination current epsilon clearances remaining bits proposal steps result) :
    ∃ all, DataExecution elimination current epsilon clearances 6 0 initialProposal all result ∧
      attemptStop all = (attemptStop steps).add inspected := by
  induction history generalizing steps result with
  | first =>
      refine ⟨steps, tail, ?_⟩
      cases found : attemptStop steps <;> rfl
  | @step remaining bits proposal inspected previous center next rounded checked nonzero nextEq induction =>
      obtain ⟨joined, execution, terminal⟩ := DataExecution.prepend rounded checked rfl nonzero nextEq tail
      obtain ⟨all, allExecution, allTerminal⟩ := induction execution
      refine ⟨all, allExecution, ?_⟩
      calc
        attemptStop all = (attemptStop joined).add inspected := allTerminal
        _ = ((attemptStop steps).add 1).add inspected := congrArg (Stop.add inspected) terminal
        _ = (attemptStop steps).add (1 + inspected) := Stop.add_add _ _ _
        _ = (attemptStop steps).add (inspected + 1) := congrArg (fun count => (attemptStop steps).add count)
          (Nat.add_comm 1 inspected)

/-- Every original certified terminal outcome has its exact deterministic numerical attempt list. -/
private theorem Finished.stop_exists (finished : Finished elimination current epsilon clearances initialProposal) :
    ∃ steps, DataExecution elimination current epsilon clearances 6 0 initialProposal steps finished.value ∧
      attemptStop steps = finished.summary := by
  cases finished with
  | accepted value inspected within equation execution =>
      cases execution with
      | accepted previous center rounded value checked =>
          obtain ⟨all, allExecution, terminal⟩ := previous.lift_stop (.accepted rounded checked)
          refine ⟨all, allExecution, ?_⟩
          exact terminal.trans (congrArg (Stop.accepted value) (Nat.add_comm 1 _))
  | exhausted inspected allInspected equation execution actual =>
      obtain ⟨bits, proposal, previous⟩ := actual
      obtain ⟨all, allExecution, terminal⟩ := previous.lift_stop .exhausted
      exact ⟨all, allExecution, terminal.trans (congrArg Stop.exhausted (Nat.zero_add _))⟩
  | zeroDerivative center derivative inspected within derivativeEq zero equation execution actual =>
      obtain ⟨remaining, bits, proposal, before, count, history, rounded, checked⟩ := actual
      have sameDerivative : derivative = Gaussian.Basic.value
          (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) :=
        derivativeEq.trans (Dense.Gaussian.Derivative.Evaluation.value_derivativeEval _ _).symm
      obtain ⟨all, allExecution, terminal⟩ := history.lift_stop
        (.stationary rounded checked sameDerivative zero)
      refine ⟨all, allExecution, ?_⟩
      exact terminal.trans (congrArg (Stop.stationary center derivative)
        ((Nat.add_comm 1 before).trans count.symm))

/-- The certified original stopping outcomes have uniquely determined complete numerical fields. -/
theorem Finished.unique (left right : Finished elimination current epsilon clearances initialProposal) :
    left = right := by
  obtain ⟨leftSteps, leftExecution, leftTerminal⟩ := left.stop_exists
  obtain ⟨rightSteps, rightExecution, rightTerminal⟩ := right.stop_exists
  have stepsEq := leftExecution.steps_unique rightExecution
  have terminalEq : left.summary = right.summary :=
    leftTerminal.symm.trans ((congrArg attemptStop stepsEq).trans rightTerminal)
  cases left <;> cases right <;> cases terminalEq <;> rfl

/-- Complete retained original histories are unique at their same original search cursor.

This compares the stopping outcome, every ordered numerical proposal and
all cached updates. The proof uses only their certified original executions.
-/
theorem Retained.unique {remaining bits : Nat} {proposal : Gaussian.Basic.Canonical}
    (left right : Retained elimination current epsilon clearances initialProposal remaining bits proposal) :
    left = right := by
  cases left with
  | mk leftFinished leftSteps leftExecution =>
      cases right with
      | mk rightFinished rightSteps rightExecution =>
          have finishedEq := leftFinished.unique rightFinished
          cases finishedEq
          have stepsEq := leftExecution.steps_unique rightExecution
          cases stepsEq
          rfl

/-- Checked restoration recovers the complete original once-run six-proposal history. -/
theorem Retained.eq_run
    (retained : Retained elimination current epsilon clearances initialProposal 6 0 initialProposal) :
    retained = run elimination current epsilon clearances initialProposal := retained.unique _

end Purelib.RootIsolation.Newton.Search.Trace
