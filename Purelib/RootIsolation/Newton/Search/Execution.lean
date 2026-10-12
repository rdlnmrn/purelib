module

public import Purelib.RootIsolation.Newton.Search.Trace
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.Tactic.QuotientFreeOmega

/-! # Execution of the retained finite Newton search

The same rounded proposals and acceptance checks produce both the refinement
and its finite stopping certificate. No second search reconstructs a miss.
-/

public section

namespace Purelib.RootIsolation.Newton.Search.Trace

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {p : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
  (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
  (initialProposal : Gaussian.Basic.Canonical)

set_option genInjectivity false in
/-- One actually inspected rounded proposal, with the numerical data used by its accepted or rejected branch. -/
inductive Attempted where
  /-- The exact precision, proposal and center of the first accepted refinement. -/
  | accepted (bits : Nat) (proposal center : Gaussian.Basic.Canonical) (value : Refinement current epsilon)
  /-- A rejected center's zero derivative terminates the original search. -/
  | stationary (bits : Nat) (proposal center derivative : Gaussian.Basic.Canonical)
  /-- The last rejected nonstationary center exhausts the budget without generating an unused next proposal. -/
  | exhausted (bits : Nat) (proposal center derivative : Gaussian.Basic.Canonical)
  /-- A rejected nonstationary center retains the exact next Newton proposal. -/
  | rejected (bits : Nat) (proposal center derivative next : Gaussian.Basic.Canonical)

set_option genInjectivity false in
/-- The retained ordered runtime steps are the actual finite search execution at the displayed cursor. -/
inductive DataExecution : Nat → Nat → Gaussian.Basic.Canonical →
    List (Attempted current epsilon) → Option (Refinement current epsilon) → Prop where
  /-- No remaining proposal produces the empty terminal trace. -/
  | exhausted {bits proposal} : DataExecution 0 bits proposal [] none
  /-- The first accepted original rounded center is the final retained step. -/
  | accepted {remaining bits proposal center value}
      (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
      (checked : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = some value) :
      DataExecution (remaining + 1) bits proposal [.accepted bits proposal center value] (some value)
  /-- The original zero derivative follows the rejected rounded-center check and stops immediately. -/
  | stationary {remaining bits proposal center derivative}
      (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
      (checked : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = none)
      (derivative_eq : derivative = Gaussian.Basic.value
        (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center))
      (zero : derivative = 0) :
      DataExecution (remaining + 1) bits proposal [.stationary bits proposal center derivative] none
  /-- The final rejected nonstationary center stops without an unused Newton update. -/
  | exhaustedAfter {bits proposal center derivative}
      (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
      (checked : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = none)
      (derivative_eq : derivative = Gaussian.Basic.value
        (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center))
      (nonzero : derivative ≠ 0) :
      DataExecution 1 bits proposal [.exhausted bits proposal center derivative] none
  /-- The original nonzero derivative and Newton update lead to exactly the retained remaining steps. -/
  | rejected {remaining bits proposal center derivative next steps result}
      (remaining_pos : 0 < remaining)
      (rounded : center = Grid.Box.roundedCenter current.box epsilon bits proposal)
      (checked : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances = none)
      (derivative_eq : derivative = Gaussian.Basic.value
        (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center))
      (nonzero : derivative ≠ 0)
      (next_eq : next = Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center))
      (tail : DataExecution remaining (bits + 2) next steps result) :
      DataExecution (remaining + 1) bits proposal (.rejected bits proposal center derivative next :: steps) result

set_option genInjectivity false in
/-- An exact finished search retaining every actual attempted center and update from the displayed continuation.

The runtime list and terminal certificate refer to the same checked execution;
proof-only histories establish correctness without substituting for its data. -/
structure Retained (remaining bits : Nat) (proposal : Gaussian.Basic.Canonical) where
  /-- The original terminal result, count and certified finite execution. -/
  finished : Finished elimination current epsilon clearances initialProposal
  /-- The exact ordered numerical steps actually inspected from this cursor. -/
  steps : List (Attempted current epsilon)
  /-- Every retained step is linked to the original check, derivative and Newton update. -/
  execution : DataExecution elimination current epsilon clearances remaining bits proposal steps finished.value

attribute [local irreducible] Newton.Search.Center.Basic.checkCenter Grid.Box.roundedCenter
  Newton.Search.Iteration.search Gaussian.Basic.value
  Dense.Gaussian.Derivative.Evaluation.derivativeEval Dense.Gaussian.Newton.Basic.newtonCenter

/-- Continue the actual finite proposal history, retaining its numerical steps and exact stopping evidence. -/
@[expose] def runFrom :
    (remaining bits : Nat) → (proposal : Gaussian.Basic.Canonical) → (inspected : Nat) →
      Prefix elimination current epsilon clearances initialProposal remaining bits proposal inspected →
      remaining + inspected = 6 →
      Newton.Search.Iteration.search elimination current epsilon 6 0 initialProposal clearances =
        Newton.Search.Iteration.search elimination current epsilon remaining bits proposal clearances →
      Retained elimination current epsilon clearances initialProposal remaining bits proposal
  | 0, _bits, _proposal, inspected, history, budget, equation =>
      ⟨.exhausted inspected (by omega0)
        (equation.trans (Newton.Search.Iteration.search_zero ..)) (.exhausted history), [], .exhausted⟩
  | remaining + 1, bits, proposal, inspected, history, budget, equation => by
      let center := Grid.Box.roundedCenter current.box epsilon bits proposal
      have unfoldSearch := equation.trans
        (Newton.Search.Iteration.search_succ elimination current epsilon remaining bits proposal clearances)
      match checked : Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances with
      | some accepted =>
          let finished : Finished elimination current epsilon clearances initialProposal :=
            .accepted accepted (inspected + 1) (by omega0) (by
              rw [unfoldSearch]
              change (match Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances with
                | some value => some value
                | none => _) = some accepted
              rw [checked]) (.accepted history center rfl accepted checked)
          exact ⟨finished, [.accepted bits proposal center accepted], .accepted rfl checked⟩
      | none =>
          let derivative := Gaussian.Basic.value
            (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center)
          if zero : derivative = 0 then
            let finished : Finished elimination current epsilon clearances initialProposal :=
              .zeroDerivative center derivative (inspected + 1) (by omega0)
                (Dense.Gaussian.Derivative.Evaluation.value_derivativeEval _ _) zero (by
                  rw [unfoldSearch]
                  change (match Newton.Search.Center.Basic.checkCenter
                      elimination current epsilon center clearances with
                    | some value => some value
                    | none => if derivative = 0 then none else _) = none
                  rw [checked, if_pos zero]) (.zeroDerivative history center rfl checked zero)
            exact ⟨finished, [.stationary bits proposal center derivative], .stationary rfl checked rfl zero⟩
          else if exhausted : remaining = 0 then
            let finished : Finished elimination current epsilon clearances initialProposal :=
              .exhausted (inspected + 1) (by omega0) (by
                rw [unfoldSearch]
                change (match Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances with
                  | some value => some value
                  | none => if derivative = 0 then none else _) = none
                rw [checked, if_neg zero, exhausted, Newton.Search.Iteration.search_zero])
                (.exhausted (exhausted ▸ Prefix.step history center _ rfl checked zero rfl))
            exact ⟨finished, [.exhausted bits proposal center derivative],
              exhausted ▸ .exhaustedAfter rfl checked rfl zero⟩
          else
            let next := Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center)
            let tail := runFrom remaining (bits + 2) next (inspected + 1)
              (.step history center next rfl checked zero rfl) (by omega0) (by
                rw [unfoldSearch]
                change (match Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances with
                  | some value => some value
                  | none => if derivative = 0 then none else _) = _
                rw [checked, if_neg zero])
            exact ⟨tail.finished, .rejected bits proposal center derivative next :: tail.steps,
              .rejected (by omega0) rfl checked rfl zero rfl tail.execution⟩
termination_by structural remaining _ _ _ _ _ _ => remaining

/-- Execute the original six-proposal search once and retain its actual numerical steps and terminal certificate. -/
@[expose] def run : Retained elimination current epsilon clearances initialProposal 6 0 initialProposal :=
  runFrom elimination current epsilon clearances initialProposal 6 0 initialProposal 0 .first rfl rfl

end Purelib.RootIsolation.Newton.Search.Trace
