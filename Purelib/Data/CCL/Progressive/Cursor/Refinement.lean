module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
public import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Grammar
public import Purelib.Data.CCL.Transducer.Mode.Semantics
public import Purelib.Data.CCL.Transducer.Mode.Observation
import Purelib.Data.List.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Data.Gaussian.Norm.Basic

section
@[expose] public section

/-!
# Persistent finite requests for progressive CCL cursors

The raw arithmetic cursor already extends one finite `List Bool` prefix.  This
module adds the missing accuracy operation: refine the finite enclosure carried
by its current quantitative mode without changing either exposed or buffered
bits.  The refined ball is transported through the exact current projective
chart, giving an arbitrarily small rational squared-chordal cylinder bound.

Everything here is a finite request on an explicit machine.  No stream, limit,
intersection, or completed value is formed.
-/

namespace Purelib.Data.CCL.Progressive.Cursor.Refinement

namespace Mode

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
/-- Read the exact ball retained by the mode's original process and current state. -/
def ball : Mode →
    Enclosure.Ball
  | .initial current => current.process.ball current.state
  | .low current => current.process.ball current.state
  | .loop current => current.process.ball current.state
  | .residual current => current.process.ball current.state

open Purelib.Data.CCL.Transducer in
/-- The original mode ball is the retained process projection's same numerical readback. -/
theorem process_ball (mode : Mode) : mode.process.ball mode.state = ball mode := by
  cases mode <;> rfl

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Rebuild the original refined mode from its exact already returned process state.

The nominal process, phase, normalization count and original domain are
retained. Possible-value bounds use the supplied original refinement identity;
the process refiner is not called by this constructor.
-/
def fromState : (mode : Mode) → (target : Fraction.Rational) → (positive : 0 < target) →
    { state : mode.process.State // state = mode.process.refine mode.state target positive } → Mode
  | .initial current, _, _, retained =>
      .initial
        { process := current.process
          state := retained.val }
  | .low current, target, positive, retained =>
      .low
        { count := current.count
          process := current.process
          state := retained.val
          upperBound := by
            intro value possible
            exact current.upperBound
              (current.process.refine_persists current.state target positive
                (retained.property ▸ possible)) }
  | .loop current, _, _, retained =>
      .loop
        { kind := current.kind
          count := current.count
          process := current.process
          state := retained.val
          domain := current.domain }
  | .residual current, target, positive, retained =>
      .residual
        { process := current.process
          state := retained.val
          count := current.count
          upper := current.upper
          upperBound := by
            intro value possible
            exact current.upperBound
              (current.process.refine_persists current.state target positive
                (retained.property ▸ possible))
          upperStrict := current.upperStrict }

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refine the original mode once and retain its process, phase, counts and quantitative bounds. -/
def refine (mode : Mode) (target : Fraction.Rational) (positive : 0 < target) : Mode :=
  fromState mode target positive ⟨mode.process.refine mode.state target positive, rfl⟩

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refining an original mode keeps its exact nominal Gaussian process owner. -/
theorem refine_process (mode : Mode) (target : Fraction.Rational) (positive : 0 < target) :
    (refine mode target positive).process = mode.process := by
  cases mode <;> rfl

section
open Purelib.Data.CCL
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every possible value after mode refinement remains possible at the original retained mode. -/
theorem refine_possible
    (mode : Mode) (target : Fraction.Rational) (positive : 0 < target)
    {value : Basic.Canonical}
    (possible : Mode.Semantics.SemanticMode.possible (refine mode target positive)
      value) :
    Mode.Semantics.SemanticMode.possible mode value := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.refine_persists current.state target positive
        possible

open Purelib.Data.Rat in
/-- The refined mode's exact ball has radius squared strictly below the positive requested target. -/
theorem refine_ball_radiusSq_lt
    (mode : Mode) (target : Fraction.Rational) (positive : 0 < target) :
    (ball (refine mode target positive)).radiusSq
      < target := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.accurate current.state target positive

open Purelib.Data.Gaussian in
/-- Every possible value of the retained mode lies in its exact process ball. -/
theorem possible_inside
    (mode : Mode) {value : Basic.Canonical}
    (possible : Mode.Semantics.SemanticMode.possible mode value) :
    (ball mode).Contains value := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.possible_inside possible

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Refining a mode leaves its projective parser-tail formula unchanged at every Gaussian value. -/
@[simp] theorem refine_parserTail
    (mode : Mode) (target : Fraction.Rational) (positive : 0 < target)
    (value : Basic.Canonical) :
    Mode.Semantics.SemanticMode.parserTail (refine mode target positive) value =
      Mode.Semantics.SemanticMode.parserTail mode value := by
  cases mode <;> rfl

open Purelib.Data.Rat in
/-- Refining a mode leaves its exact raw parser phase unchanged. -/
@[simp] theorem refine_rawPhase
    (mode : Mode) (target : Fraction.Rational) (positive : 0 < target) :
    Mode.Grammar.modeRawPhase
        (refine mode target positive) =
      Mode.Grammar.modeRawPhase mode := by
  cases mode <;> rfl
end

end Mode

namespace Machine

section
open Purelib.Data.CCL
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
/-- Construct the original refined machine from its exact returned source state.

The same process, phase, counts, emitted prefix and pending queue are retained.
The supplied state identity certifies the unchanged original positive request.
-/
def fromState (machine : Machine) (target : Fraction.Rational) (positive : 0 < target)
    (retained : { state : machine.mode.process.State //
      state = machine.mode.process.refine machine.mode.state target positive }) : Machine :=
  { mode := Mode.fromState machine.mode target positive retained
    emitted := machine.emitted
    pending := machine.pending }

/-- Refine the original current mode once while retaining both exact original words. -/
def refine (machine : Machine) (target : Fraction.Rational) (positive : 0 < target) : Machine :=
  fromState machine target positive ⟨machine.mode.process.refine machine.mode.state target positive, rfl⟩

/-- Refining the machine leaves its exact emitted prefix unchanged. -/
@[simp] theorem refine_emitted
    (machine : Machine) (target : Fraction.Rational) (positive : 0 < target) :
    ((refine machine target positive)).emitted = machine.emitted := rfl

/-- Refining the machine leaves its exact pending bit queue unchanged. -/
@[simp] theorem refine_pending
    (machine : Machine) (target : Fraction.Rational) (positive : 0 < target) :
    ((refine machine target positive)).pending = machine.pending := rfl

/-- Refining the machine leaves its exact committed word unchanged. -/
@[simp] theorem refine_committed
    (machine : Machine) (target : Fraction.Rational) (positive : 0 < target) :
    Machine.committed
        ((refine machine target positive)) =
      Machine.committed machine :=
  rfl

end

open Purelib.Data.CCL in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refining the retained machine preserves its committed-word grammar invariant. -/
theorem refine_grammar
    (machine : Machine) (target : Fraction.Rational) (positive : 0 < target)
    (grammar :
      Machine.Grammar.Invariant
        machine) :
    Machine.Grammar.Invariant
      ((refine machine target positive)) := by
  unfold Machine.Grammar.Invariant
    at grammar ⊢
  change
    (Parser.State.parse
      (Machine.committed
        machine)).phase =
      Mode.Grammar.modeRawPhase
        (Mode.refine machine.mode target positive)
  rw [Mode.refine_rawPhase]
  exact grammar
end Machine

end Purelib.Data.CCL.Progressive.Cursor.Refinement

end

public section

namespace Purelib.Data.CCL.Progressive.Cursor.Refinement

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat

/-- Rebuilding a mode from an exact retained state gives its complete original refinement. -/
theorem Mode.fromState_eq (mode : Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target)
    (retained : { state : mode.process.State // state = mode.process.refine mode.state target positive }) :
    Mode.fromState mode target positive retained = Mode.refine mode target positive := by
  rcases retained with ⟨state, same⟩
  cases same
  rfl

/-- Lift the supplied observation into the same rebuilt mode without reading its source. -/
def Mode.observationFromState (mode : Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target)
    (retained : { state : mode.process.State // state = mode.process.refine mode.state target positive })
    (observed : Process.Observation mode.process retained.val) :
    Transducer.Mode.Observation (Mode.fromState mode target positive retained) := by
  cases mode <;> exact observed

/-- Rebuilding a machine from its exact retained state gives the complete original machine refinement. -/
theorem Machine.fromState_eq (machine : Transducer.Machine) (target : Fraction.Rational) (positive : 0 < target)
    (retained : { state : machine.mode.process.State //
      state = machine.mode.process.refine machine.mode.state target positive }) :
    Machine.fromState machine target positive retained = Machine.refine machine target positive :=
  congrArg (fun mode => (⟨mode, machine.emitted, machine.pending⟩ : Transducer.Machine))
    (Mode.fromState_eq machine.mode target positive retained)

end Purelib.Data.CCL.Progressive.Cursor.Refinement

end
