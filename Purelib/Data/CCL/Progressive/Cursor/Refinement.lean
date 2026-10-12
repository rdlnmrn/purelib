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
def ball : Data.CCL.Transducer.Mode →
    Approximation.Gaussian.Enclosure.Ball
  | .initial current => current.process.ball current.state
  | .low current => current.process.ball current.state
  | .loop current => current.process.ball current.state
  | .residual current => current.process.ball current.state

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refine the retained mode's process state to the supplied positive radius-squared target.

Keep its original process, phase, normalization count and domain or upper-bound data. Transfer possible-value bounds
along that same process's refinement relation. -/
def refine : (mode : Data.CCL.Transducer.Mode) → (target :
  Fraction.Rational) → 0 < target → Data.CCL.Transducer.Mode
  | .initial current, target, positive =>
      .initial
        { process := current.process
          state := current.process.refine current.state target positive }
  | .low current, target, positive =>
      .low
        { count := current.count
          process := current.process
          state := current.process.refine current.state target positive
          upperBound := by
            intro value possible
            exact current.upperBound
              (current.process.refine_persists current.state target positive
                possible) }
  | .loop current, target, positive =>
      .loop
        { kind := current.kind
          count := current.count
          process := current.process
          state := current.process.refine current.state target positive
          domain := current.domain }
  | .residual current, target, positive =>
      .residual
        { process := current.process
          state := current.process.refine current.state target positive
          count := current.count
          upper := current.upper
          upperBound := by
            intro value possible
            exact current.upperBound
              (current.process.refine_persists current.state target positive
                possible)
          upperStrict := current.upperStrict }

section
open Purelib.Data.CCL
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every possible value after mode refinement remains possible at the original retained mode. -/
theorem refine_possible
    (mode : Data.CCL.Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target)
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
    (mode : Data.CCL.Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target) :
    (ball (refine mode target positive)).radiusSq
      < target := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.accurate current.state target positive

open Purelib.Data.Gaussian in
/-- Every possible value of the retained mode lies in its exact process ball. -/
theorem possible_inside
    (mode : Data.CCL.Transducer.Mode) {value : Basic.Canonical}
    (possible : Mode.Semantics.SemanticMode.possible mode value) :
    (ball mode).Contains value := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.possible_inside possible

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Refining a mode leaves its projective parser-tail formula unchanged at every Gaussian value. -/
@[simp] theorem refine_parserTail
    (mode : Data.CCL.Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target)
    (value : Basic.Canonical) :
    Mode.Semantics.SemanticMode.parserTail (refine mode target positive) value =
      Mode.Semantics.SemanticMode.parserTail mode value := by
  cases mode <;> rfl

open Purelib.Data.Rat in
/-- Refining a mode leaves its exact raw parser phase unchanged. -/
@[simp] theorem refine_rawPhase
    (mode : Data.CCL.Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target) :
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
/-- Refine the exact retained machine mode while preserving its emitted prefix and pending queue.

The requested positive radius-squared target is passed to the same mode process. Its phase, counts and owner remain
intact, so refinement requests no new emitted bits. -/
def refine (machine : Data.CCL.Transducer.Machine)
  (target :
  Fraction.Rational) (positive : 0 < target) :
    Data.CCL.Transducer.Machine :=
  { mode := Progressive.Cursor.Refinement.Mode.refine machine.mode target positive
    emitted := machine.emitted
    pending := machine.pending }

/-- Refining the machine leaves its exact emitted prefix unchanged. -/
@[simp] theorem refine_emitted
    (machine : Data.CCL.Transducer.Machine) (target : Fraction.Rational) (positive : 0 < target) :
    ((refine machine target positive)).emitted = machine.emitted := rfl

/-- Refining the machine leaves its exact pending bit queue unchanged. -/
@[simp] theorem refine_pending
    (machine : Data.CCL.Transducer.Machine) (target : Fraction.Rational) (positive : 0 < target) :
    ((refine machine target positive)).pending = machine.pending := rfl

/-- Refining the machine leaves its exact committed word unchanged. -/
@[simp] theorem refine_committed
    (machine : Data.CCL.Transducer.Machine) (target : Fraction.Rational) (positive : 0 < target) :
    Data.CCL.Transducer.Machine.committed
        ((refine machine target positive)) =
      Data.CCL.Transducer.Machine.committed machine :=
  rfl

end

open Purelib.Data.CCL in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refining the retained machine preserves its committed-word grammar invariant. -/
theorem refine_grammar
    (machine : Data.CCL.Transducer.Machine) (target : Fraction.Rational) (positive : 0 < target)
    (grammar :
      Data.CCL.Transducer.Machine.Grammar.Invariant
        machine) :
    Data.CCL.Transducer.Machine.Grammar.Invariant
      ((refine machine target positive)) := by
  unfold Data.CCL.Transducer.Machine.Grammar.Invariant
    at grammar ⊢
  change
    (Parser.State.parse
      (Data.CCL.Transducer.Machine.committed
        machine)).phase =
      Mode.Grammar.modeRawPhase
        (Progressive.Cursor.Refinement.Mode.refine machine.mode target positive)
  rw [Progressive.Cursor.Refinement.Mode.refine_rawPhase]
  exact grammar
end Machine

end Purelib.Data.CCL.Progressive.Cursor.Refinement

end
