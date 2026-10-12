module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial (Ready)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.CCL.Progressive.Cursor

open Purelib.Data.CCL.Progressive.Cursor.Request

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Persistent output after retryable anchored-logarithm preflight

Readiness returns an ordinary anchored chart whose output is an ordinary
coherent name.  The existing persistent cursor therefore applies unchanged.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.CCL.Cursor

/-- Start a persistent cursor at the exact output state of the certified ready logarithm branch. -/
def readyCursor
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    {output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)}
    (_ready : Ready sourceInput targetInput source state output) :
    Data.CCL.Progressive.Cursor.Request.State output.output.name.process output.output.name.state :=
  Data.CCL.Progressive.Cursor.Request.State.initial
    output.output.name.process output.output.name.state

/-- The ready logarithm cursor has exact parser semantics at its original output state. -/
theorem readyCursor_exact
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    {output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output) :
    Semantics.Basic.ExactCursor output.output.name.process output.output.name.state
      (readyCursor ready).machine :=
  (readyCursor ready).exact

/-- A finite request on the ready logarithm cursor appends exactly the requested number of bits. -/
theorem readyCursor_request_length
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    {output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor ready).request epsilonSq positive
      count).machine.emitted.length =
      (readyCursor ready).machine.emitted.length + count :=
  (readyCursor ready).request_length epsilonSq positive count

/-- A finite request on the ready logarithm cursor extends its existing raw prefix. -/
theorem readyCursor_request_extends
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    {output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    (readyCursor ready).machine.emitted.IsPrefix
      ((readyCursor ready).request epsilonSq positive
        count).machine.emitted :=
  (readyCursor ready).request_extends epsilonSq positive count

/-- A finite request preserves the ready logarithm cursor's exact parser semantics. -/
theorem readyCursor_request_exact
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    {output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    Semantics.Basic.ExactCursor output.output.name.process output.output.name.state
      ((readyCursor ready).request epsilonSq positive
        count).machine :=
  ((readyCursor ready).request epsilonSq positive count).exact

end Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.CCL.Cursor

end
