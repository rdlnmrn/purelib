import CCL.Persistent.Progressive
import CCL.Progressive.PartialLogarithm

/-!
# Persistent output after retryable anchored-logarithm preflight

Readiness returns an ordinary anchored chart whose output is an ordinary
coherent name.  The existing persistent cursor therefore applies unchanged.
-/

namespace CCL.ProgressivePartialLogarithm

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Cursor := CCL.PersistentProgressive.Cursor
abbrev ExactCursor := CCL.ProgressiveMachineSemantics.ExactCursor

def readyCursor
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    {output : AnchoredChart (preparedTarget state)}
    (_ready : Ready sourceInput targetInput source state output) :
    Cursor output.output.name.process output.output.name.state :=
  CCL.PersistentProgressive.Cursor.initial
    output.output.name.process output.output.name.state

theorem readyCursor_exact
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    {output : AnchoredChart (preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output) :
    ExactCursor output.output.name.process output.output.name.state
      (readyCursor ready).machine :=
  (readyCursor ready).exact

theorem readyCursor_request_length
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    {output : AnchoredChart (preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor ready).request epsilonSq positive count).machine.emitted.length =
      (readyCursor ready).machine.emitted.length + count :=
  (readyCursor ready).request_length epsilonSq positive count

theorem readyCursor_request_extends
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    {output : AnchoredChart (preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    (readyCursor ready).machine.emitted.IsPrefix
      ((readyCursor ready).request epsilonSq positive count).machine.emitted :=
  (readyCursor ready).request_extends epsilonSq positive count

theorem readyCursor_request_exact
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    {output : AnchoredChart (preparedTarget state)}
    (ready : Ready sourceInput targetInput source state output)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    ExactCursor output.output.name.process output.output.name.state
      ((readyCursor ready).request epsilonSq positive count).machine :=
  ((readyCursor ready).request epsilonSq positive count).exact

end CCL.ProgressivePartialLogarithm
