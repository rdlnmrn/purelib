import CCL.Persistent.Progressive
import CCL.Progressive.PartialLogQuotient

/-!
# Persistent output after dependency scheduling

Once both partial children of `log(1 + z) / z` are ready, the scheduler returns
an ordinary coherent name.  The unchanged persistent cursor therefore supplies
the standard finite prefix and parser contracts.
-/

namespace CCL.ProgressivePartialLogQuotient

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Cursor := CCL.PersistentProgressive.Cursor
abbrev ExactCursor := CCL.ProgressiveMachineSemantics.ExactCursor

def readyCursor {client : Client} {output : CoherentNamed}
    (_ready : Ready client output) :
    Cursor output.name.process output.name.state :=
  CCL.PersistentProgressive.Cursor.initial output.name.process output.name.state

theorem readyCursor_exact {client : Client} {output : CoherentNamed}
    (ready : Ready client output) :
    ExactCursor output.name.process output.name.state
      (readyCursor ready).machine :=
  (readyCursor ready).exact

theorem readyCursor_request_length {client : Client} {output : CoherentNamed}
    (ready : Ready client output) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor ready).request epsilonSq positive count).machine.emitted.length =
      (readyCursor ready).machine.emitted.length + count :=
  (readyCursor ready).request_length epsilonSq positive count

theorem readyCursor_request_extends {client : Client} {output : CoherentNamed}
    (ready : Ready client output) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) :
    (readyCursor ready).machine.emitted.IsPrefix
      ((readyCursor ready).request epsilonSq positive count).machine.emitted :=
  (readyCursor ready).request_extends epsilonSq positive count

theorem readyCursor_request_exact {client : Client} {output : CoherentNamed}
    (ready : Ready client output) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) :
    ExactCursor output.name.process output.name.state
      ((readyCursor ready).request epsilonSq positive count).machine :=
  ((readyCursor ready).request epsilonSq positive count).exact

end CCL.ProgressivePartialLogQuotient
