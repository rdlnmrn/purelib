import CCL.Persistent.Progressive
import CCL.Progressive.PartialDivision

/-!
# Persistent output after retryable division preflight

Readiness returns an ordinary coherent name unchanged.  Consequently the
existing persistent cursor supplies exact raw-parser semantics, prefix
extension, and finite request lengths without any weakened partial variant.
-/

namespace CCL.ProgressivePartialDivision

abbrev Cursor := CCL.PersistentProgressive.Cursor
abbrev ExactCursor := CCL.ProgressiveMachineSemantics.ExactCursor

/-- Start the unchanged persistent output path once preflight is ready. -/
def readyCursor {numerator denominator : CoherentNamed}
    {state : State denominator} {output : CoherentNamed}
    (_ready : Ready numerator denominator state output) :
    Cursor output.name.process output.name.state :=
  CCL.PersistentProgressive.Cursor.initial
    output.name.process output.name.state

/-- The initial ready cursor already has exact parser semantics relative to
the returned quotient's certified source state. -/
theorem readyCursor_exact {numerator denominator : CoherentNamed}
    {state : State denominator} {output : CoherentNamed}
    (ready : Ready numerator denominator state output) :
    ExactCursor output.name.process output.name.state
      (readyCursor ready).machine :=
  (readyCursor ready).exact

/-- A finite request after readiness appends exactly `count` bits. -/
theorem readyCursor_request_length
    {numerator denominator : CoherentNamed}
    {state : State denominator} {output : CoherentNamed}
    (ready : Ready numerator denominator state output)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor ready).request epsilonSq positive count).machine.emitted.length =
      (readyCursor ready).machine.emitted.length + count :=
  (readyCursor ready).request_length epsilonSq positive count

/-- A finite request after readiness never retracts the existing raw prefix. -/
theorem readyCursor_request_extends
    {numerator denominator : CoherentNamed}
    {state : State denominator} {output : CoherentNamed}
    (ready : Ready numerator denominator state output)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    (readyCursor ready).machine.emitted.IsPrefix
      ((readyCursor ready).request epsilonSq positive count).machine.emitted :=
  (readyCursor ready).request_extends epsilonSq positive count

/-- Exact parser semantics survives every finite post-readiness request. -/
theorem readyCursor_request_exact
    {numerator denominator : CoherentNamed}
    {state : State denominator} {output : CoherentNamed}
    (ready : Ready numerator denominator state output)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    ExactCursor output.name.process output.name.state
      ((readyCursor ready).request epsilonSq positive count).machine :=
  ((readyCursor ready).request epsilonSq positive count).exact

end CCL.ProgressivePartialDivision
