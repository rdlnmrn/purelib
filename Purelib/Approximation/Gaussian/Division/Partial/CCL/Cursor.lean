module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Division.Partial (Ready)
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (State)

open Purelib

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.CCL.Progressive.Cursor.Request

open Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Persistent output after retryable division preflight

Readiness returns an ordinary coherent name unchanged.  Consequently the
existing persistent cursor supplies exact raw-parser semantics, prefix
extension, and finite request lengths without any weakened partial variant.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial.CCL.Cursor

/-- Start the unchanged persistent output path once preflight is ready. -/
def readyCursor {numerator denominator :
  Coherent.CoherentNamed}
    {state : State denominator} {output : Coherent.CoherentNamed}
    (_ready : Ready numerator denominator state output) :
    Data.CCL.Progressive.Cursor.Request.State output.name.process output.name.state :=
  Data.CCL.Progressive.Cursor.Request.State.initial
    output.name.process output.name.state

/-- The initial ready cursor already has exact parser semantics relative to the returned quotient's certified source
state. -/
theorem readyCursor_exact {numerator denominator :
  Coherent.CoherentNamed}
    {state : State denominator} {output : Coherent.CoherentNamed}
    (ready : Ready numerator denominator state output) :
    ExactCursor output.name.process output.name.state
      (readyCursor ready).machine :=
  (readyCursor ready).exact

/-- A finite request after readiness appends exactly `count` bits. -/
theorem readyCursor_request_length
    {numerator denominator : Coherent.CoherentNamed}
    {state : State denominator} {output : Coherent.CoherentNamed}
    (ready : Ready numerator denominator state output)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor ready).request epsilonSq positive
      count).machine.emitted.length =
      (readyCursor ready).machine.emitted.length + count :=
  (readyCursor ready).request_length epsilonSq positive count

/-- A finite request after readiness never retracts the existing raw prefix. -/
theorem readyCursor_request_extends
    {numerator denominator : Coherent.CoherentNamed}
    {state : State denominator} {output : Coherent.CoherentNamed}
    (ready : Ready numerator denominator state output)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    (readyCursor ready).machine.emitted.IsPrefix
      ((readyCursor ready).request epsilonSq positive
        count).machine.emitted :=
  (readyCursor ready).request_extends epsilonSq positive count

/-- Exact parser semantics survives every finite post-readiness request. -/
theorem readyCursor_request_exact
    {numerator denominator : Coherent.CoherentNamed}
    {state : State denominator} {output : Coherent.CoherentNamed}
    (ready : Ready numerator denominator state output)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    ExactCursor output.name.process output.name.state
      ((readyCursor ready).request epsilonSq positive count).machine
        :=
  ((readyCursor ready).request epsilonSq positive count).exact

end Purelib.Approximation.Gaussian.Division.Partial.CCL.Cursor

end
