module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Logarithm.Quotient (Client Ready)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Quotient

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.CCL.Progressive.Cursor

open Purelib.Data.CCL.Progressive.Cursor.Request

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Persistent output after dependency scheduling

Once both partial children of `log(1 + z) / z` are ready, the scheduler returns
an ordinary coherent name.  The unchanged persistent cursor therefore supplies
the standard finite prefix and parser contracts.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient.CCL.Cursor

/-- Start a persistent cursor at the original output state of the certified ready logarithm quotient. -/
def readyCursor {client :
    Client} {output :
  Coherent.CoherentNamed}
    (_ready : Ready client output) :
    Data.CCL.Progressive.Cursor.Request.State output.name.process output.name.state :=
  Data.CCL.Progressive.Cursor.Request.State.initial output.name.process output.name.state

/-- The ready quotient cursor has exact parser semantics at its original output state. -/
theorem readyCursor_exact {client :
    Client}
  {output : Coherent.CoherentNamed}
    (ready : Ready client output) :
    Semantics.Basic.ExactCursor output.name.process output.name.state
      (readyCursor ready).machine :=
  (readyCursor ready).exact

/-- A finite request on the ready quotient cursor appends exactly the requested number of bits. -/
theorem readyCursor_request_length {client :
  Client} {output : Coherent.CoherentNamed}
    (ready : Ready client output) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor ready).request epsilonSq positive
      count).machine.emitted.length =
      (readyCursor ready).machine.emitted.length + count :=
  (readyCursor ready).request_length epsilonSq positive count

/-- A finite request on the ready quotient cursor extends its existing raw prefix. -/
theorem readyCursor_request_extends {client :
  Client} {output : Coherent.CoherentNamed}
    (ready : Ready client output) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    (readyCursor ready).machine.emitted.IsPrefix
      ((readyCursor ready).request epsilonSq positive
        count).machine.emitted :=
  (readyCursor ready).request_extends epsilonSq positive count

/-- A finite request preserves the ready quotient cursor's exact parser semantics. -/
theorem readyCursor_request_exact {client :
  Client} {output : Coherent.CoherentNamed}
    (ready : Ready client output) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    Semantics.Basic.ExactCursor output.name.process output.name.state
      ((readyCursor ready).request epsilonSq positive
        count).machine :=
  ((readyCursor ready).request epsilonSq positive count).exact

end Purelib.Approximation.Gaussian.Logarithm.Quotient.CCL.Cursor

end
