module

import Purelib.Approximation.Gaussian.Name.CCL.Semantics
public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Continuation.Basic
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.Progressive.Continuation.Approximation
import Purelib.Data.CCL.Progressive.Cursor.Image
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.CCL.Transducer (Machine)
open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- Start the persistent raw-word cursor for one owner. -/
def rootCursorAt
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) :
    Data.CCL.Progressive.Cursor.Request.State
      (continuation.toProcess index) continuation.initial :=
  Data.CCL.Progressive.Cursor.Request.State.initial
    (continuation.toProcess index) continuation.initial
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- Any two possible values after a root-cursor request have squared chordal distance at most the requested bound. -/
theorem rootCursorAt_request_chordalSq_le
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat)
    {left right : Gaussian.Basic.Canonical}
    (leftPossible : Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
      ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.mode left)
    (rightPossible : Data.CCL.Transducer.Mode.Semantics.SemanticMode.possible
      ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.mode right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (Data.CCL.Progressive.Cursor.Image.Machine.image ((continuation.rootCursorAt index).request
          epsilonSq positive count).machine left)
        (Data.CCL.Progressive.Cursor.Image.Machine.image ((continuation.rootCursorAt index).request
          epsilonSq positive count).machine right) ≤ epsilonSq :=
  (continuation.rootCursorAt index).request_pair_chordalSq_le
    epsilonSq positive count leftPossible rightPossible

end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- A root-cursor request preserves the previously emitted raw prefix. -/
theorem rootCursorAt_request_extends
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    (continuation.rootCursorAt index).machine.emitted.IsPrefix
      ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.emitted :=
  (continuation.rootCursorAt index).request_extends
    epsilonSq positive count
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- A fresh root cursor emits exactly the requested number of raw bits. -/
theorem rootCursorAt_request_length
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((continuation.rootCursorAt index).request
        epsilonSq positive count).machine.emitted.length = count := by
  have length := (continuation.rootCursorAt index).request_length
    epsilonSq positive count
  have initialLength :
      (continuation.rootCursorAt index).machine.emitted.length = 0 := rfl
  rw [initialLength, Nat.zero_add] at length
  exact length
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- Every finite advance of the retained root name remains an exact cursor for its original process and initial state.
-/
theorem rootNameAt_exact
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) (count : Nat) :
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      (continuation.toProcess index) continuation.initial
      (Machine.Advance.advance
        (continuation.rootNameAt index).machine count) :=
  open Purelib.Approximation.Gaussian in Name.CCL.Semantics.Named.advance_exact
    (continuation.rootNameAt index) count
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Continuation.Basic
open Purelib.Data.Gaussian
namespace RootContinuation

/-- Advancing a fresh root name preserves its prefix and emits exactly the requested number of bits. -/
theorem rootNameAt_productive
    {initialTable : CoefficientTable}
    (continuation : Progressive.Continuation.Basic.RootContinuation initialTable)
    (index : continuation.Index) (count : Nat) :
    (continuation.rootNameAt index).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (continuation.rootNameAt index).machine count).emitted ∧
      (Machine.Advance.advance
          (continuation.rootNameAt index).machine count).emitted.length =
        count :=
  (continuation.rootNameAt index).productive count
end RootContinuation

end Purelib.RootIsolation.Progressive.Continuation.Basic

end
