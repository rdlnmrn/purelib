module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic

open Purelib
open Purelib.Approximation.Gaussian.Name.Coherent.CCL
open Purelib.Data.CCL.Encoding.Parser
open Purelib.Data.CCL.Progressive.Cursor.Image
open Purelib.Data.CCL.Transducer.Machine
open Purelib.Data.CCL.Transducer.Machine.Committed
open Purelib.Data.CCL.Transducer.Mode.Semantics
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Geometry.Projective.Line

public section

/-!
# Persistent CCL cursors for finite progressive calculus tables

The joint-request modules prove that every channel can emit a requested finite
prefix.  This module retains those cursors between requests.  A table state is
one displayed finite list of proof-bearing cursors; requesting more accuracy
and more bits maps the ordinary persistent CCL request over that list.  Hence
later words extend earlier words instead of restarting an encoder.

There is no stream or completed table.  Every operation consumes and returns
one finite list and one natural number of additional bits.
-/

namespace ChannelCursor

/-- Append `count` bits to the existing word, then refine the same live quantitative sidecar to the displayed
squared-chordal target. -/
@[expose] def request (state :
  Cursor.Basic.ChannelCursor) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) : Cursor.Basic.ChannelCursor :=
  { channel := state.channel
    rootState := state.rootState
    cursor := state.cursor.request epsilonSq positive count }

/-- A persistent finite request retains the original coherent channel. -/
@[simp] theorem request_channel
  (state : Cursor.Basic.ChannelCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).channel = state.channel := rfl

/-- A persistent finite request extends the cursor's previously emitted raw word. -/
theorem request_word_extends (state :
  Cursor.Basic.ChannelCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    state.cursor.machine.emitted.IsPrefix
      (state.request epsilonSq positive count).cursor.machine.emitted :=
  state.cursor.request_extends epsilonSq positive count

/-- A persistent finite request appends exactly the supplied number of raw bits. -/
theorem request_word_length (state :
  Cursor.Basic.ChannelCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).cursor.machine.emitted.length =
      state.cursor.machine.emitted.length + count :=
  state.cursor.request_length epsilonSq positive count

/-- The refined raw prefix still has exact parser semantics for the original certified channel state. -/
theorem request_exact (state :
  Cursor.Basic.ChannelCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    Semantics.Basic.ExactCursor
      state.channel.name.process state.rootState
      (state.request epsilonSq positive count).cursor.machine :=
  (state.request epsilonSq positive count).cursor.exact

/-- Thus every tail admitted by the later prefix reconstructs an explicitly possible reading of the original coherent
channel. -/
theorem request_represents_origin
  (state : Cursor.Basic.ChannelCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat)
    {tail : Canonical}
    (possible : SemanticMode.possible
      (state.request epsilonSq positive count).cursor.machine.mode tail) :
    ∃ value : Canonical,
      state.channel.name.process.Possible state.rootState value ∧
        (Line.Matrix.act
          (State.parse
            (Data.CCL.Transducer.Machine.committed
              (state.request epsilonSq positive count).cursor.machine)).matrix
          (SemanticMode.parserTail
            (state.request epsilonSq positive count).cursor.machine.mode tail)).Equivalent
          (Proj.affine value) :=
  (state.request_exact epsilonSq positive count).exact possible

/-- Every two readings still admitted by the later prefix lie in a squared-chordal cylinder of the requested diameter.
-/
theorem request_pair_chordalSq_le
  (state : Cursor.Basic.ChannelCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat)
    {left right : Canonical}
    (leftPossible : SemanticMode.possible
      (state.request epsilonSq positive count).cursor.machine.mode left)
    (rightPossible : SemanticMode.possible
      (state.request epsilonSq positive count).cursor.machine.mode right) :
    Chordal.Basic.chordalSq
        (Machine.image (state.request epsilonSq positive count).cursor.machine left)
        (Machine.image (state.request epsilonSq positive count).cursor.machine right) ≤
      epsilonSq :=
  state.cursor.request_pair_chordalSq_le epsilonSq positive count
    leftPossible rightPossible

/-- A one-bit request is always another finite productive step. -/
theorem request_one_grows (state :
  Cursor.Basic.ChannelCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    (state.request epsilonSq positive 1).cursor.machine.emitted.length =
      state.cursor.machine.emitted.length + 1 :=
  state.request_word_length epsilonSq positive 1
end ChannelCursor

end

end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
