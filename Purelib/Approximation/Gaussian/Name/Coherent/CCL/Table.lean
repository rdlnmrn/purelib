module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.List.Map
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CCL

open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.List

open Purelib.Data.Rat

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table

set_option genInjectivity false in
/-- Running cursors for one explicitly displayed finite channel table. -/
structure TableCursor where
  /-- The displayed finite list of persistent coherent channel cursors. -/ entries : List Cursor.Basic.ChannelCursor

constructive_injectivity TableCursor

namespace TableCursor

/-- Read the original coherent channel from each retained table entry. -/
def channels (state :
  Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor) : List Coherent.CoherentNamed :=
  state.entries.map ChannelCursor.channel

/-- Start one persistent cursor at the original state of every displayed coherent channel. -/
def initial (channels : List
  CoherentNamed) : Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor :=
  ⟨channels.map ChannelCursor.initial⟩

/-- Make the same finite accuracy and bit-growth request of every displayed table entry. -/
def request (state :
  Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) : Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor :=
  ⟨state.entries.map
    (fun entry => entry.request epsilonSq positive count)⟩

/-- Starting a table of cursors preserves the exact original channel list. -/
@[simp] theorem initial_channels (source :
  List CoherentNamed) :
    (Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor.initial source).channels = source := by
  simp only [Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor.initial,
    Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor.channels, Map.map_map, Function.comp_def,
    ChannelCursor.initial, -eq_self, -iff_self]
  induction source with
  | nil => rfl
  | cons channel channels inductionHypothesis =>
      rw [List.map_cons, inductionHypothesis]

/-- A shared finite table request preserves the exact original channel list. -/
@[simp] theorem request_channels (state :
  Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).channels = state.channels := by
  unfold Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor.request
    Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor.channels
  simp only [Map.map_map, Function.comp_def, ChannelCursor.request, -eq_self, -iff_self]
  rfl

/-- A shared finite table request preserves the number of retained cursor entries. -/
@[simp] theorem request_length (state :
  Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).entries.length =
      state.entries.length := by
  simp only [Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor.request, Map.length_map, -eq_self, -iff_self]
  rfl

/-- The exact updated entry corresponding to every old displayed member is present in the returned finite table. -/
theorem requested_entry_mem (state :
  Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor) {entry : Cursor.Basic.ChannelCursor}
    (member : entry ∈ state.entries) (epsilonSq : Fraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    entry.request epsilonSq positive count ∈
      (state.request epsilonSq positive count).entries := by
  exact Map.mem_map.mpr ⟨entry, member, rfl⟩

/-- Per-entry persistent output contract for a finite table request. -/
theorem member_word_extends_and_grows (state :
  Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor)
    {entry : Cursor.Basic.ChannelCursor} (member : entry ∈ state.entries)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    entry.request epsilonSq positive count ∈
        (state.request epsilonSq positive count).entries ∧
      entry.cursor.machine.emitted.IsPrefix
        (entry.request epsilonSq positive count).cursor.machine.emitted ∧
      (entry.request epsilonSq positive count).cursor.machine.emitted.length =
        entry.cursor.machine.emitted.length + count ∧
      Semantics.Basic.ExactCursor
        entry.channel.name.process entry.rootState
        (entry.request epsilonSq positive count).cursor.machine :=
  ⟨state.requested_entry_mem member epsilonSq positive count,
    entry.request_word_extends epsilonSq positive count,
    entry.request_word_length epsilonSq positive count,
    entry.request_exact epsilonSq positive count⟩

/-- Successive table requests preserve all old channels and extend the already-emitted word of every current entry. -/
theorem successive_member_extends (state :
  Approximation.Gaussian.Name.Coherent.CCL.Table.TableCursor)
    {entry : Cursor.Basic.ChannelCursor} (member : entry ∈ state.entries)
    (firstTarget : Fraction.Rational) (firstPositive : 0 < firstTarget)
    (firstCount : Nat) (secondTarget : Fraction.Rational)
    (secondPositive : 0 < secondTarget) (secondCount : Nat) :
    let first := entry.request firstTarget firstPositive firstCount
    first ∈ (state.request firstTarget firstPositive firstCount).entries ∧
      first.cursor.machine.emitted.IsPrefix
        (first.request secondTarget secondPositive secondCount).cursor.machine.emitted :=
  ⟨state.requested_entry_mem member firstTarget firstPositive firstCount,
    (entry.request firstTarget firstPositive firstCount).request_word_extends
      secondTarget secondPositive secondCount⟩

end TableCursor
end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table

end

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.CCL.Progressive.QuadraticTrace
end Purelib.CCL.Progressive.QuadraticTrace

end

public section
namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table

end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table
end
