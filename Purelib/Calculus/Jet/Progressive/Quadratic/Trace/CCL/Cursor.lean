module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Table
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Projection

open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic (ChannelCursor)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

open Purelib.Approximation.Gaussian.Name.Coherent.CCL
open Purelib.Data
/-- Initialize the five projected CCL cursors at one common trace index.

The table orders increment, base, output, slope and remainder channels. Each channel uses its own process-state
representation of the same supplied natural index. -/
def cursorTableAt {increment : Nat →
  Gaussian.Basic.Canonical} (trace : Trace increment)
    (index : Nat) : Table.TableCursor :=
  ⟨[ChannelCursor.atState
      trace.incrementChannel (trace.incrementState index),
    ChannelCursor.atState
      trace.baseChannel (trace.baseState index),
    ChannelCursor.atState
      trace.outputChannel (trace.outputState index),
    ChannelCursor.atState
      trace.slopeChannel (trace.slopeState index),
    ChannelCursor.atState
      trace.remainderChannel (trace.remainderState index)]⟩

/-- The cursor table at any index retains the trace's five channels in their displayed order.

Each original channel is paired with its indexed cursor state; reading the table channels preserves the complete
original channel list. -/
@[simp] theorem cursorTableAt_channels {increment :
  Nat → Gaussian.Basic.Canonical}
    (trace : Trace increment) (index : Nat) :
    (trace.cursorTableAt index).channels = trace.channels := by
  simp only [cursorTableAt,
    Table.TableCursor.channels,
    Trace.channels, List.map,
    ChannelCursor.atState, -eq_self, -iff_self]
  rfl
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
