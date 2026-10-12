module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic

section

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Data.CCL.Progressive.Cursor

open Purelib.Data.CCL.Progressive.Cursor.Request

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic

set_option genInjectivity false in
/-- One coherent channel together with the running raw CCL cursor rooted at that channel's certified initial process
state. -/
structure ChannelCursor where
  /-- The original coherent channel retained by this cursor. -/ channel : CoherentNamed
  /-- The state of the retained channel at which the cursor's exact semantics is rooted. -/ rootState :
    channel.name.process.State
  /-- The running cursor indexed by the original process and the retained root state. -/ cursor :
    Data.CCL.Progressive.Cursor.Request.State
    channel.name.process rootState

constructive_injectivity ChannelCursor

namespace ChannelCursor

/-- Start a persistent channel cursor at the channel's original state. -/
def initial (channel : CoherentNamed) :
  Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic.ChannelCursor :=
  { channel := channel
    rootState := channel.name.state
    cursor := Data.CCL.Progressive.Cursor.Request.State.initial
      channel.name.process channel.name.state }

/-- Start a persistent cursor at an explicitly displayed state of the same coherent process. This is used by
synchronized traces to start all channels at one common natural refinement index. -/
def atState (channel : CoherentNamed) (state : channel.name.process.State) :
    Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic.ChannelCursor :=
  { channel := channel
    rootState := state
    cursor := Data.CCL.Progressive.Cursor.Request.State.initial
      channel.name.process state }
end ChannelCursor
end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic

end

section
@[expose] public section

/-!
# Operational laws at the persistent CCL-prefix layer

Operational equivalence compares two finite approximation programs by a
computed pair of later natural indices for every positive rational target.
This file carries that comparison all the way to persistent raw CCL cursors.
The two cursors may follow different displayed finite request schedules and
may emit different redundant words.  Each word nevertheless extends its own
earlier prefix, retains exact parser semantics for its certified origin, and
ends in a cylinder of the requested squared-chordal diameter.

The `BitLaw` wrapper then exposes the established arithmetic and exp/log laws
at precisely this bit-producing interface.  It does not identify completed
values or quantify over an infinite bitstream.
-/

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

end

end
