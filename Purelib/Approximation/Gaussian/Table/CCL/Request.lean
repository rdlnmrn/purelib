module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Table.Basic
public import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Table
open Purelib.Data.CCL.Transducer.Machine
open Purelib.Data.Rat

section
public section

namespace Purelib.Approximation.Gaussian.Table.CCL.Request

/-!
# Joint finite requests for coherent CCL tables

Higher jets, local polynomial models, and finite-dimensional directional data
all consist of a displayed finite list of coherent CCL channels.  This module
computes one rational request shared by every list entry.  Membership in the
finite list is enough to recover strict enclosure and semantic-allowance
bounds, persistent prefix growth, and exact parser semantics for that entry.

The recursion is over the displayed list.  There is no unbounded coordinate
space, infimum, completed vector, or quantified family of all coefficients.
-/

/-- The complete enclosure-and-CCL-output proposition for one channel at a table's shared request. -/
@[expose] def RequestContract (channels : List CoherentNamed) (channel :
  CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) : Prop :=
    let named := Request.sharedName channels channel target positive
    (named.process.ball named.state).radiusSq < target ∧
      channel.coherent.allowance named.state < target ∧
      named.machine.emitted.IsPrefix
        (Advance.advance
          named.machine count).emitted ∧
      (Advance.advance
        named.machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        named.process named.state
        (Advance.advance named.machine count)

/-- One finite member receives the complete enclosure-and-CCL-output contract at the table's shared request. -/
theorem sharedName_bitstream_and_allowance (channels : List CoherentNamed)
    {channel : CoherentNamed} (member : channel ∈ channels)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    RequestContract channels channel target positive count := by
  let named := Request.sharedName channels channel target positive
  exact
    ⟨Request.sharedName_radius_lt channels channel positive,
      Request.sharedName_allowance_lt channels member positive,
      (named.productive count).1, (named.productive count).2,
      CCL.Semantics.Named.advance_exact
        named count⟩

end Purelib.Approximation.Gaussian.Table.CCL.Request

section

namespace Purelib.Approximation.Gaussian.Table.Basic.ChannelTable

open Purelib.Approximation.Gaussian.Table.CCL

/-- Every displayed table member satisfies the complete same-budget finite contract. -/
theorem member_bitstream_and_allowance (table :
  Gaussian.Table.Basic.ChannelTable)
    {channel : CoherentNamed} (member : channel ∈ table.channels)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Request.RequestContract table.channels channel target positive count :=
  Request.sharedName_bitstream_and_allowance table.channels member target positive
    count

end Purelib.Approximation.Gaussian.Table.Basic.ChannelTable

end

end

public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

end

end

end
