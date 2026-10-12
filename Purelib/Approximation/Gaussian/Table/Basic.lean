module

public import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Table.Basic

set_option genInjectivity false in
/-- A displayed finite coefficient or coordinate table. -/
structure ChannelTable where
  /-- The displayed finite list of coherent Gaussian coefficient or coordinate channels. -/ channels : List
    CoherentNamed

constructive_injectivity ChannelTable

namespace ChannelTable

/-- The number of channels in the retained finite table. -/
def length (table :
  Approximation.Gaussian.Table.Basic.ChannelTable) : Nat := table.channels.length
end ChannelTable

end Purelib.Approximation.Gaussian.Table.Basic

end
