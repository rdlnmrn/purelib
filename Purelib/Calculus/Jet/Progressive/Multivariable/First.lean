module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Table.LinearCombination
public import Purelib.Approximation.Gaussian.Table.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Calculus.Jet.Progressive.Multivariable.First

set_option genInjectivity false in
open Purelib.Approximation.Gaussian in
/-- A coherent Gaussian value channel with a finite list of coherent partial channels.

The list length is the displayed dimension. This record retains the channels themselves; it carries no differentiation
relation between the value and partials. -/
structure MultivariableFirstJet where
  /-- The retained coherent value channel. -/ value : CoherentNamed
  /-- The ordered finite list of coherent partial-coefficient channels. -/ partials : List
    CoherentNamed

constructive_injectivity MultivariableFirstJet

namespace MultivariableFirstJet

open Purelib.Calculus.Jet.Progressive.Multivariable.First in
/-- Count the retained partial-coefficient channels. -/
def dimension (jet :
  MultivariableFirstJet) : Nat := jet.partials.length

section
open Purelib.Approximation.Gaussian
open Purelib.Calculus.Jet.Progressive.Multivariable.First
/-- Package the value channel followed by all partial channels into one finite table. -/
def table (jet :
  MultivariableFirstJet) : Table.Basic.ChannelTable :=
  ⟨jet.value :: jet.partials⟩

/-- Retain a value channel with the requested number of exact zero partial channels. -/
def constant (dimension : Nat) (value
  : CoherentNamed) :
    MultivariableFirstJet :=
  ⟨value, List.replicate dimension (CoherentNamed.Coherence.exact 0)⟩

/-- Add two progressive values and their finite partial-channel lists.

Partial channels are added entrywise, retaining any unmatched tail according to the finite list addition convention. -/
def add (left right :
  MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨CoherentNamed.add left.value right.value,
    Table.LinearCombination.addPartials left.partials right.partials⟩

/-- Negate the value channel and each retained partial channel. -/
def neg (jet : MultivariableFirstJet)
  : MultivariableFirstJet :=
  ⟨CoherentNamed.neg jet.value, jet.partials.map
    CoherentNamed.neg⟩

/-- Build the finite product rule for progressive value and partial channels.

Scale each partial list by the other value channel, then combine the lists by the retained channel addition operation.
-/
def mul (left right :
  MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨CoherentNamed.mul left.value right.value,
    Table.LinearCombination.addPartials (Table.LinearCombination.scalePartials right.value left.partials)
      (Table.LinearCombination.scalePartials left.value right.partials)⟩

/-- Combine an outer value and slope channel with an inner partial table.

The result retains the supplied outer value and scales the inner partials by the outer slope. The constructor does not
require a relation between the outer data and the inner value. -/
def compose (outerValue outerSlope :
  CoherentNamed)
    (inner : MultivariableFirstJet) : MultivariableFirstJet :=
  ⟨outerValue, Table.LinearCombination.scalePartials outerSlope inner.partials⟩

end

open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.Multivariable.First in
/-- The direction list has the same length as the retained partial-channel list. -/
def DirectionValid (jet :
  MultivariableFirstJet)
    (direction : List Gaussian.Basic.Canonical) : Prop :=
  direction.length = jet.dimension

open Purelib.Approximation.Gaussian in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.Multivariable.First in
/-- Form the finite directional channel with certified matching dimensions.

The length premise ensures that each partial channel has a corresponding displayed Gaussian direction coordinate. The
underlying finite recursion remains total. -/
def directional (jet :
  MultivariableFirstJet) (direction : List Gaussian.Basic.Canonical)
    (_valid : jet.DirectionValid direction) : CoherentNamed :=
  Table.LinearCombination.directionalSum jet.partials direction
end MultivariableFirstJet

end Purelib.Calculus.Jet.Progressive.Multivariable.First

end
