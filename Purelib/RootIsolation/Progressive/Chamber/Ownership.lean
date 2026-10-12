module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.History
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.Progressive.Chamber.Continuation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.State
import Purelib.RootIsolation.Progressive.Continuation.Basic

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Progressive.Chamber.Ownership
open Purelib.Data.Gaussian

/-! ## Effective algebraic closure on the certified simple-root locus -/

set_option genInjectivity false in
/-- Finite unique-index ownership of a rational box by one chamber seed. -/
structure ChamberOwnership
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} (chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference)
    (box : Box) where
  /-- The original finite chamber index owning the supplied box. -/ owner : chamber.Index
  /-- The supplied box refines the seed box at this exact owner index. -/ refines : box.Refines (chamber.owners.owner
    owner).box
  /-- Any seed box refined by the supplied box has the same retained owner index. -/ unique : ∀ candidate :
    chamber.Index,
    box.Refines (chamber.owners.owner candidate).box → candidate = owner

constructive_injectivity ChamberOwnership

end Purelib.RootIsolation.Progressive.Chamber.Ownership

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic.SimpleRootChamber
open Purelib.Data.Gaussian

/-- Every live owner of the executable continuation retains its original and
uniquely determined finite owner index. -/
def ownershipAt
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} (chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference)
    (history : Progressive.Chamber.History.ChamberRequestHistory) (index : chamber.Index) :
    Progressive.Chamber.Ownership.ChamberOwnership chamber
      (chamber.continuation.box history index) where
  owner := index
  refines := (chamber.run history).refinesSeed index
  unique := by
    intro candidate candidateRefines
    by_cases equal : candidate = index
    · exact equal
    · have separated := chamber.owners.pairwiseSeparated candidate index equal
      have distinct := separated.points_ne
        (candidateRefines.contains
          (chamber.continuation.box history index).contains_anchor)
        ((chamber.run history).refinesSeed index |>.contains
          (chamber.continuation.box history index).contains_anchor)
      exact (distinct rfl).elim

end Purelib.RootIsolation.Progressive.Chamber.Basic.SimpleRootChamber

end
