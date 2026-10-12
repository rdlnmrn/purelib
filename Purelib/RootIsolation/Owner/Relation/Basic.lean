module

public import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Local.Basic
public import Purelib.Approximation.Relation.Fibre
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Relation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Separation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Root witnesses on original local owners

The original polynomial and displayed rational box index a retained local winding-one owner. Its exact box equality
identifies that same owner as the witness for the displayed finite fibre.
-/

public section

namespace Purelib.RootIsolation.Owner.Relation.Basic

set_option genInjectivity false in
/-- Relation witness attached to one displayed owner box.

The original polynomial and displayed rational box index a retained local winding-one owner. Its exact box equality
identifies that same owner as the witness for the displayed finite fibre. -/
structure RootWitness (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
  Box) where
  /-- The retained local owner for the original polynomial. -/ owner : Owner.Local.Basic.LocalOwner polynomial
  /-- The retained owner's box is exactly the displayed fibre witness box. -/ owner_box : owner.box = box

constructive_injectivity RootWitness

/-- A pairwise-separated local owner family as one displayed finite fibre.

The original family count indexes the same owner boxes and exact owner-box witnesses. Its pairwise separation evidence
supplies the retained finite fibre relation without choosing new owners. -/
@[expose] def ownerFibre {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {count : Nat}
    (family : Owner.Family.Basic.OwnerFamily polynomial count) :
    Approximation.Relation.Fibre Box Box.Relation.BoxSeparated (Owner.Relation.Basic.RootWitness
      polynomial) :=
  Approximation.Relation.Fibre.ofPairwiseSeparated count
    (fun label => (family.owner label).box)
    (fun label => ⟨family.owner label, rfl⟩)
    (fun left right different =>
      ⟨family.pairwiseSeparated left right different⟩)

/-- The finite owner fibre preserves the original displayed family count. -/
@[simp] theorem ownerFibre_count
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count : Nat}
    (family : Owner.Family.Basic.OwnerFamily polynomial count) :
    (Owner.Relation.Basic.ownerFibre family).count = count := rfl

end Purelib.RootIsolation.Owner.Relation.Basic

end
