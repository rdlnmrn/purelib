module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Tactic.Ring
public import Purelib.Geometry.Rational.Box.Separation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Indexed families of local root owners

A finite family keeps the actual local owner at every displayed index and
positive separation of the retained boxes at distinct indices. The polynomial
and count remain the original correctness-bearing parameters of the family.
-/

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- An explicitly indexed, pairwise-separated family of local root owners.

Each original finite index retains its actual local owner for the same
polynomial. The displayed separation certificate compares their retained
boxes whenever those original indices differ. -/
public structure OwnerFamily (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (count :
  Nat) where
  /-- The retained local owner at each original finite index. -/ owner : Fin count → Owner.Local.Basic.LocalOwner p
  /-- Distinct original indices have separated retained owner boxes. -/ pairwiseSeparated : ∀ left right, left ≠ right →
    (owner left).box.Separated (owner right).box

constructive_injectivity OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic
