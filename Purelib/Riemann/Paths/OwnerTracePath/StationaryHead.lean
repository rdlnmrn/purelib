module

public import Purelib.Riemann.Paths.OwnerTracePath.Stationary
public import Purelib.Riemann.Paths.OwnerTracePath.Suffix

/-! # Signed agreement at the actual stationary head of an OwnerPath

The exact dropLink equation identifies the same materialized head and tail.
When that actual link has equal physical endpoints, its retained realization
certificates derive original root-name agreement. No join or continuation
factory is reconstructed.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)

/-- Compare the two original Owners of an actual stationary head, retaining its complete signed link evidence.

The supplied Option equation comes from the literal materialized path.
The endpoint equality only specializes that retained link to the same
physical point; its own realized root displacement supplies signed agreement.
-/
def stationaryHeadEquivalent {polynomial : GaussianPolynomial}
    {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)}
    (path : OwnerPath polynomial start first finish last) (suffix : Suffix last)
    (present : path.dropLink = some suffix) (same : suffix.point = start) :
    NamedEquivalent (ownerName first) (ownerName suffix.owner) :=
  OwnerPath.casesOn
    (motive := fun start first finish last path =>
      (suffix : Suffix (finish := finish) last) → path.dropLink = some suffix →
      suffix.point = start → NamedEquivalent (ownerName first) (ownerName suffix.owner))
    path
    (fun _ _ _ present _ => False.elim (by cases present))
    (fun {_start middle _finish _first center last} link tail suffix present same => by
      have equal : (⟨middle, center, tail⟩ : Suffix last) = suffix := Option.some.inj present
      cases equal
      cases same
      exact link.equivalentStationary)
    suffix present same

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
