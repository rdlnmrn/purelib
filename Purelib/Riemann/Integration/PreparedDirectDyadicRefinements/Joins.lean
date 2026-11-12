module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
public import Purelib.Riemann.Paths.OwnerTracePath.Join
import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Approximation.Gaussian.Equivalence

/-! # Actual Point-owner joins across original centered-parent boundaries

The original centered chain supplies only the coordinate identity. Its
separate original RootChain supplies the signed finish-to-start relation.
The two retained direct Queries and endpoint OwnerJoins attach the actual
physical Owners to that relation. No Point, Query, parent preparation or
primitive observation is executed again.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent next : CenteredEdge curve differential} {remaining : List (CenteredEdge curve differential)}
variable {start finish : LiftedPoint 2} {firstName lastName : Named}
variable {upper lower : Rational} {upperInside : 0 ≤ upper ∧ upper ≤ 1} {lowerInside : 0 ≤ lower ∧ lower ≤ 1}
variable (geometry : CenteredPathChain (parent :: next :: remaining) (start := start) (finish := finish))
variable (roots : RootChain (parent :: next :: remaining) firstName lastName)
variable (upperRole : upper = 1) (lowerRole : lower = 0)
variable {left : Owner (curve.polynomial.eval (parent.edge.point upper))}
variable {right : Owner (curve.polynomial.eval (next.edge.point lower))}
variable (beforeQuery : PreparedEdge.Query parent.edge upper upperInside)
variable (afterQuery : PreparedEdge.Query next.edge lower lowerInside)
variable (beforeJoin : OwnerJoin beforeQuery.owner left) (afterJoin : OwnerJoin right afterQuery.owner)

include geometry upperRole lowerRole in
/-- The original ordered centered chain identifies the two actual parent-boundary coordinates. -/
theorem nextPoint_eq : parent.edge.point upper = next.edge.point lower :=
  (congrArg parent.edge.point upperRole).trans
    (parent.edge.point_one.trans
      ((congrArg LiftedPoint.coordinate geometry.remaining.start_eq).symm.trans
        (next.edge.point_zero.symm.trans (congrArg next.edge.point lowerRole.symm))))

/-- The original adjacent root link and both retained Query joins compare the actual physical Point Owners.

Each endpoint first follows its own original direct Query. Exact scalar
fraction equalities only reindex those original query generators. The
actual RootChain.nextEquivalent is the independent signed root evidence;
coordinate equality does not supply that evidence.
-/
def nextPointEquivalent : NamedEquivalent (ownerName left) (ownerName right) :=
  let before := NamedEquivalent.transport rfl beforeQuery.name_eq.symm beforeJoin.equivalent.symm
  let beforeOne := NamedEquivalent.transport rfl (parent.edge.rootName_eq upperRole) before
  let after := NamedEquivalent.transport afterQuery.name_eq.symm rfl afterJoin.equivalent.symm
  let afterZero := NamedEquivalent.transport (next.edge.rootName_eq lowerRole) rfl after
  beforeOne.trans (roots.nextEquivalent.trans afterZero)

/-- The original endpoint/chain caches with their derived signed relation and actual boundary join and link.

The original Owners occur as whole retained values too. The single new
OwnerJoin transports only the left Owner's coordinate index. Its exact
factory certificate uses the derived signed relation; the stationary link
continues to carry both original coordinate and Owner indices.
-/
@[expose] def QueryJunction :=
    Σ _original : {value :
        (Owner (curve.polynomial.eval (parent.edge.point upper)) ×
          Owner (curve.polynomial.eval (next.edge.point lower))) ×
        (PreparedEdge.Query parent.edge upper upperInside × PreparedEdge.Query next.edge lower lowerInside) ×
        (OwnerJoin beforeQuery.owner left × OwnerJoin right afterQuery.owner) ×
        (CenteredPathChain (parent :: next :: remaining) (start := start) (finish := finish) ×
          RootChain (parent :: next :: remaining) firstName lastName) //
      value = ((left, right), (beforeQuery, afterQuery), (beforeJoin, afterJoin), (geometry, roots))},
    Σ equivalent : {value : NamedEquivalent (ownerName left) (ownerName right) //
      value = nextPointEquivalent roots upperRole lowerRole beforeQuery afterQuery beforeJoin afterJoin},
    Σ joined : {value : OwnerJoin
        (castOwnerParameter (congrArg curve.polynomial.eval (nextPoint_eq geometry upperRole lowerRole)) left) right //
      value = OwnerJoin.acquireAt (polynomial := curve.polynomial)
        (nextPoint_eq geometry upperRole lowerRole) equivalent.val},
      {link : OwnerLink curve.polynomial (parent.edge.point upper) (next.edge.point lower) left right //
        link = OwnerLink.ofJoinAt (polynomial := curve.polynomial)
          (nextPoint_eq geometry upperRole lowerRole) joined.val}

/-- Acquire the actual boundary join and link once from the retained original endpoint and chain caches. -/
def joinQueries : QueryJunction geometry roots upperRole lowerRole beforeQuery afterQuery beforeJoin afterJoin :=
  let original := ((left, right), (beforeQuery, afterQuery), (beforeJoin, afterJoin), (geometry, roots))
  let equivalent := nextPointEquivalent roots upperRole lowerRole beforeQuery afterQuery beforeJoin afterJoin
  let joined := OwnerJoin.acquireAt (polynomial := curve.polynomial)
    (nextPoint_eq geometry upperRole lowerRole) equivalent
  let link := OwnerLink.ofJoinAt (polynomial := curve.polynomial) (nextPoint_eq geometry upperRole lowerRole) joined
  ⟨⟨original, rfl⟩, ⟨equivalent, rfl⟩, ⟨joined, rfl⟩, ⟨link, rfl⟩⟩

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

end
