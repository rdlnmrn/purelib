module

public import Purelib.Riemann.Topology.PreparedRefinementRootChains
public import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints.Queries

/-! # Root chains consuming actual given parent endpoint queries

The actual geometric chain and retained RootChildBlock determine every
parent location. The supplied parent query provider is used at every
comparison, so its GIVEN endpoint queries remain the original coarse
endpoint Owners. Newly prepared child queries remain separate inputs.
-/

public section

namespace Purelib.Riemann.Topology.PreparedRefinementRootChains

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge RootChildBlock)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints
  (ParentBudget Queries samePointEquivalentUsing queryEquivalentUsing)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (Location RootSubedgeBlock)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- Construct the actual root chain with GIVEN parent queries and the SAME original child-start/root/geometric spines.

The original start relation is consumed unchanged. Its endpoint relation
uses the existing fixed-budget comparison through the supplied query
providers; no original parent endpoint query is acquired by this fold.
Every child and actual tail remains the supplied original occurrence.
-/
def rootChainUsing {parent : CenteredEdge curve differential} (budget : ParentBudget parent.edge)
    (queries : Queries parent.edge) :
    {children : List (CenteredEdge curve differential)} → {first last : LiftedPoint} →
    DirectPathChain children (start := first) (finish := last) → RootChildBlock parent children →
    (firstLocation : Location parent first.coordinate) → (lastLocation : Location parent last.coordinate) →
      RootChain children (parent.edge.rootName firstLocation.fraction firstLocation.inside)
        (parent.edge.rootName lastLocation.fraction lastLocation.inside)
  | _, _, _, .nil _, .nil, first, last =>
      .nil (samePointEquivalentUsing budget queries
        first.fraction last.fraction first.inside last.inside (first.point_eq.trans last.point_eq.symm))
  | _, _, _, .cons child chain, .cons head roots, first, last =>
      let next := RootSubedgeBlock.startLocation chain roots last
      let childBudget := ParentBudget.acquire child.edge
      let childQueries := Queries.original child.edge
      let endpoint := queryEquivalentUsing budget childBudget
        queries childQueries head 1 (of_decide_eq_true rfl) next.fraction next.inside
          (next.point_eq.trans child.edge.point_one.symm)
      let following := rootChainUsing budget queries chain roots next last
      let entry := (samePointEquivalentUsing budget queries
        first.fraction head.fraction first.inside head.inside
        (first.point_eq.trans (head.point_eq.trans child.edge.point_zero).symm)).trans head.rootEquivalent
      .cons child entry (following.changeStart endpoint.symm)
termination_by structural _ _ _ chain _ _ _ => chain

namespace EndpointSafeBlock

/-- Read the actual block's complete root chain using the SAME supplied parent endpoint-query provider.

Its original ParentBudget, geometric chain and RootChildBlock remain
unchanged. The original coarse endpoint locations are exactly zero and
one. Any supplied cached endpoint Owners are therefore consumed by the
root comparison itself, rather than merely by a later name transport.
-/
def rootChainUsing {parent : CenteredEdge curve differential} (safe : EndpointSafeBlock parent)
    (queries : Queries parent.edge) :
    RootChain safe.block.children (parent.edge.rootName 0 parent.edge.baseInside)
      (parent.edge.rootName 1 (of_decide_eq_true rfl)) :=
  PreparedRefinementRootChains.rootChainUsing safe.budget queries safe.block.chain safe.block.roots
    ⟨0, parent.edge.baseInside, parent.edge.point_zero⟩
    ⟨1, of_decide_eq_true rfl, parent.edge.point_one⟩

end EndpointSafeBlock

end Purelib.Riemann.Topology.PreparedRefinementRootChains

end
