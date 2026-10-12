module
import Purelib.Data.List.Map
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

public import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-!
# Root joins for every recast differential

Changing the numerator differential recenters the coefficient model but
retains the actual prepared root process.  Root-chain witnesses therefore
apply to the recast parent lists sampled by every period-matrix entry.
-/

namespace Purelib.Riemann.Topology.PreparedRecastRootChains

public section

namespace PreparedDirectDyadicRefinements

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastPreparedEdge)
open Purelib.Data.Rat in
/-- The rational parameter carrier of retained root-chain locations. -/
private abbrev Coordinate := Fraction.Rational

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Changing the differential preserves the exact prepared edge root name at every bounded parameter. -/
theorem recastPreparedEdge_rootName {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus} (target : Differentials.Basic.Differential genus)
    (edge : PreparedSubdivisionModelCore.PreparedEdge curve source)
    (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (recastPreparedEdge target edge).rootName parameter inside = edge.rootName parameter inside := by
  unfold PreparedConstantModels.PreparedEdge.rootName
  rfl

end PreparedDirectDyadicRefinements

namespace RootChain

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge recastPreparedEdge)
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedDirectDyadicRefinements (recastPreparedEdge_rootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Recast an ordered root chain to the target differential with the same endpoint names.

Every original parent remains in order, and the entry and tail root equivalences are transported through exact recast
root-name identities. -/
@[expose] def recast (target : Differentials.Basic.Differential genus) :
    ∀ {parents : List (CenteredEdge curve source)} {first last : Named},
      RootChain parents first last → RootChain (parents.map (recastCenteredEdge target)) first last
  | [], _, _, .nil equivalent => .nil equivalent
  | _ :: _, _, _, .cons parent entry tail => by
      refine .cons (recastCenteredEdge target parent) ?_ ?_
      · change Equivalence.NamedEquivalent _ ((recastPreparedEdge target parent.edge).rootName 0 _)
        rw [recastPreparedEdge_rootName]
        exact entry
      · exact PreparedBankRootChains.RootChain.castNames
          (recastPreparedEdge_rootName target parent.edge 1 (by decide)).symm rfl (recast target tail)

end RootChain

namespace PreparedRefinementRootEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge recastPreparedEdge)
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedDirectDyadicRefinements (recastPreparedEdge_rootName)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge RootSubedgeBlock RootSubedgeRefinement)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
/-- Recast one retained root-subedge relation to the target differential.

The exact parent fraction, inside proof and geometric point identity are preserved at every child parameter; only
differential-indexed names are transported. -/
@[expose] def RootSubedge.recast {parent child : CenteredEdge curve source} (relation : RootSubedge parent child)
    (target : Differentials.Basic.Differential genus) : RootSubedge (recastCenteredEdge target parent)
      (recastCenteredEdge target child) where
  location := fun fraction inside =>
    let retained := relation.location fraction inside
    ⟨retained.fraction, retained.inside, retained.point_eq⟩
  equivalent := fun fraction inside => by
    change Equivalence.NamedEquivalent
      ((recastPreparedEdge target parent.edge).rootName _ _)
      ((recastPreparedEdge target child.edge).rootName _ _)
    rw [recastPreparedEdge_rootName, recastPreparedEdge_rootName]
    exact relation.equivalent fraction inside

open Purelib.Curves.Hyperelliptic in
/-- Recast the ordered child relations for one original parent, preserving every child position. -/
@[expose] def RootSubedgeBlock.recast {parent : CenteredEdge curve source} (target : Differentials.Basic.Differential
  genus) :
    ∀ {children : List (CenteredEdge curve source)}, RootSubedgeBlock parent children →
      RootSubedgeBlock (recastCenteredEdge target parent) (children.map (recastCenteredEdge target))
  | _, .nil => .nil
  | _, .cons head tail => .cons (RootSubedge.recast head target) (recast target tail)

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- Recast both ordered parent and child lists with their original root-subedge witnesses.

Each retained direct chain is recast alongside its relation block, preserving the exact child concatenation and parent
order. -/
@[expose] def RootSubedgeRefinement.recast (target : Differentials.Basic.Differential genus) :
    ∀ {parents children : List (CenteredEdge curve source)}, RootSubedgeRefinement parents children →
      RootSubedgeRefinement (parents.map (recastCenteredEdge target)) (children.map (recastCenteredEdge target))
  | _, _, .nil => .nil
  | _, _, .cons chain head tail => by
      rw [List.map_cons, Purelib.Data.List.Map.map_append]
      exact .cons (PreparedDirectDyadicRefinements.DirectPathChain.recast target chain)
        (RootSubedgeBlock.recast target head) (recast target tail)

end PreparedRefinementRootEndpoints

end
end Purelib.Riemann.Topology.PreparedRecastRootChains
