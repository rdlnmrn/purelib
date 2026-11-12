module

public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Approximation.Gaussian.Equivalence

/-! # Operational root chains consuming actual retained recast parents

The target parent list is supplied as complete cached data with its whole
original recast law. The operation stores those actual supplied heads and
reuses the original root comparisons. Exact whole-value readback compares
it with the unchanged original recaster without executing that factory.
-/

public section

namespace Purelib.Riemann.Topology.PreparedRecastRootChains.RootChain

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedDirectDyadicRefinements (recastPreparedEdge_rootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source : Differential genus}

/-- Reindex an original root chain onto supplied cached recast parents in the same literal order.

The supplied list is read head by head. Its complete map law is used only
in erased root-name transports; every new RootChain constructor stores the
actual supplied head. No recast parent, center model or observation is
computed by this operation.
-/
def recastOn (target : Differential genus) :
    {parents : List (CenteredEdge curve source)} → {first last : Named} →
    (roots : RootChain parents first last) → (children : List (CenteredEdge curve target)) →
    children = parents.map (recastCenteredEdge target) → RootChain children first last
  | [], _, _, .nil equivalent, children, same => by
      cases children with
      | nil => exact .nil equivalent
      | cons child children => exact False.elim (List.cons_ne_nil child children same)
  | parent :: parents, first, _, .cons _ entry tail, children, same => by
      cases children with
      | nil => exact False.elim (List.cons_ne_nil _ _ same.symm)
      | cons child children =>
          have headEq : child = recastCenteredEdge target parent := (List.cons.inj same).1
          have tailEq : children = parents.map (recastCenteredEdge target) := (List.cons.inj same).2
          have firstEq : child.edge.rootName 0 child.edge.baseInside =
              parent.edge.rootName 0 parent.edge.baseInside := by
            cases headEq
            exact recastPreparedEdge_rootName target parent.edge 0 parent.edge.baseInside
          have lastEq : child.edge.rootName 1 (by decide) = parent.edge.rootName 1 (by decide) := by
            cases headEq
            exact recastPreparedEdge_rootName target parent.edge 1 (by decide)
          exact .cons child
            (Eq.mp (congrArg (fun name => NamedEquivalent first name) firstEq.symm) entry)
            (PreparedBankRootChains.RootChain.castNames lastEq.symm rfl
              (recastOn target tail children tailEq))

/-- On the literal mapped list the cached operation preserves the complete original recast root-chain value. -/
private theorem recastOn_map (target : Differential genus) :
    {parents : List (CenteredEdge curve source)} → {first last : Named} →
    (roots : RootChain parents first last) →
    recastOn target roots (parents.map (recastCenteredEdge target)) rfl = recast target roots
  | [], _, _, .nil _ => rfl
  | parent :: parents, first, _, .cons _ entry tail => by
      let moved := Eq.mp (congrArg (fun name => NamedEquivalent first name)
        (recastPreparedEdge_rootName target parent.edge 0 parent.edge.baseInside).symm) entry
      change RootChain.cons (recastCenteredEdge target parent) moved
          (PreparedBankRootChains.RootChain.castNames
            (recastPreparedEdge_rootName target parent.edge 1 (by decide)).symm rfl
            (recastOn target tail (parents.map (recastCenteredEdge target)) rfl)) =
        RootChain.cons (recastCenteredEdge target parent) moved
          (PreparedBankRootChains.RootChain.castNames
            (recastPreparedEdge_rootName target parent.edge 1 (by decide)).symm rfl (recast target tail))
      exact congrArg (fun retained => RootChain.cons (recastCenteredEdge target parent) moved
        (PreparedBankRootChains.RootChain.castNames
          (recastPreparedEdge_rootName target parent.edge 1 (by decide)).symm rfl retained))
        (recastOn_map target tail)

/-- The whole cached-root construction has the original recast factory after its exact parent-list index transport. -/
private theorem packaged_recastOn_eq (target : Differential genus)
    {parents : List (CenteredEdge curve source)} {first last : Named}
    (roots : RootChain parents first last) (children : List (CenteredEdge curve target))
    (same : children = parents.map (recastCenteredEdge target)) :
    PreparedBankRootChains.RootChain.castChildren same (recastOn target roots children same) = recast target roots := by
  cases same
  exact recastOn_map target roots

/-- The whole cached-root construction has the original recast factory after its exact parent-list index transport. -/
theorem recastOn_eq (target : Differential genus)
    {parents : List (CenteredEdge curve source)} {first last : Named}
    (roots : RootChain parents first last) (children : List (CenteredEdge curve target))
    (same : children = parents.map (recastCenteredEdge target)) :
    PreparedBankRootChains.RootChain.castChildren same (recastOn target roots children same) = recast target roots :=
  packaged_recastOn_eq target roots children same

end Purelib.Riemann.Topology.PreparedRecastRootChains.RootChain

end
