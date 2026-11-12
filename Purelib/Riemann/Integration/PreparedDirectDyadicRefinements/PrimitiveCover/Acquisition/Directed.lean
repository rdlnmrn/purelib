module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover.Acquisition.Chain
public import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedDyadicRefinements

/-! # Actual signed and directed primitive-safe child blocks

The original acquisition retains its real safe block, connected chain and
queries. Its positive displacement factors and original endpoint-safe
subedges give directed source grouping. Empty branches keep their given
geometric chain and separate genuine root comparison without fabrication.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover.Acquisition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain DirectPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (Queries)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements (DirectedRefinement SameDirection)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : CenteredEdge curve differential} {queries : Queries parent.edge}
variable {diameter : Rational} {positive : 0 < diameter}

/-- Every actual acquired child has the original parent's positive displacement direction.

The statement uses the actual retained block. It does not identify any
Owner from this scalar geometric relation, even for stationary points.
-/
theorem sameDirection (retained : Acquisition (count := count) parent queries diameter positive)
    {child : CenteredEdge curve differential} (member : child ∈ retained.parents) : SameDirection parent child := by
  cases retained with
  | inl _ => exact (List.not_mem_nil member).elim
  | inr actual => exact SameDirection.ofBlock actual.1.val.block member

/-- The same acquired chain, root maps and positive factors construct original directed refinement.

The independent root comparison for an empty outer request stays in the
original acquisition. Its actual empty geometric chain is sufficient for
this source-grouping proposition; it supplies no new root equality.
-/
theorem directedRefinement (retained : Acquisition (count := count) parent queries diameter positive) :
    DirectedRefinement [parent] retained.parents := by
  cases retained with
  | inl stationary =>
      let given : Acquisition (count := count) parent queries diameter positive := .inl stationary
      exact DirectedRefinement.cons (parent := parent) (parents := []) (block := []) (children := [])
        given.chain.toDirectPathChain .nil (fun _ impossible => (List.not_mem_nil impossible).elim) .nil
  | inr actual =>
      exact Eq.mp (congrArg (DirectedRefinement [parent])
        (Purelib.Data.List.Append.append_nil actual.1.val.block.children))
        (DirectedRefinement.cons actual.1.val.block.chain (EndpointSafeBlock.subedges actual.1.val)
          (fun _ member => SameDirection.ofBlock actual.1.val.block member) .nil)

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover.Acquisition

end
