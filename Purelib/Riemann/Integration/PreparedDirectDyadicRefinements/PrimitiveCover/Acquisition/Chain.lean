module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover.Acquisition
public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Data.List.Append
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedDyadicRefinements

/-! # The actual geometric child chain of a retained primitive-cover acquisition

The original strict branch already retains its ordered direct chain and
covering patches. The zero-width branch has an empty inner chain on the
same original point and sheet, with both outer roles and its independent
query/root comparison retained by the unchanged acquisition.
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
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : CenteredEdge curve differential} {queries : Queries parent.edge}
variable {diameter : Rational} {positive : 0 < diameter}

/-- Read the SAME original strict children, or the empty inner word of the retained zero-width branch. -/
@[expose] def parents : Acquisition (count := count) parent queries diameter positive →
    List (CenteredEdge curve differential)
  | .inl _ => []
  | .inr retained => retained.1.val.block.children

/-- The literal retained child list has exactly the original acquired child count. -/
theorem parents_length (retained : Acquisition (count := count) parent queries diameter positive) :
    retained.parents.length = retained.childCount := by
  cases retained <;> rfl

/-- Every actual acquired child has strict parameter endpoints, including physically stationary children.

The strict branch retains its original block's complete ordering certificate.
The zero-width branch contributes the actual empty list and requires no
strictness premise about its original parent.
-/
theorem parents_proper (retained : Acquisition (count := count) parent queries diameter positive) :
    AllParentsProper retained.parents := by
  cases retained with
  | inl _ => exact True.intro
  | inr refined => exact refined.1.val.block.proper

/-- Every retained binary power is positive. -/
private theorem binary_positive : (depth : Nat) → 0 < 2 ^ depth
  | 0 => Nat.zero_lt_succ 0
  | depth + 1 => by
      rewrite [Nat.pow_succ]
      exact Nat.mul_pos (binary_positive depth) (Nat.zero_lt_succ 1)

/-- A strict original parameter interval has a positive actual acquired child count.

The stationary branch retains an equality contradicting the given strict
order. The refined branch's SAME block has exactly two to its actual depth
children. No coordinate movement or nonstationary physical edge is assumed.
-/
theorem childCount_positive
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (retained : Acquisition (count := count) parent queries diameter positive) : 0 < retained.childCount := by
  cases retained with
  | inl stationary =>
      have impossible : parent.edge.left.parameter < parent.edge.left.parameter :=
        Eq.mpr (congrArg (fun value : Rational => parent.edge.left.parameter < value) stationary.1.property.2) proper
      change (parent.edge.left.parameter ≤ parent.edge.left.parameter ∧
        ¬parent.edge.left.parameter ≤ parent.edge.left.parameter) at impossible
      exact False.elim (impossible.2 impossible.1)
  | inr refined =>
      exact Eq.mpr (congrArg (fun size : Nat => 0 < size) refined.1.val.block.childCount)
        (binary_positive refined.1.val.block.depth)

/-- Read all SAME successful covering patches on the SAME literal child list.

A stationary branch contributes an empty covering spine. A strict branch
returns the actual retained inspection success; it neither reconstructs a
patch nor repeats its endpoint inspection.
-/
@[expose] def covered : (retained : Acquisition (count := count) parent queries diameter positive) →
    CoveredParents count retained.parents
  | .inl _ => .nil
  | .inr retained => retained.2.2.2.1.val.val

/-- Read the SAME retained signed child-root chain, including the actual empty-word comparison for zero width.

Only the stored branch field is projected. No parent budget, endpoint
query, root comparison, transport or child preparation is executed.
-/
@[expose] def roots : (retained : Acquisition (count := count) parent queries diameter positive) →
    RootChain retained.parents (parent.edge.rootName 0 parent.edge.baseInside)
      (parent.edge.rootName 1 (of_decide_eq_true rfl))
  | .inl retained => retained.2.val
  | .inr retained => retained.2.2.2.2.val

/-- Assemble the actual centered children between the original parent's full lifted endpoint roles.

The strict branch converts its GIVEN direct chain. For zero width the
retained exact parameter equality identifies only the original coordinate
and sheet pair, allowing an empty inner chain. Original query/root-owner
comparisons remain in the acquisition and are not derived from this fact.
-/
def chain : (retained : Acquisition (count := count) parent queries diameter positive) →
    CenteredPathChain retained.parents
      (start := ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩)
      (finish := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩)
  | .inl retained =>
      (CenteredPathChain.nil
        (⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩ : LiftedPoint 2)).castFinish
          (congrArg (fun fraction : Rational =>
            (⟨parent.edge.segment.pointAt fraction, parent.edge.sheet⟩ : LiftedPoint 2)) retained.1.property.2)
  | .inr retained => CenteredPathChain.ofDirect retained.1.val.block.chain

/-- Retain the actual original parent as one connected, pointwise rooted subdivision block.

A strict outcome consumes its SAME safe.budget, block.chain and block.roots
through the original EndpointSafeBlock.subedges constructor. Its locations
and root comparisons refer to every rational query on each actual child.
A zero-width outcome retains the original parent as an empty inner block
at its exact two lifted endpoint roles. Its independent signed empty-root
comparison stays in the supplied acquisition and roots getter; no root
agreement is inferred from the geometric endpoint equality below.
-/
def subedgeRefinement : (retained : Acquisition (count := count) parent queries diameter positive) →
    RootSubedgeRefinement [parent] retained.parents
  | .inl retained => by
      let source : LiftedPoint 2 :=
        ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩
      have same : source =
          (⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩ : LiftedPoint 2) :=
        congrArg (fun fraction : Rational =>
          (⟨parent.edge.segment.pointAt fraction, parent.edge.sheet⟩ : LiftedPoint 2)) retained.1.property.2
      let empty : DirectPathChain (curve := curve) (differential := differential) [] (start := source)
          (finish := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩) :=
        Eq.mp (congrArg (fun finish : LiftedPoint 2 =>
          DirectPathChain (curve := curve) (differential := differential) [] (start := source) (finish := finish))
          same) (DirectPathChain.nil source)
      exact RootSubedgeRefinement.cons (parent := parent) (parents := []) (block := []) (children := [])
        empty .nil .nil
  | .inr retained =>
      RootSubedgeRefinement.castChildren (Purelib.Data.List.Append.append_nil retained.1.val.block.children)
        (RootSubedgeRefinement.cons retained.1.val.block.chain
          (Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries.EndpointSafeBlock.subedges
            retained.1.val) .nil)

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover.Acquisition

end
