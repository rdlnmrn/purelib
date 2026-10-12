module
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Primitive

public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Data.List.Append
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Connected nested refinements of the actual prepared roots

Composition retains the original parent grouping, connected child paths and
all-query root maps.  Primitive increments telescope on each retained block,
without an integral-comparison allowance from the original coarse model.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements

open Purelib.Data.List

open Purelib.Data in
/-- The canonical Gaussian rational scalar type. -/
private abbrev Gaussian := Gaussian.Basic.Canonical

open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge RootSubedgeBlock RootSubedgeRefinement)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Retain each prepared parent as its own singleton root-refinement block.

Every parent keeps its original root-query relation and endpoint chain. The
ordered parent list supplies the same ordered children. -/
@[expose] def refl : (parents : List (CenteredEdge curve differential)) → RootSubedgeRefinement parents parents
  | [] => .nil
  | parent :: parents =>
      .cons (.cons parent (.nil _)) (.cons (.refl parent) .nil) (refl parents)

open Purelib.Geometry in
/-- Replace each parent of a connected prepared path by its retained connected child block.

The resulting path keeps the original lifted start and finish endpoints. -/
@[expose] def refinedChain : ∀ {parents children : List (CenteredEdge curve differential)} {first last :
  Path.Gaussian.Lifted.Basic.LiftedPoint 2},
    RootSubedgeRefinement parents children → DirectPathChain parents (start := first) (finish := last) →
      DirectPathChain children (start := first) (finish := last)
  | _, _, _, _, .nil, .nil point => .nil point
  | _, _, _, _, .cons chain _ tail, .cons _ remaining =>
      chain.append (refinedChain tail remaining)

/-- Transfer every descendant root query through its retained intermediate parent relation.

The resulting block is indexed by the original coarse parent and preserves the ordered final children. -/
@[expose] def refineBlock {parent : CenteredEdge curve differential} :
    ∀ {middle children : List (CenteredEdge curve differential)},
      RootSubedgeRefinement middle children → RootSubedgeBlock parent middle → RootSubedgeBlock parent children
  | _, _, .nil, .nil => .nil
  | _, _, .cons _ head tail, .cons relation remaining =>
      (head.through relation).append (refineBlock tail remaining)

set_option genInjectivity false in
/-- A retained refinement split at an original parent-list boundary.

The record keeps the ordered left and right child lists, their concatenation equation and both exact parent refinements.
-/
structure Split (first second children : List (CenteredEdge curve differential)) where
  /-- The children belonging to the original left parent block. -/ leftChildren : List (CenteredEdge curve differential)
  /-- The children belonging to the original right parent block. -/ rightChildren : List (CenteredEdge curve
    differential)
  /-- The full child list is exactly the ordered concatenation of the retained parts. -/ children_eq : children =
    leftChildren ++ rightChildren
  /-- The original left parents refine to the retained left children. -/ left : RootSubedgeRefinement first leftChildren
  /-- The original right parents refine to the retained right children. -/ right : RootSubedgeRefinement second
    rightChildren

constructive_injectivity Split

/-- Split a refinement at an existing parent-list boundary.

Structural recursion preserves the retained blocks and requires neither edge equality searches nor a new subdivision. -/
@[expose] def split : ∀ (first : List (CenteredEdge curve differential))
    {second children : List (CenteredEdge curve differential)},
    RootSubedgeRefinement (first ++ second) children → Split first second children
  | [], _, children, refinement => ⟨[], children, rfl, .nil, refinement⟩
  | _ :: first, _, _, .cons (block := block) chain head tail =>
      let remaining := split first tail
      ⟨block ++ remaining.leftChildren, remaining.rightChildren,
        (congrArg (List.append block) remaining.children_eq).trans (Append.append_assoc _ _ _).symm,
        .cons chain head remaining.left, remaining.right⟩

/-- Compose prepared root-refinement stages while preserving the original parent grouping.

Each final connected child block retains its endpoint chain and all-query root relation to the original parent. -/
@[expose] def trans : ∀ {parents middle children : List (CenteredEdge curve differential)},
    RootSubedgeRefinement parents middle → RootSubedgeRefinement middle children →
      RootSubedgeRefinement parents children
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons (block := block) chain head tail, next =>
      let parts := split block next
      (RootSubedgeRefinement.cons (refinedChain parts.left chain) (refineBlock parts.left head)
        (trans tail parts.right)).castChildren parts.children_eq.symm

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Primitive increments telescope exactly across every retained refinement block.

Only each parent's child block must be connected; the whole parent list need not form one connected path. -/
theorem incrementSum_eq (primitive : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical)
    {parents children : List (CenteredEdge curve differential)}
    (refinement : RootSubedgeRefinement parents children) :
    Polynomial.Gaussian.Path.Primitive.incrementSum primitive (children.map CenteredEdge.model) =
      Polynomial.Gaussian.Path.Primitive.incrementSum primitive (parents.map CenteredEdge.model) := by
  induction refinement with
  | nil => rfl
  | @cons parent parents block children chain head tail ih =>
      rw [Map.map_append, Polynomial.Gaussian.Path.Primitive.incrementSum_append,
        Paths.PreparedPrimitivePaths.incrementSum_eq primitive chain, ih]
      change primitive _ - primitive _ + _ = primitive (parent.edge.point 1) - primitive (parent.edge.point 0) + _
      rw [parent.edge.point_one, parent.edge.point_zero]

end Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
