module

public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Dyadic
public import Purelib.Data.List.Flatten.Occurrence
public import Purelib.Data.Vector.Dependent
public import Purelib.Integration.Partition.Interval.Chain.Indexed
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.GetD
import Purelib.Data.List.Membership
import Purelib.Data.List.Prefix.Take
import Purelib.Data.Fin.Product.Code
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Original dyadic refinement occurrences and endpoint chains

The original dyadic addition law identifies the complete refined edge word
with the ordered flattening of its coarse fibers. The existing Flatten
occurrence locator retains both original bounded indices and the full prefix
offset. All readbacks consume that actual result without locating again.
-/

public section

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

open Purelib
open Purelib.Algebra
open Purelib.Data.Rat.Fraction
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Partition (Interval)

namespace ParameterEdge

/-- Read the original dyadic edge's two exact scalar endpoints as an interval. -/
@[expose] def interval (edge : ParameterEdge) : Interval :=
  ⟨edge.left.parameter, edge.right.parameter⟩

end ParameterEdge

/-- The actual ordered dyadic interval word chains its original endpoints exactly. -/
theorem dyadicEdges_chain (depth : Nat) (left right : Endpoint) :
    Interval.Chain left.parameter right.parameter ((dyadicEdges depth left right).map ParameterEdge.interval) := by
  induction depth generalizing left right with
  | zero => exact .cons (.nil right.parameter)
  | succ depth retained =>
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      change Interval.Chain left.parameter right.parameter
        ((dyadicEdges depth left middle ++ dyadicEdges depth middle right).map ParameterEdge.interval)
      rewrite [Map.map_append]
      exact Interval.Chain.append (retained left middle) (retained middle right)

/-- Every original indexed dyadic width is nonnegative on its SAME ordered original interval. -/
theorem dyadicEdges_width_nonnegative (depth : Nat) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter) (index : Fin (dyadicEdges depth left right).length) :
    0 ≤ ((dyadicEdges depth left right)[index.val]'index.isLt).right.parameter -
      ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter :=
  Order.Arithmetic.sub_nonneg_direct (dyadicEdges_bounds depth left right ordered _
    (List.getElem_mem index.isLt)).2.1

/-- The SAME original indexed dyadic widths sum to the original outer interval width, with no count multiplier. -/
theorem dyadicEdges_sum_widths (depth : Nat) (left right : Endpoint) :
    FiniteSum.Fin.sumFin (fun index : Fin (dyadicEdges depth left right).length =>
      ((dyadicEdges depth left right)[index.val]'index.isLt).right.parameter -
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) =
          right.parameter - left.parameter := by
  let intervals := fun index : Fin (dyadicEdges depth left right).length =>
    ParameterEdge.interval ((dyadicEdges depth left right)[index.val]'index.isLt)
  have table : List.ofFn intervals = (dyadicEdges depth left right).map ParameterEdge.interval :=
    OfFn.Basic.ofFn_map_cast (dyadicEdges depth left right) rfl ParameterEdge.interval
  have chain := Eq.mpr (congrArg (Interval.Chain left.parameter right.parameter) table)
    (dyadicEdges_chain depth left right)
  exact Interval.Chain.sum_widths intervals chain

/-- The original ordered fibers refine each original coarse edge at the retained additional depth. -/
@[expose] def refinementBlocks (coarse additional : Nat) (left right : Endpoint) : List (List ParameterEdge) :=
  (dyadicEdges coarse left right).map (fun edge => dyadicEdges additional edge.left edge.right)

/-- Their exact ordered flattening is the original dyadic subdivision at the sum of depths. -/
theorem refinementBlocks_eq (coarse additional : Nat) (left right : Endpoint) :
    dyadicEdges (coarse + additional) left right = (refinementBlocks coarse additional left right).flatten :=
  (dyadicEdges_add coarse additional left right).trans (Flatten.flatMap_eq _ _)

/-- Both orders of coarse/additional depth have the SAME complete original refined word. -/
theorem refinementBlocks_comm (first last : Nat) (left right : Endpoint) :
    (refinementBlocks first last left right).flatten = (refinementBlocks last first left right).flatten :=
  (refinementBlocks_eq first last left right).symm.trans
    ((congrArg (fun depth => dyadicEdges depth left right) (Nat.add_comm first last)).trans
      (refinementBlocks_eq last first left right))

/-- Locate one actual refined occurrence in its exact original coarse fiber and retain the full prefix identity.

Only the original ordered dyadic addition equality casts the input index.
The existing Flatten.locate operation executes once. Its result retains
both bounded original occurrences and is consumed directly by the following
readbacks; equal endpoint labels never select an occurrence.
-/
def refinementOccurrence (coarse additional : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (coarse + additional) left right).length) :
    Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index) :=
  Flatten.locate (refinementBlocks coarse additional left right)
    (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index)

namespace refinementOccurrence

variable {coarse additional : Nat} {left right : Endpoint}
    {index : Fin (dyadicEdges (coarse + additional) left right).length}
    (found : Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index))

/-- Read the SAME retained coarse occurrence, transporting only the mapped-list length index. -/
@[expose] def coarseIndex : Fin (dyadicEdges coarse left right).length :=
  Fin.cast (Map.length_map _ _) found.1

/-- Read the SAME selected original coarse edge from its retained bounded occurrence. -/
@[expose] def coarseEdge : ParameterEdge :=
  (dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt

/-- The SAME retained fiber is the original dyadic refinement of the selected coarse edge. -/
theorem block_eq :
    (refinementBlocks coarse additional left right)[found.1.val]'found.1.isLt =
      dyadicEdges additional
        ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).left
        ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).right :=
  Map.getElem_map _ _ found.1.val (coarseIndex found).isLt found.1.isLt

/-- Read the SAME retained inner occurrence at its original selected coarse fiber. -/
@[expose] def localIndex : Fin (dyadicEdges additional
    ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).left
    ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).right).length :=
  Fin.cast (congrArg List.length (block_eq found)) found.2.val

/-- The actual refined edge is that SAME bounded inner edge of the retained original coarse occurrence. -/
theorem edge_eq : (dyadicEdges (coarse + additional) left right)[index.val]'index.isLt =
    (dyadicEdges additional
      ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).left
      ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).right)[
        (localIndex found).val]'(localIndex found).isLt := by
  have original := Data.List.at_cast (refinementBlocks_eq coarse additional left right) index
  have inner := Data.List.at_cast (block_eq found) found.2.val
  exact original.symm.trans (found.2.property.1.trans inner.symm)

/-- The exact prefix before the selected original coarse occurrence has its original fixed dyadic fiber length. -/
theorem prefix_length :
    ((refinementBlocks coarse additional left right).take found.1.val).flatten.length =
      (coarseIndex found).val * 2 ^ additional := by
  let edges := dyadicEdges coarse left right
  let fiber := fun edge : ParameterEdge => dyadicEdges additional edge.left edge.right
  have prefix_eq : (refinementBlocks coarse additional left right).take found.1.val =
      (edges.take (coarseIndex found).val).map fiber :=
    (Map.map_take fiber edges (coarseIndex found).val).symm
  have size : (edges.take (coarseIndex found).val).length = (coarseIndex found).val :=
    Prefix.Take.length_take_of_le (coarseIndex found).isLt.le
  calc
    _ = ((edges.take (coarseIndex found).val).map fiber).flatten.length := congrArg (fun entries =>
      entries.flatten.length) prefix_eq
    _ = ((edges.take (coarseIndex found).val).flatMap fiber).length :=
      (congrArg List.length (Flatten.flatMap_eq _ _)).symm
    _ = (edges.take (coarseIndex found).val).length * 2 ^ additional :=
      Flatten.flatMap_length_of_constant _ fiber (2 ^ additional)
        (fun edge _member => dyadicEdges_length additional edge.left edge.right)
    _ = _ := congrArg (fun length => length * 2 ^ additional) size

/-- The original refined edge retains its full coarse-prefix offset and same inner natural coordinate. -/
theorem offset : index.val =
    ((refinementBlocks coarse additional left right).take found.1.val).flatten.length + (localIndex found).val :=
  found.2.property.2

/-- The retained refined edge lies inside its SAME original coarse interval with its original orientation. -/
theorem bounds (ordered : left.parameter ≤ right.parameter) :
    ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).left.parameter ≤
        ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).left.parameter ∧
      ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).left.parameter ≤
        ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).right.parameter ∧
      ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).right.parameter ≤
        ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).right.parameter := by
  have coarseBounds := dyadicEdges_bounds coarse left right ordered _ (List.getElem_mem (coarseIndex found).isLt)
  have retained := dyadicEdges_bounds additional _ _ coarseBounds.2.1 _ (List.getElem_mem (localIndex found).isLt)
  exact Eq.mpr (congrArg (fun edge : ParameterEdge =>
    ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).left.parameter ≤
      edge.left.parameter ∧ edge.left.parameter ≤ edge.right.parameter ∧ edge.right.parameter ≤
        ((dyadicEdges coarse left right)[(coarseIndex found).val]'(coarseIndex found).isLt).right.parameter)
      (edge_eq found)) retained

/-- Two original dyadic occurrence outcomes at the SAME flattened index retain exactly the SAME coarse/local indices.

All dyadic fibers have the original length 2^additional. Their full prefix
offsets give the same row-major natural code. Existing finite-pair code
injectivity identifies the two bounded indices independently of their edge
values, so repeated parameter labels do not select or merge occurrences.
-/
theorem unique
    (last : Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index)) : found = last := by
  let encode := fun retained : Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index) =>
    (coarseIndex retained,
      Fin.cast (dyadicEdges_length additional (coarseEdge retained).left (coarseEdge retained).right)
        (localIndex retained))
  have firstCode : index.val = (encode found).1.val * 2 ^ additional + (encode found).2.val :=
    (offset found).trans (congrArg (fun length => length + (localIndex found).val) (prefix_length found))
  have lastCode : index.val = (encode last).1.val * 2 ^ additional + (encode last).2.val :=
    (offset last).trans (congrArg (fun length => length + (localIndex last).val) (prefix_length last))
  have same := Data.Fin.Product.Code.pairCode_injective (firstCode.symm.trans lastCode)
  have outer : found.1 = last.1 := Fin.ext (congrArg (fun pair => pair.1.val) same)
  have inner : found.2.val.val = last.2.val.val := congrArg (fun pair => pair.2.val) same
  cases found with
  | mk firstOuter firstInner =>
      cases last with
      | mk lastOuter lastInner =>
          cases outer
          exact congrArg (Sigma.mk firstOuter) (Subtype.ext (Fin.ext inner))

end refinementOccurrence

/-- Transport an original refined occurrence through the SAME complete dyadic word at the commuted depth sum. -/
@[expose] def commutedIndex (first last : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + last) left right).length) :
    Fin (dyadicEdges (last + first) left right).length :=
  Fin.cast (congrArg (fun depth => (dyadicEdges depth left right).length) (Nat.add_comm first last)) index

/-- Commuting the total depth preserves that SAME original refined edge occurrence. -/
theorem commutedIndex_edge (first last : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + last) left right).length) :
    (dyadicEdges (last + first) left right)[(commutedIndex first last left right index).val]'
      (commutedIndex first last left right index).isLt =
        (dyadicEdges (first + last) left right)[index.val]'index.isLt :=
  Data.List.at_cast (congrArg (fun depth => dyadicEdges depth left right) (Nat.add_comm first last)) index

/-- Both original coarse/fine occurrence outcomes at the SAME exact common refined edge.

This is the original product of two Flatten.Occurrence results, with both
bounded source indices retained. It adds no geometric or root hypothesis.
-/
@[expose] def RefinementPair (first last : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + last) left right).length) :=
  Flatten.Occurrence (refinementBlocks first last left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq first last left right)) index) ×
    Flatten.Occurrence (refinementBlocks last first left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq last first left right))
        (commutedIndex first last left right index))

/-- Materialize both original occurrence lookups once, preserving complete outcomes and exact common-edge indices. -/
def refinementPair (first last : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + last) left right).length) : RefinementPair first last left right index :=
  ⟨refinementOccurrence first last left right index,
    refinementOccurrence last first left right (commutedIndex first last left right index)⟩

/-- Materialize the two original occurrence outcomes once at every SAME common-fine coordinate. -/
def refinementPairs (first last : Nat) (left right : Endpoint) :
    Data.Vector.DependentVector (fun index => RefinementPair first last left right index) :=
  Data.Vector.DependentVector.ofFn (fun index => refinementPair first last left right index)

/-- The actual stored pair at every common-fine coordinate retains both complete original lookup factories. -/
theorem refinementPairs_get (first last : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + last) left right).length) :
    (refinementPairs first last left right).get index = refinementPair first last left right index :=
  Data.Vector.DependentVector.ofFn_get _ index

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

end
