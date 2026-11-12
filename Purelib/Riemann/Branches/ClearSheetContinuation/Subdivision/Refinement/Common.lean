module

public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Refinement.Parameters
import Purelib.Data.List.GetD
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Refinement

/-! # Common original dyadic occurrences above an additional minimum

The common grid has depth first+(last+minimum). Its two original coarse
occurrence outcomes are computed once at the SAME fine index, retaining
the original bounded child indices, local inputs and prefix offsets.
No root, point observation or source preparation is selected by this grid.
-/

public section

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

open Purelib
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Interval
open Purelib.Integration.Polynomial.Gaussian

/-- Reindex the SAME fine edge at the equal depth last+(first+minimum). -/
@[expose] def commonIndex (first last minimum : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + (last + minimum)) left right).length) :
    Fin (dyadicEdges (last + (first + minimum)) left right).length :=
  Fin.cast (congrArg (fun depth => (dyadicEdges depth left right).length)
    (Nat.add_left_comm first last minimum)) index

/-- The equal-depth index transport preserves the entire original fine parameter edge. -/
theorem commonIndex_edge (first last minimum : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + (last + minimum)) left right).length) :
    (dyadicEdges (last + (first + minimum)) left right)[(commonIndex first last minimum left right index).val]'
      (commonIndex first last minimum left right index).isLt =
        (dyadicEdges (first + (last + minimum)) left right)[index.val]'index.isLt :=
  Data.List.at_cast (congrArg (fun depth => dyadicEdges depth left right)
    (Nat.add_left_comm first last minimum)) index

/-- The common depth retains the requested extra minimum before either original coarse grid is queried. -/
theorem commonDepth_minimum (first last minimum : Nat) : minimum ≤ first + (last + minimum) :=
  (Nat.le_add_left minimum last).trans (Nat.le_add_left (last + minimum) first)

/-- The common depth refines the first original coarse depth without altering its occurrence order. -/
theorem commonDepth_first (first last minimum : Nat) : first ≤ first + (last + minimum) :=
  Nat.le_add_right first (last + minimum)

/-- The same common depth also refines the second original coarse depth. -/
theorem commonDepth_last (first last minimum : Nat) : last ≤ first + (last + minimum) :=
  (Nat.le_add_right last minimum).trans (Nat.le_add_left (last + minimum) first)

/-- The exact product of both original occurrence outcomes at one common fine edge above the retained minimum. -/
@[expose] def RefinementPairAbove (first last minimum : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + (last + minimum)) left right).length) :=
  Flatten.Occurrence (refinementBlocks first (last + minimum) left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq first (last + minimum) left right)) index) ×
    Flatten.Occurrence (refinementBlocks last (first + minimum) left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq last (first + minimum) left right))
        (commonIndex first last minimum left right index))

/-- Compute each of the two original occurrence lookups once at the SAME common fine index. -/
def refinementPairAbove (first last minimum : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + (last + minimum)) left right).length) :
    RefinementPairAbove first last minimum left right index :=
  ⟨refinementOccurrence first (last + minimum) left right index,
    refinementOccurrence last (first + minimum) left right (commonIndex first last minimum left right index)⟩

/-- Retain both original coarse/fine outcomes once at every actual common-grid occurrence. -/
def refinementPairsAbove (first last minimum : Nat) (left right : Endpoint) :
    Data.Vector.DependentVector (fun index => RefinementPairAbove first last minimum left right index) :=
  Data.Vector.DependentVector.ofFn (fun index => refinementPairAbove first last minimum left right index)

/-- Every stored pair retains both whole original lookup factories at the unchanged fine index. -/
theorem refinementPairsAbove_get (first last minimum : Nat) (left right : Endpoint)
    (index : Fin (dyadicEdges (first + (last + minimum)) left right).length) :
    (refinementPairsAbove first last minimum left right).get index =
      refinementPairAbove first last minimum left right index :=
  Data.Vector.DependentVector.ofFn_get _ index

namespace RefinementPairAbove

variable {first last minimum : Nat} {left right : Endpoint}
    {index : Fin (dyadicEdges (first + (last + minimum)) left right).length}
    (pair : RefinementPairAbove first last minimum left right index)

/-- The two actual retained outcomes read the identical original physical parameter at every fine-edge input. -/
theorem parameter_eq (value : Rational) :
    refinementOccurrence.parameter pair.1 value = refinementOccurrence.parameter pair.2 value :=
  congrArg (fun edge : ParameterEdge =>
    Cell.Restriction.parameter edge.left.parameter edge.right.parameter value)
      (commonIndex_edge first last minimum left right index).symm

/-- The second original coarse input normalizes the SAME first-side physical parameter. -/
theorem last_input_eq (value : Rational) :
    refinementOccurrence.input pair.2 value =
      ConvexCombination.segmentParameter
        (refinementOccurrence.coarseEdge pair.2).left.parameter
        (refinementOccurrence.coarseEdge pair.2).right.parameter
        (refinementOccurrence.parameter pair.1 value) :=
  (refinementOccurrence.input_eq pair.2 value).trans
    (congrArg (ConvexCombination.segmentParameter
      (refinementOccurrence.coarseEdge pair.2).left.parameter
      (refinementOccurrence.coarseEdge pair.2).right.parameter) (pair.parameter_eq value).symm)

/-- Both original bounded child inputs retain their unit interval, with no condition on physical parent displacement. -/
theorem inputs_inside (ordered : left.parameter ≤ right.parameter) (value : Rational)
    (inside : 0 ≤ value ∧ value ≤ 1) :
    (0 ≤ refinementOccurrence.input pair.1 value ∧ refinementOccurrence.input pair.1 value ≤ 1) ∧
      (0 ≤ refinementOccurrence.input pair.2 value ∧ refinementOccurrence.input pair.2 value ≤ 1) :=
  ⟨refinementOccurrence.input_inside pair.1 ordered value inside,
    refinementOccurrence.input_inside pair.2 ordered value inside⟩

/-- The SAME physical fraction lies in both original coarse intervals with their retained forward orientation. -/
theorem bounds (ordered : left.parameter ≤ right.parameter) (value : Rational)
    (inside : 0 ≤ value ∧ value ≤ 1) :
    ((refinementOccurrence.coarseEdge pair.1).left.parameter ≤ refinementOccurrence.parameter pair.1 value ∧
      refinementOccurrence.parameter pair.1 value ≤ (refinementOccurrence.coarseEdge pair.1).right.parameter) ∧
    ((refinementOccurrence.coarseEdge pair.2).left.parameter ≤ refinementOccurrence.parameter pair.1 value ∧
      refinementOccurrence.parameter pair.1 value ≤ (refinementOccurrence.coarseEdge pair.2).right.parameter) := by
  refine ⟨refinementOccurrence.parameter_bounds pair.1 ordered value inside, ?_⟩
  exact Eq.mpr (congrArg (fun parameter : Rational =>
    (refinementOccurrence.coarseEdge pair.2).left.parameter ≤ parameter ∧
      parameter ≤ (refinementOccurrence.coarseEdge pair.2).right.parameter) (pair.parameter_eq value))
    (refinementOccurrence.parameter_bounds pair.2 ordered value inside)

end RefinementPairAbove

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

end
