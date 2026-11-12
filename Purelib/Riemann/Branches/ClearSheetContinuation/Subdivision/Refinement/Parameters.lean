module

public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Restriction
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Query parameters on the same retained dyadic refinement occurrence

The original coarse/fine occurrence keeps its exact common-edge index.
A child-local query has both its original physical parent parameter and
its normalized coarse-cell parameter, with their exact interpolation law.
The two retained sides of a RefinementPair read the same physical fraction.
-/

public section

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Interval.ConvexCombination
open Purelib.Integration.Polynomial.Gaussian

namespace refinementOccurrence

variable {coarse additional : Nat} {left right : Endpoint}
    {index : Fin (dyadicEdges (coarse + additional) left right).length}
    (found : Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index))

/-- Read the same physical outer parameter at an input of this actual common refined edge. -/
@[expose] def parameter
    {coarse additional : Nat} {left right : Endpoint}
    {index : Fin (dyadicEdges (coarse + additional) left right).length}
    (_found : Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index))
    (input : Rational) : Rational :=
  Cell.Restriction.parameter
    ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).left.parameter
    ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).right.parameter input

/-- Read the corresponding original coarse-cell input using the same retained normalized fine interval. -/
@[expose] def input (value : Rational) : Rational :=
  Cell.Restriction.parameter
    (ParameterEdge.intervals (coarseEdge found) additional (localIndex found)).start
    (ParameterEdge.intervals (coarseEdge found) additional (localIndex found)).finish value

/-- Every bounded fine input stays inside the same original coarse parameter edge. -/
theorem parameter_bounds (ordered : left.parameter ≤ right.parameter) (value : Rational)
    (inside : 0 ≤ value ∧ value ≤ 1) :
    (coarseEdge found).left.parameter ≤ parameter found value ∧
      parameter found value ≤ (coarseEdge found).right.parameter := by
  have actual := bounds found ordered
  exact Geometry.Rational.Box.coordinate_between
    ⟨actual.1, actual.2.1.trans actual.2.2⟩ ⟨actual.1.trans actual.2.1, actual.2.2⟩ inside

/-- The same physical query remains in the original unit parameter interval, including either outer endpoint. -/
theorem parameter_inside (value : Rational) (inside : 0 ≤ value ∧ value ≤ 1) :
    0 ≤ parameter found value ∧ parameter found value ≤ 1 :=
  Cell.Restriction.parameter_inside
    ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).left.inside
    ((dyadicEdges (coarse + additional) left right)[index.val]'index.isLt).right.inside inside

/-- The original coarse input normalizes exactly the same common-edge physical parameter.

The complete retained occurrence supplies its original fine edge identity.
No coordinate inversion, strict physical displacement or new locator is used.
-/
theorem input_eq (value : Rational) : input found value =
    segmentParameter (coarseEdge found).left.parameter (coarseEdge found).right.parameter
      (parameter found value) := by
  have affine := segmentParameter_affine (coarseEdge found).left.parameter (coarseEdge found).right.parameter
    ((dyadicEdges additional (coarseEdge found).left (coarseEdge found).right)[
      (localIndex found).val]'(localIndex found).isLt).left.parameter
    ((dyadicEdges additional (coarseEdge found).left (coarseEdge found).right)[
      (localIndex found).val]'(localIndex found).isLt).right.parameter value
  exact affine.trans (congrArg (fun edge : ParameterEdge =>
    segmentParameter (coarseEdge found).left.parameter (coarseEdge found).right.parameter
      (Cell.Restriction.parameter edge.left.parameter edge.right.parameter value)) (edge_eq found).symm)

/-- Every original normalized coarse input stays in its unit interval with the actual dyadic bounds. -/
theorem input_inside (ordered : left.parameter ≤ right.parameter) (value : Rational)
    (inside : 0 ≤ value ∧ value ≤ 1) : 0 ≤ input found value ∧ input found value ≤ 1 := by
  have coarseBounds := dyadicEdges_bounds coarse left right ordered _ (List.getElem_mem (coarseIndex found).isLt)
  have endpoints := ParameterEdge.Restrictions.endpoints_inside
    (coarse := coarseEdge found) (depth := additional) coarseBounds.2.1 (localIndex found)
  exact Cell.Restriction.parameter_inside endpoints.1 endpoints.2 inside

end refinementOccurrence

namespace RefinementPair

variable {first last : Nat} {left right : Endpoint}
    {index : Fin (dyadicEdges (first + last) left right).length}
    (pair : RefinementPair first last left right index)

/-- The two actual retained coarse/fine outcomes read the identical original physical query parameter. -/
theorem parameter_eq (value : Rational) :
    refinementOccurrence.parameter pair.1 value = refinementOccurrence.parameter pair.2 value :=
  congrArg (fun edge : ParameterEdge => Cell.Restriction.parameter edge.left.parameter edge.right.parameter value)
    (commutedIndex_edge first last left right index).symm

/-- The second actual coarse input normalizes that SAME first-side physical fraction. -/
theorem last_input_eq (value : Rational) : refinementOccurrence.input pair.2 value =
    segmentParameter (refinementOccurrence.coarseEdge pair.2).left.parameter
      (refinementOccurrence.coarseEdge pair.2).right.parameter (refinementOccurrence.parameter pair.1 value) :=
  (refinementOccurrence.input_eq pair.2 value).trans
    (congrArg (segmentParameter (refinementOccurrence.coarseEdge pair.2).left.parameter
      (refinementOccurrence.coarseEdge pair.2).right.parameter) (pair.parameter_eq value).symm)

/-- The same first-side physical fraction lies inside the second actual retained coarse edge. -/
theorem last_bounds (ordered : left.parameter ≤ right.parameter) (value : Rational)
    (inside : 0 ≤ value ∧ value ≤ 1) :
    (refinementOccurrence.coarseEdge pair.2).left.parameter ≤ refinementOccurrence.parameter pair.1 value ∧
      refinementOccurrence.parameter pair.1 value ≤ (refinementOccurrence.coarseEdge pair.2).right.parameter :=
  Eq.mpr (congrArg (fun parameter : Rational =>
    (refinementOccurrence.coarseEdge pair.2).left.parameter ≤ parameter ∧
      parameter ≤ (refinementOccurrence.coarseEdge pair.2).right.parameter) (pair.parameter_eq value))
    (refinementOccurrence.parameter_bounds pair.2 ordered value inside)

end RefinementPair

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

end
