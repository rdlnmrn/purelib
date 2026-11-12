module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.HalfOpen
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual interior fractions in the original acquired segment's half-open image

The SAME retained mesh pays strict child progress. Its original centered
parent equation reads each arbitrary fraction on that actual segment.
Fractions strictly below one stay below the child request endpoint, so
they inherit the existing half-open window predicate. Fraction one keeps
its separate actual endpoint and needs the original next/return handoff.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge centeredEdges centeredEdges_point)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
    {differential : Differential genus} {sheet : Fin 2} {count : Nat}
    {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
    (parents : Parents differential sheet count retained)

/-- A strict interior fraction of an actual acquired child lies below its original requested endpoint parameter.

The original paid mesh and unchanged parents equation supply strict
progress. The bound therefore holds for this actual child, including
geometrically constant physical segments, without a new mesh or depth.
-/
theorem child_query_parameter_lt_right (child : CenteredEdge curve differential)
    (member : child ∈ parents.covered.parents) (fraction : Rational) (below : fraction < 1) :
    PreparedSheetContinuation.parameterAt child.edge.left child.edge.request fraction <
      child.edge.request.endpoint.parameter := by
  have strict := parents.child_parameter_strict child member
  change child.edge.left.parameter < child.edge.request.endpoint.parameter at strict
  have positive := Arithmetic.sub_pos_direct strict
  have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct below positive
  have shifted := Arithmetic.add_lt_add_left_direct scaled child.edge.left.parameter
  have endpoint : child.edge.left.parameter +
      1 * (child.edge.request.endpoint.parameter - child.edge.left.parameter) =
        child.edge.request.endpoint.parameter := by ring1
  exact Eq.mpr (congrArg (fun value => value < child.edge.request.endpoint.parameter)
    (PreparedSheetContinuation.parameterAt_eq_affine child.edge.left child.edge.request fraction))
    (shifted.trans_eq endpoint)

/-- Every admitted strict interior fraction of an actual acquired child has a literal original half-open visit.

Only the retained parent occurrence, its mesh strictness and original
all-fraction point law are used. This statement does not include fraction
one or substitute it by a source query at a different occurrence.
-/
theorem child_query_halfOpen (child : CenteredEdge curve differential)
    (member : child ∈ parents.covered.parents) (fraction : Rational)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (below : fraction < 1) :
    (ClearPath.cons segment (ClearPath.nil finish)).HalfOpen (child.edge.point fraction) := by
  have original : child ∈ centeredEdges curve differential sheet
      retained.traced.prepared.subdivision parents.centers :=
    Eq.mp (congrArg (fun entries => child ∈ entries) parents.parents_eq) member
  have nonnegative := (PreparedSheetContinuation.parameterAt_inside
    child.edge.left child.edge.request child.edge.ordered fraction inside).1
  have upper := (parents.child_query_parameter_lt_right child member fraction below).trans_le
    child.edge.request.endpoint.inside.2
  exact Or.inl ⟨PreparedSheetContinuation.parameterAt child.edge.left child.edge.request fraction,
    nonnegative, upper, centeredEdges_point curve differential sheet
      retained.traced.prepared.subdivision parents.centers child original fraction⟩

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
