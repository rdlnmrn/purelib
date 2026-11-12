module

public import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints
import Purelib.Data.Rat.Fraction.Field

/-! # Retained actual queries for original parent/child root comparisons

The endpoint selector keeps the two GIVEN original QueryAt records at
fractions zero and one. Only strict interior fractions execute the original
query producer. The comparison reuses the original fixed-box path and
retained-owner algorithm on those SAME cached query Owners.
-/

public section

namespace Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge RootChildAt)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- Original actual queries at their exact original affine edge points, without replacing their nominal parent. -/
@[expose] def Queries (edge : PreparedEdge curve differential) :=
  (fraction : Rational) → (inside : 0 ≤ fraction ∧ fraction ≤ 1) → QueryAt edge fraction inside (edge.point fraction)

namespace Queries

/-- Read a supplied original query at an exactly identified physical point by whole-record index transport only. -/
def atPoint {edge : PreparedEdge curve differential} (queries : Queries edge)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) {point : Gaussian}
    (equal : edge.point fraction = point) : QueryAt edge fraction inside point :=
  (queries fraction inside).castPoint equal

/-- The original uncached query provider, retaining its original point-index transport and query operation. -/
@[expose] def original (edge : PreparedEdge curve differential) : Queries edge :=
  fun fraction inside => queryAt edge fraction inside rfl

/-- Keep both original endpoint query caches; execute the original producer only at strict interior fractions.

The actual first and last Owner records are read from the GIVEN queries.
Fraction equalities transport those whole records with their original
name/refinement certificates. Neither endpoint Owner is acquired again.
-/
@[expose] def withEndpoints (edge : PreparedEdge curve differential)
    (first : QueryAt edge 0 edge.baseInside (edge.point 0))
    (last : QueryAt edge 1 (of_decide_eq_true rfl) (edge.point 1)) : Queries edge :=
  fun fraction inside =>
    if atFirst : fraction = 0 then by
      cases atFirst
      exact first
    else if atLast : fraction = 1 then by
      cases atLast
      exact last
    else queryAt edge fraction inside rfl

/-- The zero-fraction selector returns the SAME complete supplied endpoint query. -/
theorem withEndpoints_zero (edge : PreparedEdge curve differential)
    (first : QueryAt edge 0 edge.baseInside (edge.point 0))
    (last : QueryAt edge 1 (of_decide_eq_true rfl) (edge.point 1)) :
    withEndpoints edge first last 0 edge.baseInside = first := by
  unfold withEndpoints
  rewrite [dif_pos rfl]
  rfl

/-- The unit-fraction selector returns the independent SAME complete supplied finishing query. -/
theorem withEndpoints_one (edge : PreparedEdge curve differential)
    (first : QueryAt edge 0 edge.baseInside (edge.point 0))
    (last : QueryAt edge 1 (of_decide_eq_true rfl) (edge.point 1)) :
    withEndpoints edge first last 1 (of_decide_eq_true rfl) = last := by
  unfold withEndpoints
  rewrite [dif_neg (of_decide_eq_true rfl : (1 : Rational) ≠ 0), dif_pos rfl]
  rfl

end Queries

/-- Compare two original parent queries using the GIVEN provider and original fixed-box budget.

The two supplied query records keep both actual Owner values. Only the
whole point index of the first record changes; the original compareQueries
algorithm derives the signed relation from their genuine box refinements.
-/
def samePointEquivalentUsing {parent : PreparedEdge curve differential} (budget : ParentBudget parent)
    (queries : Queries parent) (first second : Rational) (firstInside : 0 ≤ first ∧ first ≤ 1)
    (secondInside : 0 ≤ second ∧ second ≤ 1) (equal : parent.point first = parent.point second) :
    NamedEquivalent (parent.rootName first firstInside) (parent.rootName second secondInside) :=
  compareQueries budget (queries.atPoint first firstInside equal) (queries second secondInside)
    (budget.pointMovement second secondInside rfl)

/-- Propagate an original child-start relation using the SAME given parent and child query providers.

All four actual query records are selected once, before the retained
comparison is returned. The existing pathData and retainedEquivalent
constructors perform the finite comparison on their original budgets,
Owners, name equations and box-refinement witnesses. A parent endpoint
provider can therefore reuse its GIVEN coarse endpoint Owners throughout.
-/
def queryEquivalentUsing {parent child : CenteredEdge curve differential}
    (budget : ParentBudget parent.edge) (childBudget : ParentBudget child.edge)
    (parentQueries : Queries parent.edge) (childQueries : Queries child.edge)
    (start : RootChildAt parent child) (childFraction : Rational)
    (childInside : 0 ≤ childFraction ∧ childFraction ≤ 1)
    (finishFraction : Rational) (finishInside : 0 ≤ finishFraction ∧ finishFraction ≤ 1)
    (finishEq : parent.edge.point finishFraction = child.edge.point childFraction) :
    NamedEquivalent (parent.edge.rootName finishFraction finishInside)
      (child.edge.rootName childFraction childInside) :=
  let path := pathData budget childBudget start childFraction childInside finishFraction finishInside finishEq
  have zeroPoint : child.edge.point 0 = child.edge.point (childFraction * 0) :=
    congrArg child.edge.point (Data.Rat.Fraction.Field.mul_zero_direct childFraction).symm
  have onePoint : child.edge.point childFraction = child.edge.point (childFraction * 1) :=
    congrArg child.edge.point (Data.Rat.Fraction.Field.mul_one_direct childFraction).symm
  let firstStart := parentQueries.atPoint start.fraction start.inside (start.point_eq.trans zeroPoint)
  let secondStart := childQueries.atPoint 0 child.edge.baseInside zeroPoint
  let firstFinish := parentQueries.atPoint finishFraction finishInside (finishEq.trans onePoint)
  let secondFinish := childQueries.atPoint childFraction childInside onePoint
  let startAgreement := NamedEquivalent.transport firstStart.name_eq.symm secondStart.name_eq.symm start.rootEquivalent
  let retained := path.retainedEquivalent firstStart.owner secondStart.owner firstStart.refines secondStart.refines
    startAgreement firstFinish.owner secondFinish.owner firstFinish.refines secondFinish.refines
  NamedEquivalent.transport firstFinish.name_eq secondFinish.name_eq retained

end Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints

end
