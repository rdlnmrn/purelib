module

public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
import Purelib.Curves.Legendre.Periods.Fibre

/-! # Signed agreement of actual prepared queries at the same lifted point

This invariant concerns every actual indexed parent query, including
strict interior fractions and repeated occurrences on unrelated parents.
It is stronger than an adjacent or returning RootChain. The two retained
observation bundles, whole lifted-point equality and both exact prepared
source owners remain explicit; no coordinates or labels choose a root.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Read the original prepared model coordinate and parent sheet at one actual indexed query.

The original preparation, parent, parameter and sheet remain unchanged.
This projection names their exact lifted key; it performs no observation,
root selection, coordinate continuation or request preparation.
-/
@[expose] def queryKey (prepared : PreparedParents covered floor targets) (index : Fin parents.length)
    (input : Rational) : LiftedPoint 2 :=
  ⟨(prepared.entry index).preparation.cell.models.coordinate.point input,
    (parents[index.val]'index.isLt).edge.sheet⟩

/-- Actual query roots agree at every same lifted point of this SAME retained prepared-parent family.

Both bounded occurrences, physical fractions, unit-interval payments and
complete original observation bundles are inputs. Their whole lifted keys
contain the actual model coordinate and original parent sheet. This exact
function type adds no owner, cache, runtime identifier or replacement root.
-/
@[expose] def QueryAgreement (prepared : PreparedParents covered floor targets) :=
  (firstIndex lastIndex : Fin parents.length) →
  (firstInput lastInput : Rational) →
  (_firstInside : 0 ≤ firstInput ∧ firstInput ≤ 1) →
  (_lastInside : 0 ≤ lastInput ∧ lastInput ≤ 1) →
  (first : CellModels.Observations frame
    (PreparedParent.liftedCell (parents[firstIndex.val]'firstIndex.isLt))
    (prepared.entry firstIndex).preparation.cell.models
    (prepared.entry firstIndex).preparation.query.requests firstInput) →
  (last : CellModels.Observations frame
    (PreparedParent.liftedCell (parents[lastIndex.val]'lastIndex.isLt))
    (prepared.entry lastIndex).preparation.cell.models
    (prepared.entry lastIndex).preparation.query.requests lastInput) →
  queryKey prepared firstIndex firstInput = queryKey prepared lastIndex lastInput →
  NamedEquivalent first.retained.sample.certificate.value.name last.retained.sample.certificate.value.name

namespace QueryAgreement

/-- Signed agreement of strict root queries on the same original prepared-parent family.

Both actual direct Queries, interval bounds and strict terminal exclusions
are inputs. The relation uses the entire original lifted key, including its
sheet. This exact function type retains both independently queried roots.
-/
@[expose] def StrictRoots (prepared : PreparedParents covered floor targets) :=
  (leftIndex rightIndex : Fin parents.length) →
  (leftFraction rightFraction : Rational) →
  (leftInside : 0 ≤ leftFraction ∧ leftFraction ≤ 1) →
  (rightInside : 0 ≤ rightFraction ∧ rightFraction ≤ 1) →
  (_leftBelow : leftFraction < 1) → (_rightBelow : rightFraction < 1) →
  (_leftDirect : PreparedEdge.Query (parents[leftIndex.val]'leftIndex.isLt).edge leftFraction leftInside) →
  (_rightDirect : PreparedEdge.Query (parents[rightIndex.val]'rightIndex.isLt).edge rightFraction rightInside) →
  queryKey prepared leftIndex leftFraction = queryKey prepared rightIndex rightFraction →
  NamedEquivalent ((parents[leftIndex.val]'leftIndex.isLt).edge.rootName leftFraction leftInside)
    ((parents[rightIndex.val]'rightIndex.isLt).edge.rootName rightFraction rightInside)

/-- Exact target-cache equality transports agreement on the SAME whole original preparation product.

Equality elimination preserves every parent, model, query, RootOwner and
observation input. No source preparation, query callback or numerical
accuracy is recomputed, substituted or assigned a different request.
-/
def castTargets {replacement : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets) (equal : targets = replacement)
    (retained : QueryAgreement prepared) : QueryAgreement (PreparedParents.castTargets prepared equal) := by
  cases equal
  exact retained

/-- Whole target-index transport retains the identical original query-agreement operation heterogeneously. -/
theorem castTargets_heq {replacement : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets) (equal : targets = replacement)
    (retained : QueryAgreement prepared) : HEq (castTargets prepared equal retained) retained := by
  cases equal
  unfold castTargets
  rfl

end QueryAgreement

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
