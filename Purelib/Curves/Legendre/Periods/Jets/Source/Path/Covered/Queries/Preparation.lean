module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Riemann.Integration.PreparedConstantModels

/-! # All-query agreement across actual preparations on the same original cover

The old and new preparations keep their actual Targets, query requests and
observations. Original patch comparisons attach their retained sample owners
to the same two original direct edge Queries. The old all-query invariant
then transports to the new preparation without a new root or bank admission.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.QueryAgreement

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

/-- Transport genuine all-query agreement to another actual preparation of the SAME original covered parents.

Each invocation materializes two old observation bundles and two original
direct edge Queries once. Those are genuinely new callback work; they are
not claimed to be historical cache reuse. The two supplied new bundles are
consumed unchanged. Both whole original parent/patch owners and Targets stay
indexed, and no desired new signed relation or Completion is supplied.
-/
def reprepare
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} {firstFloor lastFloor : Nat}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat} {firstTargets : CellEndpoints.Targets firstPath firstStage}
    {lastTargets : CellEndpoints.Targets lastPath lastStage}
    (first : PreparedParents covered firstFloor firstTargets)
    (last : PreparedParents covered lastFloor lastTargets) (agreement : QueryAgreement first) :
    QueryAgreement last := by
  intro firstIndex lastIndex firstInput lastInput firstInside lastInside firstObserved lastObserved sameKey
  let oldFirst := (first.entry firstIndex).preparation.query.observe frame
    firstInput firstInside.1 firstInside.2
  let oldLast := (first.entry lastIndex).preparation.query.observe frame
    lastInput lastInside.1 lastInside.2
  let firstDirect := PreparedEdge.Query.build (parents[firstIndex.val]'firstIndex.isLt).edge firstInput firstInside
  let lastDirect := PreparedEdge.Query.build (parents[lastIndex.val]'lastIndex.isLt).edge lastInput lastInside
  have firstPoint := ((first.entry firstIndex).queryPoint_eq firstInput).trans
    ((last.entry firstIndex).queryPoint_eq firstInput).symm
  have lastPoint := ((first.entry lastIndex).queryPoint_eq lastInput).trans
    ((last.entry lastIndex).queryPoint_eq lastInput).symm
  have oldKey :
      (⟨(first.entry firstIndex).preparation.cell.models.coordinate.point firstInput,
        (parents[firstIndex.val]'firstIndex.isLt).edge.sheet⟩ : LiftedPoint 2) =
        ⟨(first.entry lastIndex).preparation.cell.models.coordinate.point lastInput,
          (parents[lastIndex.val]'lastIndex.isLt).edge.sheet⟩ :=
    (congrArg (fun point : Canonical =>
      (⟨point, (parents[firstIndex.val]'firstIndex.isLt).edge.sheet⟩ : LiftedPoint 2)) firstPoint).trans
      (sameKey.trans (congrArg (fun point : Canonical =>
        (⟨point, (parents[lastIndex.val]'lastIndex.isLt).edge.sheet⟩ : LiftedPoint 2)) lastPoint).symm)
  let oldRoots := agreement firstIndex lastIndex firstInput lastInput firstInside lastInside oldFirst oldLast oldKey
  let firstOld := (first.entry firstIndex).querySampleEquivalent
    firstInput firstInside oldFirst.retained.sample firstDirect
  let firstNew := (last.entry firstIndex).querySampleEquivalent
    firstInput firstInside firstObserved.retained.sample firstDirect
  let lastOld := (first.entry lastIndex).querySampleEquivalent
    lastInput lastInside oldLast.retained.sample lastDirect
  let lastNew := (last.entry lastIndex).querySampleEquivalent
    lastInput lastInside lastObserved.retained.sample lastDirect
  exact firstNew.symm.trans (firstOld.trans (oldRoots.trans (lastOld.symm.trans lastNew)))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.QueryAgreement

end
