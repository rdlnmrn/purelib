module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly
public import Purelib.Polynomial.Geometry.ClearPath.HalfOpen
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.HalfOpen
import Purelib.Data.List.Membership
import Purelib.Data.Fin

/-! # Literal half-open visits of the same retained physical source occurrences

Every original child source uses its own acquired Segment, actual Mesh and
original Parents. Strict progress puts that same point below its physical
endpoint. Structural lookup injects the witness into the unchanged Route;
no source, query, continuation, Owner or path is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine.Sources

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain (PreparedPathCenteredData)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- The retained physical parent-word list has exactly one entry per original clear-path Segment occurrence. -/
theorem parentWords_length
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (parentWords width path within owner retained sources).length = path.segmentCount
  | _, _, .nil _, _, _, _, _ => rfl
  | _, _, .cons _head tail, within, _owner, retained, sources =>
      congrArg Nat.succ (parentWords_length width tail within.tail retained.1.traced.finishOwner retained.2
        sources.2.2)
termination_by structural _ _ path _ _ _ _ => path

/-- A half-open visit of the selected original segment is a visit of the unchanged physical path. -/
private theorem segmentAt_visit
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) : {start finish : Canonical} →
    (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (outer : Fin (parentWords width path within owner retained sources).length) →
    (point : Canonical) →
    (ClearPath.cons (segmentAt width path within owner retained sources outer).segment
      (ClearPath.nil (segmentAt width path within owner retained sources outer).endpoints.2)).HalfOpen point →
    path.HalfOpen point
  | _, _, .nil _, _, _, _, _, outer, _, _ => Fin.elim0 outer
  | _, _, .cons _head tail, within, _owner, retained, sources, outer, point, visit => by
      revert visit
      refine Data.Fin.cases_induction ?_ (fun next => ?_) outer
      · intro here
        cases here with
        | inl atHead => exact Or.inl atHead
        | inr impossible => exact False.elim impossible
      · intro here
        exact Or.inr (segmentAt_visit width tail within.tail retained.1.traced.finishOwner
          retained.2 sources.2.2 next point here)
termination_by structural _ _ path _ _ _ _ _ _ _ => path

/-- The selected actual original child source belongs to the SAME retained Route's half-open moving image.

The child's paid mesh proves a half-open visit of its retained physical
segment. Structural lookup injects that visit into the unchanged path.
Degenerate physical edges keep their actual strict child parameters.
-/
theorem segmentAt_halfOpen
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) {start finish : Canonical}
    (path : ClearPath (Paths.polynomial parameter) ambient start finish)
    (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
    (retained : Acquisition.Spine width path within owner)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained)
    (outer : Fin (parentWords width path within owner retained sources).length)
    (child : Fin (segmentAt width path within owner retained sources outer).parents.covered.parents.length) :
    path.HalfOpen
      (((segmentAt width path within owner retained sources outer).parents.covered.parents[child.val]'
        child.isLt).edge.point 0) := by
  let selected := segmentAt width path within owner retained sources outer
  exact segmentAt_visit width path within owner retained sources outer _
    (selected.parents.child_start_halfOpen _ (List.getElem_mem child.isLt))

section Located

variable {width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
  AccuracyRequest}
variable {start finish : Canonical}
variable (path : ClearPath (Paths.polynomial parameter) ambient start finish)
variable (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
variable (retained : Acquisition.Spine width path within owner)
variable (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width path within owner retained)
variable (index : Fin (assemble width path within owner retained sources).geometry.parents.length)
variable (position : Data.List.Flatten.Occurrence (parentWords width path within owner retained sources)
  (flattenedIndex path within owner retained sources index))

include position

/-- The SAME retained location derives the actual assembled source's half-open visit without another lookup. -/
theorem located_halfOpen :
    path.HalfOpen (((assemble width path within owner retained sources).geometry.parents[index.val]'
      index.isLt).edge.point 0) := by
  have original := segmentAt_halfOpen width path within owner retained sources position.1
    (child path within owner retained sources index position)
  have same := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge.point 0)
    (parent_eq path within owner retained sources index position)
  exact Eq.mpr (congrArg (fun point => path.HalfOpen point) same) original

end Located

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine.Sources

end
