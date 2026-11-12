module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Directed
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
public import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Paths.PreparedPathTrace
public import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements

/-! # Directed grouping of the SAME actual geometric child word

Each actual original block contributes its own positive displacement
factors and original signed subedge certificates. Literal empty branches,
whole center/Owner transports and original parent-list factories remain
separate. This proposition is finite source grouping, not a new runtime
root, query, geometry or independently canonical cycle construction.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (centeredEdges)
open Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels (canonicalCenterStates)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements (DirectedRefinement)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Cache.Geometry

/-- Refine the original canonical parent extraction using the SAME actual whole child-geometry cache.

The retained center-selection factory identifies each complete segment's
original parents. Equality elimination transports its original finishing
Owner and the unchanged following cache together. Every child retains its
parent location and signed root-query comparison at all rational parameters;
no new source, root, Head or geometry preparation is executed.
-/
theorem directedRefinement (diameter : Rational) (positive : 0 < diameter)
    {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (lineage : TraceLineage prepared)
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) (factory : materialized = lineage.ownerPath)
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory)
    (canonical : centers = Centers.build lineage) :
    DirectedRefinement (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet prepared).parents
      (parents diameter positive lineage centers materialized factory geometry) :=
  TraceLineage.casesOn
    (motive := fun {start finish _path owner} prepared lineage =>
      (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
      (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
        (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
      (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      centers = Centers.build lineage →
      DirectedRefinement (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet prepared).parents
        (parents diameter positive lineage centers materialized factory geometry))
    lineage
    (fun _ _ _centers _materialized _factory _geometry _canonical => .nil)
    (fun {_start _middle _finish _segment _tail _owner _within first _middleOwner _rest}
        budget fits finishOwnerEq remaining centers _materialized _factory geometry canonical => by
      have selected := canonical.trans (Centers.build_cons (frame := frame) (basis := basis) (sheet := sheet)
        budget fits finishOwnerEq remaining)
      have headCenters := congrArg Prod.fst selected
      have tailCenters := congrArg Prod.snd selected
      let head := Refinement.Cache.Geometry.directedRefinement (frame := frame) (basis := basis)
        (sheet := sheet) (count := count) diameter positive budget first.subdivision centers.1 fits
        geometry.1.val.front geometry.2.1.val
      have headParents : (CenteredPathChain.dataOfCompleteSegment (Fibre.frameCurve frame) basis sheet first).parents =
          centeredEdges (Fibre.frameCurve frame) basis sheet first.subdivision centers.1 :=
        (CenteredPathChain.dataOfCompleteSegment_parents (Fibre.frameCurve frame) basis sheet first).trans
          (congrArg (centeredEdges (Fibre.frameCurve frame) basis sheet first.subdivision) headCenters.symm)
      let actualHead := Eq.mpr (congrArg (fun original => DirectedRefinement original
        (Refinement.Cache.Geometry.parents diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val)) headParents) head
      have tailParents :
          (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet
            (PreparedPathTrace.PreparedPath.castOwner finishOwnerEq _rest)).parents =
          (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet _rest).parents := by
        cases finishOwnerEq
        rfl
      let tailResult := directedRefinement diameter positive remaining centers.2
        geometry.1.val.following geometry.1.val.following_eq geometry.2.2 tailCenters
      exact Eq.mpr (congrArg (fun original => DirectedRefinement
        ((CenteredPathChain.dataOfCompleteSegment (Fibre.frameCurve frame) basis sheet first).parents ++ original)
        (parents diameter positive (.cons budget fits finishOwnerEq remaining) centers
          _materialized _factory geometry)) tailParents) (actualHead.append tailResult))
    centers materialized factory geometry canonical
termination_by structural lineage

end Cache.Geometry

namespace Geometry

/-- The given whole canonical center factory yields rooted refinement from its original prepared parent list.

Definitions of source programs and canonical periods remain independent of
this certificate. Its child list is precisely the list retained by the
actual geometry, including stationary and repeated occurrences.
-/
theorem directedRefinement
    {start finish : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath clearPath owner}
    {lineage : TraceLineage prepared}
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
    {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive lineage inputCenters materialized factory)
    (canonical : inputCenters = Centers.build lineage) :
    DirectedRefinement (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet prepared).parents
      retained.parents :=
  Cache.Geometry.directedRefinement (frame := frame) (basis := basis) (sheet := sheet) (count := count)
    diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory) retained.cache
    (retained.centers_eq.trans canonical)

/-- The original root-closed walk's actual initial parents refine to its SAME retained sheet-zero children.

The original initial-state parent readback supplies the coarse-word identity.
This transfers signed pointwise root evidence; it supplies no parameter-loop
monodromy or independent canonical homology or integral comparison.
-/
theorem initialDirected
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner closed.traced.prepared)}
    {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (canonical : inputCenters = Centers.build closed.traced.lineage) :
    DirectedRefinement (closed.initial (curve := Fibre.frameCurve frame) basis).state.parents retained.parents :=
  Eq.mpr (congrArg (fun original => DirectedRefinement original retained.parents)
    (closed.initial_parents (curve := Fibre.frameCurve frame) basis)) (retained.directedRefinement canonical)

/-- Refine the SAME retained period walk's original initial parent cache to its actual geometric children.

The period's whole initial-state factory transports the original closed-walk
readback. Its A or corrected-B word, signed roots and existing preparations
are retained unchanged; no period programme or geometric owner is rebuilt.
-/
theorem periodDirected
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base))
    (period : PeriodWalk (curve := Fibre.frameCurve frame) grid base owner basis)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) period.closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner period.closed.traced.prepared)}
    {factory : materialized = period.closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive period.closed.traced.lineage inputCenters materialized factory)
    (canonical : inputCenters = Centers.build period.closed.traced.lineage) :
    DirectedRefinement period.initial.state.parents retained.parents :=
  Eq.mpr (congrArg (fun current => DirectedRefinement current.state.parents retained.parents)
    period.initial_eq) (initialDirected owner period.closed retained canonical)

/-- The actual retained children group on the literal original period's clear-path segments.

The period initial-state factory identifies its original coarse parents;
the actual positive-scale child blocks supply directed refinement. The
original PathSources.refine operation then preserves the same full path,
stationary outer roles and ordered original source segments. No root or
geometric return is inferred from a coordinate or numerical closure test.
-/
theorem periodSources
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base))
    (period : PeriodWalk (curve := Fibre.frameCurve frame) grid base owner basis)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) period.closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner period.closed.traced.prepared)}
    {factory : materialized = period.closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive period.closed.traced.lineage inputCenters materialized factory)
    (canonical : inputCenters = Centers.build period.closed.traced.lineage) :
    PathSources 0 period.closed.walk.path retained.parents := by
  have parentEq := (congrArg (fun current => current.state.parents) period.initial_eq).trans
    (period.closed.initial_parents (curve := Fibre.frameCurve frame) basis)
  have original : PathSources 0 period.closed.walk.path period.initial.state.parents :=
    Eq.mpr (congrArg (fun parents => PathSources 0 period.closed.walk.path parents) parentEq)
      (PathSources.ofPreparedPath (curve := Fibre.frameCurve frame) basis 0 period.closed.traced.prepared)
  exact original.refine (retained.periodDirected owner period canonical)

end Geometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
