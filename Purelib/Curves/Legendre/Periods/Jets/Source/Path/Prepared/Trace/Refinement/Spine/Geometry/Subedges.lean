module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Subedges
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries

/-! # Rooted refinement of the original canonical parent word

The retained canonical center factory identifies the coarse parents with
those extracted from the original prepared path. Each actual cached Head
supplies its pointwise rooted subedge refinement; the unchanged following
cache supplies the tail. Canonical-cycle and integral realization remain
separate from this geometric refinement certificate.
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
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)

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
def subedgeRefinement (diameter : Rational) (positive : 0 < diameter)
    {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (lineage : TraceLineage prepared)
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) (factory : materialized = lineage.ownerPath)
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory)
    (canonical : centers = Centers.build lineage) :
    RootSubedgeRefinement (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet prepared).parents
      (parents diameter positive lineage centers materialized factory geometry) :=
  TraceLineage.casesOn
    (motive := fun {start finish _path owner} prepared lineage =>
      (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
      (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
        (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
      (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      centers = Centers.build lineage →
      RootSubedgeRefinement (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet prepared).parents
        (parents diameter positive lineage centers materialized factory geometry))
    lineage
    (fun _ _ _centers _materialized _factory _geometry _canonical => .nil)
    (fun {_start _middle _finish _segment _tail _owner _within first _middleOwner _rest}
        budget fits finishOwnerEq remaining centers _materialized _factory geometry canonical => by
      have selected := canonical.trans (Centers.build_cons (frame := frame) (basis := basis) (sheet := sheet)
        budget fits finishOwnerEq remaining)
      have headCenters := congrArg Prod.fst selected
      have tailCenters := congrArg Prod.snd selected
      let head := Refinement.Cache.Geometry.subedgeRefinement (frame := frame) (basis := basis)
        (sheet := sheet) (count := count) diameter positive budget first.subdivision centers.1 fits
        geometry.1.val.front geometry.2.1.val
      have headParents : (CenteredPathChain.dataOfCompleteSegment (Fibre.frameCurve frame) basis sheet first).parents =
          centeredEdges (Fibre.frameCurve frame) basis sheet first.subdivision centers.1 :=
        (CenteredPathChain.dataOfCompleteSegment_parents (Fibre.frameCurve frame) basis sheet first).trans
          (congrArg (centeredEdges (Fibre.frameCurve frame) basis sheet first.subdivision) headCenters.symm)
      let actualHead := Eq.mpr (congrArg (fun original => RootSubedgeRefinement original
        (Refinement.Cache.Geometry.parents diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val)) headParents) head
      have tailParents :
          (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet
            (PreparedPathTrace.PreparedPath.castOwner finishOwnerEq _rest)).parents =
          (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet _rest).parents := by
        cases finishOwnerEq
        rfl
      let tailResult := subedgeRefinement diameter positive remaining centers.2
        geometry.1.val.following geometry.1.val.following_eq geometry.2.2 tailCenters
      exact Eq.mpr (congrArg (fun original => RootSubedgeRefinement
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
def subedgeRefinement
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
    RootSubedgeRefinement (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet prepared).parents
      retained.parents :=
  Cache.Geometry.subedgeRefinement (frame := frame) (basis := basis) (sheet := sheet) (count := count)
    diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory) retained.cache
    (retained.centers_eq.trans canonical)

/-- The original root-closed walk's actual initial parents refine to its SAME retained sheet-zero children.

The original initial-state parent readback supplies the coarse-word identity.
This transfers signed pointwise root evidence; it supplies no parameter-loop
monodromy or independent canonical homology or integral comparison.
-/
def initialSubedges
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := 0) closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner closed.traced.prepared)}
    {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (canonical : inputCenters = Centers.build closed.traced.lineage) :
    RootSubedgeRefinement (closed.initial (curve := Fibre.frameCurve frame) basis).state.parents retained.parents :=
  Eq.mpr (congrArg (fun original => RootSubedgeRefinement original retained.parents)
    (closed.initial_parents (curve := Fibre.frameCurve frame) basis)) (retained.subedgeRefinement canonical)

/-- Refine the SAME retained period walk's original initial parent cache to its actual geometric children.

The period's whole initial-state factory transports the original closed-walk
readback. Its A or corrected-B word, signed roots and existing preparations
are retained unchanged; no period programme or geometric owner is rebuilt.
-/
def periodSubedges
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
    RootSubedgeRefinement period.initial.state.parents retained.parents :=
  Eq.mpr (congrArg (fun current => RootSubedgeRefinement current.state.parents retained.parents)
    period.initial_eq) (initialSubedges owner period.closed retained canonical)

end Geometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
