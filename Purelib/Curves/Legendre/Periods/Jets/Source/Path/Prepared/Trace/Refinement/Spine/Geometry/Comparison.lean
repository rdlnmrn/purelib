module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry
import Purelib.Riemann.Paths.PreparedPathTrace.Materialized.Primitive
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
import Purelib.Tactic.Ring

/-! # Actual whole old-Spine comparison on given pre-observation geometry

The retained original materialized heads supply the same path splits,
raw Traces and following paths. Only old observations are split afterward;
source comparisons consume the given covered geometry banks. The existing
Cache.Completion owns the resulting telescope and integral-error bound.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Cache

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Geometry

variable {diameter : Rational} {positive : 0 < diameter}
variable {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
variable {lineage : TraceLineage prepared}
variable {centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {firstPath lastPath : OwnerPath (Paths.polynomial parameter) start owner finish
  (PreparedPathGluing.finishOwner prepared)}
variable {firstFactory : firstPath = lineage.ownerPath} {lastFactory : lastPath = lineage.ownerPath}

/-- Transport the same whole geometry bank through exact complete materialized-path equality.

Both original whole-path factory proofs remain indices. This operation
executes no split, trace, query, Owner or geometry constructor; all actual
retained cache values survive unchanged.
-/
def castPath (same : firstPath = lastPath)
    (retained : Geometry (count := count) diameter positive lineage centers firstPath firstFactory) :
    Geometry (count := count) diameter positive lineage centers lastPath lastFactory := by
  cases same
  exact retained

/-- Reflexive whole-path transport retains the SAME complete original geometry value.

This readback exposes only the given-value identity. The path transport
operation and its body remain opaque to source-bank consumers.
-/
theorem castPath_refl
    (retained : Geometry (count := count) diameter positive lineage centers firstPath firstFactory) :
    castPath (firstFactory := firstFactory) (lastFactory := firstFactory) rfl retained = retained := by
  unfold castPath
  rfl

/-- Exact complete path-index transport preserves the total actual child count. -/
theorem castPath_childCount (same : firstPath = lastPath)
    (retained : Geometry (count := count) diameter positive lineage centers firstPath firstFactory) :
    childCount diameter positive lineage centers lastPath lastFactory (castPath same retained) =
      childCount diameter positive lineage centers firstPath firstFactory retained := by
  cases same
  rfl

end Geometry

variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {floor : Nat} {accuracy : AccuracyRequest}

/-- Compare the actual old Spine to source sums on the same retained whole geometry without splitting its path again.

Every original Head supplies its already computed materialized split.
The existing withObservedHead operation splits only the given old Spine.
Whole original Trace/path factory equalities transport the same geometry
banks to its actual callbacks; no coordinate or sheet label identifies
an Owner. Existing Completion.cons supplies the exact original telescope.
-/
def fromGeometry (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    Geometry (count := count) diameter positive lineage centers materialized factory →
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) →
      Completion (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers materialized observed
  | _, _, _, _, _, .nil _ _, _centers, _materialized, factory, _geometry, observed => by
      refine ⟨PUnit.unit, ?_⟩
      cases factory
      change (0 : Canonical) = observed.first.value - observed.first.value - 0
      ring1
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory, geometry, observed =>
      geometry.1.val.withData
        (TraceLineage.withObservedHead
          first budget fits finishOwnerEq remaining materialized observed
          (fun _divided _dividedFactory _same front _frontKept followingPath _followingKept followingFactory
              _views _viewsFactory headObserved _headKept tailObserved _tailKept firstValue lastValue shared =>
            have sameTrace : geometry.1.val.front = front :=
              PreparedTraceBudget.Trace.eq_of_factories geometry.1.val.front front
            let headGeometry := Refinement.Cache.Geometry.castTrace (frame := frame) (basis := basis)
              (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
              (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
              sameTrace geometry.2.1.val
            let compared := Refinement.compareFromGeometry (frame := frame) (basis := basis) (sheet := sheet)
              (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
              row diameter positive request budget first.subdivision centers.1 fits front headGeometry headObserved
            have sameFollowing : geometry.1.val.following = followingPath :=
              geometry.1.val.following_eq.trans followingFactory.symm
            let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
              (count := count) (diameter := diameter) (positive := positive)
              (lineage := remaining) (centers := centers.2)
              (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
              sameFollowing geometry.2.2
            let following := fromGeometry row diameter positive request remaining centers.2
              followingPath followingFactory followingGeometry tailObserved
            Completion.cons (frame := frame) (basis := basis) (sheet := sheet)
              (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
              row diameter positive request first budget fits finishOwnerEq remaining centers materialized observed
              front headObserved compared followingPath tailObserved following firstValue lastValue shared))
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ => lineage

/-- The numerical completion has exactly the child count retained before any old observation request was selected.

Pointwise laws of the original opaque observer transport this scalar
projection. Every head count comes from the same retained raw bank and
every tail count from the same whole-path index transport; no private
observation body or alternate whole factory is reduced by this proof.
-/
theorem fromGeometry_childCount
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) →
      childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers
        (fromGeometry (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request lineage centers materialized factory geometry observed).val =
      Geometry.childCount diameter positive lineage centers materialized factory geometry
  | _, _, _, _, _, .nil _ _, _, _, _, _, _ => rfl
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory, geometry, observed => by
      let project := fun completed : Completion (count := count) (floor := floor) (targets := targets)
          (accuracy := accuracy) row diameter positive request
          (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
          centers materialized observed =>
        childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request
          (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
          centers completed.val
      let expected := Geometry.childCount diameter positive
        (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
        centers materialized factory geometry
      let consume : TraceLineage.ObservedHeadConsumer
          first budget fits finishOwnerEq remaining materialized observed
          (Completion (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request
            (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
            centers materialized observed) :=
        fun _divided _dividedFactory _same front _frontKept followingPath _followingKept followingFactory
            _views _viewsFactory headObserved _headKept tailObserved _tailKept firstValue lastValue shared =>
          have sameTrace : geometry.1.val.front = front :=
            PreparedTraceBudget.Trace.eq_of_factories geometry.1.val.front front
          let headGeometry := Refinement.Cache.Geometry.castTrace (frame := frame) (basis := basis)
            (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
            (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
            sameTrace geometry.2.1.val
          let compared := Refinement.compareFromGeometry (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request budget first.subdivision centers.1 fits front headGeometry headObserved
          have sameFollowing : geometry.1.val.following = followingPath :=
            geometry.1.val.following_eq.trans followingFactory.symm
          let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (diameter := diameter) (positive := positive)
            (lineage := remaining) (centers := centers.2)
            (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
            sameFollowing geometry.2.2
          let following := fromGeometry row diameter positive request remaining centers.2
            followingPath followingFactory followingGeometry tailObserved
          Completion.cons (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request first budget fits finishOwnerEq remaining centers materialized observed
            front headObserved compared followingPath tailObserved following firstValue lastValue shared

      let mapped : TraceLineage.ObservedHeadConsumer
          first budget fits finishOwnerEq remaining materialized observed Nat :=
        fun divided dividedFactory same front frontKept followingPath followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared =>
          project (consume divided dividedFactory same front frontKept followingPath followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared)
      let ignored : TraceLineage.ObservedHeadConsumer
          first budget fits finishOwnerEq remaining materialized observed Nat :=
        fun _divided _dividedFactory _same _front _frontKept _followingPath _followingKept _followingFactory
            _views _viewsFactory _headObserved _headKept _tailObserved _tailKept _firstValue _lastValue _shared =>
          expected
      have each : ∀ divided dividedFactory same front frontKept followingPath followingKept followingFactory
          views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared,
          mapped divided dividedFactory same front frontKept followingPath followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared =
          ignored divided dividedFactory same front frontKept followingPath followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared := by
        intro divided dividedFactory same front frontKept followingPath followingKept followingFactory
          views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared
        have sameTrace : geometry.1.val.front = front :=
          PreparedTraceBudget.Trace.eq_of_factories geometry.1.val.front front
        let headGeometry := Refinement.Cache.Geometry.castTrace (frame := frame) (basis := basis)
          (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits) sameTrace geometry.2.1.val
        let compared := Refinement.compareFromGeometry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request budget first.subdivision centers.1 fits front headGeometry headObserved
        have sameFollowing : geometry.1.val.following = followingPath :=
          geometry.1.val.following_eq.trans followingFactory.symm
        let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (diameter := diameter) (positive := positive)
          (lineage := remaining) (centers := centers.2)
          (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
          sameFollowing geometry.2.2
        let following := fromGeometry (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request remaining centers.2
            followingPath followingFactory followingGeometry tailObserved
        have assembled := Completion.cons_val (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request first budget fits finishOwnerEq remaining centers materialized observed
          front headObserved compared followingPath tailObserved following firstValue lastValue shared
        have read := congrArg (fun cached : Cache (count := count) (floor := floor) (targets := targets)
            (accuracy := accuracy) row diameter positive request
            (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining) centers =>
          childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request
            (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining) centers cached)
          assembled
        have headCount := Refinement.compareFromGeometry_childCount
          (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor)
          (targets := targets) (accuracy := accuracy)
          row diameter positive request budget first.subdivision centers.1 fits front headGeometry headObserved
        have headCast := Refinement.Cache.Geometry.castTrace_childCount (frame := frame) (basis := basis)
          (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits) sameTrace geometry.2.1.val
        have tailCount := fromGeometry_childCount row diameter positive request remaining centers.2
          followingPath followingFactory followingGeometry tailObserved
        have tailCast := Geometry.castPath_childCount (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (diameter := diameter) (positive := positive) (lineage := remaining) (centers := centers.2)
          (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory) sameFollowing geometry.2.2
        exact read.trans (congrArg₂ Nat.add (headCount.trans headCast) (tailCount.trans tailCast))
      have outerRead := congrArg project (geometry.1.val.withData_eq
        (TraceLineage.withObservedHead
          first budget fits finishOwnerEq remaining materialized observed consume))
      have mappedRead := TraceLineage.withObservedHead_map
        first budget fits finishOwnerEq remaining materialized observed consume project
        geometry.1.val.1.val geometry.1.val.1.property geometry.1.val.2.1.down
        geometry.1.val.2.2.1.val geometry.1.val.2.2.1.property
        geometry.1.val.2.2.2.val geometry.1.val.2.2.2.property.1 geometry.1.val.2.2.2.property.2
      have callbackRead := TraceLineage.withObservedHead_congr
        first budget fits finishOwnerEq remaining materialized observed mapped ignored each
        geometry.1.val.1.val geometry.1.val.1.property geometry.1.val.2.1.down
        geometry.1.val.2.2.1.val geometry.1.val.2.2.1.property
        geometry.1.val.2.2.2.val geometry.1.val.2.2.2.property.1 geometry.1.val.2.2.2.property.2
      have forgotten := TraceLineage.withObservedHead_forget
        first budget fits finishOwnerEq remaining materialized observed
        (fun _divided _dividedFactory _same _front _frontKept _followingPath _followingKept _followingFactory =>
          expected)
        geometry.1.val.1.val geometry.1.val.1.property geometry.1.val.2.1.down
        geometry.1.val.2.2.1.val geometry.1.val.2.2.1.property
        geometry.1.val.2.2.2.val geometry.1.val.2.2.2.property.1 geometry.1.val.2.2.2.property.2
      exact outerRead.trans (mappedRead.trans (callbackRead.trans forgotten))
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ => lineage

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Cache

end
