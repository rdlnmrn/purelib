module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Sources
import Purelib.Riemann.Paths.PreparedPathTrace.Materialized.Primitive
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Integrals

/-! # Shared six-channel sources through the SAME complete materialized lineage

The given geometry already retains every actual Head, front and following
path. One numeric source bank precedes all row observations. Independent
old row Spines consume that same bank through original observation splits
and the existing Completion.cons telescope.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Refinement.Cache renaming Geometry -> SegmentGeometry
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {floor : Nat} {accuracy : AccuracyRequest}

namespace Cache
namespace Geometry

/-- One actual row-independent six-channel source product on every original retained complete-segment head.

The geometry supplies its exact original front Trace and literal following
path. Empty lineages have no head; stationary/repeated old segments and
requests remain separate positions with their original geometric owners.
-/
@[expose] def Sources (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    Geometry (count := count) diameter positive lineage centers materialized factory → Type 2
  | _, _, _, _, _, .nil _ _, _, _, _, _ => PUnit
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry =>
      SegmentGeometry.Sources (count := count) (floor := floor) (targets := targets)
          diameter positive budget first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val ×
        Sources diameter positive remaining centers.2 geometry.1.val.following geometry.1.val.following_eq geometry.2.2
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

namespace Sources

/-- Prepare all six numeric source channels once on the SAME actual complete geometry before any row observation. -/
def build (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
      Sources (count := count) (floor := floor) (targets := targets)
        diameter positive lineage centers materialized factory geometry
  | _, _, _, _, _, .nil _ _, _, _, _, _ => PUnit.unit
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry =>
      let head := SegmentGeometry.Sources.build (count := count) (floor := floor) (targets := targets)
        diameter positive budget first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val
      let following := build diameter positive remaining centers.2
        geometry.1.val.following geometry.1.val.following_eq geometry.2.2
      ⟨head, following⟩
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

/-- Read the six original numerical cell lists in literal segment/request/refined-child order from the SAME bank. -/
@[expose] def cells (channel : Fin 6) (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry → List CellModel
  | _, _, _, _, _, .nil _ _, _, _, _, _, _ => []
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry, sourceBank =>
      SegmentGeometry.Sources.cells (count := count) (floor := floor) (targets := targets)
          channel diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val sourceBank.1 ++
        cells channel diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ => lineage

/-- Read the SAME ordered whole source-bank model integrals independently of all primitive observations. -/
@[expose] def integrals (row : Row) (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry → List Canonical
  | _, _, _, _, _, .nil _ _, _, _, _, _, _ => []
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry, sourceBank =>
      SegmentGeometry.Sources.integrals row diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val sourceBank.1 ++
        integrals row diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ => lineage

/-- The whole actual row sum is the exact original combination of the SAME six ordered source-model lists. -/
theorem combine_eq (row : Row) (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry) →
    gaussianSum (integrals row diameter positive lineage centers materialized factory geometry sourceBank) =
      Row.combine parameter row (fun channel =>
        (PathModel.mk (cells channel diameter positive lineage centers
          materialized factory geometry sourceBank)).integralSample)
  | _, _, _, _, _, .nil _ _, _, _, _, _, _ => (Row.combine_zero parameter row).symm
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry, sourceBank => by
      have head := SegmentGeometry.Sources.combine_eq row diameter positive budget
        first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val sourceBank.1
      have tail := combine_eq row diameter positive remaining centers.2
        geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2
      have added := Row.combine_add parameter row
        (fun channel => (PathModel.mk (SegmentGeometry.Sources.cells
          channel diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val sourceBank.1)).integralSample)
        (fun channel => (PathModel.mk (cells channel diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2)).integralSample)
      have lists := Row.combine_congr parameter row _ _ (fun channel =>
        (PathModel.integralSample_mk_append
          (SegmentGeometry.Sources.cells channel diameter positive budget first.subdivision centers.1
            fits geometry.1.val.front geometry.2.1.val sourceBank.1)
          (cells channel diameter positive remaining centers.2
            geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2)).symm)
      exact (gaussianSum_append _ _).trans
        ((congrArg₂ (fun first last : Canonical => first + last) head tail).trans (added.symm.trans lists))
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ => lineage

variable {diameter : Rational} {positive : 0 < diameter}
variable {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
variable {lineage : TraceLineage prepared}
variable {centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {firstPath lastPath : OwnerPath (Paths.polynomial parameter) start owner finish
  (PreparedPathGluing.finishOwner prepared)}
variable {firstFactory : firstPath = lineage.ownerPath} {lastFactory : lastPath = lineage.ownerPath}

/-- Whole materialized-path equality transports the SAME source bank together with its actual geometry. -/
def castPath (same : firstPath = lastPath)
    (geometry : Geometry (count := count) diameter positive lineage centers firstPath firstFactory)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers firstPath firstFactory geometry) :
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers lastPath lastFactory
        (Geometry.castPath (firstFactory := firstFactory) (lastFactory := lastFactory) same geometry) := by
  cases same
  exact Eq.mpr (congrArg (fun actual : Geometry (count := count)
      diameter positive lineage centers firstPath firstFactory =>
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers firstPath firstFactory actual) (Geometry.castPath_refl geometry)) sourceBank

/-- Exact whole-path geometry transport preserves the SAME source-bank row-model integral list. -/
theorem castPath_integrals (same : firstPath = lastPath)
    (geometry : Geometry (count := count) diameter positive lineage centers firstPath firstFactory)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers firstPath firstFactory geometry) (row : Row) :
    integrals row diameter positive lineage centers lastPath lastFactory
        (Geometry.castPath (firstFactory := firstFactory) (lastFactory := lastFactory) same geometry)
        (castPath (count := count) (floor := floor) (targets := targets) same geometry sourceBank) =
      integrals row diameter positive lineage centers firstPath firstFactory geometry sourceBank := by
  have transport : ∀ (first last : Geometry (count := count)
      diameter positive lineage centers firstPath firstFactory) (equal : first = last)
      (values : Sources (count := count) (floor := floor) (targets := targets)
        diameter positive lineage centers firstPath firstFactory last),
      integrals row diameter positive lineage centers firstPath firstFactory first
        (Eq.mpr (congrArg (fun actual => Sources (count := count) (floor := floor) (targets := targets)
          diameter positive lineage centers firstPath firstFactory actual) equal) values) =
      integrals row diameter positive lineage centers firstPath firstFactory last values := by
    intro first last equal values
    cases equal
    rfl
  cases same
  unfold castPath
  exact transport _ _ (Geometry.castPath_refl geometry) sourceBank

end Sources
end Geometry

/-- Consume ONE supplied source bank with the actual old row Spine and original materialized Head splits.

The retained Head yields its actual front and following paths. Only the
old observations are split; exact whole Trace/path equalities transport
the SAME source and geometry banks. Original Completion.cons derives the
literal integral/error telescope without preparing another source.
-/
def fromSources (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
    Geometry.Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry →
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) →
      Completion (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers materialized observed
  | _, _, _, _, _, .nil _ _, _centers, _materialized, factory, _geometry, _sourceBank, observed => by
      refine ⟨PUnit.unit, ?_⟩
      cases factory
      change (0 : Canonical) = observed.first.value - observed.first.value - 0
      ring1
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory, geometry, sourceBank, observed =>
      geometry.1.val.withData
        (TraceLineage.withObservedHead
          first budget fits finishOwnerEq remaining materialized observed
          (fun _divided _dividedFactory _same front _frontKept followingPath _followingKept followingFactory
              _views _viewsFactory headObserved _headKept tailObserved _tailKept firstValue lastValue junction =>
            have sameTrace : geometry.1.val.front = front :=
              PreparedTraceBudget.Trace.eq_of_factories geometry.1.val.front front
            let headGeometry := SegmentGeometry.castTrace (frame := frame) (basis := basis)
              (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
              (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
              sameTrace geometry.2.1.val
            let headSources := SegmentGeometry.Sources.castTrace
              (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor) (targets := targets)
              (diameter := diameter) (positive := positive) (budget := budget)
              (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
              sameTrace geometry.2.1.val sourceBank.1
            let compared := Refinement.compareFromSources (frame := frame) (basis := basis) (sheet := sheet)
              (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
              row diameter positive request budget first.subdivision centers.1 fits
                front headGeometry headSources headObserved
            have sameFollowing : geometry.1.val.following = followingPath :=
              geometry.1.val.following_eq.trans followingFactory.symm
            let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
              (count := count) (diameter := diameter) (positive := positive)
              (lineage := remaining) (centers := centers.2)
              (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
              sameFollowing geometry.2.2
            let followingSources := Geometry.Sources.castPath (frame := frame) (basis := basis) (sheet := sheet)
              (count := count) (floor := floor) (targets := targets) (diameter := diameter) (positive := positive)
              (lineage := remaining) (centers := centers.2)
              (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
              sameFollowing geometry.2.2 sourceBank.2
            let following := fromSources row diameter positive request remaining centers.2
              followingPath followingFactory followingGeometry followingSources tailObserved
            Completion.cons (frame := frame) (basis := basis) (sheet := sheet)
              (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
              row diameter positive request first budget fits finishOwnerEq remaining centers materialized observed
              front headObserved compared followingPath tailObserved following firstValue lastValue junction))
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ _ => lineage

/-- Actual whole given-bank completions retain EXACTLY their original ordered source-model integral lists.

Original opaque Head map/congruence/forget laws project the actual same-bank
lists. The SAME head/tail model products follow the original Trace/path
transports, including empty and repeated outer occurrences; no source or
old observation is replayed to establish this readback.
-/
theorem fromSources_integrals
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
    (sourceBank : Geometry.Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry) →
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) →
      integrals (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers
        (fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request lineage centers materialized factory geometry sourceBank observed).val =
      Geometry.Sources.integrals row diameter positive lineage centers materialized factory geometry sourceBank
  | _, _, _, _, _, .nil _ _, _, _, _, _, _, _ => rfl
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory, geometry, sourceBank, observed => by
      let project := fun completed : Completion (count := count) (floor := floor) (targets := targets)
          (accuracy := accuracy) row diameter positive request
          (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
          centers materialized observed =>
        integrals (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request
          (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
          centers completed.val
      let expected := Geometry.Sources.integrals row diameter positive
        (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
        centers materialized factory geometry sourceBank
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
          let headGeometry := SegmentGeometry.castTrace (frame := frame) (basis := basis)
            (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
            (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
            sameTrace geometry.2.1.val
          let headSources := SegmentGeometry.Sources.castTrace
            (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor) (targets := targets)
            (diameter := diameter) (positive := positive) (budget := budget)
            (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
            sameTrace geometry.2.1.val sourceBank.1
          let compared := Refinement.compareFromSources (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request budget first.subdivision centers.1 fits
              front headGeometry headSources headObserved
          have sameFollowing : geometry.1.val.following = followingPath :=
            geometry.1.val.following_eq.trans followingFactory.symm
          let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (diameter := diameter) (positive := positive)
            (lineage := remaining) (centers := centers.2)
            (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
            sameFollowing geometry.2.2
          let followingSources := Geometry.Sources.castPath (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (floor := floor) (targets := targets) (diameter := diameter) (positive := positive)
            (lineage := remaining) (centers := centers.2)
            (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
            sameFollowing geometry.2.2 sourceBank.2
          let following := fromSources row diameter positive request remaining centers.2
            followingPath followingFactory followingGeometry followingSources tailObserved
          Completion.cons (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request first budget fits finishOwnerEq remaining centers materialized observed
            front headObserved compared followingPath tailObserved following firstValue lastValue shared

      let mapped : TraceLineage.ObservedHeadConsumer
          first budget fits finishOwnerEq remaining materialized observed (List Canonical) :=
        fun divided dividedFactory same front frontKept followingPath followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared =>
          project (consume divided dividedFactory same front frontKept followingPath followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared)
      let ignored : TraceLineage.ObservedHeadConsumer
          first budget fits finishOwnerEq remaining materialized observed (List Canonical) :=
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
        let headGeometry := SegmentGeometry.castTrace (frame := frame) (basis := basis)
          (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits) sameTrace geometry.2.1.val
        let headSources := SegmentGeometry.Sources.castTrace
          (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor) (targets := targets)
          (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
          sameTrace geometry.2.1.val sourceBank.1
        let compared := Refinement.compareFromSources (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request budget first.subdivision centers.1 fits
            front headGeometry headSources headObserved
        have sameFollowing : geometry.1.val.following = followingPath :=
          geometry.1.val.following_eq.trans followingFactory.symm
        let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (diameter := diameter) (positive := positive)
          (lineage := remaining) (centers := centers.2)
          (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
          sameFollowing geometry.2.2
        let followingSources := Geometry.Sources.castPath (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (diameter := diameter) (positive := positive)
          (lineage := remaining) (centers := centers.2)
          (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
          sameFollowing geometry.2.2 sourceBank.2
        let following := fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request remaining centers.2
            followingPath followingFactory followingGeometry followingSources tailObserved
        have assembled := Completion.cons_val (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request first budget fits finishOwnerEq remaining centers materialized observed
          front headObserved compared followingPath tailObserved following firstValue lastValue shared
        have read := congrArg (fun cached : Cache (count := count) (floor := floor) (targets := targets)
            (accuracy := accuracy) row diameter positive request
            (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining) centers =>
          integrals (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request
            (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining) centers cached)
          assembled
        have headRead := Refinement.compareFromSources_integrals
          (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor)
          (targets := targets) (accuracy := accuracy)
          row diameter positive request budget first.subdivision centers.1 fits
            front headGeometry headSources headObserved
        have headCast := SegmentGeometry.Sources.castTrace_integrals
          (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor) (targets := targets)
          (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
          sameTrace geometry.2.1.val sourceBank.1 row
        have tailRead := fromSources_integrals row diameter positive request remaining centers.2
          followingPath followingFactory followingGeometry followingSources tailObserved
        have tailCast := Geometry.Sources.castPath_integrals (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (diameter := diameter) (positive := positive)
          (lineage := remaining) (centers := centers.2)
          (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
          sameFollowing geometry.2.2 sourceBank.2 row
        exact read.trans (congrArg₂ List.append (headRead.trans headCast) (tailRead.trans tailCast))
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
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ _ => lineage

/-- The complete GIVEN-bank numerical fold preserves the SAME child count known before primitive observations.

Original opaque Head map/congruence/forget laws transport only this scalar
projection. The SAME given source bank follows each exact front/tail
transport; both raw counts and the whole geometric count are derived
from their original actual caches without replaying a source producer.
-/
theorem fromSources_childCount
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    (geometry : Geometry (count := count) diameter positive lineage centers materialized factory) →
    (sourceBank : Geometry.Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry) →
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) →
      childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers
        (fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request lineage centers materialized factory geometry sourceBank observed).val =
      Geometry.childCount diameter positive lineage centers materialized factory geometry
  | _, _, _, _, _, .nil _ _, _, _, _, _, _, _ => rfl
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory, geometry, sourceBank, observed => by
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
          let headGeometry := SegmentGeometry.castTrace (frame := frame) (basis := basis)
            (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
            (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
            sameTrace geometry.2.1.val
          let headSources := SegmentGeometry.Sources.castTrace
            (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor) (targets := targets)
            (diameter := diameter) (positive := positive) (budget := budget)
            (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
            sameTrace geometry.2.1.val sourceBank.1
          let compared := Refinement.compareFromSources (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request budget first.subdivision centers.1 fits
              front headGeometry headSources headObserved
          have sameFollowing : geometry.1.val.following = followingPath :=
            geometry.1.val.following_eq.trans followingFactory.symm
          let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (diameter := diameter) (positive := positive)
            (lineage := remaining) (centers := centers.2)
            (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
            sameFollowing geometry.2.2
          let followingSources := Geometry.Sources.castPath (frame := frame) (basis := basis) (sheet := sheet)
            (count := count) (floor := floor) (targets := targets) (diameter := diameter) (positive := positive)
            (lineage := remaining) (centers := centers.2)
            (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
            sameFollowing geometry.2.2 sourceBank.2
          let following := fromSources row diameter positive request remaining centers.2
            followingPath followingFactory followingGeometry followingSources tailObserved
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
        let headGeometry := SegmentGeometry.castTrace (frame := frame) (basis := basis)
          (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits) sameTrace geometry.2.1.val
        let headSources := SegmentGeometry.Sources.castTrace
          (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor) (targets := targets)
          (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits)
          sameTrace geometry.2.1.val sourceBank.1
        let compared := Refinement.compareFromSources (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request budget first.subdivision centers.1 fits
            front headGeometry headSources headObserved
        have sameFollowing : geometry.1.val.following = followingPath :=
          geometry.1.val.following_eq.trans followingFactory.symm
        let followingGeometry := Geometry.castPath (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (diameter := diameter) (positive := positive)
          (lineage := remaining) (centers := centers.2)
          (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
          sameFollowing geometry.2.2
        let followingSources := Geometry.Sources.castPath (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (diameter := diameter) (positive := positive)
          (lineage := remaining) (centers := centers.2)
          (firstFactory := geometry.1.val.following_eq) (lastFactory := followingFactory)
          sameFollowing geometry.2.2 sourceBank.2
        let following := fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request remaining centers.2
            followingPath followingFactory followingGeometry followingSources tailObserved
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
        have headCount := Refinement.compareFromSources_childCount
          (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor)
          (targets := targets) (accuracy := accuracy)
          row diameter positive request budget first.subdivision centers.1 fits
            front headGeometry headSources headObserved
        have headCast := SegmentGeometry.castTrace_childCount (frame := frame) (basis := basis)
          (sheet := sheet) (count := count) (diameter := diameter) (positive := positive) (budget := budget)
          (subdivision := first.subdivision) (centers := centers.1) (fits := fits) sameTrace geometry.2.1.val
        have tailCount := fromSources_childCount row diameter positive request remaining centers.2
          followingPath followingFactory followingGeometry followingSources tailObserved
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
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ _ => lineage

end Cache

variable {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
variable {diameter : Rational} {positive : 0 < diameter} {lineage : TraceLineage prepared}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) start owner finish
  (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
variable (retained : Geometry (count := count) diameter positive lineage inputCenters materialized factory)

namespace Geometry

/-- The row-independent complete numeric source bank indexed by these SAME retained whole geometry inputs. -/
@[expose] def Sources := Cache.Geometry.Sources (count := count) (floor := floor) (targets := targets)
  diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory) retained.cache

namespace Sources

/-- Prepare the complete six-channel bank once on GIVEN whole geometry after targets and before observations. -/
def build : Sources (count := count) (floor := floor) (targets := targets) retained :=
  Cache.Geometry.Sources.build (count := count) (floor := floor) (targets := targets)
    diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory) retained.cache

/-- Read an actual whole-path six-channel model's literal stored source-cell list without executing a source factory. -/
@[expose] def cells (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (channel : Fin 6) : List CellModel :=
  Cache.Geometry.Sources.cells (count := count) (floor := floor) (targets := targets)
    channel diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory)
    retained.cache sourceBank

/-- Read the actual polynomial integration model on one literal list of the SAME whole numerical bank. -/
@[expose] def model (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (channel : Fin 6) : PathModel := PathModel.mk (cells retained sourceBank channel)

/-- Read one actual row-model list from this SAME retained whole numerical source bank. -/
@[expose] def integrals (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (row : Row) : List Canonical :=
  Cache.Geometry.Sources.integrals row diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache sourceBank

/-- The literal whole numerical bank row is the original exact combination of its SAME six models. -/
theorem combine_eq (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (row : Row) :
    gaussianSum (integrals (count := count) (floor := floor) (targets := targets) retained sourceBank row) =
      Row.combine parameter row (fun channel =>
        (model (count := count) (floor := floor) (targets := targets) retained sourceBank channel).integralSample) :=
  Cache.Geometry.Sources.combine_eq row diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache sourceBank

end Sources

/-- A row completion on the SAME full bank has exactly the geometry's original retained pre-observation count. -/
theorem fromSources_childCount
    (row : Row) (request : AccuracyRequest)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (observed : Primitive.Spine (row.expression parameter) accuracy retained.path) :
    Cache.childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage retained.centers
      (Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage retained.centers retained.path (retained.path_eq.trans factory)
        retained.cache sourceBank observed).val = retained.childCount :=
  (Cache.fromSources_childCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage retained.centers retained.path (retained.path_eq.trans factory)
    retained.cache sourceBank observed).trans retained.childCount_eq.symm

/-- Three independent complete old row Spines consume ONE GIVEN whole six-channel bank on the SAME actual path.

No source, geometry, query or observation is built by this consumer. Its
existing Completion results retain the original old path, actual signed
residuals and finite integral-error telescopes. Closure and Stage/jet
realization remain additional certificates.
-/
def rowsFromSources (request : AccuracyRequest)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (observed : (row : Row) → Primitive.Spine (row.expression parameter) accuracy retained.path) :
    Cache.Completion (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        (Row.connection 0) diameter positive request lineage retained.centers retained.path
          (observed (Row.connection 0)) ×
      Cache.Completion (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        (Row.connection 1) diameter positive request lineage retained.centers retained.path
          (observed (Row.connection 1)) ×
      Cache.Completion (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        Row.scalar diameter positive request lineage retained.centers retained.path (observed Row.scalar) :=
  let zero := Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    (Row.connection 0) diameter positive request lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache sourceBank (observed (Row.connection 0))
  let one := Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    (Row.connection 1) diameter positive request lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache sourceBank (observed (Row.connection 1))
  let scalar := Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    Row.scalar diameter positive request lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache sourceBank (observed Row.scalar)
  ⟨zero, one, scalar⟩

/-- The three-row operation retains exactly its three GIVEN-bank completion values, without a second traversal. -/
theorem rowsFromSources_eq (request : AccuracyRequest)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (observed : (row : Row) → Primitive.Spine (row.expression parameter) accuracy retained.path) :
    rowsFromSources (count := count) (floor := floor) (targets := targets)
      retained request sourceBank observed =
      ⟨Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          (Row.connection 0) diameter positive request lineage retained.centers
          retained.path (retained.path_eq.trans factory) retained.cache sourceBank (observed (Row.connection 0)),
        Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          (Row.connection 1) diameter positive request lineage retained.centers
          retained.path (retained.path_eq.trans factory) retained.cache sourceBank (observed (Row.connection 1)),
        Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          Row.scalar diameter positive request lineage retained.centers
          retained.path (retained.path_eq.trans factory) retained.cache sourceBank (observed Row.scalar)⟩ := by
  unfold rowsFromSources
  rfl

end Geometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
