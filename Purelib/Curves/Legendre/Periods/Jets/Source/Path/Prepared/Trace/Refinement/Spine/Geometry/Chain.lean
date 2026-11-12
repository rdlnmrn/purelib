module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Chain
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Materialized.Sources
import Purelib.Data.List.Append
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

/-! # The actual global refined child list, covering spine and lifted chain

The supplied whole geometry retains its actual materialized Heads and raw
geometry banks. Reading their children and chains follows those SAME
original splits in complete-segment/request/child order. Full geometric
endpoint equalities use only original coordinates and the retained sheet;
actual RootOwner/query/return certificates remain separate unchanged data.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Refinement.Cache renaming Geometry -> SegmentGeometry
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain allParentsProper_append)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

namespace Cache.Geometry

/-- Read all SAME refined children in literal complete-segment, original-request and child order. -/
@[expose] def parents (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
    Cache.Geometry (count := count) diameter positive lineage centers materialized factory →
      List (CenteredEdge (Fibre.frameCurve frame) basis)
  | _, _, _, _, _, .nil _ _, _, _, _, _ => []
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry =>
      SegmentGeometry.parents diameter positive budget first.subdivision centers.1 fits
        geometry.1.val.front geometry.2.1.val ++
      parents diameter positive remaining centers.2 geometry.1.val.following geometry.1.val.following_eq geometry.2.2
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

/-- The actual whole-path child list retains strict parameter order at every original occurrence.

Each complete segment reads its existing acquisition certificates. The
original finite append law combines them with the same retained suffix;
empty inner blocks and physically stationary strict children remain intact.
-/
theorem parents_proper (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      AllParentsProper (parents diameter positive lineage centers materialized factory geometry)
  | _, _, _, _, _, .nil _ _, _, _, _, _ => True.intro
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry =>
      allParentsProper_append
        (SegmentGeometry.parents_proper diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val)
        (parents_proper diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2)
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

/-- The global literal child list has exactly the count retained before choosing Targets or observations. -/
theorem parents_length (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      (parents diameter positive lineage centers materialized factory geometry).length =
        childCount diameter positive lineage centers materialized factory geometry
  | _, _, _, _, _, .nil _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry =>
      (Data.List.Append.length_append
        (SegmentGeometry.parents diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val)
        (parents diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2)).trans
          (congrArg₂ Nat.add
            (SegmentGeometry.parents_length diameter positive budget first.subdivision centers.1 fits
              geometry.1.val.front geometry.2.1.val)
            (parents_length diameter positive remaining centers.2
              geometry.1.val.following geometry.1.val.following_eq geometry.2.2))
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

/-- Exact starting-Owner transport preserves strictness of the SAME original prepared requests. -/
private theorem uncastProper {start finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {first last : Owner ((Paths.polynomial parameter).eval start)} (same : first = last)
    (prepared : PreparedPath path first)
    (proper : PreparedClearPathModels.PreparedPath.AllEdgesProper
      (PreparedPathTrace.PreparedPath.castOwner same prepared)) :
    PreparedClearPathModels.PreparedPath.AllEdgesProper prepared := by
  cases same
  exact proper

/-- Every strict original request contributes to the SAME actual whole refined child count. -/
private theorem requestCount_le_childCount (diameter : Rational) (positive : 0 < diameter)
    {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (lineage : TraceLineage prepared)
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) (factory : materialized = lineage.ownerPath)
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory)
    (proper : PreparedClearPathModels.PreparedPath.AllEdgesProper prepared) :
    Trace.Materialized.Sources.requestCount lineage ≤
      childCount diameter positive lineage centers materialized factory geometry :=
  TraceLineage.casesOn
    (motive := fun {start finish _path owner} prepared lineage =>
      (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
      (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
        (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
      (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      PreparedClearPathModels.PreparedPath.AllEdgesProper prepared →
        Trace.Materialized.Sources.requestCount lineage ≤
          childCount diameter positive lineage centers materialized factory geometry)
    lineage
    (fun _ _ _centers _materialized _factory _geometry _proper => Nat.le_refl 0)
    (fun {_start _middle _finish _segment _tail _owner _within first _middleOwner rest}
        budget fits finishOwnerEq remaining centers _materialized _factory geometry proper => by
      have headBound := SegmentGeometry.stepCount_le_childCount
        (frame := frame) (basis := basis) (sheet := sheet) (count := count)
        diameter positive budget first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val proper.1
      have firstCount : first.subdivision.requests.length ≤
          SegmentGeometry.childCount diameter positive budget first.subdivision centers.1 fits
            geometry.1.val.front geometry.2.1.val :=
        Eq.mpr (congrArg (fun size : Nat => size ≤ SegmentGeometry.childCount
          diameter positive budget first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val)
            first.subdivision.requests_length) headBound
      have followingCount := requestCount_le_childCount diameter positive remaining centers.2
        geometry.1.val.following geometry.1.val.following_eq geometry.2.2
        (uncastProper finishOwnerEq rest proper.2)
      exact Nat.add_le_add firstCount followingCount)
    centers materialized factory geometry proper
termination_by structural lineage

/-- The SAME proper original prepared path has no more requests than its retained refined child word. -/
theorem stepCount_le_childCount (diameter : Rational) (positive : 0 < diameter)
    {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (lineage : TraceLineage prepared)
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) (factory : materialized = lineage.ownerPath)
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory)
    (proper : PreparedClearPathModels.PreparedPath.AllEdgesProper prepared) :
    prepared.stepCount ≤ childCount diameter positive lineage centers materialized factory geometry :=
  Eq.mp (congrArg (fun size : Nat => size ≤ childCount diameter positive lineage centers materialized factory geometry)
    (Trace.Materialized.Sources.requestCount_eq_stepCount lineage))
      (requestCount_le_childCount diameter positive lineage centers materialized factory geometry proper)

/-- Read the SAME original successful child coverings across all actual whole-path segments. -/
@[expose] def covered (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      CoveredParents count (parents diameter positive lineage centers materialized factory geometry)
  | _, _, _, _, _, .nil _ _, _, _, _, _ => .nil
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry =>
      (SegmentGeometry.covered diameter positive budget first.subdivision centers.1 fits
        geometry.1.val.front geometry.2.1.val).append
      (covered diameter positive remaining centers.2
        geometry.1.val.following geometry.1.val.following_eq geometry.2.2)
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

/-- Assemble the actual full child chain using the original complete-segment endpoint laws.

Each retained raw chain starts at parameter zero and ends at its actual
subdivision.endpoint. CompleteSegment.start_eq and finish_eq identify
those coordinates with the original segment endpoints. The common sheet
then gives the geometric lifted-point seam. This constructs no RootOwner
agreement and leaves every actual query/root/closing witness unchanged.
-/
def chain (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      CenteredPathChain (parents diameter positive lineage centers materialized factory geometry)
        (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩)
  | _, _, _, _, _, .nil point _, _, _, _, _ => .nil ⟨point, sheet⟩
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry =>
      (((SegmentGeometry.chain diameter positive budget first.subdivision centers.1 fits
        geometry.1.val.front geometry.2.1.val).castStart
          (congrArg (fun coordinate : Canonical => (⟨coordinate, sheet⟩ : LiftedPoint 2)) first.start_eq)).castFinish
            (congrArg (fun coordinate : Canonical => (⟨coordinate, sheet⟩ : LiftedPoint 2)) first.finish_eq)).append
      (chain diameter positive remaining centers.2 geometry.1.val.following geometry.1.val.following_eq geometry.2.2)
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

end Cache.Geometry

namespace Geometry

variable {diameter : Rational} {positive : 0 < diameter}
variable {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
variable {lineage : TraceLineage prepared}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) start owner finish
  (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
variable (retained : Materialized.Geometry (count := count)
  diameter positive lineage inputCenters materialized factory)

/-- Read the global literal child list from the SAME retained input path, centers and whole geometry bank. -/
@[expose] def parents : List (CenteredEdge (Fibre.frameCurve frame) basis) :=
  Cache.Geometry.parents diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache

/-- Every actual retained whole-path child has strictly ordered parameter endpoints. -/
theorem parents_proper : AllParentsProper retained.parents :=
  Cache.Geometry.parents_proper diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache

/-- The global list length is the SAME actual child count computed before requests. -/
theorem parents_length : retained.parents.length = retained.childCount :=
  (Cache.Geometry.parents_length diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache).trans retained.childCount_eq.symm

/-- Read the SAME original successful covering patches on the literal global child list. -/
@[expose] def covered : CoveredParents count retained.parents :=
  Cache.Geometry.covered diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache

/-- Read the actual global centered child chain between the original whole geometric endpoint roles. -/
def chain : CenteredPathChain retained.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩) :=
  Cache.Geometry.chain diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache

/-- Original strict request count is bounded by the SAME pre-observation retained whole child count. -/
theorem stepCount_le_childCount (proper : PreparedClearPathModels.PreparedPath.AllEdgesProper prepared) :
    prepared.stepCount ≤ retained.childCount :=
  Eq.mpr (congrArg (fun size : Nat => prepared.stepCount ≤ size) retained.childCount_eq)
    (Cache.Geometry.stepCount_le_childCount diameter positive lineage retained.centers
      retained.path (retained.path_eq.trans factory) retained.cache proper)

/-- The actual allocation path has precisely the retained child count, with no guessed count or shape equality. -/
theorem path_cellCount : retained.chain.path.cellCount = retained.childCount :=
  (CenteredPathChain.path_cellCount retained.chain).trans retained.parents_length

end Geometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
