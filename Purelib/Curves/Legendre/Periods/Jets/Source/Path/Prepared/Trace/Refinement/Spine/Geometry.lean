module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Comparison
import Purelib.Riemann.Paths.PreparedPathTrace.Materialized

/-! # Original whole-lineage geometry before primitive observations

Each actual complete-segment Head retains the same materialized split,
raw Trace and following path. Its original raw geometry bank is acquired
once, then recursion follows the literal cached following path. Counts
are read before any source target, primitive request or old Spine exists.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Cache

/-- One actual retained materialized head and raw child-geometry bank per original complete segment, in order.

The supplied whole-path factory certifies each original split. The same
Head.front indexes the raw geometry bank and Head.following indexes its
tail. Original stationary or empty-request segments retain their actual
outer Head; only an empty complete lineage has no segment entry.
-/
@[expose] def Geometry (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → materialized = lineage.ownerPath → Type 2
  | _, _, _, _, _, .nil _ _, _, _, _ => PUnit
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory =>
      Σ retainedHead : {value : PreparedPathTrace.PreparedPath.TraceLineage.Head
          first budget fits finishOwnerEq remaining
          (materialized.reindexOwners rfl (PreparedPathTrace.PreparedPath.castOwner_finishOwner finishOwnerEq rest)) //
        value = PreparedPathTrace.PreparedPath.TraceLineage.Head.build
          first budget fits finishOwnerEq remaining materialized factory},
      (_rawGeometry : {value : Refinement.Cache.Geometry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) diameter positive budget first.subdivision centers.1 fits retainedHead.val.front //
        value = Refinement.Cache.Geometry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) diameter positive budget first.subdivision centers.1 fits retainedHead.val.front}) ×
        Geometry diameter positive remaining centers.2 retainedHead.val.following retainedHead.val.following_eq
termination_by structural _ _ _ _ _ lineage _ _ _ => lineage

namespace Geometry

/-- Retain actual whole-lineage splits and acquire their same raw child geometry before any observation request.

Each whole certified Head is bound before its dependent geometry and tail.
The existing original withCons producer runs only inside Head.build, once
per actual segment. No old source, Vertex, observation or canonical path
is reconstructed by this geometry traversal.
-/
def build (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
      Geometry (count := count) diameter positive lineage centers materialized factory
  | _, _, _, _, _, .nil _ _, _, _, _ => PUnit.unit
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory =>
      let retainedHead : {value : PreparedPathTrace.PreparedPath.TraceLineage.Head
          first budget fits finishOwnerEq remaining
          (materialized.reindexOwners rfl (PreparedPathTrace.PreparedPath.castOwner_finishOwner finishOwnerEq rest)) //
        value = PreparedPathTrace.PreparedPath.TraceLineage.Head.build
          first budget fits finishOwnerEq remaining materialized factory} :=
        ⟨PreparedPathTrace.PreparedPath.TraceLineage.Head.build
          first budget fits finishOwnerEq remaining materialized factory, rfl⟩
      let rawGeometry : {value : Refinement.Cache.Geometry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) diameter positive budget first.subdivision centers.1 fits retainedHead.val.front //
        value = Refinement.Cache.Geometry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) diameter positive budget first.subdivision centers.1 fits retainedHead.val.front} :=
        ⟨Refinement.Cache.Geometry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) diameter positive budget first.subdivision centers.1 fits retainedHead.val.front, rfl⟩
      let following := build diameter positive remaining centers.2
        retainedHead.val.following retainedHead.val.following_eq
      ⟨retainedHead, rawGeometry, following⟩
termination_by structural _ _ _ _ _ lineage _ _ _ => lineage

/-- Count the same actual refined children across all retained complete segments before selecting numerical requests. -/
@[expose] def childCount (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    (factory : materialized = lineage.ownerPath) →
    Geometry (count := count) diameter positive lineage centers materialized factory → Nat
  | _, _, _, _, _, .nil _ _, _, _, _, _ => 0
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, retained =>
      Refinement.Cache.Geometry.childCount diameter positive budget first.subdivision centers.1 fits
        retained.1.val.front retained.2.1.val +
      childCount diameter positive remaining centers.2 retained.1.val.following retained.1.val.following_eq retained.2.2
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

end Geometry

end Cache

variable {start finish : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath clearPath owner}
variable (diameter : Rational) (positive : 0 < diameter) (lineage : TraceLineage prepared)
variable (inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
variable (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
  (PreparedPathGluing.finishOwner prepared)) (factory : materialized = lineage.ownerPath)

/-- The same whole input path and centers, actual complete-lineage geometry and once-computed child count.

The original whole materialized path and center products remain runtime
data even for an empty lineage. Existing dependent products retain every
complete cache with its factory; no numerical request or observation is
present in this preparation.
-/
@[expose] def Geometry :=
  Σ keptPath : {value : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared) // value = materialized},
  Σ keptCenters : {value : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage // value = inputCenters},
  Σ cached : {value : Cache.Geometry (count := count) diameter positive lineage keptCenters.val
      keptPath.val (keptPath.property.trans factory) //
    value = Cache.Geometry.build (count := count) diameter positive lineage keptCenters.val
      keptPath.val (keptPath.property.trans factory)},
  {children : Nat // children = Cache.Geometry.childCount diameter positive lineage keptCenters.val
    keptPath.val (keptPath.property.trans factory) cached.val}

namespace Geometry

/-- Retain the original whole inputs, acquire their actual geometry once and compute the literal child count once. -/
def build : Geometry (count := count) diameter positive lineage inputCenters materialized factory :=
  let keptPath : {value : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared) // value = materialized} := ⟨materialized, rfl⟩
  let keptCenters : {value : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage //
      value = inputCenters} :=
    ⟨inputCenters, rfl⟩
  let cached : {value : Cache.Geometry (count := count) diameter positive lineage keptCenters.val
      keptPath.val (keptPath.property.trans factory) //
    value = Cache.Geometry.build (count := count) diameter positive lineage keptCenters.val
      keptPath.val (keptPath.property.trans factory)} :=
    ⟨Cache.Geometry.build (count := count) diameter positive lineage keptCenters.val
      keptPath.val (keptPath.property.trans factory), rfl⟩
  let children := Cache.Geometry.childCount diameter positive lineage keptCenters.val
    keptPath.val (keptPath.property.trans factory) cached.val
  ⟨keptPath, keptCenters, cached, ⟨children, rfl⟩⟩

variable {diameter positive lineage inputCenters materialized factory}
variable (retained : Geometry (count := count) diameter positive lineage inputCenters materialized factory)

/-- Read the same complete original materialized path, including its actual endpoint Owners. -/
@[expose] def path : OwnerPath (Paths.polynomial parameter) start owner finish
    (PreparedPathGluing.finishOwner prepared) := retained.1.val

/-- The whole retained original path is the given materialization. -/
theorem path_eq : retained.path = materialized := retained.1.property

/-- Read the same complete original center product without selecting any center again. -/
@[expose] def centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage := retained.2.1.val

/-- The whole retained center product is the original supplied value. -/
theorem centers_eq : retained.centers = inputCenters := retained.2.1.property

/-- Read the same complete geometry bank at its retained whole input path and center indices. -/
@[expose] def cache : Cache.Geometry (count := count) diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) := retained.2.2.1.val

/-- The complete retained geometry bank has its original actual-input constructor factory. -/
theorem cache_eq : retained.cache = Cache.Geometry.build (count := count) diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) := retained.2.2.1.property

/-- Read the literal total child count computed before source and old-observation requests. -/
@[expose] def childCount : Nat := retained.2.2.2.val

/-- The retained count belongs to the same actual whole geometry bank and both retained input owners. -/
theorem childCount_eq : retained.childCount = Cache.Geometry.childCount diameter positive lineage retained.centers
    retained.path (retained.path_eq.trans factory) retained.cache := retained.2.2.2.property

end Geometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
