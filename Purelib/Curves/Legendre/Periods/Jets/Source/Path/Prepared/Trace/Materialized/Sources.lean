module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Subdivision
public import Purelib.Riemann.Paths.PreparedPathTrace.Lineage
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods

/-! # Original source products along one retained prepared-path lineage

The structural product keeps one existing complete subdivision Sources
cache per original segment. Its optional producer consumes a primitive
cover of that SAME prepared path. It does not replace the original trace
with a separately acquired covered trace. Newly prepared sources are
materialized once, before their common use by different relation rows.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath CompleteSegment)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.PreparedPath (PrimitiveCover)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
    {ambient : Geometry.Rational.Box}

/-- The exact original source products in the SAME retained lineage's segment order.

The empty lineage has no segments. A cons retains its whole existing
Trace.Sources head and the source product for its original remaining
lineage, before the erased starting-Owner transport. Repeated and
stationary segment occurrences remain separate positions.
-/
@[expose] def Sources :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    TraceLineage prepared → Type 1
  | _, _, _, _, _, .nil _ _ => PUnit
  | _, _, _, _, _, .cons (first := first) _budget _fits _finishOwnerEq remaining =>
      Trace.Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
        (sheet := sheet) first.subdivision × Sources remaining
termination_by structural _ _ _ _ _ lineage => lineage

namespace Sources

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Undo only the actual starting-Owner transport on the SAME supplied primitive cover. -/
private def uncastCover {start finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {first last : Owner ((Paths.polynomial parameter).eval start)}
    (equal : first = last) {prepared : PreparedPath path first}
    (covered : PrimitiveCover (Riemann.Paths.PreparedPathTrace.PreparedPath.castOwner equal prepared)) :
    PrimitiveCover prepared := by
  cases equal
  exact covered

/-- Prepare one original segment's centers, covering patches and six-channel source bank on its given primitive mesh. -/
private def prepareSegment {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner ((Paths.polynomial parameter).eval start)}
    (first : CompleteSegment segment within owner) (bounds : Bounds segment) (mesh : Mesh bounds)
    (meshEq : first.subdivision.parameterEdges = mesh.edges) :
    Trace.Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) first.subdivision :=
  let centers := Riemann.Integration.PreparedSubdivisionAutomaticModels.canonicalCenterStates
    (Fibre.frameCurve frame) basis sheet first.subdivision
  let covered := CoveredParents.ofSubdivision bounds mesh sheet count first.subdivision centers
    (fun edge member => Eq.mp (congrArg (fun edges => edge ∈ edges) meshEq) member)
  let prepared := prepareCovered (frame := frame) (basis := basis) covered floor targets
  ⟨centers, covered, prepared⟩

/-- Prepare sources once on each original subdivision certified by its SAME primitive-cover mesh.

The original cover supplies bounds, mesh and the exact parameter-edge
factory for the given subdivision. Canonical centers are new work on
that original subdivision, selected once and stored with its actual
covering patches and completed six-channel sources. The tail consumes
the supplied original cover through its exact Owner transport; no root
trace, continuation, mesh, source or observation is replayed.
-/
def build :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → PrimitiveCover prepared →
    Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage
  | _, _, _, _, _, .nil _ _, _ => PUnit.unit
  | _, _, _, _, _, .cons (first := first) _budget _fits finishOwnerEq remaining, covered =>
      let parts := PrimitiveCover.headTail covered
      let head := prepareSegment (frame := frame) (basis := basis) (targets := targets)
        (count := count) (floor := floor) (sheet := sheet) first parts.1 parts.2.1.val parts.2.1.property
      let following := build remaining (uncastCover finishOwnerEq parts.2.2)
      ⟨head, following⟩
termination_by structural _ _ _ _ _ lineage _ => lineage

/-- Count actual original moving requests before source preparation or primitive observation. -/
@[expose] def requestCount :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    TraceLineage prepared → Nat
  | _, _, _, _, _, .nil _ _ => 0
  | _, _, _, _, _, .cons (first := first) _budget _fits _finishOwnerEq remaining =>
      first.subdivision.requests.length + requestCount remaining
termination_by structural _ _ _ _ _ lineage => lineage

/-- An exact original Owner transport preserves the original prepared-path step count. -/
private theorem castOwner_stepCount {start finish : Canonical}
    {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {first last : Owner ((Paths.polynomial parameter).eval start)} (equal : first = last)
    (prepared : PreparedPath path first) :
    (Riemann.Paths.PreparedPathTrace.PreparedPath.castOwner equal prepared).stepCount = prepared.stepCount := by
  cases equal
  rfl

/-- The source occurrence count is the SAME original prepared path's retained total subdivision count. -/
theorem requestCount_eq_stepCount :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → requestCount lineage = prepared.stepCount
  | _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, .cons (first := first) _budget _fits finishOwnerEq remaining =>
      congrArg₂ Nat.add first.subdivision.requests_length
        ((requestCount_eq_stepCount remaining).trans (castOwner_stepCount finishOwnerEq _).symm)
termination_by structural _ _ _ _ _ lineage => lineage

end Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Materialized

end
