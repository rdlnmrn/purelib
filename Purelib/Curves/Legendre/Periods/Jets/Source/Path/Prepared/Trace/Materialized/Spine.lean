module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Materialized.Sources
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Materialized
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Tactic.Ring

/-! # Same-cache row primitive comparisons along the full retained lineage

The original materialized path and old primitive Spine are inputs.
Each exact segment boundary splits those same caches once. The original
source comparison consumes its same head product and old observations,
then the literal remaining lineage consumes their unchanged suffix.
Every stationary/moving/retention block remains in the finite telescope.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Materialized

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget (ownerPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
    {ambient : Geometry.Rational.Box} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- One actual existing comparison per original segment, with its SAME whole old raw observation Spine.

The stored old Spine is obtained by exact segment and endpoint/Owner
transports from the given materialized old input. The existing Compared
value retains the same source product, old observations and actual
endpoint-comparison factory. No canonical path supplies runtime data.
-/
@[expose] def Cache (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage → Type 1
  | _, _, _, _, _, .nil _ _, _ => PUnit
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining, sources =>
      (Σ old : Primitive.Spine (row.expression parameter) accuracy (ownerPath budget first.subdivision fits),
        Trace.Compared row (frame := frame) (basis := basis) budget allocation first.subdivision sources.1 fits old) ×
          Cache row allocation remaining sources.2
termination_by structural _ _ _ _ _ lineage _ => lineage

namespace Cache

/-- Read every retained original row integral in its literal segment and moving-request order. -/
@[expose] def integrals (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage) → Cache row allocation lineage sources → List Canonical
  | _, _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, sources, retained =>
      retained.1.2.integrals ++ integrals row allocation remaining sources.2 retained.2
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- Read every actual complete-block error, including both original stationary roles at each moving request. -/
@[expose] def errors (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage) → Cache row allocation lineage sources → List Canonical
  | _, _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, sources, retained =>
      retained.1.2.blockErrors ++ errors row allocation remaining sources.2 retained.2
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- The actual block count is the original lineage's pre-observation request count. -/
theorem errors_length (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage) → (retained : Cache row allocation lineage sources) →
    (errors row allocation lineage sources retained).length = Sources.requestCount lineage
  | _, _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, sources, retained =>
      (Append.length_append retained.1.2.blockErrors
        (errors row allocation remaining sources.2 retained.2)).trans
        (congrArg₂ Nat.add retained.1.2.blockErrors_length
          (errors_length row allocation remaining sources.2 retained.2))
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- Every actual retained block is paid by its own original old observations and source allocation. -/
theorem errors_bounded (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage) → (retained : Cache row allocation lineage sources) →
    ∀ error ∈ errors row allocation lineage sources retained, Norm.Basic.normSq error ≤ 26 * targets.endpoint
  | _, _, _, _, _, .nil _ _, _, _, _, member => by cases member
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      sources, retained, error, member => by
      rcases Membership.mem_append.mp member with inHead | inTail
      · exact Trace.Cache.blockErrors_bounded row (frame := frame) (basis := basis) budget allocation
          first.subdivision retained.1.2.sources fits retained.1.2.observed.first retained.1.2.observed.2
          retained.1.2.cache error inHead
      · exact errors_bounded row allocation remaining sources.2 retained.2 error inTail
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

/-- The actual comparison cache together with its exact SAME-old-Spine endpoint telescope. -/
@[expose] def Completion (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance)
    {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (lineage : TraceLineage prepared)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared))
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) :=
  {retained : Cache row allocation lineage sources //
    gaussianSum (errors row allocation lineage sources retained) =
      observed.last.value - observed.first.value - gaussianSum (integrals row allocation lineage sources retained)}

/-- Compare the SAME old materialized Spine on every original segment without another trace or observation.

The retained lineage chooses each actual constructor boundary. The
existing withObservedCons splits the given old observations once; the
old head is passed to Request.fromObserved, and the literal old suffix
is passed to the original remaining lineage. Both original stationary
handoffs and accepted zero-displacement requests remain in each block.
The telescope is derived from the actual shared Vertex, not from a
separately normalized primitive or a coordinate-only Owner equality.
-/
def build (row : Row) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) →
    materialized = lineage.ownerPath →
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) →
    Completion row allocation lineage sources materialized observed
  | _, _, _, _, _, .nil _ _, _sources, _materialized, factory, observed => by
      refine ⟨PUnit.unit, ?_⟩
      cases factory
      change (0 : Canonical) = observed.first.value - observed.first.value - 0
      ring1
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      sources, materialized, factory, observed =>
      PreparedPathTrace.PreparedPath.TraceLineage.withObservedCons
        first budget fits finishOwnerEq remaining materialized observed factory
        (fun _divided _dividedFactory _same front _frontKept followingPath _followingKept followingFactory
            _views _viewsFactory headObserved _headKept tailObserved _tailKept firstValue lastValue shared => by
          let rawObserved := Request.castObserved row budget first.subdivision fits
            front.path front.path_eq headObserved
          let compared := Request.fromObserved row (frame := frame) (basis := basis)
            budget first.subdivision fits front.path front.path_eq sources.1 allocation headObserved
          let following := build row allocation remaining sources.2 followingPath followingFactory tailObserved
          let retained : Cache row allocation
              (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining) sources :=
            ⟨⟨rawObserved, compared⟩, following.val⟩
          refine ⟨retained, ?_⟩
          have sourceEq := Request.castObserved_eq_castPath row budget first.subdivision fits
            front.path front.path_eq headObserved
          have rawFirst := (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
              (ownerPath budget first.subdivision fits) => old.first.value) sourceEq).trans
            (Primitive.Spine.castPath_first_value front.path_eq headObserved)
          have rawLast := (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
              (ownerPath budget first.subdivision fits) => old.last.value) sourceEq).trans
            (Primitive.Spine.castPath_last_value front.path_eq headObserved)
          have headFirst := (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
              (ownerPath budget first.subdivision fits) => old.first.value) compared.observed_eq).trans
            (rawFirst.trans firstValue)
          have headLast := (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
              (ownerPath budget first.subdivision fits) => old.last.value) compared.observed_eq).trans
            (rawLast.trans shared.symm)
          have headSum := compared.blockErrors_sum_eq
          change gaussianSum (compared.blockErrors ++
              errors row allocation remaining sources.2 following.val) =
            observed.last.value - observed.first.value - gaussianSum (compared.integrals ++
              integrals row allocation remaining sources.2 following.val)
          have headValue := congrArg₂ (fun first last : Canonical =>
            last - first - gaussianSum compared.integrals) headFirst headLast
          have tailValue := congrArg (fun last : Canonical => last - tailObserved.first.value -
            gaussianSum (integrals row allocation remaining sources.2 following.val)) lastValue
          have scalar :
              (tailObserved.first.value - observed.first.value - gaussianSum compared.integrals) +
                (observed.last.value - tailObserved.first.value -
                  gaussianSum (integrals row allocation remaining sources.2 following.val)) =
              observed.last.value - observed.first.value - (gaussianSum compared.integrals +
                gaussianSum (integrals row allocation remaining sources.2 following.val)) := by ring1
          exact (Norm.Sum.Basic.gaussianSum_append _ _).trans
            ((congrArg₂ (fun first last : Canonical => first + last)
              (headSum.trans headValue) (following.property.trans tailValue)).trans
              (scalar.trans (congrArg (fun total : Canonical => observed.last.value - observed.first.value - total)
                (Norm.Sum.Basic.gaussianSum_append _ _)).symm)))
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

end Cache

variable {start finish : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath clearPath owner}
    (row : Row) (lineage : TraceLineage prepared)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
      (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared))
    (factory : materialized = lineage.ownerPath)
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)

/-- The complete original source family and old Spine accompany the actual ordered comparison execution.

The whole original path, source family and old Spine remain retained
values. The completed cache has its exact construction equation on those same inputs, including
its derived endpoint telescope. An arbitrary source target cannot replace
the required equality with the old Spine's actual request allocation.
-/
@[expose] def Compared :=
  (_keptPath : {value : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared) // value = materialized}) ×
  (Σ keptSources : {value : Sources (frame := frame) (basis := basis) (targets := targets) (count := count)
      (floor := floor) (sheet := sheet) lineage // value = sources},
    Σ keptObserved : {value : Primitive.Spine (row.expression parameter) accuracy materialized // value = observed},
      {completed : Cache.Completion row allocation lineage keptSources.val materialized keptObserved.val //
        completed = Cache.build row allocation lineage keptSources.val materialized factory keptObserved.val})

/-- Construct every actual original segment comparison once on the SAME source and old observation inputs. -/
def compare : Compared row lineage sources materialized factory observed allocation :=
  let completed := Cache.build row allocation lineage sources materialized factory observed
  ⟨⟨materialized, rfl⟩, ⟨⟨sources, rfl⟩, ⟨observed, rfl⟩, ⟨completed, rfl⟩⟩⟩

namespace Compared

variable {row lineage sources materialized factory observed allocation}
    (retained : Compared row lineage sources materialized factory observed allocation)

/-- Read the whole supplied actual materialized path, including all original links and Owners. -/
@[expose] def path : OwnerPath (Paths.polynomial parameter) start owner finish
    (PreparedPathGluing.finishOwner prepared) := retained.1.val

/-- The retained path is the literal supplied execution, without evaluating its canonical factory. -/
theorem path_eq : retained.path = materialized := retained.1.property

/-- Read the SAME whole supplied original source family, without selecting a center, cover or model again. -/
@[expose] def sourceFamily : Sources (frame := frame) (basis := basis) (targets := targets) (count := count)
    (floor := floor) (sheet := sheet) lineage := retained.2.1.val

/-- Read the complete original old Spine, with every original request, Vertex, tail and stationary comparison. -/
@[expose] def observations : Primitive.Spine (row.expression parameter) accuracy materialized := retained.2.2.1.val

/-- Read the actual derived comparison execution and its old endpoint telescope. -/
@[expose] def completed : Cache.Completion row allocation lineage retained.sourceFamily materialized
    retained.observations := retained.2.2.2.val

/-- The whole retained source family is literally the original supplied product. -/
theorem sourceFamily_eq : retained.sourceFamily = sources := retained.2.1.property

/-- The whole retained old observation Spine is literally the original supplied execution. -/
theorem observations_eq : retained.observations = observed := retained.2.2.1.property

/-- The actual completed cache is the original construction on the SAME retained whole inputs. -/
theorem completed_eq : retained.completed = Cache.build row allocation lineage retained.sourceFamily
    materialized factory retained.observations := retained.2.2.2.property

/-- Read the actual ordered source-model integrals, preserving every repeated and stationary source occurrence. -/
@[expose] def integrals : List Canonical :=
  Cache.integrals row allocation lineage retained.sourceFamily retained.completed.val

/-- Read the actual original stationary/moving/retention block errors in the same complete occurrence order. -/
@[expose] def errors : List Canonical :=
  Cache.errors row allocation lineage retained.sourceFamily retained.completed.val

/-- The actual error list contains exactly one block for every original prepared moving request. -/
theorem errors_length : retained.errors.length = prepared.stepCount :=
  (Cache.errors_length row allocation lineage retained.sourceFamily retained.completed.val).trans
    (Sources.requestCount_eq_stepCount lineage)

/-- The SAME actual source integrals telescope against the distinct old first and last values. -/
theorem errors_sum_eq : gaussianSum retained.errors =
    observed.last.value - observed.first.value - gaussianSum retained.integrals :=
  retained.completed.property.trans (congrArg (fun value : Canonical => value - gaussianSum retained.integrals)
    (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy materialized =>
      old.last.value - old.first.value) retained.observations_eq))

/-- The original finite source allocation pays the actual whole-row endpoint/source-integral residual.

The original prepared request count determines the explicit square
charge. This is not global requested accuracy: old targets and accuracy
must have their actual stated equality. Primitive constants are used
only inside their own cached increments, and no cross-face normalization,
closed signed root return or canonical-cycle realization is asserted.
-/
theorem integral_error_le : Norm.Basic.normSq
    (observed.last.value - observed.first.value - gaussianSum retained.integrals) ≤
      (prepared.stepCount : Rational) * ((prepared.stepCount : Rational) * (26 * targets.endpoint)) := by
  have paid := Norm.Sum.Bounds.normSq_sum_le retained.errors (26 * targets.endpoint)
    (Cache.errors_bounded row allocation lineage retained.sourceFamily retained.completed.val)
  rewrite [retained.errors_sum_eq, retained.errors_length] at paid
  exact paid

end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Materialized

end
