module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Materialized.Sources
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Actual refined-source comparisons along the complete unchanged old Spine

One split of the given materialized path and old observations selects
each actual original segment. The literal old raw segment enters the
same-subdivision refinement fold; the actual old suffix enters its
unchanged lineage. Complete new source banks and every old stationary
role remain in the ordered telescope, with its endpoint term explicit.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianNormSqSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath CompleteSegment)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
    {ambient : Geometry.Rational.Box} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The supplied actual center states in original segment/request order, independent of primitive coverage.

Each original complete segment retains its original subdivision-indexed
center product. No mesh, root trace, source preparation or primitive
observation is reconstructed by storing these same products.
-/
@[expose] def Centers :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    TraceLineage prepared → Type 1
  | _, _, _, _, _, .nil _ _ => PUnit
  | _, _, _, _, _, .cons (first := first) _budget _fits _finishOwnerEq remaining =>
      CenterStates (Fibre.frameCurve frame) basis sheet first.subdivision × Centers remaining
termination_by structural _ _ _ _ _ lineage => lineage

namespace Centers

/-- Select center states once on the SAME original subdivisions, without preparing roots, covers or sources.

These are new center-state selections when no original center product is
supplied. They are retained as actual data before any source refinement;
no old root path, Vertex, model observation or primitive cover is replaced.
-/
def build :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → Centers (frame := frame) (basis := basis) (sheet := sheet) lineage
  | _, _, _, _, _, .nil _ _ => PUnit.unit
  | _, _, _, _, _, .cons (first := first) _budget _fits _finishOwnerEq remaining =>
      let head := Riemann.Integration.PreparedSubdivisionAutomaticModels.canonicalCenterStates
        (Fibre.frameCurve frame) basis sheet first.subdivision
      let tail := build remaining
      ⟨head, tail⟩
termination_by structural _ _ _ _ _ lineage => lineage

/-- The selected centers of a nonempty lineage retain its original canonical head and selected tail.

This readback exposes the constructor equation without exposing the
implementation of the complete center-selection operation.
-/
theorem build_cons {start middle finish : Canonical}
    {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
    {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {within : head.WithinAmbient}
    {first : CompleteSegment head within owner}
    {finishOwner : Owner ((Paths.polynomial parameter).eval middle)} {rest : PreparedPath tail finishOwner}
    (budget : PreparedTraceBudget head PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint)
    (fits : budget.RequestsFit PreparedClearPathModels.zeroEndpoint first.subdivision.requests)
    (finishOwnerEq : finishOwner = first.finishOwner) (remaining : TraceLineage rest) :
    build (frame := frame) (basis := basis) (sheet := sheet)
      (.cons (first := first) budget fits finishOwnerEq remaining) =
      (Riemann.Integration.PreparedSubdivisionAutomaticModels.canonicalCenterStates
        (Fibre.frameCurve frame) basis sheet first.subdivision,
        build (frame := frame) (basis := basis) (sheet := sheet) remaining) := by
  conv =>
    lhs
    unfold build

/-- Read the SAME original centers from an already retained source product, without any new center selection. -/
def fromSources :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    Trace.Materialized.Sources (frame := frame) (basis := basis) (targets := targets)
      (count := count) (floor := floor) (sheet := sheet) lineage →
      Centers (frame := frame) (basis := basis) (sheet := sheet) lineage
  | _, _, _, _, _, .nil _ _, _ => PUnit.unit
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, sources =>
      ⟨sources.1.1, fromSources remaining sources.2⟩
termination_by structural _ _ _ _ _ lineage _ => lineage

end Centers

/-- One actual refinement comparison on each SAME old raw segment Spine and its unchanged original center product.

The actual raw Trace and old Spine are the supplied materialized prefix
and its original complete-segment transport. Its
refinement outcome retains every original stationary role and every new
source child before the literal remaining lineage is consumed.
-/
@[expose] def Cache (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → Centers (frame := frame) (basis := basis) (sheet := sheet) lineage → Type 2
  | _, _, _, _, _, .nil _ _, _ => PUnit
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining, centers =>
      (Σ trace : PreparedTraceBudget.Trace budget first.subdivision fits,
        Σ old : Primitive.Spine (row.expression parameter) accuracy trace.path,
          Refinement.Compared (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
            (accuracy := accuracy)
            row diameter positive request budget first.subdivision centers.1 fits trace old) ×
              Cache row diameter positive request remaining centers.2
termination_by structural _ _ _ _ _ lineage _ => lineage

namespace Cache

/-- Flatten SAME actual child source samples in original segment, request and refined-child order. -/
@[expose] def integrals (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    Cache
      (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers → List Canonical
  | _, _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, centers, retained =>
      retained.1.2.2.integrals ++ integrals row diameter positive request remaining centers.2 retained.2
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- Flatten all actual new refinement residuals and both retained old stationary roles per original request. -/
@[expose] def errors (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    Cache
      (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers → List Canonical
  | _, _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, centers, retained =>
      retained.1.2.2.errors ++ errors row diameter positive request remaining centers.2 retained.2
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- Sum the exact actual segment residual counts, including stationary and empty-child request outcomes. -/
@[expose] def residualCount (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    Cache (count := count) (floor := floor) (targets := targets)
      (accuracy := accuracy) row diameter positive request lineage centers → Nat
  | _, _, _, _, _, .nil _ _, _, _ => 0
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, centers, retained =>
      retained.1.2.2.residualCount + residualCount row diameter positive request remaining centers.2 retained.2
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- Sum all SAME actual refined child counts in original segment/request order. -/
@[expose] def childCount (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    Cache (count := count) (floor := floor) (targets := targets)
      (accuracy := accuracy) row diameter positive request lineage centers → Nat
  | _, _, _, _, _, .nil _ _, _, _ => 0
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, centers, retained =>
      retained.1.2.2.childCount + childCount row diameter positive request remaining centers.2 retained.2
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- The actual residual count is twice all actual children plus three roles per original old request. -/
theorem residualCount_eq (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (retained : Cache
      (count := count) (floor := floor) (targets := targets)
        (accuracy := accuracy) row diameter positive request lineage centers) →
      residualCount
        (count := count) (floor := floor) (targets := targets)
          (accuracy := accuracy) row diameter positive request lineage centers retained =
        2 * childCount
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request lineage centers retained +
          3 * Trace.Materialized.Sources.requestCount lineage
  | _, _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, _, .cons (first := first) _budget _fits _finishOwnerEq remaining, centers, retained => by
      have head := retained.1.2.2.residualCount_eq
      have following := residualCount_eq row diameter positive request remaining centers.2 retained.2
      change retained.1.2.2.residualCount + _ = 2 * (retained.1.2.2.childCount + _) +
        3 * (first.subdivision.requests.length + Trace.Materialized.Sources.requestCount remaining)
      omega0
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- Sum all actual mixed-request/source charges and old stationary allowances without discarding endpoint floors. -/
@[expose] def charge (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    Cache
      (count := count) (floor := floor) (targets := targets)
        (accuracy := accuracy) row diameter positive request lineage centers → Rational
  | _, _, _, _, _, .nil _ _, _, _ => 0
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, centers, retained =>
      retained.1.2.2.charge + charge row diameter positive request remaining centers.2 retained.2
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- The actual flattened error word has the exact sum of its retained original occurrence counts. -/
theorem errors_length (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (retained : Cache
      (count := count) (floor := floor) (targets := targets)
        (accuracy := accuracy) row diameter positive request lineage centers) →
    (errors
      (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage centers retained).length =
      residualCount
        (count := count) (floor := floor) (targets := targets)
          (accuracy := accuracy) row diameter positive request lineage centers retained
  | _, _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, centers, retained =>
      (Data.List.Append.length_append _ _).trans (congrArg₂ Nat.add retained.1.2.2.errors_length
        (errors_length row diameter positive request remaining centers.2 retained.2))
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- Both old stationary allowances and each genuine refinement payment bound the SAME flattened error norm sum. -/
theorem normSum_le (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (retained : Cache
      (count := count) (floor := floor) (targets := targets)
        (accuracy := accuracy) row diameter positive request lineage centers) →
    gaussianNormSqSum (errors
      (count := count) (floor := floor) (targets := targets)
        (accuracy := accuracy) row diameter positive request lineage centers retained) ≤
      charge
        (count := count) (floor := floor) (targets := targets)
          (accuracy := accuracy) row diameter positive request lineage centers retained
  | _, _, _, _, _, .nil _ _, _, _ => Data.Rat.Fraction.Order.Basic.le_refl 0
  | _, _, _, _, _, .cons _budget _fits _finishOwnerEq remaining, centers, retained =>
      (Norm.Sum.Basic.gaussianNormSqSum_append _ _).trans_le
        (Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct retained.1.2.2.normSum_le
          (normSum_le row diameter positive request remaining centers.2 retained.2))
termination_by structural _ _ _ _ _ lineage _ _ => lineage

/-- The actual comparison cache together with the exact SAME whole-old-Spine endpoint telescope.

The equality concerns the literal supplied old first and last values and
all actually retained refined source samples. The producer derives it
from each genuine segment split and shared old Vertex; it is not an input
agreement or root-return premise.
-/
@[expose] def Completion (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (lineage : TraceLineage prepared) (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared))
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) :=
  {retained : Cache (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage centers //
    gaussianSum (errors
      (count := count) (floor := floor) (targets := targets)
        (accuracy := accuracy) row diameter positive request lineage centers retained) =
      observed.last.value - observed.first.value -
        gaussianSum (integrals
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request lineage centers retained)}

namespace Completion

section Cons

variable {start middle finish : Canonical}
    {head : ClearSegment (Paths.polynomial parameter) ambient start middle}
    {tail : ClearPath (Paths.polynomial parameter) ambient middle finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {within : head.WithinAmbient}
    {middleOwner : Owner ((Paths.polynomial parameter).eval middle)} {rest : PreparedPath tail middleOwner}
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (first : CompleteSegment head within owner)
    (budget : PreparedTraceBudget head PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint)
    (fits : budget.RequestsFit PreparedClearPathModels.zeroEndpoint first.subdivision.requests)
    (finishOwnerEq : middleOwner = first.finishOwner) (remaining : TraceLineage rest)
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet)
      (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining))
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner
        (PreparedPath.cons head tail owner within first (PreparedPathTrace.PreparedPath.castOwner finishOwnerEq rest))))
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized)
    (front : PreparedTraceBudget.Trace budget first.subdivision fits)
    (headObserved : Primitive.Spine (row.expression parameter) accuracy front.path)
    (compared : Refinement.Compared (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets) (accuracy := accuracy)
      row diameter positive request budget first.subdivision centers.1 fits front headObserved)
    (followingPath : OwnerPath (Paths.polynomial parameter) middle middleOwner finish
      (PreparedPathGluing.finishOwner rest))
    (tailObserved : Primitive.Spine (row.expression parameter) accuracy followingPath)
    (following : Completion (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets) (accuracy := accuracy)
      row diameter positive request remaining centers.2 followingPath tailObserved)
    (firstValue : headObserved.first.value = observed.first.value)
    (lastValue : tailObserved.last.value = observed.last.value)
    (shared : tailObserved.first.value = headObserved.last.value)

/-- Join the actual first comparison to the following completion using original old observation readbacks.

The complete head and tail caches are retained unchanged. The three scalar
identities come from the actual split's first, last and shared old Vertices;
only this finite telescope is assembled, with no new source preparation,
path split, numerical comparison or root-return premise.
-/
def cons :
    Completion (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      (accuracy := accuracy) row diameter positive request
      (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining)
      centers materialized observed := by
  let retained : Cache (count := count) (floor := floor) (targets := targets)
    (accuracy := accuracy) row diameter positive request
      (TraceLineage.cons (first := first) (rest := rest) budget fits finishOwnerEq remaining) centers :=
    ⟨⟨front, headObserved, compared⟩, following.val⟩
  refine ⟨retained, ?_⟩
  have headFirst := firstValue
  have headLast := shared.symm
  have headValue := congrArg₂ (fun first last : Canonical =>
    last - first - gaussianSum compared.integrals) headFirst headLast
  have tailValue := congrArg (fun last : Canonical => last - tailObserved.first.value -
    gaussianSum (integrals
      (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request remaining centers.2 following.val)) lastValue
  have scalar :
      (tailObserved.first.value - observed.first.value - gaussianSum compared.integrals) +
        (observed.last.value - tailObserved.first.value -
          gaussianSum (integrals
            (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
              row diameter positive request remaining centers.2 following.val)) =
      observed.last.value - observed.first.value - (gaussianSum compared.integrals +
        gaussianSum (integrals
          (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
            row diameter positive request remaining centers.2 following.val)) := by ring1
  change gaussianSum (compared.errors ++
      errors
        (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request remaining centers.2 following.val) =
    observed.last.value - observed.first.value - gaussianSum
      (compared.integrals ++ integrals
        (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request remaining centers.2 following.val)
  exact (Norm.Sum.Basic.gaussianSum_append _ _).trans
    ((congrArg₂ (fun first last : Canonical => first + last)
      (compared.sum_errors.trans headValue) (following.property.trans tailValue)).trans
      (scalar.trans (congrArg (fun total : Canonical => observed.last.value - observed.first.value - total)
        (Norm.Sum.Basic.gaussianSum_append _ _)).symm))

/-- The shared constructor retains precisely the given whole head comparison and the literal completed tail. -/
theorem cons_val :
    (cons row diameter positive request first budget fits finishOwnerEq remaining
      centers materialized observed front headObserved compared followingPath tailObserved following
      firstValue lastValue shared).val = ⟨⟨front, headObserved, compared⟩, following.val⟩ := by
  unfold cons
  rfl

end Cons

variable {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    {row : Row} {diameter : Rational} {positive : 0 < diameter} {request : AccuracyRequest}
    {lineage : TraceLineage prepared}
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)}
    {observed : Primitive.Spine (row.expression parameter) accuracy materialized}

/-- The actual completion telescope and norm charges bound its source sum against the same old endpoint readings.

This operation consumes the given actual Cache.Completion. It does not
require the old convenience Cache.build factory; given-geometry and old
convenience clients therefore share this same finite Cauchy comparison.
-/
theorem integral_error_le (retained : Completion (count := count) (floor := floor) (targets := targets)
    (accuracy := accuracy) row diameter positive request lineage inputCenters materialized observed) :
    Norm.Basic.normSq (observed.last.value - observed.first.value - gaussianSum
      (integrals (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage inputCenters retained.val)) ≤
      (residualCount (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage inputCenters retained.val : Rational) *
      charge (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
        row diameter positive request lineage inputCenters retained.val := by
  let actualErrors := errors (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage inputCenters retained.val
  have cauchy := (Norm.Basic.normSq_eq_canonical (gaussianSum actualErrors)).trans_le
    (Norm.Sum.Basic.normSq_gaussianSum_le actualErrors)
  have normBound := normSum_le (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage inputCenters retained.val
  have paid := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct normBound
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le actualErrors.length))
  have scalar := (congrArg Norm.Basic.normSq retained.property).symm.trans_le (cauchy.trans paid)
  exact scalar.trans_eq (congrArg (fun total : Nat => (total : Rational) *
    charge (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage inputCenters retained.val)
    (errors_length (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage inputCenters retained.val))

end Completion

/-- Split the SAME actual old path and observations once per original segment and refine only its actual moving parents.

Every raw old Trace and Spine is the supplied actual materialized prefix.
The following old Spine is the actual old suffix with the literal shared
Vertex. Refinement builds sources on sufficiently covered new children;
it assumes no primitive cover for the old root subdivision and executes
no canonical path or old observation factory to obtain runtime data.
-/
def build (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) → (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → materialized = lineage.ownerPath →
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized) →
      Completion
        (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request lineage centers materialized observed
  | _, _, _, _, _, .nil _ _, _centers, _materialized, factory, observed => by
      refine ⟨PUnit.unit, ?_⟩
      cases factory
      change (0 : Canonical) = observed.first.value - observed.first.value - 0
      ring1
  | _, _, _, _, _, .cons (first := first) (rest := rest) budget fits finishOwnerEq remaining,
      centers, materialized, factory, observed =>
      PreparedPathTrace.PreparedPath.TraceLineage.withObservedCons
        first budget fits finishOwnerEq remaining materialized observed factory
        (fun _divided _dividedFactory _same front _frontKept followingPath _followingKept followingFactory
            _views _viewsFactory headObserved _headKept tailObserved _tailKept firstValue lastValue shared => by
          let compared := Refinement.compare (frame := frame) (basis := basis) (count := count)
            (floor := floor) (targets := targets)
            row diameter positive request budget first.subdivision centers.1 fits front headObserved
          let following := build row diameter positive request remaining centers.2
            followingPath followingFactory tailObserved
          exact Completion.cons (count := count) (floor := floor) (targets := targets)
            (accuracy := accuracy) row diameter positive request first budget fits finishOwnerEq remaining
            centers materialized observed front headObserved compared followingPath tailObserved following
            firstValue lastValue shared)
termination_by structural _ _ _ _ _ lineage _ _ _ _ => lineage

end Cache

variable {start finish : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath clearPath owner}
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (lineage : TraceLineage prepared) (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) (factory : materialized = lineage.ownerPath)
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized)

/-- Retain the whole old path/Spine, actual original centers and complete new source-refinement execution.

The existing dependent product stores each whole given input with its
identity. The exact completed-cache factory consumes those same retained
inputs. No original path, old observation, root preparation or canonical
trace is replayed to recover data for the comparison.
-/
@[expose] def Compared :=
  (_keptPath : {value : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared) // value = materialized}) ×
  (Σ keptCenters : {value : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage // value = centers},
    Σ keptObserved : {value : Primitive.Spine (row.expression parameter) accuracy materialized // value = observed},
      {completed : Cache.Completion (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request lineage keptCenters.val materialized keptObserved.val //
        completed = Cache.build (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
          row diameter positive request lineage keptCenters.val materialized factory keptObserved.val})

/-- Execute the actual old-lineage/refined-source comparison once on these SAME whole old inputs. -/
def compare : Compared (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage centers materialized factory observed :=
  let completed := Cache.build (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage centers materialized factory observed
  ⟨⟨materialized, rfl⟩, ⟨⟨centers, rfl⟩, ⟨observed, rfl⟩, ⟨completed, rfl⟩⟩⟩

namespace Compared

variable {row diameter positive request lineage centers materialized factory observed}
variable (retained : Compared (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
  row diameter positive request lineage centers materialized factory observed)

/-- Read the SAME whole given old materialized path; no canonical path factory supplies its runtime data. -/
@[expose] def path : OwnerPath (Paths.polynomial parameter) start owner finish
    (PreparedPathGluing.finishOwner prepared) := retained.1.val

/-- Read the unchanged whole supplied old primitive Spine with every original observation and stationary outcome. -/
@[expose] def observations : Primitive.Spine (row.expression parameter) accuracy materialized := retained.2.2.1.val

/-- Read the SAME whole original center product, whether supplied or explicitly selected once beforehand. -/
@[expose] def parentCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage := retained.2.1.val

/-- Read the actual complete refinement execution and its derived old-Spine telescope. -/
@[expose] def completed : Cache.Completion
  (count := count) (floor := floor) (targets := targets)
    (accuracy := accuracy) row diameter positive request lineage retained.parentCenters
    materialized retained.observations := retained.2.2.2.val

/-- The complete old path remains the literal given materialized value. -/
theorem path_eq : retained.path = materialized := retained.1.property

/-- Every old Vertex, request and tail remains in the literal given observation Spine. -/
theorem observations_eq : retained.observations = observed := retained.2.2.1.property

/-- The actual complete source-refinement cache retains its exact whole execution factory on the SAME old inputs. -/
theorem completed_eq : retained.completed = Cache.build
  (count := count) (floor := floor) (targets := targets)
    (accuracy := accuracy) row diameter positive request lineage retained.parentCenters
    materialized factory retained.observations := retained.2.2.2.property

/-- Read actual refined source samples in original segment/request/child order. -/
@[expose] def integrals : List Canonical := Cache.integrals
  (count := count) (floor := floor) (targets := targets) (accuracy := accuracy) row diameter positive request lineage
  retained.parentCenters retained.completed.val

/-- Read both old stationary contributions per request and every actual new refinement residual. -/
@[expose] def errors : List Canonical := Cache.errors
  (count := count) (floor := floor) (targets := targets) (accuracy := accuracy) row diameter positive request lineage
  retained.parentCenters retained.completed.val

/-- Read the exact actual residual count; no stationary or repeated occurrence is discarded. -/
@[expose] def residualCount : Nat := Cache.residualCount
  (count := count) (floor := floor) (targets := targets) (accuracy := accuracy) row diameter positive request lineage
  retained.parentCenters retained.completed.val

/-- Read the SAME actual total refined child count, including each repeated original request. -/
@[expose] def childCount : Nat := Cache.childCount
  (count := count) (floor := floor) (targets := targets) (accuracy := accuracy) row diameter positive request lineage
  retained.parentCenters retained.completed.val

/-- The actual residual count is twice all refined children plus three roles per SAME original prepared step. -/
theorem residualCount_eq : retained.residualCount = 2 * retained.childCount + 3 * prepared.stepCount :=
  (Cache.residualCount_eq
    (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage retained.parentCenters retained.completed.val).trans
    (congrArg (fun count : Nat => 2 * retained.childCount + 3 * count)
      (Trace.Materialized.Sources.requestCount_eq_stepCount lineage))

/-- Read all actual old/request/source charges, retaining their original tolerances. -/
@[expose] def charge : Rational := Cache.charge
  (count := count) (floor := floor) (targets := targets) (accuracy := accuracy) row diameter positive request lineage
  retained.parentCenters retained.completed.val

/-- The closing endpoint contribution is the SAME given old last-minus-first value; it is not assumed to vanish. -/
@[expose] def endpointContribution : Canonical := retained.observations.last.value - retained.observations.first.value

/-- The retained endpoint contribution is the exact literal old last-minus-first value, without a return assumption. -/
theorem endpointContribution_eq : retained.endpointContribution = observed.last.value - observed.first.value :=
  congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy materialized =>
    old.last.value - old.first.value) retained.observations_eq

/-- The whole actual error word has its internally derived occurrence count. -/
theorem errors_length : retained.errors.length = retained.residualCount :=
  Cache.errors_length
    (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage retained.parentCenters retained.completed.val

/-- The SAME actual refined source sum retains the given old final and first values exactly. -/
theorem sum_errors : gaussianSum retained.errors = observed.last.value - observed.first.value -
    gaussianSum retained.integrals :=
  retained.completed.property.trans (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy
    materialized => old.last.value - old.first.value - gaussianSum retained.integrals) retained.observations_eq)

/-- The actual old stationary and new refinement comparisons pay the full actual norm sum internally. -/
theorem normSum_le : gaussianNormSqSum retained.errors ≤ retained.charge :=
  Cache.normSum_le
    (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage retained.parentCenters retained.completed.val

/-- The actual residual count and mixed-request charges bound the refined source sum against the unchanged old Spine.

Old observation floors remain explicit in the charge. This is a finite
source-integral comparison, not arbitrary requested accuracy, geometric
row-model attachment, primitive normalization, canonical-cycle incidence
or global root return. The actual endpoint contribution remains visible.
-/
theorem integral_error_le : Norm.Basic.normSq (observed.last.value - observed.first.value -
    gaussianSum retained.integrals) ≤ (retained.residualCount : Rational) * retained.charge := by
  have actual := Cache.Completion.integral_error_le (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    (row := row) (diameter := diameter) (positive := positive) (request := request)
    (lineage := lineage) (inputCenters := retained.parentCenters) (materialized := materialized)
    (observed := retained.observations) retained.completed
  have same := congrArg Norm.Basic.normSq (congrArg
    (fun old : Primitive.Spine (row.expression parameter) accuracy materialized =>
      old.last.value - old.first.value - gaussianSum retained.integrals) retained.observations_eq)
  exact same.symm.trans_le actual

end Compared

/-- One explicit center selection and complete source-refinement comparison on the unchanged whole old input.

The center producer runs once on the original subdivisions without an
old primitive-cover requirement. The actual comparison then consumes
that same stored product. Both full factories accompany the retained
old path/Spine and all actual refined-source and join caches.
-/
@[expose] def Acquisition :=
  Σ selected : {value : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage //
      value = Centers.build (frame := frame) (basis := basis) (sheet := sheet) lineage},
  {retained : Compared (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage selected.val materialized factory observed //
    retained = compare (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
      row diameter positive request lineage selected.val materialized factory observed}

/-- Select centers once and construct the complete actual source refinement on the SAME old path and old Spine. -/
def acquire : Acquisition (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage materialized factory observed :=
  let selected := Centers.build (frame := frame) (basis := basis) (sheet := sheet) lineage
  let retained := compare (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage selected materialized factory observed
  ⟨⟨selected, rfl⟩, ⟨retained, rfl⟩⟩

namespace Acquisition

variable {row diameter positive request lineage materialized factory observed}
variable (retained : Acquisition (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
  row diameter positive request lineage materialized factory observed)

/-- Read the SAME completed whole-old-Spine/source refinement built on its one actual stored center selection. -/
@[expose] def compared : Compared
  (count := count) (floor := floor) (targets := targets) (accuracy := accuracy)
    row diameter positive request lineage retained.1.val materialized factory observed :=
  retained.2.val

/-- The actual whole comparison consumes the SAME retained center product and unchanged old path/Spine. -/
theorem compared_eq : retained.compared = compare row diameter positive request lineage retained.1.val
    materialized factory observed := retained.2.property

end Acquisition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
