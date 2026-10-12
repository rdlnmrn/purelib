module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedBlockComparison
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Batteries.Logic
import Init.Core
import Init.Data.List.FinRange
import Init.Data.List.Lemmas
import Init.Data.List.OfFn
import Init.Data.Nat.MinMax
import Init.GetElem
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

/-! Controlled source references for the same retained bank that carries the
cross-parent boundary estimate. Parent depths may differ; no primitive is
resampled to manufacture agreement with the physical shared-face reference. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.LinkedRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (SourceRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries (BoundaryBankRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests (CertifiedSourceSum certifySourceSum)
open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (CenteredEdge curve differential)}
  {target requested : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {original : Request regular other parents
    target minimum}
  {request : BoundaryBankRequest original
    requested}
  (evaluated : BoundaryBankRequest.Evaluation
    request)

/-- Each actual member of the original proper parent bank has strictly ordered parameter endpoints. -/
theorem proper_member {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (proper : PreparedDyadicRefinements.AllParentsProper parents) {parent : PreparedSubdivisionModelCore.CenteredEdge
      curve differential}
    (member : parent ∈ parents) : parent.edge.left.parameter < parent.edge.request.endpoint.parameter := by
  induction parents with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
    rcases Data.List.Membership.mem_cons.mp member with same | member
    · subst parent; exact proper.1
    · exact ih proper.2 member

set_option genInjectivity false in
/-- The two controlled original source requests and their cached endpoint data on one retained parent.

Both requests reuse the exact acquired primitive polynomials and preserve their original point and increment readbacks.
-/
structure ControlledEntry (i : Fin original.plans.length) where
  /-- The original first controlled source request on this exact retained parent. -/ first :
    PairedParentRequest.Request.SourceRequest (PairedParentCharts.ChartParent original i).parent original.allowance
    minimum
  /-- The original second controlled request on this retained parent recast to the other differential. -/ second :
    PairedParentRequest.Request.SourceRequest (PreparedEdgeRecasting.recastCenteredEdge other
    (PairedParentCharts.ChartParent original i).parent) original.allowance minimum
  /-- The first original controlled request uses the exact acquired source primitive polynomial. -/ first_eq :
    first.localRequest.request.model.primitive.value = (evaluated.entries.get i).samples.source.primitive.value
  /-- The second original controlled request uses the exact acquired recast source primitive polynomial. -/ second_eq :
    second.localRequest.request.model.primitive.value = (evaluated.entries.get i).samples.otherSource.primitive.value
  /-- The cached actual paired original source value at the parent's first parameter. -/ firstPoint :
    Stokes.PrimitivePoint
  /-- The first point cache equals the retained original paired source value at zero. -/ firstPoint_eq : firstPoint =
    CommonRibbonRequest.sourceValues
    (evaluated.entries.get i).samples.source (evaluated.entries.get i).samples.otherSource 0
  /-- The cached actual paired original source value at the parent's last parameter. -/ lastPoint :
    Stokes.PrimitivePoint
  /-- The last point cache equals the retained original paired source value at one. -/ lastPoint_eq : lastPoint =
    CommonRibbonRequest.sourceValues
    (evaluated.entries.get i).samples.source (evaluated.entries.get i).samples.otherSource 1
  /-- The cached first original controlled source increment. -/ firstIncrement : InverseRootPolynomial.Gaussian
  /-- The first increment cache is exactly the actual original local request increment. -/ firstIncrement_eq :
    firstIncrement = LocalRequest.increment first.localRequest
  /-- The cached second original controlled source increment. -/ secondIncrement : InverseRootPolynomial.Gaussian
  /-- The second increment cache is exactly the actual original recast request increment. -/ secondIncrement_eq :
    secondIncrement = LocalRequest.increment second.localRequest

constructive_injectivity ControlledEntry

/-- Reuse both acquired original primitive samples to prepare their controlled requests and cache the exact endpoint
values and increments. -/
@[expose] def ControlledEntry.build (i : Fin original.plans.length) :
  ControlledEntry evaluated i := by
  let plan := PairedParentCharts.ChartParent original i
  have member : plan ∈ original.plans := List.getElem_mem i.isLt
  have inParents : plan.parent ∈ parents := Eq.mp
    (congrArg (fun values => plan.parent ∈ values) original.parents_eq)
    (Map.mem_map_of_mem (f := Plan.parent) member)
  have proper := proper_member original.proper
    inParents
  have after : plan.index ≤ request.index := (Plan.index_le member).trans
    (original.index_eq.symm.trans_le request.original_le)
  have firstLater := ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans after
  have secondLater := ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans after
  let first := plan.source.sourceRequest proper (evaluated.entries.get i).samples.source firstLater
  let second := plan.otherSource.sourceRequest proper (evaluated.entries.get i).samples.otherSource secondLater
  let firstPoint := CommonRibbonRequest.sourceValues
    (evaluated.entries.get i).samples.source (evaluated.entries.get i).samples.otherSource 0
  let lastPoint := CommonRibbonRequest.sourceValues
    (evaluated.entries.get i).samples.source (evaluated.entries.get i).samples.otherSource 1
  have firstIncrement : lastPoint.left - firstPoint.left = LocalRequest.increment first.localRequest := by
    dsimp only [LocalRequest.increment, -eq_self, -iff_self]
    rw [plan.source.sourceRequest_primitive proper _ firstLater]
    rfl
  have secondIncrement : lastPoint.right - firstPoint.right = LocalRequest.increment second.localRequest := by
    dsimp only [LocalRequest.increment, -eq_self, -iff_self]
    rw [plan.otherSource.sourceRequest_primitive proper _ secondLater]
    rfl
  exact ⟨first, second,
    plan.source.sourceRequest_primitive proper _ firstLater,
    plan.otherSource.sourceRequest_primitive proper _ secondLater,
    firstPoint, rfl, lastPoint, rfl,
    lastPoint.left - firstPoint.left, firstIncrement, lastPoint.right - firstPoint.right, secondIncrement⟩

/-- The complete original controlled entry bank indexed by the retained parent plans. -/
@[expose] def ControlledEntries := Data.Vector.DependentVector
  (ControlledEntry evaluated)

/-- Prepare each original parent's controlled requests and cache its actual paired endpoint values and increments. -/
@[expose] def controlledEntries : ControlledEntries
  evaluated := DependentVector.ofFn
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.ControlledEntry.build evaluated)

/-- The retained plan indices enumerate exactly the original parent list in order. -/
theorem indexed_parents :
    (List.finRange original.plans.length).map (fun i => (PairedParentCharts.ChartParent original i).parent) = parents :=
      by
  unfold List.finRange
  rw [OfFn.Basic.map_ofFn]
  have readback := congrArg (List.map Plan.parent) (OfFn.Basic.ofFn_getElem original.plans)
  rw [OfFn.Basic.map_ofFn] at readback
  exact readback.trans original.parents_eq

/-- The cached first source increments in original retained parent order. -/
@[expose] def firstIncrements (entries :
  ControlledEntries evaluated) :=
  (List.finRange original.plans.length).map (fun i => (entries.get i).firstIncrement)

/-- The cached second source increments in original retained parent order. -/
@[expose] def secondIncrements (entries :
  ControlledEntries evaluated) :=
  (List.finRange original.plans.length).map (fun i => (entries.get i).secondIncrement)

/-- The actual paired original source increment paths at each retained parent's own paid depth. -/
@[expose] def Evaluation.sourcePaths (evaluated : BoundaryBankRequest.Evaluation request) :=
  List.ofFn (fun i : Fin original.plans.length => DyadicPairedPrimitivePaths.increments
    (CommonRibbonRequest.sourceValues (evaluated.entries.get i).samples.source (evaluated.entries.get
      i).samples.otherSource)
    ((PairedParentCharts.ChartParent original i).common.depth + (request.plans.get i).depth) 0 1)

/-- The complete actual parent source path total equals its two retained controlled increment caches. -/
theorem ControlledEntry.source_total {i : Fin original.plans.length} (entry :
  ControlledEntry evaluated i) :
    PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues (evaluated.entries.get i).samples.source (evaluated.entries.get
        i).samples.otherSource)
      ((PairedParentCharts.ChartParent original i).common.depth + (request.plans.get i).depth) 0 1) =
        ⟨entry.firstIncrement, entry.secondIncrement⟩ := by
  rw [DyadicPairedPrimitivePaths.increments_total, entry.firstIncrement_eq, entry.secondIncrement_eq]
  dsimp only [LocalRequest.increment, -eq_self, -iff_self]
  rw [entry.first_eq, entry.second_eq]
  rfl

/-- The full joined source path has exactly the cached controlled increments used by the two shared-face references, in
their original parent order. -/
theorem sourcePaths_total (entries :
  ControlledEntries evaluated) :
    Purelib.Integration.Path.PairedIncrementArea.total
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated).flatten =
      ⟨gaussianSum (firstIncrements evaluated
        entries), Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (secondIncrements evaluated entries)⟩
        := by
  have totals : (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths
    evaluated).map PairedIncrementArea.total =
      (List.finRange original.plans.length).map (fun i =>
        (⟨(entries.get i).firstIncrement, (entries.get i).secondIncrement⟩ : Stokes.PrimitivePoint)) := by
    dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths,
      List.finRange, -eq_self, -iff_self]
    rw [OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
    apply OfFn.Basic.ofFn_congr
    intro i
    exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.ControlledEntry.source_total evaluated
      (entries.get i)
  rw [PairedAreaBlocks.total_flatten, totals]
  unfold PairedIncrementArea.total firstIncrements
    secondIncrements
  rw [Data.List.Map.map_map, Data.List.Map.map_map]
  rfl

/-- The original polygon of cached paired parent increments in retained order. -/
@[expose] def sourcePolygon (entries :
  ControlledEntries evaluated) : List PrimitivePoint
  :=
  List.ofFn (fun i : Fin original.plans.length => ⟨(entries.get i).firstIncrement, (entries.get i).secondIncrement⟩)

/-- The finite sum of actual original endpoint chord areas from the retained parent endpoint caches. -/
@[expose] def sourceChordArea (entries :
  ControlledEntries evaluated) : Gaussian :=
  FiniteSum.Fin.sumFin (fun i => Stokes.edgeArea (entries.get i).firstPoint (entries.get i).lastPoint)

/-- The actual original parent path totals form exactly the retained cached source polygon. -/
theorem sourcePaths_polygon (entries :
  ControlledEntries evaluated) :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated).map
      PairedIncrementArea.total = sourcePolygon
      evaluated entries := by
  dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths,
    sourcePolygon, -eq_self, -iff_self]
  rw [OfFn.Basic.map_ofFn]
  exact OfFn.Basic.ofFn_congr (fun i =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.ControlledEntry.source_total evaluated
    (entries.get i))

/-- The full source area includes the polygon of all parent totals and subtracts the actual source endpoint chords, even
with unequal parent depths. -/
theorem sourcePaths_area (entries : ControlledEntries
  evaluated) :
    PairedIncrementArea.area (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths
      evaluated).flatten =
      evaluated.sourceArea - sourceChordArea
        evaluated entries +
        PairedIncrementArea.area (sourcePolygon
          evaluated entries) := by
  rw [PairedAreaBlocks.area_flatten,
    sourcePaths_polygon evaluated entries]
  have internal : Data.Gaussian.Norm.Sum.Basic.gaussianSum
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated).map
    PairedIncrementArea.area) =
      evaluated.sourceArea - sourceChordArea
        evaluated entries := by
    dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths, -eq_self,
      -iff_self]
    rw [OfFn.Basic.map_ofFn, ← Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum, evaluated.sourceArea_eq]
    unfold sourceChordArea
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro i
    dsimp only [Function.comp_def, -eq_self, -iff_self]
    rw [DyadicPairedPrimitivePaths.increments_area, (entries.get i).firstPoint_eq, (entries.get i).lastPoint_eq,
      evaluated.source_readback request i]
  exact congrArg (fun value => value + PairedIncrementArea.area
    (sourcePolygon evaluated entries)) internal

/-- The controlled first source sum certificate on the exact retained original parents and cached increment total. -/
@[expose] def FirstSourceSum (entries :
  ControlledEntries evaluated) :=
  PairedSourceRequests.CertifiedSourceSum parents target minimum (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (firstIncrements evaluated entries))

/-- The controlled second source sum certificate on the recast original parents and cached increment total. -/
@[expose] def SecondSourceSum (entries :
  ControlledEntries evaluated) :=
  PairedSourceRequests.CertifiedSourceSum (parents.map (PreparedEdgeRecasting.recastCenteredEdge other)) target minimum
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (secondIncrements evaluated entries))

/-- Certify the actual cached first source total from the original controlled requests and retained movement payment. -/
@[expose] def firstSourceSum (entries :
  ControlledEntries evaluated) :
  FirstSourceSum evaluated entries :=
  PairedSourceRequests.certifySourceSum (genus := genus) (curve := curve) (differential := differential)
    (fun i => (PairedParentCharts.ChartParent original i).parent) (fun i => (entries.get i).first)
    (fun i => (entries.get i).firstIncrement) (fun i => (entries.get i).firstIncrement_eq.symm)
    (List.finRange original.plans.length)
      indexed_parents original.positive
      (PairedSourceRequests.target_positive original) (PairedSourceRequests.local_paid original)
    original.sourceMass original.sourceMass_eq original.source_paid

/-- Certify the actual cached second source total on the recast original parents with the same retained movement
payment. -/
@[expose] def secondSourceSum (entries :
  ControlledEntries evaluated) :
  SecondSourceSum evaluated entries := by
  have parentEq : (List.finRange original.plans.length).map (fun i => PreparedEdgeRecasting.recastCenteredEdge other
    (PairedParentCharts.ChartParent original i).parent) =
      parents.map (PreparedEdgeRecasting.recastCenteredEdge other) := by
    have mapped := congrArg (List.map (PreparedEdgeRecasting.recastCenteredEdge other))
      (indexed_parents (original := original))
    rw [Data.List.Map.map_map] at mapped
    dsimp only [Function.comp_def] at mapped
    exact mapped
  exact PairedSourceRequests.certifySourceSum (genus := genus) (curve := curve) (differential := other)
    (fun i => PreparedEdgeRecasting.recastCenteredEdge other (PairedParentCharts.ChartParent original i).parent) (fun i
      => (entries.get i).second)
    (fun i => (entries.get i).secondIncrement) (fun i => (entries.get i).secondIncrement_eq.symm)
    (List.finRange original.plans.length) parentEq original.positive (PairedSourceRequests.target_positive original)
    ((congrArg (Aggregate.perTerm target) (Data.List.Map.length_map ..)).symm ▸ (PairedSourceRequests.local_paid
      original))
    original.sourceMass (original.sourceMass_eq.trans (PreparedRefinementMovement.movementMass_recast other
      parents).symm)
    original.source_paid

set_option genInjectivity false in
/-- The complete original controlled source bank and cached full path summary.

Both certified source sums, the polygon of parent totals and every actual endpoint chord correction are retained. -/
structure Sources where
  /-- The actual original controlled source requests and cached endpoint data. -/ entries :
    ControlledEntries evaluated
  /-- The first source sum certificate consuming these exact retained original entries. -/ first :
    FirstSourceSum evaluated entries
  /-- The second source sum certificate consuming those same retained entries. -/ second :
    SecondSourceSum evaluated entries
  /-- The cached complete original polygon of paired parent increments. -/ polygon : PairedIncrementArea.Summary
    (sourcePolygon evaluated entries)
  /-- The cached sum of all actual original source endpoint chord areas. -/ chords : InverseRootPolynomial.Gaussian
  /-- The chord cache equals the original endpoint chord sum of the retained entries. -/ chords_eq : chords =
    sourceChordArea evaluated entries
  /-- The complete original flattened source path summary with its actual total and area. -/ path :
    PairedIncrementArea.Summary
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated).flatten
  /-- The full source area retains its original parent areas, endpoint chord subtraction and complete polygon of parent
    totals. -/ path_area : path.areaValue = evaluated.sourceArea - chords + polygon.areaValue

constructive_injectivity Sources

/-- Prepare the original controlled entries once and cache both certified sums and the full source area with all
endpoint and polygon corrections. -/
@[expose] def sources : Sources evaluated := by
  let entries := controlledEntries evaluated
  let first := firstSourceSum evaluated entries
  let second := secondSourceSum evaluated entries
  let polygon := PairedIncrementArea.Summary.build
    (sourcePolygon evaluated entries)
  let chords := sourceChordArea evaluated entries
  let total := (⟨first.val.primitiveSum, second.val.primitiveSum⟩ : Stokes.PrimitivePoint)
  have totalEq : total = PairedIncrementArea.total
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated).flatten := by
    rw [sourcePaths_total evaluated entries]
    exact congrArg₂ PrimitivePoint.mk first.property.1 second.property.1
  have areaEq : evaluated.sourceArea - chords + polygon.areaValue =
      PairedIncrementArea.area
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated).flatten :=
        by
    rw [sourcePaths_area evaluated entries,
      polygon.area_eq]
  exact ⟨entries, first, second, polygon, chords, rfl,
    ⟨total, totalEq, evaluated.sourceArea - chords + polygon.areaValue, areaEq⟩, rfl⟩

open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)

/-- The actual complete retained chart increment paths in original parent order. -/
@[expose] def Evaluation.chartPaths := List.ofFn (fun i : Fin original.plans.length =>
  VertexTrace.increments (Evaluation.chartTrace (evaluated.entries.get i)) id)

/-- The polygon of actual original chart-parent endpoint totals. -/
@[expose] def Evaluation.chartPolygon := List.ofFn (fun i : Fin original.plans.length =>
  Evaluation.chartTraceTotal (evaluated.entries.get i))

/-- The complete dependent bank of original chart path summaries on the retained parent indices. -/
@[expose] def Evaluation.ParentCharts := Data.Vector.DependentVector (fun i : Fin original.plans.length =>
  PairedIncrementArea.Summary (VertexTrace.increments (Evaluation.chartTrace (evaluated.entries.get i)) id))

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests in
set_option genInjectivity false in
/-- The paid comparison between the original full source path and complete parent chart paths.

Both original polygons, cached totals, per-parent magnitude bounds and the actual complete area discrepancy remain
retained. -/
structure Sources.ChartComparison (sources : Sources
  evaluated) where
  /-- The actual original per-parent chart summaries. -/ parents :
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.ParentCharts evaluated)
  /-- Every original retained parent chart total satisfies the common slope-derived magnitude bound. -/
    parent_totals_bounded : ∀ i, PrimitivePoint.Bounded
    (parents.get i).totalValue (4 * (original.slope + 1))
  /-- The cached polygon of actual original chart-parent totals. -/ polygon : PairedIncrementArea.Summary
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPolygon evaluated)
  /-- The cached full chart path summary in original retained parent order. -/ chart : PairedIncrementArea.Summary
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths evaluated).flatten)
  /-- The complete chart area is the sum of original parent areas plus the actual polygon of parent totals. -/ area_eq :
    chart.areaValue = FiniteSum.Fin.sumFin (fun i => (parents.get i).areaValue) + polygon.areaValue
  /-- The cached complete original source-versus-chart area comparison bound. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The error cache equals the retained original block scale times its paid allowance. -/ error_eq : error =
    request.blockScale * request.allowance
  /-- The actual original full source-minus-chart area discrepancy has squared norm at most the retained error. -/
    bounded : Data.Gaussian.Norm.Basic.normSq (sources.path.areaValue - chart.areaValue) ≤ error
  /-- The original requested target pays the actual complete source-versus-chart area discrepancy. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (sources.path.areaValue - chart.areaValue) < requested
  /-- The actual original full source and chart totals satisfy the retained componentwise requested bound. -/
    total_accurate : PrimitivePoint.Bounded
    (sources.path.totalValue.sub chart.totalValue) requested

constructive_injectivity Sources.ChartComparison

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests
/-- Both polygons of parent totals are paid. This compares the entire source path with the joined chart paths of its
parents, with no origin or chord term subtracted from either area. All summaries come from the retained bank. -/
@[expose] def Sources.compareCharts (sources :
  Sources evaluated) : sources.ChartComparison
  evaluated := by
  let charts : (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.ParentCharts evaluated) :=
    DependentVector.ofFn (fun i => Evaluation.chartTraceSummary (evaluated.entries.get i))
  let polygon := PairedIncrementArea.Summary.build
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPolygon evaluated)
  have totalsEq : (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths
    evaluated).map PairedIncrementArea.total =
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPolygon evaluated) := by
    dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths,
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPolygon, -eq_self, -iff_self]
    rw [OfFn.Basic.map_ofFn]
    exact OfFn.Basic.ofFn_congr (fun i => Evaluation.chartTrace_total (evaluated.entries.get i))
  have areasEq : Data.Gaussian.Norm.Sum.Basic.gaussianSum
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths evaluated).map
    PairedIncrementArea.area) =
      FiniteSum.Fin.sumFin (fun i => (charts.get i).areaValue) := by
    dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths, -eq_self,
      -iff_self]
    rw [OfFn.Basic.map_ofFn, ← Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum]
    exact FiniteSum.Fin.sumFin_congr (fun i => (charts.get i).area_eq.symm)
  let chart : PairedIncrementArea.Summary
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths evaluated).flatten) :=
    ⟨polygon.totalValue, polygon.total_eq.trans (by rw [PairedAreaBlocks.total_flatten, totalsEq]),
      FiniteSum.Fin.sumFin (fun i => (charts.get i).areaValue) + polygon.areaValue,
      by rw [PairedAreaBlocks.area_flatten, totalsEq, areasEq, polygon.area_eq]⟩
  let pairs := List.ofFn (fun i : Fin original.plans.length =>
    ((evaluated.entries.get i).sourceBlocks.flatten, VertexTrace.increments (Evaluation.chartTrace
      (evaluated.entries.get i)) id))
  have localSmall (i : Fin original.plans.length) : (request.plans.get i).allowance ≤ 1 := by
    have divided : request.allowance / 32 ≤ request.allowance := by
      calc
        _ = 1 * (request.allowance / 32) := (Fraction.Field.one_mul _).symm
        _ ≤ 32 * (request.allowance / 32) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide +kernel)
          (Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide +kernel))
        _ = request.allowance := by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by
          decide +kernel)
    exact ((request.plans.get i).allowance_eq.trans_le (Fraction.Order.Basic.min_le_left _ _)).trans (divided.trans
      request.small)
  have localTotals (i : Fin original.plans.length) :
      PrimitivePoint.Bounded
        ((evaluated.certificates.get i).blocks.source.totalValue.sub
        (charts.get i).totalValue) request.allowance := by
    have before := BlockBank.joined_total_accurate (evaluated.entries.get i) (evaluated.certificates.get i).blocks
      (localSmall i)
    rw [← (charts.get i).total_eq] at before
    have allowance : 16 * (request.plans.get i).allowance ≤ request.allowance := by
      calc
        _ ≤ 32 * (request.plans.get i).allowance := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide +kernel) (request.plans.get i).positive.le
        _ ≤ 32 * (request.allowance / 32) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          ((request.plans.get i).allowance_eq.trans_le (Fraction.Order.Basic.min_le_left _ _)) (by decide +kernel)
        _ = request.allowance := by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by
          decide +kernel)
    exact ⟨before.1.trans allowance, before.2.trans allowance⟩
  have sourceBounds (i : Fin original.plans.length) :
      PrimitivePoint.Bounded
        (evaluated.certificates.get i).blocks.source.totalValue (2 * original.slope) := by
    have bounds := original.plan_bounds (PairedParentCharts.ChartParent original i) (List.getElem_mem i.isLt)
    have combined := Fraction.Order.Arithmetic.add_le_add_direct bounds.1 bounds.2
    rw [show original.slope + original.slope = 2 * original.slope by ring1] at combined
    have before := (evaluated.certificates.get i).blocks.source_magnitude (evaluated.entries.get i)
    exact ⟨before.1.trans combined, before.2.trans combined⟩
  have densityNonnegative : 0 ≤ 4 * (original.slope + 1) := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg original.slope_nonnegative (by decide))
  have larger : 2 * original.slope ≤ 4 * (original.slope + 1) := by
    calc
      _ ≤ 2 * original.slope + (2 * original.slope + 4) := le_add_of_nonneg_right
        (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) original.slope_nonnegative) (by decide))
      _ = _ := by ring1
  have areas : ∀ pair ∈ pairs,
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area pair.1 - PairedIncrementArea.area pair.2) ≤
        request.allowance := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (evaluated.certificates.get i).blocks.source.area_eq]
    exact (Evaluation.joined_source_accurate
      (request.plans.get i) (evaluated.entries.get i) (evaluated.certificates.get i) (localSmall i)).le
  have totals : ∀ pair ∈ pairs,
      PrimitivePoint.Bounded
        ((PairedIncrementArea.total pair.1).sub (PairedIncrementArea.total pair.2)) request.allowance := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (evaluated.certificates.get i).blocks.source.total_eq, ← (charts.get i).total_eq]
    exact localTotals i
  have left : ∀ pair ∈ pairs, PrimitivePoint.Bounded
      (PairedIncrementArea.total pair.1) (4 * (original.slope + 1)) := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (evaluated.certificates.get i).blocks.source.total_eq]
    exact ⟨(sourceBounds i).1.trans larger, (sourceBounds i).2.trans larger⟩
  have parentTotals (i : Fin original.plans.length) : PrimitivePoint.Bounded
      (charts.get i).totalValue (4 * (original.slope + 1)) := by
    have scalar (a b : InverseRootPolynomial.Gaussian) (sourceBound : Data.Gaussian.Basic.Canonical.normSq a ≤ 2 *
      original.slope)
        (error : Data.Gaussian.Basic.Canonical.normSq (a - b) ≤ request.allowance) :
          Data.Gaussian.Basic.Canonical.normSq b ≤ 4 * (original.slope + 1) := by
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at sourceBound error ⊢
      have estimate := Data.Gaussian.Norm.Bounds.normSq_sub_le_two a (a - b)
      rw [show a - (a - b) = b by ring1] at estimate
      have small : request.allowance ≤ (2 : InverseRootPolynomial.Coordinate) := request.small.trans (by decide)
      exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct sourceBound (error.trans small)) (by decide)).trans_eq (by ring1))
    exact ⟨scalar _ _ (sourceBounds i).1 (localTotals i).1, scalar _ _ (sourceBounds i).2 (localTotals i).2⟩
  have right : ∀ pair ∈ pairs, PrimitivePoint.Bounded
      (PairedIncrementArea.total pair.2) (4 * (original.slope + 1)) := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (charts.get i).total_eq]
    exact parentTotals i
  have bound := PairedBlockComparison.blocks_area_difference_bound pairs request.positive.le densityNonnegative areas
    totals left right
  have leftEq : pairs.map Prod.fst =
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated) := by
    dsimp only [pairs, Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths,
      -eq_self, -iff_self]
    rw [OfFn.Basic.map_ofFn]
    exact OfFn.Basic.ofFn_congr (fun i => (evaluated.entries.get i).sourceBlocks_full)
  have rightEq : pairs.map Prod.snd =
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths evaluated) := by
    rw [OfFn.Basic.map_ofFn]
    rfl
  have countEq : pairs.length = original.plans.length := Data.List.OfFn.Basic.length_ofFn
  rw [leftEq, rightEq, countEq, ← sources.path.area_eq, ← chart.area_eq] at bound
  have scale : 2 * ((original.plans.length : InverseRootPolynomial.Coordinate)^2 * request.allowance +
      16 * (original.plans.length : InverseRootPolynomial.Coordinate)^4 * request.allowance * (4 * (original.slope +
        1))) =
      request.blockScale * request.allowance := by rw [request.blockScale_eq]; ring1
  have bounded := bound.trans_eq scale
  let totalPairs := pairs.map (fun pair =>
    (PairedIncrementArea.total pair.1, PairedIncrementArea.total pair.2))
  have totalBound := PairedIncrementArea.total_bound request.positive.le
    (values := totalPairs.map (fun pair => pair.1.sub pair.2)) (by
      intro value member
      obtain ⟨pair, inTotalPairs, rfl⟩ := Map.mem_map.mp member
      obtain ⟨blocks, inPairs, rfl⟩ := Map.mem_map.mp inTotalPairs
      exact totals blocks inPairs) (count := original.plans.length)
    (by rw [Data.List.Map.length_map, Data.List.Map.length_map, countEq])
  rw [PairedIncrementComparison.total_differences] at totalBound
  have totalLeft : totalPairs.map Prod.fst =
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths evaluated).map
    PairedIncrementArea.total := by
    rw [← leftEq, Data.List.Map.map_map, Data.List.Map.map_map]; rfl
  have totalRight : totalPairs.map Prod.snd =
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths evaluated).map
    PairedIncrementArea.total := by
    rw [← rightEq, Data.List.Map.map_map, Data.List.Map.map_map]; rfl
  rw [totalLeft, totalRight, ← PairedAreaBlocks.total_flatten,
    ← PairedAreaBlocks.total_flatten, ← sources.path.total_eq, ← chart.total_eq] at totalBound
  have totalPaid : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * request.allowance ≤ requested := by
    have paid := request.paid.le
    exact (show (original.plans.length : InverseRootPolynomial.Coordinate)^2 * request.allowance =
      (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
        InverseRootPolynomial.Coordinate) * request.allowance) by ring1).trans_le paid
  exact ⟨charts, parentTotals, polygon, chart, rfl, request.blockScale * request.allowance, rfl,
    bounded, bounded.trans_lt request.block_paid, ⟨totalBound.1.trans totalPaid, totalBound.2.trans totalPaid⟩⟩

/-- The original junction request pays the area change from inserting all actual joins between the retained complete
parent chart traces. -/
theorem Sources.ChartComparison.insertion_accurate {junctionTarget : InverseRootPolynomial.Coordinate}
    {linked : PairedBoundaryClosure.LinkedRequest request junctionTarget} (certificate : linked.Certificate)
    (sources : Sources certificate.boundary)
      (comparison : sources.ChartComparison certificate.boundary) :
    Data.Gaussian.Norm.Basic.normSq (comparison.chart.areaValue -
      PairedIncrementArea.area (VertexTrace.increments (Evaluation.chartTrace certificate.boundary) id)) <
        junctionTarget := by
  have magnitude : (0 : InverseRootPolynomial.Coordinate) ≤ 4 * (original.slope + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg original.slope_nonnegative (by decide))
  have larger : linked.allowance ≤ 4 * (original.slope + 1) := by
    have atLeastOne : (1 : InverseRootPolynomial.Coordinate) ≤ original.slope + 1 := le_add_of_nonneg_left
      original.slope_nonnegative
    have atLeastFour := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct atLeastOne (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
    exact linked.small.trans ((by decide : (1 : InverseRootPolynomial.Coordinate) ≤ 4 * 1).trans atLeastFour)
  have totals (i : Fin original.plans.length) :
      PrimitivePoint.Bounded
        (PairedIncrementArea.total (VertexTrace.increments (Evaluation.chartTrace (certificate.boundary.entries.get i))
          id))
        (4 * (original.slope + 1)) := (comparison.parents.get i).total_eq ▸ comparison.parent_totals_bounded i
  have inserted := Evaluation.parentTrace_insertion certificate.boundary linked.positive.le magnitude larger totals
    (Certificate.trace_increments_bounded certificate)
  change Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths
    certificate.boundary).flatten -
    PairedIncrementArea.area (VertexTrace.increments (Evaluation.chartTrace certificate.boundary) id)) ≤ _ at inserted
  rw [← comparison.chart.area_eq] at inserted
  have equal : 32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * linked.allowance * (4
    * (original.slope + 1)) =
      linked.insertionScale * linked.allowance := by rw [linked.insertionScale_eq]; ring1
  exact inserted.trans_lt (equal.trans_lt linked.insertion_paid)

end

/-- The original fourth-power insertion scale dominates the retained squared count for every finite bank, including
zero. -/
private theorem insertion_total_scale (count : Nat) {slope : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ slope)
  :
    (count : InverseRootPolynomial.Coordinate)^2 ≤ 32 * (count : InverseRootPolynomial.Coordinate)^4 * (4 * (slope + 1))
      := by
  cases count with
  | zero =>
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, -eq_self,
      -iff_self]; exact le_rfl
  | succ count =>
      have one : (1 : InverseRootPolynomial.Coordinate) ≤ (count + 1 : Nat) := Fraction.Cast.Order.natCast_le_direct
        (Nat.succ_le_succ (Nat.zero_le _))
      have square : (1 : InverseRootPolynomial.Coordinate) ≤ ((count + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 :=
        (one_pow 2).symm.trans_le (Fraction.Order.Arithmetic.pow_le_pow_direct (by decide) one 2)
      have squareNonnegative := Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct
        (Nat.zero_le (count + 1))) 2
      have fourth : ((count + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 ≤ ((count + 1 : Nat) :
        InverseRootPolynomial.Coordinate)^4 := by
        exact (show _ = ((count + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * 1 by ring1).trans_le
          ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square squareNonnegative).trans_eq (by ring1))
      have magnitude : (1 : InverseRootPolynomial.Coordinate) ≤ 32 * (4 * (slope + 1)) :=
        (by decide +kernel : (1 : InverseRootPolynomial.Coordinate) ≤ 32 * (4 * 1)).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (le_add_of_nonneg_left nonnegative)
              (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)) (by
                  decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 32))
      exact fourth.trans ((show ((count + 1 : Nat) : InverseRootPolynomial.Coordinate)^4 =
        1 * ((count + 1 : Nat) : InverseRootPolynomial.Coordinate)^4 by ring1).trans_le
          ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct magnitude
            (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (count +
              1))) 4)).trans_eq (by ring1)))

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests in
/-- The original junction request pays the componentwise total change from inserting every actual retained parent chart
join. -/
theorem Sources.ChartComparison.insertion_total_accurate {junctionTarget : InverseRootPolynomial.Coordinate}
    {linked : PairedBoundaryClosure.LinkedRequest request junctionTarget} (certificate : linked.Certificate)
    (sources : Sources certificate.boundary)
      (comparison : sources.ChartComparison certificate.boundary) :
    PrimitivePoint.Bounded
      (comparison.chart.totalValue.sub
        (PairedIncrementArea.total (VertexTrace.increments (Evaluation.chartTrace certificate.boundary) id)))
          junctionTarget := by
  have magnitude : (0 : InverseRootPolynomial.Coordinate) ≤ 4 * (original.slope + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg original.slope_nonnegative (by decide))
  have larger : linked.allowance ≤ 4 * (original.slope + 1) := by
    have atLeastOne : (1 : InverseRootPolynomial.Coordinate) ≤ original.slope + 1 := le_add_of_nonneg_left
      original.slope_nonnegative
    exact linked.small.trans ((by decide : (1 : InverseRootPolynomial.Coordinate) ≤ 4 * 1).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct atLeastOne (by decide)))
  have totals (i : Fin original.plans.length) :
      PrimitivePoint.Bounded
        (PairedIncrementArea.total (VertexTrace.increments (Evaluation.chartTrace (certificate.boundary.entries.get i))
          id))
        (4 * (original.slope + 1)) := (comparison.parents.get i).total_eq ▸ comparison.parent_totals_bounded i
  have inserted := Evaluation.parentTrace_total_insertion certificate.boundary linked.positive.le magnitude larger
    totals
    (Certificate.trace_increments_bounded certificate)
  change PrimitivePoint.Bounded
    ((PairedIncrementArea.total
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths
      certificate.boundary).flatten).sub _) _ at inserted
  rw [← comparison.chart.total_eq] at inserted
  have paid : ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * linked.allowance ≤
    junctionTarget := by
    have scale := insertion_total_scale (2 *
      original.plans.length - 1) original.slope_nonnegative
    rw [← linked.insertionScale_eq] at scale
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scale linked.positive.le).trans
      linked.insertion_paid.le
  exact ⟨inserted.1.trans paid, inserted.2.trans paid⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests
