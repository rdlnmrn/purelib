module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Init.Core
import Init.Data.List.FinRange
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.GetElem
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests

public section

/-! The parity-independent chart bank supplies the actual controlled source
requests used by shared-face comparisons. Its primitive polynomials are reused,
and their endpoint increments are cached once for both sum certificates. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Data.List
open Purelib.Data.Vector
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (SourceRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests (CertifiedSourceSum certifySourceSum)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass_recast)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (CenteredEdge curve differential)}
  {target requested : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum depth : Nat}
  {original : Request regular other parents
    target minimum}
  {request : ChartBankRequest original depth
    requested}
  (evaluated : Evaluation
    request)

/-- Every actual member of the original proper parent list has strictly ordered parameter endpoints. -/
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
/-- Both original controlled differential requests on one retained chart parent.

The exact acquired primitive polynomials are reused and both endpoint increments are cached with readback equalities. -/
structure ControlledEntry (i : Fin original.plans.length) where
  /-- The first controlled differential request on the actual retained original chart parent. -/ first :
    PairedParentRequest.Request.SourceRequest (PairedParentCharts.ChartParent original i).parent original.allowance
    minimum
  /-- The second controlled differential request on that same parent recast to the original second differential. -/
    second : PairedParentRequest.Request.SourceRequest (PreparedEdgeRecasting.recastCenteredEdge other
    (PairedParentCharts.ChartParent original i).parent) original.allowance minimum
  /-- The first request uses exactly the primitive polynomial of the original acquired source sample. -/ first_eq :
    first.localRequest.request.model.primitive.value = (evaluated.entries.get i).samples.source.primitive.value
  /-- The second request uses exactly the primitive polynomial of the original acquired recast source sample. -/
    second_eq : second.localRequest.request.model.primitive.value = (evaluated.entries.get
    i).samples.otherSource.primitive.value
  /-- The cached endpoint increment of the original first differential request. -/ firstIncrement :
    InverseRootPolynomial.Gaussian
  /-- The first increment cache equals the actual retained local request increment. -/ firstIncrement_eq :
    firstIncrement = (LocalRequest.increment first.localRequest)
  /-- The cached endpoint increment of the original second differential request. -/ secondIncrement :
    InverseRootPolynomial.Gaussian
  /-- The second increment cache equals the actual retained local request increment. -/ secondIncrement_eq :
    secondIncrement = (LocalRequest.increment second.localRequest)

constructive_injectivity ControlledEntry

/-- Reuse both acquired original primitive samples to build their controlled requests and cache the two exact endpoint
increments. -/
@[expose] def ControlledEntry.build (i : Fin original.plans.length) :
  ControlledEntry evaluated i := by
  let plan := PairedParentCharts.ChartParent original i
  have member : plan ∈ original.plans := List.getElem_mem i.isLt
  have inParents : plan.parent ∈ parents := Eq.mp
    (congrArg (fun values => plan.parent ∈ values) original.parents_eq)
    (Map.mem_map_of_mem (f := Plan.parent) member)
  have proper := proper_member original.proper inParents
  have after : plan.index ≤ request.index := (Plan.index_le member).trans
    (original.index_eq.symm.trans_le request.original_le)
  have firstLater := ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans after
  have secondLater := ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans after
  let first := plan.source.sourceRequest proper (evaluated.entries.get i).samples.source firstLater
  let second := plan.otherSource.sourceRequest proper (evaluated.entries.get i).samples.otherSource secondLater
  exact ⟨first, second,
    plan.source.sourceRequest_primitive proper _ firstLater,
    plan.otherSource.sourceRequest_primitive proper _ secondLater,
    (LocalRequest.increment first.localRequest), rfl, (LocalRequest.increment second.localRequest), rfl⟩

/-- The dependent complete controlled request bank on the original chart parent indices. -/
@[expose] def ControlledEntries := Data.Vector.DependentVector
  (ControlledEntry evaluated)

/-- Prepare each actual original chart parent's two controlled requests and cached endpoint increments. -/
@[expose] def controlledEntries : ControlledEntries
  evaluated := DependentVector.ofFn
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.ControlledEntry.build evaluated)

/-- Reading parent identities from the original finite plan indices yields exactly the retained parent list. -/
theorem indexed_parents :
    (List.finRange original.plans.length).map (fun i => (PairedParentCharts.ChartParent original i).parent) = parents :=
      by
  unfold List.finRange
  rw [OfFn.Basic.map_ofFn]
  have readback := congrArg (List.map Plan.parent) (OfFn.Basic.ofFn_getElem original.plans)
  rw [OfFn.Basic.map_ofFn] at readback
  exact readback.trans original.parents_eq

/-- The cached first-differential endpoint increments in original parent order. -/
@[expose] def firstIncrements (entries :
  ControlledEntries evaluated) :=
  (List.finRange original.plans.length).map (fun i => (entries.get i).firstIncrement)

/-- The cached second-differential endpoint increments in original parent order. -/
@[expose] def secondIncrements (entries :
  ControlledEntries evaluated) :=
  (List.finRange original.plans.length).map (fun i => (entries.get i).secondIncrement)

/-- The complete paired source path on one original parent totals its two retained controlled increment caches. -/
theorem ControlledEntry.source_total {i : Fin original.plans.length} (entry :
  ControlledEntry evaluated i) :
    PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues (evaluated.entries.get i).samples.source (evaluated.entries.get
        i).samples.otherSource)
      (original.depth + depth) 0 1) = ⟨entry.firstIncrement, entry.secondIncrement⟩ := by
  rw [DyadicPairedPrimitivePaths.increments_total, entry.firstIncrement_eq, entry.secondIncrement_eq]
  dsimp only [LocalRequest.increment, -eq_self, -iff_self]
  rw [entry.first_eq, entry.second_eq]
  rfl

/-- The full joined source path has exactly the cached controlled increments used by the two shared-face references, in
their original parent order. -/
theorem sourcePaths_total (entries : ControlledEntries
  evaluated) :
    Purelib.Integration.Path.PairedIncrementArea.total evaluated.sourcePaths.flatten =
      ⟨gaussianSum (firstIncrements evaluated
        entries), Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (secondIncrements evaluated entries)⟩ :=
        by
  have totals : evaluated.sourcePaths.map PairedIncrementArea.total =
      (List.finRange original.plans.length).map (fun i =>
        (⟨(entries.get i).firstIncrement, (entries.get i).secondIncrement⟩ : Stokes.PrimitivePoint)) := by
    dsimp only [Evaluation.sourcePaths, List.finRange, -eq_self, -iff_self]
    rw [OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
    apply OfFn.Basic.ofFn_congr
    intro i
    exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.ControlledEntry.source_total evaluated
      (entries.get i)
  rw [PairedAreaBlocks.total_flatten, totals]
  unfold PairedIncrementArea.total firstIncrements
    secondIncrements
  rw [Data.List.Map.map_map, Data.List.Map.map_map]
  rfl

/-- The acquired joined chart total is exactly the pair of original cached controlled source sums. -/
theorem joinedCharts_total_readback (entries :
  ControlledEntries evaluated) :
    (Evaluation.joinedCharts request evaluated).chart.totalValue =
      ⟨gaussianSum (firstIncrements evaluated entries),
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (secondIncrements evaluated entries)⟩ :=
  (Evaluation.joinedCharts_total request evaluated).trans
    (sourcePaths_total evaluated entries)

/-- The controlled first-differential sum certificate on the exact original parent list and cached increment total. -/
@[expose] def FirstSourceSum (entries :
  ControlledEntries evaluated) :=
  PairedSourceRequests.CertifiedSourceSum parents target minimum (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (firstIncrements evaluated entries))

/-- The controlled second-differential sum certificate on the recast original parent list and cached increment total. -/
@[expose] def SecondSourceSum (entries :
  ControlledEntries evaluated) :=
  PairedSourceRequests.CertifiedSourceSum (parents.map (PreparedEdgeRecasting.recastCenteredEdge other)) target minimum
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (secondIncrements evaluated entries))

/-- Certify the cached first-differential total using the original controlled requests and retained aggregate payment.
-/
@[expose] def firstSourceSum (entries :
  ControlledEntries evaluated) :
  FirstSourceSum evaluated entries :=
  PairedSourceRequests.certifySourceSum (genus := genus) (curve := curve) (differential := differential)
    (fun i => (PairedParentCharts.ChartParent original i).parent) (fun i => (entries.get i).first)
    (fun i => (entries.get i).firstIncrement) (fun i => (entries.get i).firstIncrement_eq.symm)
    (List.finRange original.plans.length)
      indexed_parents original.positive
    (PairedSourceRequests.target_positive original)
    (PairedSourceRequests.local_paid original)
    original.sourceMass original.sourceMass_eq original.source_paid

/-- Certify the cached second-differential total on the recast original parents with the same retained movement mass and
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
    (List.finRange original.plans.length) parentEq original.positive
    (PairedSourceRequests.target_positive original)
    ((congrArg (Aggregate.perTerm target) (Data.List.Map.length_map ..)).symm ▸
      PairedSourceRequests.local_paid original)
    original.sourceMass (original.sourceMass_eq.trans (PreparedRefinementMovement.movementMass_recast other
      parents).symm)
    original.source_paid

set_option genInjectivity false in
/-- The complete retained controlled request bank and both certified original cached source sums. -/
structure Sources where
  /-- The actual original per-parent controlled requests and cached increments. -/ entries :
    ControlledEntries evaluated
  /-- The first-differential certificate consuming the exact retained entry bank. -/ first :
    FirstSourceSum evaluated entries
  /-- The second-differential certificate consuming the same retained entry bank. -/ second :
    SecondSourceSum evaluated entries

constructive_injectivity Sources

/-- Prepare the controlled entries once and retain both complete source sum certificates on those exact caches. -/
@[expose] def sources : Sources evaluated :=
  let entries := controlledEntries evaluated
  ⟨entries, firstSourceSum evaluated entries,
    secondSourceSum evaluated entries⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests
