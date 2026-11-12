module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.CommonReadings
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.RootPathTransport.Numerical
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Tactic.Ring

/-! # Actual stationary root observations and retained primitive endpoint jumps

The original selections derive three new handoff links between unchanged
Owners. Their actual root-expression observations have their own payment.
The independent analytic primitive endpoint jumps are computed separately
from the retained common readings and physical polynomial. Their sum keeps
the original physical residual; root agreement does not identify constants.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues (atPoint)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerSelection)
open Purelib.Riemann.RootContinuation.RootPathTransport.TransportRow (Numerical)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential} {requestTarget : Rational}
variable {cuts : List Rational} {partition : Geometry.Rectangle.AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval} {domains : FaceDomainBank frames faces.regulars}
variable {request : LocalRequest parent count requestTarget}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {retained : PrimitiveFragmentCell.RegularRequest domains request fragment location}
variable {upper : retained.UpperEndpoint} {parentSheet : Fin 2}
variable {lower : CoveredTracedPath retained.compared.acquired.inward.path
  (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)}
variable {forward : CoveredTracedPath upper.acquired.outward.path
  (upper.acquired.faceFrame.owners upper.acquired.entry.sheet)}
variable {lowerParents : ParentCache lower differential parentSheet}
variable {upperParents : ParentCache forward differential parentSheet}

namespace PrimitiveFragmentCell.RegularRequest.UpperEndpoint.CommonReadings

variable {tolerance : Rational} {positive : 0 < tolerance}
variable {prepared : Preparation (lowerParents := lowerParents) (upperParents := upperParents) tolerance positive}
variable {lowerEq : lower = CoveredTracedPath.build retained.compared.acquired.inward.path
  retained.compared.acquired.inward.within
  (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)}
variable {lowerParentsEq : lowerParents = ParentCache.build lower differential parentSheet}
variable {lowerSelection : OwnerSelection retained.compared.acquired.faceFrame.owners lower.traced.finishOwner}
variable {lowerSelectionEq : lowerSelection = retained.compared.acquired.faceFrame.select lower.traced.finishOwner}
variable {forwardEq : forward = CoveredTracedPath.build upper.acquired.outward.path upper.acquired.outward.within
  (upper.acquired.faceFrame.owners upper.acquired.entry.sheet)}
variable {upperParentsEq : upperParents = ParentCache.build forward differential parentSheet}
variable {upperSelection : OwnerSelection upper.acquired.pointFrame.owners forward.traced.finishOwner}
variable {upperSelectionEq : upperSelection = upper.acquired.pointFrame.select forward.traced.finishOwner}

variable {requested : Requests (prepared := prepared) (lowerEq := lowerEq) (lowerParentsEq := lowerParentsEq)
    (lowerSelection := lowerSelection) (lowerSelectionEq := lowerSelectionEq) (forwardEq := forwardEq)
    (upperParentsEq := upperParentsEq) (upperSelection := upperSelection) (upperSelectionEq := upperSelectionEq)}

namespace Requests

/-- Compare the new lower finish to the literal upper source through the derived SAME face-sheet equality. -/
def anchorEquivalent : NamedEquivalent (ownerName (Numerical.covered requested.backward).traced.finishOwner)
    (ownerName (upper.acquired.faceFrame.owners upper.acquired.entry.sheet)) :=
  NamedEquivalent.transport rfl
    (congrArg (fun sheet => ownerName (retained.compared.shared.models.frame.owners sheet)) upper.sheet_eq)
    requested.backward.anchorEquivalent

/-- Three complete newly acquired joins retain both actual Owners and their original signed selection witnesses.

These are new stationary comparisons, not replacements for old connector
joins or the literal circuit closing join. No route, trace, query, Point,
parent cache, numerical request or primitive reading is acquired here.
-/
@[expose] def Handoffs :=
  {value : OwnerJoin retained.sample.owner
      (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index) //
    value = OwnerJoin.acquire retained.sample.owner
      (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)
      retained.compared.acquired.selected.equivalent} ×
  {value : OwnerJoin (Numerical.covered requested.backward).traced.finishOwner
      (upper.acquired.faceFrame.owners upper.acquired.entry.sheet) //
    value = OwnerJoin.acquire (Numerical.covered requested.backward).traced.finishOwner
      (upper.acquired.faceFrame.owners upper.acquired.entry.sheet) (anchorEquivalent (requested := requested))} ×
  {value : OwnerJoin (Numerical.covered requested.outward).traced.finishOwner upper.sample.owner //
    value = OwnerJoin.acquire (Numerical.covered requested.outward).traced.finishOwner upper.sample.owner
      requested.outward.pointEquivalent}

namespace Handoffs

/-- Acquire the source, anchor and target comparisons once from their retained signed selection routes. -/
def build : Handoffs (requested := requested) :=
  let source := OwnerJoin.acquire retained.sample.owner
    (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)
    retained.compared.acquired.selected.equivalent
  let anchor := OwnerJoin.acquire (Numerical.covered requested.backward).traced.finishOwner
    (upper.acquired.faceFrame.owners upper.acquired.entry.sheet) (anchorEquivalent (requested := requested))
  let target := OwnerJoin.acquire (Numerical.covered requested.outward).traced.finishOwner upper.sample.owner
    requested.outward.pointEquivalent
  ⟨⟨source, rfl⟩, ⟨anchor, rfl⟩, ⟨target, rfl⟩⟩

section Retained

variable (handoffs : Handoffs (requested := requested))

/-- Read the complete source join without another root comparison. -/
def source : OwnerJoin retained.sample.owner
    (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index) := handoffs.1.val

/-- Read the complete new-lower-finish to new-upper-source join at the actual face anchor. -/
def anchor : OwnerJoin (Numerical.covered requested.backward).traced.finishOwner
    (upper.acquired.faceFrame.owners upper.acquired.entry.sheet) := handoffs.2.1.val

/-- Read the complete new-upper-finish to original-upper-Point join. -/
def target : OwnerJoin (Numerical.covered requested.outward).traced.finishOwner upper.sample.owner :=
  handoffs.2.2.val

/-- The source join is the whole original acquisition on the literal supplied Point and source-frame Owners. -/
theorem source_eq : handoffs.source = OwnerJoin.acquire retained.sample.owner
    (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index)
    retained.compared.acquired.selected.equivalent := handoffs.1.property

/-- The anchor join is its whole acquisition with the internally derived old/new face-sheet comparison. -/
theorem anchor_eq : handoffs.anchor = OwnerJoin.acquire (Numerical.covered requested.backward).traced.finishOwner
    (upper.acquired.faceFrame.owners upper.acquired.entry.sheet) (anchorEquivalent (requested := requested)) :=
  handoffs.2.1.property

/-- The target join is its whole acquisition using the original retained new-to-old endpoint comparison. -/
theorem target_eq : handoffs.target = OwnerJoin.acquire (Numerical.covered requested.outward).traced.finishOwner
    upper.sample.owner requested.outward.pointEquivalent := handoffs.2.2.property

/-- Form the one-link source path from this SAME already completed source join. -/
@[expose] def sourcePath : OwnerPath curve.polynomial fragment.first retained.sample.owner fragment.first
    (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index) :=
  .cons (OwnerLink.stationary curve.polynomial fragment.first handoffs.source)
    (.nil fragment.first (retained.compared.acquired.pointFrame.owners retained.compared.acquired.selected.index))

/-- Form the one-link anchor path from this exact lower-finish/upper-source comparison cache. -/
@[expose] def anchorPath : OwnerPath curve.polynomial location.face.cell.box.anchor
    (Numerical.covered requested.backward).traced.finishOwner location.face.cell.box.anchor
    (upper.acquired.faceFrame.owners upper.acquired.entry.sheet) :=
  .cons (OwnerLink.stationary curve.polynomial location.face.cell.box.anchor handoffs.anchor)
    (.nil location.face.cell.box.anchor (upper.acquired.faceFrame.owners upper.acquired.entry.sheet))

/-- Form the one-link target path from this SAME new-to-old comparison, without rebuilding its join. -/
@[expose] def targetPath : OwnerPath curve.polynomial fragment.last
    (Numerical.covered requested.outward).traced.finishOwner
    fragment.last upper.sample.owner :=
  .cons (OwnerLink.stationary curve.polynomial fragment.last handoffs.target) (.nil fragment.last upper.sample.owner)

/-- One count-derived root-observation request and three whole original observation executions on these exact links.

Only the formal root generator is observed. The analytic primitive caches
remain separate inputs; this observation cache does not normalize their
constants or supply their domain/canonical attachment.
-/
@[expose] def RootObservations (rootRequest : AccuracyRequest) :=
  Σ accuracy : {value : AccuracyRequest // value = Primitive.localRequest rootRequest 3},
  {value : Primitive.Spine (Expression.generator (radicand := curve.polynomial)) accuracy.val handoffs.sourcePath //
    value = Primitive.Spine.build (expression := Expression.generator) handoffs.sourcePath
      ⟨Expression.defined_generator fragment.first, Expression.defined_generator fragment.first⟩} ×
  {value : Primitive.Spine (Expression.generator (radicand := curve.polynomial)) accuracy.val handoffs.anchorPath //
    value = Primitive.Spine.build (expression := Expression.generator) handoffs.anchorPath
      ⟨Expression.defined_generator location.face.cell.box.anchor,
        Expression.defined_generator location.face.cell.box.anchor⟩} ×
  {value : Primitive.Spine (Expression.generator (radicand := curve.polynomial)) accuracy.val handoffs.targetPath //
    value = Primitive.Spine.build (expression := Expression.generator) handoffs.targetPath
      ⟨Expression.defined_generator fragment.last, Expression.defined_generator fragment.last⟩}

end Retained

namespace RootObservations

variable {handoffs : Handoffs (requested := requested)}

/-- Request the two original root-expression observations and one stationary comparison per retained handoff once. -/
def build (handoffs : Handoffs (requested := requested)) (rootRequest : AccuracyRequest) :
    handoffs.RootObservations rootRequest :=
  let accuracy := Primitive.localRequest rootRequest 3
  let source := Primitive.Spine.build (expression := Expression.generator) (accuracy := accuracy) handoffs.sourcePath
    ⟨Expression.defined_generator fragment.first, Expression.defined_generator fragment.first⟩
  let anchor := Primitive.Spine.build (expression := Expression.generator) (accuracy := accuracy) handoffs.anchorPath
    ⟨Expression.defined_generator location.face.cell.box.anchor,
        Expression.defined_generator location.face.cell.box.anchor⟩
  let target := Primitive.Spine.build (expression := Expression.generator) (accuracy := accuracy) handoffs.targetPath
    ⟨Expression.defined_generator fragment.last, Expression.defined_generator fragment.last⟩
  ⟨⟨accuracy, rfl⟩, ⟨source, rfl⟩, ⟨anchor, rfl⟩, ⟨target, rfl⟩⟩

variable {rootRequest : AccuracyRequest} (roots : handoffs.RootObservations rootRequest)

/-- Read the actual common count-derived request selected before the six new endpoint observations. -/
def accuracy : AccuracyRequest := roots.1.val

/-- Read the entire original source observation execution and its actual signed comparison. -/
def source : Primitive.Spine (Expression.generator (radicand := curve.polynomial)) roots.accuracy
    handoffs.sourcePath := roots.2.1.val

/-- Read the entire original anchor observation execution on the two distinct numerical endpoint Owners. -/
def anchor : Primitive.Spine (Expression.generator (radicand := curve.polynomial)) roots.accuracy
    handoffs.anchorPath := roots.2.2.1.val

/-- Read the entire original target observation execution without replacing the retained upper Point Owner. -/
def target : Primitive.Spine (Expression.generator (radicand := curve.polynomial)) roots.accuracy
    handoffs.targetPath := roots.2.2.2.val

/-- The actual local request is the original aggregate factory on three retained stationary occurrences. -/
theorem accuracy_eq : roots.accuracy = Primitive.localRequest rootRequest 3 := roots.1.property

/-- The complete source observation cache is the original factory on the literal cached source link. -/
theorem source_eq : roots.source = Primitive.Spine.build (expression := Expression.generator) handoffs.sourcePath
    ⟨Expression.defined_generator fragment.first, Expression.defined_generator fragment.first⟩ := roots.2.1.property

/-- The complete anchor observation cache is the original factory on the literal cached anchor link. -/
theorem anchor_eq : roots.anchor = Primitive.Spine.build (expression := Expression.generator) handoffs.anchorPath
    ⟨Expression.defined_generator location.face.cell.box.anchor,
        Expression.defined_generator location.face.cell.box.anchor⟩ :=
  roots.2.2.1.property

/-- The complete target observation cache is the original factory on the literal cached target link. -/
theorem target_eq : roots.target = Primitive.Spine.build (expression := Expression.generator) handoffs.targetPath
    ⟨Expression.defined_generator fragment.last, Expression.defined_generator fragment.last⟩ := roots.2.2.2.property

/-- The source root-expression jump is the actual last-minus-first observation difference, without a zero claim. -/
theorem source_increment : Norm.Sum.Basic.gaussianSum roots.source.jumps =
    roots.source.last.value - roots.source.first.value := roots.source.stationary_increment_eq

/-- The anchor retains the actual two distinct endpoint observations and their signed value difference. -/
theorem anchor_increment : Norm.Sum.Basic.gaussianSum roots.anchor.jumps =
    roots.anchor.last.value - roots.anchor.first.value := roots.anchor.stationary_increment_eq

/-- The target root-expression jump uses the retained numerical finish and original Point observations. -/
theorem target_increment : Norm.Sum.Basic.gaussianSum roots.target.jumps =
    roots.target.last.value - roots.target.first.value := roots.target.stationary_increment_eq

/-- Read every retained root-observation jump in source, anchor, target order, including coincident occurrences. -/
def jumps : List Canonical := roots.source.jumps ++ (roots.anchor.jumps ++ roots.target.jumps)

/-- The original three one-link paths contribute exactly three stationary occurrences. -/
theorem jumps_length : roots.jumps.length = 3 := by
  have source := Primitive.Tail.jumps_length handoffs.sourcePath roots.source.first roots.source.2
  have anchor := Primitive.Tail.jumps_length handoffs.anchorPath roots.anchor.first roots.anchor.2
  have target := Primitive.Tail.jumps_length handoffs.targetPath roots.target.first roots.target.2
  change roots.source.jumps.length = 1 at source
  change roots.anchor.jumps.length = 1 at anchor
  change roots.target.jumps.length = 1 at target
  rewrite [jumps, Append.length_append, Append.length_append, source, anchor, target]
  rfl

/-- Every actual stationary root-expression jump is paid by its own unchanged endpoint observations and link. -/
theorem jumps_bounded : ∀ jump ∈ roots.jumps, normSq jump ≤ roots.accuracy.tolerance := by
  intro jump member
  rcases Membership.mem_append.mp member with member | member
  · exact Primitive.Tail.jumps_bounded handoffs.sourcePath roots.source.first roots.source.2 jump member
  · rcases Membership.mem_append.mp member with member | member
    · exact Primitive.Tail.jumps_bounded handoffs.anchorPath roots.anchor.first roots.anchor.2 jump member
    · exact Primitive.Tail.jumps_bounded handoffs.targetPath roots.target.first roots.target.2 jump member

/-- The internally selected local requests pay the actual total root-expression observation jump.

This bound concerns only the formal root generator and its real endpoint
observations. It supplies no equality or normalization of independent
analytic primitive constants or their mesh offsets.
-/
theorem error_lt : normSq (Norm.Sum.Basic.gaussianSum roots.jumps) < rootRequest.tolerance := by
  have estimate := Norm.Sum.Bounds.normSq_sum_le roots.jumps roots.accuracy.tolerance roots.jumps_bounded
  rewrite [roots.jumps_length] at estimate
  have allocation : roots.accuracy.tolerance = Aggregate.perTerm rootRequest.tolerance 3 :=
    congrArg AccuracyRequest.tolerance roots.accuracy_eq
  have payment := Aggregate.count_mul_allowance_lt (Nat.le_refl 3) rootRequest.positive allocation.le
  rewrite [Aggregate.countCoordinate_eq] at payment
  exact estimate.trans_lt payment

end RootObservations

end Handoffs

end Requests

namespace Readings

section Retained

variable (observed : Readings (requested := requested))

/-- The two actual primitive endpoint jumps and the complete physical-fragment residual bound.

The old polynomial and the common retained mesh readings keep their own
owners and constants. Both oriented jumps are computed once; they are not
identified with the unrelated root-expression observation jumps above.
-/
@[expose] def PrimitiveJumps :=
  {value : Canonical // value = atPoint observed.shared.readings fragment.first -
    request.request.model.primitive.value.eval fragment.first} ×
  {value : Canonical // value = request.request.model.primitive.value.eval fragment.last -
    atPoint observed.shared.readings fragment.last} ×
  {value : Rational // value = Aggregate.countCoordinate retained.compared.split.count *
    (32 * Aggregate.countCoordinate retained.compared.split.count * prepared.budget.grid.globalBound +
      2 * Algebra.FiniteSum.Rational.Squares.coordinateSum (retained.compared.split.pieces.map fun piece =>
        request.facePieceCharge retained.compared.domain prepared.shared.bounds piece prepared.budget.grid.index))}

end Retained

namespace PrimitiveJumps

variable {observed : Readings (requested := requested)}

/-- Compute the two true primitive endpoint mismatches and the original complete physical residual payment once. -/
def build (observed : Readings (requested := requested)) : observed.PrimitiveJumps :=
  let source := atPoint observed.shared.readings fragment.first -
    request.request.model.primitive.value.eval fragment.first
  let target := request.request.model.primitive.value.eval fragment.last -
    atPoint observed.shared.readings fragment.last
  let bound := Aggregate.countCoordinate retained.compared.split.count *
    (32 * Aggregate.countCoordinate retained.compared.split.count * prepared.budget.grid.globalBound +
      2 * Algebra.FiniteSum.Rational.Squares.coordinateSum (retained.compared.split.pieces.map fun piece =>
        request.facePieceCharge retained.compared.domain prepared.shared.bounds piece prepared.budget.grid.index))
  ⟨⟨source, rfl⟩, ⟨target, rfl⟩, ⟨bound, rfl⟩⟩

variable (jumps : observed.PrimitiveJumps)

/-- Read the actual old-to-common primitive jump at the retained lower Point. -/
def source : Canonical := jumps.1.val

/-- Read the actual common-to-old primitive jump at the retained upper Point. -/
def target : Canonical := jumps.2.1.val

/-- Read the original count-weighted physical ownership and analytic-residual payment. -/
def bound : Rational := jumps.2.2.val

/-- The source scalar is the true difference of the same retained primitive readings. -/
theorem source_eq : jumps.source = atPoint observed.shared.readings fragment.first -
    request.request.model.primitive.value.eval fragment.first := jumps.1.property

/-- The target scalar preserves the reverse orientation from common readings back to the old primitive. -/
theorem target_eq : jumps.target = request.request.model.primitive.value.eval fragment.last -
    atPoint observed.shared.readings fragment.last := jumps.2.1.property

/-- The cached bound retains every original physical split charge and its full actual count. -/
theorem bound_eq : jumps.bound = Aggregate.countCoordinate retained.compared.split.count *
    (32 * Aggregate.countCoordinate retained.compared.split.count * prepared.budget.grid.globalBound +
      2 * Algebra.FiniteSum.Rational.Squares.coordinateSum (retained.compared.split.pieces.map fun piece =>
        request.facePieceCharge retained.compared.domain prepared.shared.bounds piece prepared.budget.grid.index)) :=
  jumps.2.2.property

/-- The physical primitive increment equals the shared increment plus its actual two endpoint mismatches. -/
theorem physical_increment : request.request.model.primitive.value.eval fragment.last -
    request.request.model.primitive.value.eval fragment.first = jumps.source +
      (atPoint observed.shared.readings fragment.last -
        atPoint observed.shared.readings fragment.first) + jumps.target := by
  rewrite [jumps.source_eq, jumps.target_eq]
  ring1

/-- The original physical residual pays the true combined primitive endpoint jump.

Neither endpoint mismatch is bounded separately or identified with zero. -/
theorem error_le : normSq (jumps.source + jumps.target) ≤ jumps.bound := by
  have signed : jumps.source + jumps.target =
      -((atPoint observed.shared.readings fragment.last -
        atPoint observed.shared.readings fragment.first) -
        (request.request.model.primitive.value.eval fragment.last -
          request.request.model.primitive.value.eval fragment.first)) := by
    rewrite [jumps.source_eq, jumps.target_eq]
    ring1
  rewrite [signed, Norm.Basic.normSq_neg, jumps.bound_eq]
  exact observed.physical_accurate

/-- Both new actual numerical integrals compare to the old physical primitive with its explicit nonzero residual.

The common increment joins these two quantities. The original physical
count-weighted charge and new numerical tolerance are both retained. No
stationary root-expression bound is substituted for a primitive payment.
-/
theorem replacement_le : normSq ((request.request.model.primitive.value.eval fragment.last -
    request.request.model.primitive.value.eval fragment.first) -
      (requested.lowerRequest.integralSample + requested.upperRequest.integralSample)) ≤
    2 * (jumps.bound + tolerance) := by
  have signed : (request.request.model.primitive.value.eval fragment.last -
      request.request.model.primitive.value.eval fragment.first) -
        (requested.lowerRequest.integralSample + requested.upperRequest.integralSample) =
      (jumps.source + jumps.target) +
        ((atPoint observed.shared.readings fragment.last -
          atPoint observed.shared.readings fragment.first) -
          (requested.lowerRequest.integralSample + requested.upperRequest.integralSample)) := by
    rewrite [jumps.source_eq, jumps.target_eq]
    ring1
  rewrite [signed]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct jumps.error_le observed.replacement_accurate.le) (by decide))

end PrimitiveJumps

end Readings

end PrimitiveFragmentCell.RegularRequest.UpperEndpoint.CommonReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
