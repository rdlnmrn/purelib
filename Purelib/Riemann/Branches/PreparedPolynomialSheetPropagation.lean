module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Mathlib.Order.Basic
public import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

@[expose] public section

/-!
# Polynomial sheets along actual covered prepared chains

An inverse polynomial is aligned with an operational root if it agrees with
every sufficiently accurate local model of that occurrence. The finite
three-model cocycle propagates this property through each covered prepared
edge, using the edge's actual root queries. No new root is selected and no
sign-agreement hypothesis is needed at later vertices.
-/

section

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.InverseModelRootSamples (RootSamples)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Refine the original inverse-root model by the supplied index plus two, retaining the overlap-ready residual
threshold. -/
def overlapRefine {polynomial : Polynomial} {box : Box} (model : Model polynomial box) (index : Nat) :
    OverlapReady polynomial box :=
  ⟨model.refine (index + 2), by
    rw [Model.refine_bound]
    apply (quarterRadius_antitone model.bound_nonnegative (Nat.le_add_left 2 index)).trans
    rw [Geometric.Basic.quarterRadius_eq_mul_pow]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct model.bound_small
      (by decide +kernel : (0 : Coordinate) ≤ (1 / 4) ^ 2)).trans
      (by decide +kernel : (1 / 16 : Coordinate) * (1 / 4) ^ 2 ≤ 1 / 256)⟩

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

section
open Purelib.Data.Gaussian

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

/-- Retain the original two model evaluations as an unflipped overlap sample using the supplied nearestness inequality.
-/
private def unflippedSample {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) (point : Gaussian)
    (nearest : normSq (left.value.eval point - right.value.eval point) ≤
      normSq
      (left.value.eval point + right.value.eval point)) :
    OverlapSample left right point :=
  ⟨left.value.eval point, rfl, right.value.eval point, rfl, ⟨false, right.value.eval point, rfl, by
    simpa only [Norm.Basic.normSq_eq_canonical] using nearest⟩⟩

/-- An unflipped overlap sample retains nearestness of the original evaluations.

The cached sign-adjusted value selects the unchanged right evaluation. Its
original value equations transport the retained quadrance comparison directly. -/
private theorem nearest_of_unflipped {polynomial : Polynomial} {leftBox rightBox : Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Gaussian}
    (sample : OverlapSample left right point) (unflipped : sample.alignment.flip = false) :
    normSq (left.value.eval point - right.value.eval point) ≤ normSq
      (left.value.eval point + right.value.eval point) := by
  have nearest := sample.alignment.nearest
  rw [sample.alignment.value_eq, unflipped] at nearest
  rw [if_neg (show ¬(false = true) from fun impossible => by cases impossible)] at nearest
  simpa only [Norm.Basic.normSq_eq_canonical, sample.leftValue_eq, sample.rightValue_eq] using nearest

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

end

section
open Purelib.Data.Gaussian

namespace Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial.OverlapReady

/-- Compose nearestness of three overlap-ready original model evaluations at the same retained point.

All three original boxes contain the point. The retained overlap cocycle identifies the direct flip with the two
supplied unflipped comparisons. -/
theorem nearest_trans
  {polynomial : Polynomial} {firstBox middleBox lastBox : Box}
    (first : OverlapReady polynomial firstBox) (middle : OverlapReady polynomial middleBox)
    (last : OverlapReady polynomial lastBox) {point : Gaussian}
    (firstInside : firstBox.Contains point) (middleInside : middleBox.Contains point) (lastInside : lastBox.Contains
      point)
    (firstMiddle : normSq (first.model.value.eval point - middle.model.value.eval point) ≤
      normSq (first.model.value.eval point + middle.model.value.eval point))
    (middleLast : normSq (middle.model.value.eval point - last.model.value.eval point) ≤
      normSq (middle.model.value.eval point + last.model.value.eval point)) :
    normSq (first.model.value.eval point - last.model.value.eval point) ≤
      normSq (first.model.value.eval point + last.model.value.eval point) := by
  let direct := OverlapSample.build first.model last.model point
  have cocycle := OverlapReady.cocycle first middle last firstInside middleInside lastInside
    (Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.unflippedSample first.model middle.model point
      firstMiddle)
    (Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.unflippedSample middle.model last.model point
      middleLast) direct
  exact Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.nearest_of_unflipped direct cocycle

end Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial.OverlapReady

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

/-- Nearestness of two original inverse-root models at a common segment start persists to its retained finish.

Both endpoints belong to both original model boxes; the retained edge transition preserves the unflipped start sample
throughout the exact segment. -/
theorem nearest_finish {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) {start finish : Gaussian}
    (leftStart : leftBox.Contains start) (leftFinish : leftBox.Contains finish)
    (rightStart : rightBox.Contains start) (rightFinish : rightBox.Contains finish)
    (nearest : normSq (left.value.eval start - right.value.eval start) ≤
      normSq
      (left.value.eval start + right.value.eval start)) :
    normSq (left.value.eval finish - right.value.eval finish) ≤ normSq
      (left.value.eval finish + right.value.eval finish) := by
  let edge : EdgeTransition left right start finish :=
    ⟨leftStart, leftFinish, rightStart, rightFinish,
      unflippedSample left right start nearest⟩
  exact nearest_of_unflipped (OverlapSample.build left right
    finish) edge.flip_eq_finish.symm

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model

end

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
/-- An overlap-ready model agrees in sign with every retained continued root reading equivalent to the specified
original root name.

The predicate retains the point, model and original name. Each comparison uses the supplied continued neighborhood and
point owner with its exact indexed refinement plus two. -/
def RootAligned {polynomial : Polynomial} {box : Box} (model : OverlapReady polynomial box)
    (point : Gaussian) (root : Name.Basic.Named) : Prop :=
  ∀ {count : Nat} (patch : ContinuedNeighborhood polynomial count) (_inside : patch.box.Contains point)
    (sample : ContinuedNeighborhood.Point patch point)
    (_roots : NamedEquivalent root sample.certificate.value.name) (index : Nat),
    normSq (model.model.value.eval point - (patch.base.refine (index + 2)).value.eval point) ≤
      normSq (model.model.value.eval point + (patch.base.refine (index + 2)).value.eval point)

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

section

variable {polynomial : Polynomial} {box : Box} {model : OverlapReady polynomial box}
  {point : Gaussian} {first last : Purelib.Approximation.Gaussian.Name.Basic.Named}

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.RootAligned

open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Bounds
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment ownerAtStart zeroEndpoint)
open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.Approximation.Gaussian in
/-- Transport retained model alignment along an operational equivalence of the original root names. -/
theorem changeName (aligned : RootAligned model point first) (equivalent :
  NamedEquivalent first last) :
    RootAligned model point last :=
  fun patch inside sample roots index => aligned patch inside sample (equivalent.trans roots) index

/-- The actual retained model samples align every continued representative of their same operational root.

The supplied comparison relates only the original numerical sample channel
to the displayed root name. Each arbitrary continued representative is
then compared through its original root-equivalence certificate. The
result is the existing model alignment predicate, not an assumed later
sheet relation or a newly acquired model.
-/
theorem ofSamples {source : Model polynomial box} (data : RootSamples source point)
    (small : source.bound ≤ 1 / 256) (inside : box.Contains point)
    (root : Approximation.Gaussian.Name.Basic.Named)
    (same : Approximation.Gaussian.Equivalence.Equivalent (data.approximation small inside)
      (Approximation.Gaussian.Name.Sampling.approximation root)) (index : Nat) :
    RootAligned (Model.overlapRefine source index) point root := by
  intro count patch patchInside sample roots refinement
  have comparison : Approximation.Gaussian.Equivalence.Equivalent
      (data.approximation small inside)
      (Approximation.Gaussian.Name.Sampling.approximation sample.certificate.value.name) :=
    same.trans roots
  have nearest := ContinuedNeighborhood.Point.samples_nearest
    (polynomial := polynomial) (right := patch) (point := point)
    data small inside sample patchInside comparison index (refinement + 2)
  change normSq ((source.refine (index + 2)).value.eval point -
      (patch.base.refine (refinement + 2)).value.eval point) ≤
    normSq ((source.refine (index + 2)).value.eval point +
      (patch.base.refine (refinement + 2)).value.eval point)
  simpa only [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical] using nearest

/-- Alignment of the original model persists between two actual point owners of one continued neighborhood.

Both endpoints lie in the retained model box and the supplied continued
patch. The original two-model edge sign and three-model cocycle transfer
the same aligned sheet to every continued representative at the finish.
The two original point owners and all refinement indices remain inputs.
-/
theorem throughNeighborhood {count : Nat} {patch : ContinuedNeighborhood polynomial count}
    {start finish : Gaussian} (firstSample : ContinuedNeighborhood.Point patch start)
    (lastSample : ContinuedNeighborhood.Point patch finish)
    (firstInside : box.Contains start) (lastInside : box.Contains finish)
    (patchStart : patch.box.Contains start) (patchFinish : patch.box.Contains finish)
    (aligned : RootAligned model start firstSample.certificate.value.name) :
    RootAligned model finish lastSample.certificate.value.name := by
  intro otherCount other otherInside sample roots index
  have initial := aligned patch patchStart firstSample (NamedEquivalent.refl _) 0
  have transported := (Model.nearest_finish model.model)
    (patch.base.refine 2) firstInside lastInside
    (patch.box_refines.contains patchStart) (patch.box_refines.contains patchFinish) initial
  have next := lastSample.equivalent_nearest sample patchFinish otherInside roots 2 (index + 2)
  apply model.nearest_trans (Model.overlapRefine patch.base.model 0)
    (Model.overlapRefine other.base.model index)
    lastInside (patch.box_refines.contains patchFinish) (other.box_refines.contains otherInside) transported
  simpa only [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    Purelib.Riemann.Normalization.OwnerSeededInverseRoot.SeededNeighborhood.refine,
    Model.overlapRefine] using next

/-- A real primitive-mesh step propagates the same model alignment to its actual retained advanced owner.

The original request, prepared-owner cache, ordered endpoint and strict
variation budget determine the unchanged advancement. Uniform mesh
membership supplies a common continued patch; its existing common-source
comparison identifies both original readings. Reserve retention may
recondition the terminal owner and is handled by its actual equivalence.
-/
theorem preparedStep {ambient : Box} {start finish : Gaussian}
    (segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (bounds : Bounds segment) (mesh : Mesh bounds)
    (left : PreparedSheetContinuation.Endpoint)
    (owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : PreparedSheetContinuation.StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left owner request)
    (ordered : left.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment left owner request).track.initial.clearance.bound)
    (member : ({ left := left, right := request.endpoint } :
      ClearSheetContinuation.Subdivision.ParameterEdge) ∈ mesh.edges)
    (firstInside : box.Contains (segment.pointAt left.parameter))
    (lastInside : box.Contains (segment.pointAt request.endpoint.parameter))
    (aligned : RootAligned model (segment.pointAt left.parameter) (ownerRootName owner.parameterNonzero owner)) :
    RootAligned model (segment.pointAt request.endpoint.parameter)
      (ownerRootName (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside)
        (PreparedSheetContinuation.advance segment within left owner request small)) := by
  let source := cached.preparedOwner
  have cachedSmall : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      source.track.initial.clearance.bound := by
    change ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound
    rewrite [cached.preparedOwner_eq]
    exact small
  let seed := Bounds.PreparedSeed.acquire bounds left.parameter left.inside source
  let patch := seed.neighborhood 0
  have patchStart : patch.box.Contains (segment.pointAt left.parameter) :=
    seed.neighborhood_center 0 ▸ patch.center_inside
  have patchFinish : patch.box.Contains (segment.pointAt request.endpoint.parameter) :=
    mesh.point_inside member seed 0 ⟨ordered, le_rfl⟩
  let firstSample := ContinuedNeighborhood.Point.acquire patch (segment.pointAt left.parameter) patchStart
  let lastSample := ContinuedNeighborhood.Point.acquire patch (segment.pointAt request.endpoint.parameter) patchFinish
  have sourceSame : NamedEquivalent (ownerRootName owner.parameterNonzero owner)
      (ownerRootName source.parameterNonzero source) := by
    have actual := PreparedSheetContinuation.sourceRootEquivalent segment left owner request
    rewrite [← cached.preparedOwner_eq] at actual
    exact actual
  have firstSame : NamedEquivalent (ownerRootName source.parameterNonzero source)
      firstSample.certificate.value.name :=
    PreparedSeed.pointEquivalent seed 0 patchStart source (Purelib.Geometry.Rational.Box.refines_refl _) (by
      simpa only [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical,
        Purelib.Data.Gaussian.Basic.sub_self, Purelib.Data.Gaussian.Basic.Canonical.normSq_zero]
        using source.track.initial.clearance.positive) firstSample
  have firstAligned : RootAligned model (segment.pointAt left.parameter) firstSample.certificate.value.name :=
    aligned.changeName (sourceSame.trans firstSame)
  have lastAligned : RootAligned model (segment.pointAt request.endpoint.parameter)
      lastSample.certificate.value.name :=
    firstAligned.throughNeighborhood firstSample lastSample firstInside lastInside patchStart patchFinish
  have displacement : Purelib.Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) < source.track.initial.clearance.bound :=
    (ClearSheetContinuation.evaluation_variation_le segment within left.parameter request.endpoint.parameter
      left.inside request.endpoint.inside).trans_lt cachedSmall
  let moved := ExactQuadraticOwnerClearance.reservedTransport source
    (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside) displacement
    (PreparedSheetContinuation.transportReserve segment left request)
  have movedSame : NamedEquivalent (ownerRootName moved.parameterNonzero moved)
      lastSample.certificate.value.name :=
    PreparedSeed.pointEquivalent seed 0 patchFinish moved
      (ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines source _ displacement _)
      (by simpa only [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical] using displacement) lastSample
  have retainedSame : NamedEquivalent (ownerRootName moved.parameterNonzero moved)
      (ownerRootName (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside)
        (PreparedSheetContinuation.advance segment within left owner request small)) := by
    have keep : NamedEquivalent (ownerRootName moved.parameterNonzero moved)
        (ownerRootName (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside)
          (PreparedSheetContinuation.advanceCached segment within left owner request cached cachedSmall)) :=
      PreparedSheetContinuation.retainedAtReserveRootEquivalent moved
        (PreparedSheetContinuation.preparedClearanceLower segment left request)
    have same := PreparedSheetContinuation.advanceCached_eq_advance segment within left owner request cached
      cachedSmall small
    exact Approximation.Gaussian.Equivalence.NamedEquivalent.transport rfl
      (congrArg (fun actual => ownerRootName actual.parameterNonzero actual) same) keep
  apply RootAligned.changeName lastAligned
  exact movedSame.symm.trans retainedSame

/-- Alignment follows every original request in a primitive-covered subdivision and its exact terminal owner.

The actual parameter-edge list belongs to the supplied primitive mesh.
The same ambient box refines the model box, so every queried endpoint
lies inside that model. Structural induction consumes the retained
request, cache and advanced owner at each head, followed by its literal
tail; no subdivision or endpoint owner is reacquired.
-/
theorem alongSubdivision {ambient : Box} {start finish : Gaussian}
    (segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (enclosure : ambient.Refines box)
    (bounds : Bounds segment) (mesh : Mesh bounds)
    {left : PreparedSheetContinuation.Endpoint}
    {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : PreparedSheetContinuation.Subdivision segment within left owner)
    (covered : ∀ edge, edge ∈ subdivision.parameterEdges → edge ∈ mesh.edges)
    (aligned : RootAligned model (segment.pointAt left.parameter) (ownerRootName owner.parameterNonzero owner)) :
    RootAligned model (segment.pointAt subdivision.endpoint.parameter)
      (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner) := by
  revert covered aligned
  induction subdivision with
  | stop left owner =>
      intro _ aligned
      exact aligned
  | next left owner request cached ordered small remaining inductionHypothesis =>
      intro covered aligned
      have head : ({ left := left, right := request.endpoint } :
          ClearSheetContinuation.Subdivision.ParameterEdge) ∈ mesh.edges :=
        covered _ (by
          rewrite [PreparedSheetContinuation.Subdivision.parameterEdges_next]
          exact List.Mem.head _)
      have tail : ∀ edge, edge ∈ remaining.parameterEdges → edge ∈ mesh.edges := by
        intro edge member
        apply covered edge
        rewrite [PreparedSheetContinuation.Subdivision.parameterEdges_next]
        exact List.Mem.tail _ member
      have nextAligned : RootAligned model (segment.pointAt request.endpoint.parameter)
          (ownerRootName (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside)
            (PreparedSheetContinuation.advance segment within left owner request small)) :=
        aligned.preparedStep segment within bounds mesh left owner request cached ordered small head
          (enclosure.contains (segment.pointAt_contains within left.parameter left.inside))
          (enclosure.contains (segment.pointAt_contains within request.endpoint.parameter request.endpoint.inside))
      apply inductionHypothesis tail
      exact nextAligned

/-- An original complete prepared segment preserves model alignment at its exact displayed finish owner.

The complete segment retains the actual subdivision from its transported
source owner. The supplied primitive mesh is identified with that same
parameter-edge list. Original point and owner-name transport laws recover
the displayed endpoint indices without rebuilding either owner.
-/
theorem completeSegment {ambient : Box} {start finish : Gaussian}
    (segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (enclosure : ambient.Refines box)
    {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) (bounds : Bounds segment) (mesh : Mesh bounds)
    (meshEq : prepared.subdivision.parameterEdges = mesh.edges)
    (aligned : RootAligned model start (ownerRootName owner.parameterNonzero owner)) :
    RootAligned model finish (ownerRootName prepared.finishOwner.parameterNonzero prepared.finishOwner) := by
  have sourceName : ownerRootName (ownerAtStart segment owner).parameterNonzero (ownerAtStart segment owner) =
      ownerRootName owner.parameterNonzero owner := by
    unfold ownerAtStart
    exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ owner
  have initial : RootAligned model (segment.pointAt zeroEndpoint.parameter)
      (ownerRootName (ownerAtStart segment owner).parameterNonzero (ownerAtStart segment owner)) := by
    rewrite [sourceName, prepared.start_eq]
    exact aligned
  have terminal : RootAligned model (segment.pointAt prepared.subdivision.endpoint.parameter)
      (ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner) := by
    apply RootAligned.alongSubdivision segment within enclosure bounds mesh prepared.subdivision
    · intro edge member
      rewrite [meshEq] at member
      exact member
    · exact initial
  have finishName : ownerRootName prepared.finishOwner.parameterNonzero prepared.finishOwner =
      ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner := by
    unfold CompleteSegment.finishOwner CompleteSegment.terminalOwner
    exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _
  have pointType : RootAligned model (segment.pointAt prepared.subdivision.endpoint.parameter)
      (ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner) =
      RootAligned model finish
        (ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner) :=
    congrArg (fun coordinate : Gaussian => RootAligned model coordinate
      (ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner))
      prepared.finish_eq
  have finalAligned : RootAligned model finish
      (ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner) := by
    apply Eq.mp pointType
    exact terminal
  rewrite [finishName]
  exact @finalAligned

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.RootAligned

end

end

section

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named LiftedPoint)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {box : Box} {model : OverlapReady curve.polynomial box}

namespace Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Normalization in
/-- Propagate an original model's root alignment across a covered prepared edge.

Both original edge endpoints lie in the model box, and the retained prepared patch covers the finish. Edge sign
constancy and equivalent point-root readings preserve alignment with the exact finish query. -/
theorem advance {parent : CenteredEdge curve differential} {count : Nat}
    (patch : PreparedPatch parent) (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (firstInside : box.Contains (parent.edge.point 0)) (lastInside : box.Contains (parent.edge.point 1))
    (aligned : RootAligned model (parent.edge.point 0) (parent.edge.rootName 0 parent.edge.baseInside)) :
    RootAligned model (parent.edge.point 1) (parent.edge.rootName 1 (by decide)) := by
  let middle := patch.neighborhood count
  let first := ContinuedNeighborhood.Point.acquire middle (parent.edge.point 0) (patch.start_inside count)
  let last := ContinuedNeighborhood.Point.acquire middle (parent.edge.point 1) covered
  have initial : RootAligned model (parent.edge.point 0) first.certificate.value.name :=
    aligned.changeName (patch.point_equivalent count 0 parent.edge.baseInside (patch.start_inside count) first)
  have advanced : RootAligned model (parent.edge.point 1) last.certificate.value.name :=
    initial.throughNeighborhood first last firstInside lastInside (patch.start_inside count) covered
  apply RootAligned.changeName advanced
  exact (patch.point_equivalent count 1 (by decide) covered last).symm

/-- Every original prepared edge in the ordered list has both endpoints in the specified retained box. -/
def EndpointsIn (box : Box) : List (CenteredEdge curve differential) → Prop
  | [] => True
  | parent :: rest => box.Contains (parent.edge.point 0) ∧ box.Contains (parent.edge.point 1) ∧ EndpointsIn box rest

open Purelib.Curves.Hyperelliptic.Integration in
/-- Propagate original model alignment along a retained geometric and root-name chain of covered prepared edges.

Each original edge has both endpoints in the model box. The exact covered-parent certificates and incoming root
equivalences transport alignment to the final retained endpoint and name. -/
theorem alongChain : ∀ {parents : List (CenteredEdge curve differential)} {start finish : LiftedPoint}
    {first last : Named} {count : Nat},
    DirectPathChain parents (start := start) (finish := finish) → RootChain parents first last →
    CoveredParents count parents → EndpointsIn box parents →
    RootAligned model start.coordinate first → RootAligned model finish.coordinate last
  | [], _, _, _, _, _, .nil _, .nil equivalent, .nil, _, aligned => aligned.changeName equivalent
  | _ :: _, _, _, _, _, _, .cons parent chain, .cons _ entry roots, .cons patch covered remaining, inside, aligned => by
      have initial : RootAligned model (parent.edge.point 0) (parent.edge.rootName 0 parent.edge.baseInside) := by
        rw [parent.edge.point_zero]
        exact aligned.changeName entry
      have advanced : RootAligned model (parent.edge.point 1) (parent.edge.rootName 1 (by decide)) :=
        advance patch covered inside.1 inside.2.1 initial
      rw [parent.edge.point_one] at advanced
      exact alongChain chain roots remaining inside.2.2 advanced

end Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation

end
