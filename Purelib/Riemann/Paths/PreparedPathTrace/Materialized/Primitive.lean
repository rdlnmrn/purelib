module

public import Purelib.Riemann.Paths.PreparedPathTrace.Materialized
public import Purelib.Riemann.Paths.OwnerTracePath.Split.Primitive
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Same old primitive observations on retained materialized segment traces

The original complete segment supplies exact endpoints and whole Owner
identities. The given raw Trace is heterogeneously the same materialized
path. These independent original certificates transport the old Spine;
no trace, canonical ownerPath, observation or root preparation executes.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath CompleteSegment ownerAtStart zeroEndpoint oneEndpoint)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget (Trace)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter_heq)
open Purelib.Polynomial.Geometry (ClearPath)

namespace CompleteSegment

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Owner (polynomial.eval start)} {expression : Expression polynomial} {accuracy : AccuracyRequest}
    (prepared : CompleteSegment segment within owner)
    {budget : PreparedTraceBudget segment zeroEndpoint oneEndpoint}
    {fits : budget.RequestsFit zeroEndpoint prepared.subdivision.requests}
    (materialized : OwnerPath polynomial start owner finish prepared.finishOwner)
    (trace : Trace budget prepared.subdivision fits) (kept : HEq trace.path materialized)
    (observed : Primitive.Spine expression accuracy materialized)

/-- Transport the complete GIVEN old Spine to the SAME raw retained Trace using the original endpoint/Owner laws.

Whole-path HEq is used only after the original endpoints and Owners have
been separately reindexed. It does not manufacture a root identity from
geometry. Every old Vertex, request, tail and stationary comparison is
preserved through these erased exact transports.
-/
def observations : Primitive.Spine expression accuracy trace.path := by
  have firstOwner : HEq (ownerAtStart segment owner) owner := by
    unfold ownerAtStart
    exact castOwnerParameter_heq _ _
  let raw := materialized.castEndpoints prepared.start_eq.symm prepared.finish_eq.symm firstOwner.symm
    prepared.finishOwner_heq_terminalOwner
  let sampled := Primitive.Spine.castEndpoints prepared.start_eq.symm prepared.finish_eq.symm firstOwner.symm
    prepared.finishOwner_heq_terminalOwner observed
  have actual : raw = trace.path := eq_of_heq
    ((OwnerPath.castEndpoints_heq _ _ _ _ materialized).trans kept.symm)
  exact Primitive.Spine.castPath actual sampled

/-- The SAME entire old observation execution survives the raw segment transport heterogeneously. -/
theorem observations_heq : HEq (observations prepared materialized trace kept observed) observed := by
  unfold observations
  exact (Primitive.Spine.castPath_heq _ _).trans
    (Primitive.Spine.castEndpoints_heq _ _ _ _ observed)

/-- Raw trace transport preserves the exact old first observation value. -/
theorem observations_first_value : (observations prepared materialized trace kept observed).first.value =
    observed.first.value := by
  unfold observations
  exact (Primitive.Spine.castPath_first_value _ _).trans
    (Primitive.Spine.castEndpoints_first_value _ _ _ _ observed)

/-- Raw trace transport preserves the distinct old final observation value. -/
theorem observations_last_value : (observations prepared materialized trace kept observed).last.value =
    observed.last.value := by
  unfold observations
  exact (Primitive.Spine.castPath_last_value _ _).trans
    (Primitive.Spine.castEndpoints_last_value _ _ _ _ observed)

end CompleteSegment

namespace PreparedPath.TraceLineage

variable {polynomial : GaussianPolynomial} {ambient : Box} {start middle finish : Canonical}
    {head : ClearSegment polynomial ambient start middle} {tail : ClearPath polynomial ambient middle finish}
    {owner : Owner (polynomial.eval start)} {within : head.WithinAmbient}
    {expression : Expression polynomial} {accuracy : AccuracyRequest}
    (first : CompleteSegment head within owner) (budget : PreparedTraceBudget head zeroEndpoint oneEndpoint)
    (fits : budget.RequestsFit zeroEndpoint first.subdivision.requests)
    {middleOwner : Owner (polynomial.eval middle)} {rest : PreparedPath tail middleOwner}
    (finishOwnerEq : middleOwner = first.finishOwner) (remaining : PreparedPath.TraceLineage rest)
    (materialized : OwnerPath polynomial start owner finish
      (PreparedPathGluing.finishOwner
        (PreparedPath.cons head tail owner within first (PreparedPath.castOwner finishOwnerEq rest))))
    (observed : Primitive.Spine expression accuracy materialized)

/-- The actual segment split together with its SAME two old observation pieces and original raw Trace.

Every original head factory is retained. The complete original primitive
split is computed from the given materialized path and Spine, preserving
its literal shared Vertex. Exact transports keep both old observation
pieces at the raw segment and original remaining-lineage indices.
-/
@[expose] def ObservedHeadConsumer (Result : Type u) :=
  let displayed := materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)
  let displayedObservation := Primitive.Spine.castEndpoints rfl rfl (heq_of_eq rfl)
    (heq_of_eq (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) observed
  (divided : OwnerPath.Split displayed) →
  divided = OwnerPath.splitAt (3 * first.subdivision.stepCount) displayed →
  (same : divided.suffix =
    (⟨middle, first.finishOwner, remaining.ownerPath.reindexOwners finishOwnerEq rfl⟩ :
      OwnerPath.Suffix (PreparedPathGluing.finishOwner rest))) →
  (front : Trace budget first.subdivision fits) →
  HEq front.path divided.initial →
  (following : OwnerPath polynomial middle middleOwner finish (PreparedPathGluing.finishOwner rest)) →
  HEq following divided.suffix.path → following = remaining.ownerPath →
  (views : Primitive.Spine.Split (expression := expression) (accuracy := accuracy)
    divided.initial divided.suffix.path) →
  views = OwnerPath.Split.observations divided displayedObservation →
  (headObserved : Primitive.Spine expression accuracy front.path) →
  HEq headObserved views.before →
  (tailObserved : Primitive.Spine expression accuracy following) →
  HEq tailObserved views.after →
  headObserved.first.value = observed.first.value →
  tailObserved.last.value = observed.last.value →
  tailObserved.first.value = headObserved.last.value → Result

set_option genInjectivity false in
/-- The whole old observation cache at its displayed endpoint index, with its original cast factory.

The original Spine remains the sole data field. Its nominal cache boundary
retains the exact owner-index transport without expanding the recursive
observation tail in the type of the shared head operation.
-/
private structure DisplayedSpine where
  /-- The same whole old observations at their displayed endpoint owners. -/
  val : Primitive.Spine expression accuracy
    (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest))
  /-- The complete original endpoint-index transport of the given old observations. -/
  property : val = Primitive.Spine.castEndpoints rfl rfl (heq_of_eq rfl)
    (heq_of_eq (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) observed

/-- Split the old observations on a given retained materialized head, using the same displayed observation cache.

The exact whole observation factory pays the original callback indices.
Only the old Spine is split and transported; the supplied path split,
raw Trace, actual following path and all their certificates are forwarded
unchanged. No materialized-path split or trace producer is executed.
-/
private def observationsAtHead
    (retained : DisplayedSpine (first := first) (rest := rest) (finishOwnerEq := finishOwnerEq)
      (materialized := materialized) (observed := observed))
    {Result : Type u}
    (consume : ObservedHeadConsumer first budget fits finishOwnerEq remaining materialized observed Result) :
    HeadConsumer first budget fits finishOwnerEq remaining
      (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) Result :=
  fun divided dividedFactory same front frontKept following followingKept followingFactory =>
      let displayedObservation := retained.val
      let views := OwnerPath.Split.observations divided displayedObservation
      let prefixPath := OwnerPath.Split.prefixCast divided same
      let prefixObserved := OwnerPath.Split.prefixObservations divided same views.before
      have rawKept : HEq front.path prefixPath :=
        frontKept.trans (OwnerPath.Split.prefixCast_heq divided same).symm
      let headObserved := CompleteSegment.observations first prefixPath front rawKept prefixObserved
      have headKept : HEq headObserved views.before :=
        (CompleteSegment.observations_heq first prefixPath front rawKept prefixObserved).trans
          (OwnerPath.Split.prefixObservations_heq divided same views.before)
      let oldFollowing := OwnerPath.Suffix.observationsCast same views.after
      let reindexed := Primitive.Spine.castEndpoints rfl rfl
        (heq_of_eq finishOwnerEq.symm) (heq_of_eq rfl) oldFollowing
      have reindexedPath : (OwnerPath.Suffix.pathCast same).reindexOwners finishOwnerEq.symm rfl = following :=
        eq_of_heq ((OwnerPath.castEndpoints_heq rfl rfl (heq_of_eq finishOwnerEq.symm) (heq_of_eq rfl)
          (OwnerPath.Suffix.pathCast same)).trans
            ((OwnerPath.Suffix.pathCast_heq same).trans followingKept.symm))
      let tailObserved := Primitive.Spine.castPath reindexedPath reindexed
      have tailKept : HEq tailObserved views.after :=
        (Primitive.Spine.castPath_heq reindexedPath reindexed).trans
          ((Primitive.Spine.castEndpoints_heq rfl rfl (heq_of_eq finishOwnerEq.symm)
            (heq_of_eq rfl) oldFollowing).trans (OwnerPath.Suffix.observationsCast_heq same views.after))
      have headFirst : headObserved.first.value = views.before.first.value :=
        (CompleteSegment.observations_first_value first prefixPath front rawKept prefixObserved).trans
          (OwnerPath.Split.prefixObservations_first_value divided same views.before)
      have headLast : headObserved.last.value = views.before.last.value :=
        (CompleteSegment.observations_last_value first prefixPath front rawKept prefixObserved).trans
          (OwnerPath.Split.prefixObservations_last_value divided same views.before)
      have tailFirst : tailObserved.first.value = views.after.first.value :=
        (Primitive.Spine.castPath_first_value reindexedPath reindexed).trans
          ((Primitive.Spine.castEndpoints_first_value rfl rfl (heq_of_eq finishOwnerEq.symm)
            (heq_of_eq rfl) oldFollowing).trans (OwnerPath.Suffix.observationsCast_first_value same views.after))
      have tailLast : tailObserved.last.value = views.after.last.value :=
        (Primitive.Spine.castPath_last_value reindexedPath reindexed).trans
          ((Primitive.Spine.castEndpoints_last_value rfl rfl (heq_of_eq finishOwnerEq.symm)
            (heq_of_eq rfl) oldFollowing).trans (OwnerPath.Suffix.observationsCast_last_value same views.after))
      have displayedFirst : displayedObservation.first.value = observed.first.value :=
        (congrArg (fun old : Primitive.Spine expression accuracy
          (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) => old.first.value)
          retained.property).trans (Primitive.Spine.castEndpoints_first_value _ _ _ _ observed)
      have displayedLast : displayedObservation.last.value = observed.last.value :=
        (congrArg (fun old : Primitive.Spine expression accuracy
          (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) => old.last.value)
          retained.property).trans (Primitive.Spine.castEndpoints_last_value _ _ _ _ observed)
      have firstValue : headObserved.first.value = observed.first.value := headFirst.trans
        ((congrArg (fun vertex : OwnerPath.Primitive.Vertex expression start owner accuracy => vertex.value)
          (OwnerPath.Split.observations_first divided displayedObservation)).trans
          displayedFirst)
      have lastValue : tailObserved.last.value = observed.last.value := tailLast.trans
        ((congrArg (fun vertex : OwnerPath.Primitive.Vertex expression finish
            (PreparedPathGluing.finishOwner rest) accuracy => vertex.value)
          (OwnerPath.Split.observations_last divided displayedObservation)).trans
          displayedLast)
      have shared : tailObserved.first.value = headObserved.last.value := tailFirst.trans
        ((congrArg (fun vertex : OwnerPath.Primitive.Vertex expression
          divided.suffix.point divided.suffix.owner accuracy =>
          vertex.value) views.shared).trans headLast.symm)
      have viewsFactory := congrArg (fun old : Primitive.Spine expression accuracy
        (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) =>
          OwnerPath.Split.observations divided old) retained.property
      consume divided dividedFactory same front frontKept following followingKept followingFactory
        views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared

/-- Observe the given retained head of the same materialized path without splitting that path again.

The existing HeadConsumer supplies the actual split, raw Trace, following
path and complete original factories. The same old observation cache is
transported once and split on those given pieces; the existing observed
callback retains every old Vertex, shared reading and request unchanged.
-/
def withObservedHead {Result : Type u}
    (consume : ObservedHeadConsumer first budget fits finishOwnerEq remaining materialized observed Result) :
    HeadConsumer first budget fits finishOwnerEq remaining
      (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) Result :=
  let displayedObservation := Primitive.Spine.castEndpoints rfl rfl (heq_of_eq rfl)
    (heq_of_eq (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) observed
  observationsAtHead first budget fits finishOwnerEq remaining materialized observed
    ⟨displayedObservation, rfl⟩ consume

/-- Read the SAME old primitive segment and literal old suffix through the original retained cons-lineage split.

One materialized count split and one old observation split execute. Whole
suffix identities transport the original prefix and suffix; original
complete-segment endpoint/Owner laws attach the raw Trace. Only the supplied
Spine is consumed. No canonical path, source, root or observation factory
is executed, and no original request or stationary comparison is replaced.
-/
def withObservedCons
    (factory : materialized =
      (PreparedPath.TraceLineage.cons (first := first) (rest := rest)
        budget fits finishOwnerEq remaining).ownerPath) {Result : Type u}
    (consume : ObservedHeadConsumer first budget fits finishOwnerEq remaining materialized observed Result) :
    Result := by
  let displayedObservation := Primitive.Spine.castEndpoints rfl rfl (heq_of_eq rfl)
    (heq_of_eq (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) observed
  let retainedHead := Head.build first budget fits finishOwnerEq remaining materialized factory
  exact retainedHead.withData
    (observationsAtHead first budget fits finishOwnerEq remaining materialized observed
      ⟨displayedObservation, rfl⟩ consume)

/-- The original materialized observer uses the same head operation after its one actual path split. -/
theorem withObservedCons_eq
    (factory : materialized =
      (PreparedPath.TraceLineage.cons (first := first) (rest := rest)
        budget fits finishOwnerEq remaining).ownerPath) {Result : Type u}
    (consume : ObservedHeadConsumer first budget fits finishOwnerEq remaining materialized observed Result) :
    withObservedCons first budget fits finishOwnerEq remaining materialized observed factory consume =
      withCons first budget fits finishOwnerEq remaining materialized factory
        (withObservedHead first budget fits finishOwnerEq remaining materialized observed consume) := by
  unfold withObservedCons withObservedHead
  exact Head.build_withData (first := first) (budget := budget) (fits := fits)
    (finishOwnerEq := finishOwnerEq) (remaining := remaining) materialized factory
    (observationsAtHead first budget fits finishOwnerEq remaining materialized observed
      ⟨Primitive.Spine.castEndpoints rfl rfl (heq_of_eq rfl)
        (heq_of_eq (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) observed, rfl⟩ consume)

/-- Postcomposition commutes with the given-head observation operation at the same retained original fields. -/
theorem withObservedHead_map {Result : Type u} {Next : Type v}
    (consume : ObservedHeadConsumer first budget fits finishOwnerEq remaining materialized observed Result)
    (project : Result → Next) :
    ∀ divided dividedFactory same front frontKept following followingKept followingFactory,
      project (withObservedHead first budget fits finishOwnerEq remaining materialized observed consume
        divided dividedFactory same front frontKept following followingKept followingFactory) =
      withObservedHead first budget fits finishOwnerEq remaining materialized observed
        (fun divided dividedFactory same front frontKept following followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared =>
          project (consume divided dividedFactory same front frontKept following followingKept followingFactory
            views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared))
        divided dividedFactory same front frontKept following followingKept followingFactory := by
  intro divided dividedFactory same front frontKept following followingKept followingFactory
  unfold withObservedHead observationsAtHead
  rfl

/-- Pointwise equality of callbacks preserves the same given-head observation result.

Only the callbacks' actual values at the retained complete input fields
are compared. No equality of whole functions or function extensionality
is used to transport the original observation caches.
-/
theorem withObservedHead_congr {Result : Type u}
    (firstConsume lastConsume :
      ObservedHeadConsumer first budget fits finishOwnerEq remaining materialized observed Result)
    (agree : ∀ divided dividedFactory same front frontKept following followingKept followingFactory
        views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared,
      firstConsume divided dividedFactory same front frontKept following followingKept followingFactory
        views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared =
      lastConsume divided dividedFactory same front frontKept following followingKept followingFactory
        views viewsFactory headObserved headKept tailObserved tailKept firstValue lastValue shared) :
    ∀ divided dividedFactory same front frontKept following followingKept followingFactory,
      withObservedHead first budget fits finishOwnerEq remaining materialized observed firstConsume
        divided dividedFactory same front frontKept following followingKept followingFactory =
      withObservedHead first budget fits finishOwnerEq remaining materialized observed lastConsume
        divided dividedFactory same front frontKept following followingKept followingFactory := by
  intro divided dividedFactory same front frontKept following followingKept followingFactory
  unfold withObservedHead observationsAtHead
  exact agree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- A callback ignoring the observation fields receives exactly the original retained materialized head.

The actual split, raw Trace, following path and all their complete
factory/HEq certificates remain unchanged. The claim forgets only the
additional observation values; it supplies no reading or root equality.
-/
theorem withObservedHead_forget {Result : Type u}
    (consume : HeadConsumer first budget fits finishOwnerEq remaining
      (materialized.reindexOwners rfl (PreparedPath.castOwner_finishOwner finishOwnerEq rest)) Result) :
    ∀ divided dividedFactory same front frontKept following followingKept followingFactory,
      withObservedHead first budget fits finishOwnerEq remaining materialized observed
        (fun divided dividedFactory same front frontKept following followingKept followingFactory
            _views _viewsFactory _headObserved _headKept _tailObserved _tailKept _firstValue _lastValue _shared =>
          consume divided dividedFactory same front frontKept following followingKept followingFactory)
        divided dividedFactory same front frontKept following followingKept followingFactory =
      consume divided dividedFactory same front frontKept following followingKept followingFactory := by
  intro divided dividedFactory same front frontKept following followingKept followingFactory
  unfold withObservedHead observationsAtHead
  rfl

end PreparedPath.TraceLineage

end Purelib.Riemann.Paths.PreparedPathTrace

end
