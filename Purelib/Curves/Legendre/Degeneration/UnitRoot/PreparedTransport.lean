module

public import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.Riemann.Paths.PreparedSubdivisionTrace
public import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Tactic.Ring

/-!
# Original signed cofactor roots through prepared continuation handoffs

Each accepted prepared step retains its actual source cache and endpoint
reconditioning. A fixed-box comparison path derives a finite dyadic comparison
from that cache and the original whole-patch reference budget. The comparison
mesh changes neither the prepared requests nor the transported owner.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.UnitRoot.PreparedTransport

open Purelib.RootIsolation.SquareRoot

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation
  (Endpoint StepRequest CachedSource Subdivision prepared parameterAt parameterAt_inside parameterAt_between
    parameterAt_zero parameterAt_one parameterAt_eq_affine transported advance sourceRootEquivalent
    retainedAtReserveRootEquivalent preparedClearanceLower)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.RootIsolation
open Purelib.Riemann.Paths.PreparedClearPathModels
  (zeroEndpoint ownerAtStart CompleteSegment PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedSegment TracedPath)
open Purelib.Riemann.Paths

/-- An original cofactor-clear axis segment in the selected spatial collision patch. -/
abbrev Segment (site : Fin 2) := ClearSegment (unitPolynomial site) (spatialBox site)

/-- An original finite axis path for the cofactor polynomial in the selected spatial patch. -/
abbrev Path (site : Fin 2) := Polynomial.Geometry.ClearPath (unitPolynomial site) (spatialBox site)

variable {site : Fin 2} {start finish : Canonical}

/-- Construct the original horizontal cofactor-clear segment from intrinsic endpoint admission.

The whole spatial square's cofactor lower bound supplies the retained line
clearance one quarter, including all points between the supplied endpoints.
-/
def horizontal (site : Fin 2) (first last height : Rational)
    (firstInside : (spatialBox site).Contains (Components.Basic.point first height))
    (lastInside : (spatialBox site).Contains (Components.Basic.point last height)) :
    Segment site (Components.Basic.point first height) (Components.Basic.point last height) :=
  .horizontal first last height firstInside.1 firstInside.2.1 lastInside.1 lastInside.2.1
    { bound := 1 / 4
      positive := by decide +kernel
      lower := by
        intro coordinate lower upper
        have bound := unit_lower site (show (spatialBox site).Contains (Components.Basic.point coordinate height) from
          ⟨lower, upper, firstInside.2.2.1, firstInside.2.2.2⟩)
        rewrite [Norm.Basic.normSq_eq_canonical] at bound
        exact bound }

/-- The intrinsic horizontal segment retains its original fixed coordinate inside the same spatial square. -/
theorem horizontal_within (site : Fin 2) (first last height : Rational)
    (firstInside : (spatialBox site).Contains (Components.Basic.point first height))
    (lastInside : (spatialBox site).Contains (Components.Basic.point last height)) :
    (horizontal site first last height firstInside lastInside).WithinAmbient :=
  ⟨firstInside.2.2.1, firstInside.2.2.2⟩

/-- Construct the original vertical cofactor-clear segment from intrinsic endpoint admission.

The whole spatial square's cofactor lower bound supplies the retained line
clearance one quarter without checking only the two endpoint values.
-/
def vertical (site : Fin 2) (width first last : Rational)
    (firstInside : (spatialBox site).Contains (Components.Basic.point width first))
    (lastInside : (spatialBox site).Contains (Components.Basic.point width last)) :
    Segment site (Components.Basic.point width first) (Components.Basic.point width last) :=
  .vertical width first last firstInside.2.2.1 firstInside.2.2.2 lastInside.2.2.1 lastInside.2.2.2
    { bound := 1 / 4
      positive := by decide +kernel
      lower := by
        intro coordinate lower upper
        have bound := unit_lower site (show (spatialBox site).Contains (Components.Basic.point width coordinate) from
          ⟨firstInside.1, firstInside.2.1, lower, upper⟩)
        rewrite [Norm.Basic.normSq_eq_canonical] at bound
        exact bound }

/-- The intrinsic vertical segment retains its original fixed coordinate inside the same spatial square. -/
theorem vertical_within (site : Fin 2) (width first last : Rational)
    (firstInside : (spatialBox site).Contains (Components.Basic.point width first))
    (lastInside : (spatialBox site).Contains (Components.Basic.point width last)) :
    (vertical site width first last firstInside lastInside).WithinAmbient :=
  ⟨firstInside.1, firstInside.2.1⟩

/-- The displayed start of the original patch-contained segment lies in that same spatial patch. -/
theorem start_inside (segment : Segment site start finish) (within : segment.WithinAmbient) :
    (spatialBox site).Contains start := by
  have admitted := segment.pointAt_contains within 0 (by decide +kernel)
  rewrite [segment.pointAt_zero] at admitted
  exact admitted

/-- The displayed finish of the original patch-contained segment lies in that same spatial patch. -/
theorem finish_inside (segment : Segment site start finish) (within : segment.WithinAmbient) :
    (spatialBox site).Contains finish := by
  have admitted := segment.pointAt_contains within 1 (by decide +kernel)
  rewrite [segment.pointAt_one] at admitted
  exact admitted

/-- Equal original spatial points give the same independent signed cofactor name. -/
private theorem patchName_eq {first last : Canonical} (equal : first = last)
    (firstInside : (spatialBox site).Contains first) (lastInside : (spatialBox site).Contains last) :
    ownerRootName (owner site first firstInside).parameterNonzero (owner site first firstInside) =
      ownerRootName (owner site last lastInside).parameterNonzero (owner site last lastInside) := by
  cases equal
  rfl

/-- Cache the full accepted variation on the exact prepared source owner. -/
private def stepBudget (segment : Segment site start finish) (left : Endpoint)
    (source : Owner ((unitPolynomial site).eval (segment.pointAt left.parameter)))
    (request : StepRequest) (cached : CachedSource segment left source request)
    (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound) : FixedRootBoxBudget.Budget cached.preparedOwner :=
  FixedRootBoxBudget.Budget.acquire cached.preparedOwner
    (ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter)
    (ClearSheetContinuation.variationBound_nonneg segment _ _) small

/-- Compare the actual accepted step against the independently retained whole-patch reference box.

Every comparison parameter evaluates the original spatial segment. The two
movement payments and the squared Lipschitz scale come from its retained
variation bound and patch containment, without a supplied comparison mesh.
-/
private def comparisonPath (segment : Segment site start finish) (within : segment.WithinAmbient)
    (left : Endpoint) (source : Owner ((unitPolynomial site).eval (segment.pointAt left.parameter)))
    (request : StepRequest) (cached : CachedSource segment left source request)
    (ordered : left.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound) :
    FixedRootBoxPath.PathData (stepBudget segment left source request cached small) (Transport.budget site) where
  point time := (unitPolynomial site).eval (segment.pointAt (parameterAt left request time))
  nonzero time inside := segment.pointAt_eval_ne_zero _ (parameterAt_inside left request ordered time inside)
  firstMovement := by
    intro time inside
    have bounds := parameterAt_between left request ordered time inside
    have movement := ClearSheetContinuation.evaluation_variation_le segment within left.parameter
      (parameterAt left request time) left.inside (parameterAt_inside left request ordered time inside)
    rewrite [Norm.Basic.normSq_eq_canonical] at movement
    exact movement.trans (ClearSheetContinuation.variationBound_le_of_between segment bounds.1 bounds.2)
  secondMovement := by
    intro time inside
    exact Transport.movement site
      (segment.pointAt_contains within (parameterAt left request time)
        (parameterAt_inside left request ordered time inside))
  scale := ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter
  scale_nonnegative := ClearSheetContinuation.variationBound_nonneg segment _ _
  variation := by
    intro first last firstInside lastInside
    have movement := ClearSheetContinuation.evaluation_variation_le segment within
      (parameterAt left request first) (parameterAt left request last)
      (parameterAt_inside left request ordered first firstInside)
      (parameterAt_inside left request ordered last lastInside)
    rewrite [Norm.Basic.normSq_eq_canonical] at movement
    refine movement.trans_eq ?_
    rewrite [ClearSheetContinuation.variationBound_eq_denseLipschitz,
      ClearSheetContinuation.variationBound_eq_denseLipschitz,
      parameterAt_eq_affine, parameterAt_eq_affine]
    ring1

/-- The comparison path starts at the actual prepared request's source radicand. -/
private theorem comparisonPath_zero (segment : Segment site start finish) (within : segment.WithinAmbient)
    (left : Endpoint) (source : Owner ((unitPolynomial site).eval (segment.pointAt left.parameter)))
    (request : StepRequest) (cached : CachedSource segment left source request)
    (ordered : left.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound) :
    (comparisonPath segment within left source request cached ordered small).point 0 =
      (unitPolynomial site).eval (segment.pointAt left.parameter) := by
  change (unitPolynomial site).eval (segment.pointAt (parameterAt left request 0)) = _
  rewrite [parameterAt_zero]
  rfl

/-- The comparison path finishes at the actual accepted request's target radicand. -/
private theorem comparisonPath_one (segment : Segment site start finish) (within : segment.WithinAmbient)
    (left : Endpoint) (source : Owner ((unitPolynomial site).eval (segment.pointAt left.parameter)))
    (request : StepRequest) (cached : CachedSource segment left source request)
    (ordered : left.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound) :
    (comparisonPath segment within left source request cached ordered small).point 1 =
      (unitPolynomial site).eval (segment.pointAt request.endpoint.parameter) := by
  change (unitPolynomial site).eval (segment.pointAt (parameterAt left request 1)) = _
  rewrite [parameterAt_one]
  rfl

/-- The original operational comparison of an actual cofactor owner with its independent signed patch reading.

This exact type alias keeps both original root names and spatial ownership in
one compact dependent signature. It introduces no additional comparison record.
-/
@[irreducible, expose] def ReadingAgreement (site : Fin 2) (point : Canonical)
    (inside : (spatialBox site).Contains point) (actual : Owner ((unitPolynomial site).eval point)) : Type :=
  NamedEquivalent (ownerRootName actual.parameterNonzero actual)
    (ownerRootName (owner site point inside).parameterNonzero (owner site point inside))

/-- The same original reading comparison at an admitted retained segment parameter. -/
@[irreducible, expose] def Agreement (segment : Segment site start finish) (within : segment.WithinAmbient)
    (endpoint : Endpoint) (actual : Owner ((unitPolynomial site).eval (segment.pointAt endpoint.parameter))) : Type :=
  ReadingAgreement site (segment.pointAt endpoint.parameter)
    (segment.pointAt_contains within endpoint.parameter endpoint.inside) actual

/-- An actual accepted prepared step preserves agreement with the independent signed patch root.

The retained cache supplies source preparation, the moving fixed-box comparison
and the actual endpoint-retention handoff. All three comparisons retain their
original owners; an internally computed comparison depth pays both boxes.
-/
def step_agrees (segment : Segment site start finish) (within : segment.WithinAmbient)
    (left : Endpoint) (source : Owner ((unitPolynomial site).eval (segment.pointAt left.parameter)))
    (request : StepRequest) (cached : CachedSource segment left source request)
    (ordered : left.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      (prepared segment left source request).track.initial.clearance.bound)
    (initial : Agreement segment within left source) :
    Agreement segment within request.endpoint (advance segment within left source request small) := by
  unfold Agreement ReadingAgreement at initial ⊢
  have cachedSmall : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound := by
    rewrite [cached.preparedOwner_eq]
    exact small
  let path := comparisonPath segment within left source request cached ordered cachedSmall
  let zeroEq := comparisonPath_zero segment within left source request cached ordered cachedSmall
  let oneEq := comparisonPath_one segment within left source request cached ordered cachedSmall
  let independentFirst := owner site (segment.pointAt left.parameter)
    (segment.pointAt_contains within left.parameter left.inside)
  let independentLast := owner site (segment.pointAt request.endpoint.parameter)
    (segment.pointAt_contains within request.endpoint.parameter request.endpoint.inside)
  let moved := transported segment within left source request small
  have preparedAgreement : NamedEquivalent (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner)
      (ownerRootName independentFirst.parameterNonzero independentFirst) := by
    rewrite [cached.preparedOwner_eq]
    exact (sourceRootEquivalent segment left source request).symm.trans initial
  let firstStart := Owner.Transport.castOwnerParameter zeroEq.symm cached.preparedOwner
  let secondStart := Owner.Transport.castOwnerParameter zeroEq.symm independentFirst
  let firstFinish := Owner.Transport.castOwnerParameter oneEq.symm moved
  let secondFinish := Owner.Transport.castOwnerParameter oneEq.symm independentLast
  have sourceAgreement : NamedEquivalent (ownerRootName firstStart.parameterNonzero firstStart)
      (ownerRootName secondStart.parameterNonzero secondStart) :=
    NamedEquivalent.transport (ownerRootName_castOwnerParameter zeroEq.symm cached.preparedOwner).symm
      (ownerRootName_castOwnerParameter zeroEq.symm independentFirst).symm preparedAgreement
  have firstStartRefines : firstStart.track.initial.box.Refines cached.preparedOwner.track.initial.box := by
    rewrite [Owner.Transport.castOwnerParameter_initial_box]
    exact Box.refines_refl _
  have secondStartRefines : secondStart.track.initial.box.Refines (Transport.source site).track.initial.box := by
    rewrite [Owner.Transport.castOwnerParameter_initial_box, owner_initial_box, Transport.source_box]
    exact Box.refines_refl _
  have firstFinishRefines : firstFinish.track.initial.box.Refines cached.preparedOwner.track.initial.box := by
    rewrite [Owner.Transport.castOwnerParameter_initial_box, cached.preparedOwner_eq]
    unfold moved transported
    exact SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines _ _ _ _
  have secondFinishRefines : secondFinish.track.initial.box.Refines (Transport.source site).track.initial.box := by
    rewrite [Owner.Transport.castOwnerParameter_initial_box, owner_initial_box, Transport.source_box]
    exact Box.refines_refl _
  let compared := path.retainedEquivalent firstStart secondStart firstStartRefines secondStartRefines sourceAgreement
    firstFinish secondFinish firstFinishRefines secondFinishRefines
  have targetAgreement : NamedEquivalent (ownerRootName moved.parameterNonzero moved)
      (ownerRootName independentLast.parameterNonzero independentLast) :=
    NamedEquivalent.transport (ownerRootName_castOwnerParameter oneEq.symm moved)
      (ownerRootName_castOwnerParameter oneEq.symm independentLast) compared
  exact (retainedAtReserveRootEquivalent moved (preparedClearanceLower segment left request)).symm.trans targetAgreement

/-- Every actual prepared subdivision carries its original signed cofactor root to the independent endpoint reading.

Recursion follows the stored subdivision, including its exact prepared caches
and retained endpoint owners. Each moving step derives its own finite
comparison and composes both actual handoffs before consuming the original tail.
-/
def subdivision_agrees (segment : Segment site start finish) (within : segment.WithinAmbient) :
    ∀ {left : Endpoint} {source : Owner ((unitPolynomial site).eval (segment.pointAt left.parameter))}
      (subdivision : Subdivision segment within left source),
      Agreement segment within left source →
      Agreement segment within subdivision.endpoint subdivision.terminalOwner
  | _, _, .stop _ _, initial => initial
  | _, _, .next left source request cached ordered small remaining, initial =>
      subdivision_agrees segment within remaining
        (step_agrees segment within left source request cached ordered small initial)

/-- An actual complete segment ends at the independently constructed signed patch root.

The supplied subdivision and its original terminal-owner transport determine
the comparison. Preparation and integration requests are not rebuilt.
-/
def complete_agrees (segment : Segment site start finish) (within : segment.WithinAmbient)
    {source : Owner ((unitPolynomial site).eval start)} (prepared : CompleteSegment segment within source)
    (initial : NamedEquivalent (ownerRootName source.parameterNonzero source)
      (ownerRootName (owner site start (start_inside segment within)).parameterNonzero
        (owner site start (start_inside segment within)))) :
    NamedEquivalent (ownerRootName prepared.finishOwner.parameterNonzero prepared.finishOwner)
      (ownerRootName (owner site finish (finish_inside segment within)).parameterNonzero
        (owner site finish (finish_inside segment within))) := by
  have startName : ownerRootName (ownerAtStart segment source).parameterNonzero (ownerAtStart segment source) =
      ownerRootName source.parameterNonzero source := by
    unfold ownerAtStart
    exact ownerRootName_castOwnerParameter _ _
  have startPoint : segment.pointAt zeroEndpoint.parameter = start := segment.pointAt_zero
  have independentStart := patchName_eq startPoint
    (segment.pointAt_contains within zeroEndpoint.parameter zeroEndpoint.inside) (start_inside segment within)
  have startAgreement : Agreement segment within zeroEndpoint (ownerAtStart segment source) := by
    unfold Agreement ReadingAgreement
    exact NamedEquivalent.transport startName.symm independentStart.symm initial
  have terminalAgreement := subdivision_agrees segment within prepared.subdivision startAgreement
  unfold Agreement ReadingAgreement at terminalAgreement
  have finishName : ownerRootName prepared.finishOwner.parameterNonzero prepared.finishOwner =
      ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner := by
    unfold CompleteSegment.finishOwner CompleteSegment.terminalOwner
    exact ownerRootName_castOwnerParameter _ _
  have independentName :
      ownerRootName
        (owner site (segment.pointAt prepared.subdivision.endpoint.parameter)
          (segment.pointAt_contains within prepared.subdivision.endpoint.parameter
            prepared.subdivision.endpoint.inside)).parameterNonzero
        (owner site (segment.pointAt prepared.subdivision.endpoint.parameter)
          (segment.pointAt_contains within prepared.subdivision.endpoint.parameter
            prepared.subdivision.endpoint.inside)) =
        ownerRootName (owner site finish (finish_inside segment within)).parameterNonzero
          (owner site finish (finish_inside segment within)) := by
    exact patchName_eq prepared.finish_eq _ _
  exact NamedEquivalent.transport finishName.symm independentName terminalAgreement

/-- Compare an actual traced segment's cached finish owner with the independent signed endpoint reading.

The comparison consumes the original complete segment and transports its
result to the exact cached finish owner, without rebuilding its preparation.
-/
def traced_agrees (segment : Segment site start finish) (within : segment.WithinAmbient)
    {source : Owner ((unitPolynomial site).eval start)} (traced : TracedSegment segment within source)
    (initial : NamedEquivalent (ownerRootName source.parameterNonzero source)
      (ownerRootName (owner site start (start_inside segment within)).parameterNonzero
        (owner site start (start_inside segment within)))) :
    NamedEquivalent (ownerRootName traced.finishOwner.parameterNonzero traced.finishOwner)
      (ownerRootName (owner site finish (finish_inside segment within)).parameterNonzero
        (owner site finish (finish_inside segment within))) := by
  have retainedName := congrArg (fun actual : Owner ((unitPolynomial site).eval finish) =>
    ownerRootName actual.parameterNonzero actual) traced.finishOwner_eq
  exact NamedEquivalent.transport retainedName.symm rfl (complete_agrees segment within traced.prepared initial)

/-- Construct actual complete signed cofactor continuation from an intrinsic patch-contained axis segment.

The existing total traced-segment builder computes its sufficient finite
budget and retains the actual preparation requests, endpoint cache and owner
path. Its initial owner is the independent original signed cofactor reading.
-/
def build (segment : Segment site start finish) (within : segment.WithinAmbient) :
    TracedSegment segment within (owner site start (start_inside segment within)) :=
  TracedSegment.build segment within (owner site start (start_inside segment within))

/-- Compare the actual retained result of complete signed cofactor continuation with the independent finish reading.

The supplied result keeps the same original starting owner and its stored
subdivision. Reflexive initial agreement and the computed prepared handoffs
derive the endpoint comparison without caller-supplied sample inequalities.
-/
def build_agrees (segment : Segment site start finish) (within : segment.WithinAmbient)
    (traced : TracedSegment segment within (owner site start (start_inside segment within))) :
    NamedEquivalent (ownerRootName traced.finishOwner.parameterNonzero traced.finishOwner)
      (ownerRootName (owner site finish (finish_inside segment within)).parameterNonzero
        (owner site finish (finish_inside segment within))) :=
  traced_agrees segment within traced (NamedEquivalent.refl _)

/-- Two actual prepared results from the original signed source have equivalent retained finish-owner names.

Both stored request spines and finish caches remain independent. Their derived
comparisons compose through the same original signed endpoint reading, giving
operational endpoint agreement without identifying the two preparations.
-/
def builds_agree (segment : Segment site start finish) (within : segment.WithinAmbient)
    (first second : TracedSegment segment within (owner site start (start_inside segment within))) :
    NamedEquivalent (ownerRootName first.finishOwner.parameterNonzero first.finishOwner)
      (ownerRootName second.finishOwner.parameterNonzero second.finishOwner) :=
  (build_agrees segment within first).trans (build_agrees segment within second).symm

/-- All retained segments carry an admitted path start to an admitted finish in the same spatial patch.

The empty path retains its supplied point admission. Every nonempty step
uses its whole-segment containment, including the exact shared endpoint.
-/
theorem path_finish_inside : ∀ {start finish : Canonical} (path : Path site start finish), path.WithinAmbient →
    (spatialBox site).Contains start → (spatialBox site).Contains finish
  | _, _, .nil _, _, inside => inside
  | _, _, .cons head tail, within, _ => path_finish_inside tail within.tail (finish_inside head within.head)

/-- Construct a cofactor-clear horizontal-then-vertical path between any two admitted spatial points.

The actual intermediate corner takes the target real coordinate and source
imaginary coordinate. Rectangle admission proves its two segments clear on
their full lines, with their exact shared corner retained as a path index.
-/
def axisPath (site : Fin 2) (first last : Canonical)
    (firstInside : (spatialBox site).Contains first) (lastInside : (spatialBox site).Contains last) :
    Path site first last :=
  let corner := Components.Basic.point last.re first.im
  have cornerInside : (spatialBox site).Contains corner :=
    ⟨lastInside.1, lastInside.2.1, firstInside.2.2.1, firstInside.2.2.2⟩
  .cons (horizontal site first.re last.re first.im firstInside cornerInside)
    (.cons (vertical site last.re first.im last.im cornerInside lastInside) (.nil last))

/-- The two internally constructed axis pieces remain in the same original spatial patch. -/
theorem axisPath_within (site : Fin 2) (first last : Canonical)
    (firstInside : (spatialBox site).Contains first) (lastInside : (spatialBox site).Contains last) :
    (axisPath site first last firstInside lastInside).WithinAmbient :=
  .cons (horizontal_within site first.re last.re first.im firstInside
    ⟨lastInside.1, lastInside.2.1, firstInside.2.2.1, firstInside.2.2.2⟩)
    (.cons (vertical_within site last.re first.im last.im
      ⟨lastInside.1, lastInside.2.1, firstInside.2.2.1, firstInside.2.2.2⟩ lastInside) (.nil last))

/-- Actual prepared path tails preserve the original signed reading through every complete segment.

The fold follows the stored path spine. Its next source is the actual preceding
complete segment's finish owner; independent point readings serve only as the
comparison owners and never replace the source of the retained tail.
-/
def path_agrees : ∀ {start finish : Canonical} (path : Path site start finish)
    (within : path.WithinAmbient) (inside : (spatialBox site).Contains start)
    {source : Owner ((unitPolynomial site).eval start)} (prepared : PreparedPath path source),
    ReadingAgreement site start inside source →
      ReadingAgreement site finish (path_finish_inside path within inside) (PreparedPathGluing.finishOwner prepared)
  | _, _, .nil _, _, _, _, .nil _ _, initial => initial
  | _, _, .cons head tail, within, _, _, .cons _ _ _ headWithin first remaining, initial => by
      have firstAgreement := complete_agrees head headWithin first (by
        unfold ReadingAgreement at initial
        exact initial)
      have nextAgreement : ReadingAgreement site _ (finish_inside head headWithin) first.finishOwner := by
        unfold ReadingAgreement
        exact firstAgreement
      exact path_agrees tail within.tail (finish_inside head headWithin) remaining nextAgreement

/-- Compare an actual traced path's cached finish owner with the independent signed endpoint reading.

The stored preparation spine supplies all segment handoffs. Its exact
finish-owner equation transports that result to the cached owner retained by
the deferred geometric trace.
-/
def tracedPath_agrees (path : Path site start finish) (within : path.WithinAmbient)
    (inside : (spatialBox site).Contains start)
    {source : Owner ((unitPolynomial site).eval start)} (traced : TracedPath path source)
    (initial : ReadingAgreement site start inside source) :
    ReadingAgreement site finish (path_finish_inside path within inside) traced.finishOwner := by
  have result := path_agrees path within inside traced.prepared initial
  unfold ReadingAgreement at result ⊢
  have retainedName := congrArg (fun actual : Owner ((unitPolynomial site).eval finish) =>
    ownerRootName actual.parameterNonzero actual) traced.finishOwner_eq
  exact NamedEquivalent.transport retainedName.symm rfl result

/-- Construct complete signed cofactor transport along an admitted finite spatial axis path.

Each segment computes its sufficient finite preparation bound. The original
path builder retains its request caches, finish owners, exact owner handoffs
and deferred concatenated geometric trace.
-/
def buildPath (path : Path site start finish) (within : path.WithinAmbient)
    (inside : (spatialBox site).Contains start) : TracedPath path (owner site start inside) :=
  TracedPath.build path within (owner site start inside)

/-- The actual path result agrees with the independent signed finish reading without an initial comparison input. -/
def buildPath_agrees (path : Path site start finish) (within : path.WithinAmbient)
    (inside : (spatialBox site).Contains start) (traced : TracedPath path (owner site start inside)) :
    ReadingAgreement site finish (path_finish_inside path within inside) traced.finishOwner := by
  apply tracedPath_agrees path within inside traced
  unfold ReadingAgreement
  exact NamedEquivalent.refl _

/-- Two independently prepared admitted paths with the same endpoints compare their actual cached finish owners.

Each path retains its own segment list, requests, handoffs and deferred trace.
The derived endpoint comparisons compose through the same signed patch reading;
this compares the root names rather than asserting equality of geometric traces.
-/
def buildPaths_agree (first second : Path site start finish)
    (firstWithin : first.WithinAmbient) (secondWithin : second.WithinAmbient)
    (inside : (spatialBox site).Contains start)
    (left : TracedPath first (owner site start inside)) (right : TracedPath second (owner site start inside)) :
    NamedEquivalent (ownerRootName left.finishOwner.parameterNonzero left.finishOwner)
      (ownerRootName right.finishOwner.parameterNonzero right.finishOwner) := by
  have leftAgreement := buildPath_agrees first firstWithin inside left
  have rightAgreement := buildPath_agrees second secondWithin inside right
  unfold ReadingAgreement at leftAgreement rightAgreement
  exact leftAgreement.trans rightAgreement.symm

/-- Close the actual returning cofactor owner trace using its derived endpoint agreement.

The synchronized closing readings and their stationary edge keep the original
source, cached finish owner and complete deferred trace. No supplied root join
or newly prepared loop is needed.
-/
def closePath {base : Canonical} (path : Path site base base) (within : path.WithinAmbient)
    (inside : (spatialBox site).Contains base) (traced : TracedPath path (owner site base inside)) :
    OwnerTracePath.OwnerPath.ClosedRealization traced.trace.get := by
  have returned := buildPath_agrees path within inside traced
  unfold ReadingAgreement at returned
  exact traced.trace.get.close
    (OwnerTraceReadings.OwnerJoin.acquire traced.finishOwner (owner site base inside) returned)

/-- A returning admitted cofactor path cannot have odd winding on its actual retained moving vertices.

Its independently derived root return closes the exact retained owner trace.
The existing finite square-root winding comparison excludes an odd original
cofactor winding without replacing the stored path by a matrix word.
-/
theorem not_odd_closedPath {base : Canonical} (path : Path site base base) (within : path.WithinAmbient)
    (inside : (spatialBox site).Contains base) (traced : TracedPath path (owner site base inside)) (turns : Int) :
    Polynomial.Winding.Polygon.Basic.chainRaw (unitPolynomial site) base
      (PreparedPathTrace.PreparedPath.movingVertices traced.prepared) ≠ 4 * (2 * turns + 1) := by
  have returned := buildPath_agrees path within inside traced
  unfold ReadingAgreement at returned
  exact fun odd => traced.root_not_equivalent_of_odd turns odd returned

end Purelib.Curves.Legendre.Degeneration.UnitRoot.PreparedTransport
