module

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
public import Purelib.Data.List.DependentProduct
public import Purelib.Geometry.Rational.Box.Outside.Preparation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Data.List.Map

/-! # Checked primitive coverage on the original retained parents

Every parent occurrence acquires one original patch and materializes its
neighborhood once. The original exact box inspection is stored on that
same neighborhood and physical finish. All inspections execute before
resolution, so a local failed coverage test retains every original
attempt, including stationary and repeated occurrences. Such a failure
requests local refinement; it is not a pole or an impossibility claim.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rational.Box (PointExclusion)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

namespace Inspection

/-- The original patch, its once materialized neighborhood and the actual original finish inspection.

Each whole value carries its original factory identity. The exact parent
is the original nominal index; no point, root owner or continuation is
reconstructed from coordinate agreement. The neighborhood remains data
so a successful later source producer can consume the checked cache.
-/
@[expose] def AtParent (count : Nat) (parent : CenteredEdge curve differential) :=
  (patch : {value : PreparedPatch parent // value = PreparedPatch.acquire parent}) ×
  (neighborhood : {value : ContinuedNeighborhood curve.polynomial count // value = patch.val.neighborhood count}) ×
  {outcome : PointExclusion neighborhood.val.box (parent.edge.point 1) //
    outcome = Geometry.Rational.Box.inspectPoint neighborhood.val.box (parent.edge.point 1)}

namespace AtParent

variable {parent : CenteredEdge curve differential}

/-- Inspect the SAME supplied original patch once, retaining its complete factory and actual neighborhood.

The neighborhood and original point inspection are computed once from
this actual patch. The whole patch identity certifies the original
canonical parent index without replacing its bounds or seed at runtime.
-/
def fromPatch (count : Nat) {parent : CenteredEdge curve differential}
    (patch : PreparedPatch parent) (factory : patch = PreparedPatch.acquire parent) : AtParent count parent :=
  let neighborhood := patch.neighborhood count
  let outcome := Geometry.Rational.Box.inspectPoint neighborhood.box (parent.edge.point 1)
  ⟨⟨patch, factory⟩, ⟨neighborhood, rfl⟩, ⟨outcome, rfl⟩⟩

/-- Acquire one original patch, build its neighborhood once and inspect that exact physical finish once. -/
def build (count : Nat) (parent : CenteredEdge curve differential) : AtParent count parent :=
  fromPatch count (PreparedPatch.acquire parent) rfl

/-- Supplied-patch inspection preserves the whole original canonical inspection factory. -/
theorem fromPatch_eq_build (count : Nat) {parent : CenteredEdge curve differential}
    (patch : PreparedPatch parent) (factory : patch = PreparedPatch.acquire parent) :
    fromPatch count patch factory = build count parent := by
  cases factory
  rfl

variable (inspected : AtParent count parent)

/-- Read the same acquired original patch, retaining its exact parent and prepared seed. -/
@[expose] def patch : PreparedPatch parent := inspected.1.val

/-- Read the actual neighborhood inspected before any source-model preparation. -/
@[expose] def neighborhood : ContinuedNeighborhood curve.polynomial count := inspected.2.1.val

/-- Read the cached exact finite box inspection without repeating it. -/
@[expose] def outcome : PointExclusion inspected.neighborhood.box (parent.edge.point 1) := inspected.2.2.val

/-- The retained patch has its exact original factory on this same parent. -/
theorem patch_eq : inspected.patch = PreparedPatch.acquire parent := inspected.1.property

/-- The inspected neighborhood has the exact factory of the retained original patch. -/
theorem neighborhood_eq : inspected.neighborhood = inspected.patch.neighborhood count := inspected.2.1.property

/-- The cached test is the original inspection of this SAME neighborhood and physical finish. -/
theorem outcome_eq : inspected.outcome =
    Geometry.Rational.Box.inspectPoint inspected.neighborhood.box (parent.edge.point 1) := inspected.2.2.property

/-- Coverage is ready precisely in the stored inspection's actual contained-point branch. -/
@[expose] def Ready : Prop :=
  match inspected.outcome with
  | .apart _ => False
  | .inconclusive _ => True

/-- Decide readiness by reading the stored outcome, without a second coordinate or neighborhood test. -/
def readyDecision : Decidable inspected.Ready := by
  match same : inspected.outcome with
  | .apart _ =>
      exact .isFalse (fun impossible => by unfold Ready at impossible; rewrite [same] at impossible; exact impossible)
  | .inconclusive _ =>
      exact .isTrue (by unfold Ready; rewrite [same]; exact True.intro)

/-- Derive original covering containment from the actual stored contained-point certificate.

The whole neighborhood-factory equation transports only the original
box-containment proposition. It supplies no root or sheet identity.
-/
theorem inside (ready : inspected.Ready) :
    (inspected.patch.neighborhood count).box.Contains (parent.edge.point 1) := by
  have actual : inspected.neighborhood.box.Contains (parent.edge.point 1) := by
    unfold Ready at ready
    generalize inspected.outcome = outcome at ready
    cases outcome with
    | apart _ => exact ready.elim
    | inconclusive inside => exact inside
  exact Eq.mp (congrArg (fun neighborhood : ContinuedNeighborhood curve.polynomial count =>
    neighborhood.box.Contains (parent.edge.point 1)) inspected.neighborhood_eq) actual

/-- Actual containment forces the cached original inspection into its ready branch.

The whole retained inspection equation identifies the result of the
original point test. No new neighborhood or coordinate inspection is
computed by this proposition.
-/
theorem ready_of_inside (inside : inspected.neighborhood.box.Contains (parent.edge.point 1)) : inspected.Ready := by
  unfold Ready
  rewrite [inspected.outcome_eq]
  unfold Geometry.Rational.Box.inspectPoint
  rewrite [dif_pos inside]
  exact True.intro

/-- A supplied patch inspection retains the exact original patch value. -/
theorem fromPatch_patch (count : Nat) {parent : CenteredEdge curve differential}
    (patch : PreparedPatch parent) (factory : patch = PreparedPatch.acquire parent) :
    (fromPatch count patch factory).patch = patch := by
  unfold fromPatch AtParent.patch
  rfl

/-- A supplied patch inspection's actual neighborhood has the original factory on that SAME patch. -/
theorem fromPatch_neighborhood (count : Nat) {parent : CenteredEdge curve differential}
    (patch : PreparedPatch parent) (factory : patch = PreparedPatch.acquire parent) :
    (fromPatch count patch factory).neighborhood = patch.neighborhood count := by
  unfold fromPatch AtParent.neighborhood
  rfl

/-- The original local outside witness and margin, indexed by its exact cached inspection branch. -/
@[expose] def Request :=
  {outside : Geometry.Rational.Box.OutsideSide.Prepared inspected.neighborhood.box (parent.edge.point 1) //
    inspected.outcome = .apart outside}

/-- Return the original failed coverage branch as a typed local refinement request, without rechecking it. -/
def request (pending : ¬inspected.Ready) : inspected.Request := by
  match same : inspected.outcome with
  | .apart outside => exact ⟨outside, same⟩
  | .inconclusive _ =>
      have ready : inspected.Ready := by unfold Ready; rewrite [same]; exact True.intro
      exact False.elim (pending ready)

/-- A local refinement request retains the actual strictly positive outside margin of this same box and point. -/
theorem request_positive (pending : ¬inspected.Ready) : 0 < (inspected.request pending).val.margin :=
  (inspected.request pending).val.positive

end AtParent

end Inspection

/-- Store every original parent's complete patch, neighborhood and box-test outcome in original occurrence order. -/
@[expose] def Inspection (parents : List (CenteredEdge curve differential)) :=
  DependentProduct parents (fun index => Inspection.AtParent count (parents[index.val]'index.isLt))

namespace Inspection

/-- Materialize every original parent inspection once, retaining all failures as well as all successful tests. -/
def build (parents : List (CenteredEdge curve differential)) : Inspection (count := count) parents :=
  DependentProduct.ofFn parents (fun index => AtParent.build count (parents[index.val]'index.isLt))

/-- Read the same complete inspection at an original bounded parent occurrence. -/
@[expose] def entry {parents : List (CenteredEdge curve differential)}
    (inspected : Inspection (count := count) parents) (index : Fin parents.length) :
    AtParent count (parents[index.val]'index.isLt) := DependentProduct.get parents inspected index

/-- The complete inspection product has its exact original ordered materialization factory. -/
theorem build_eq (parents : List (CenteredEdge curve differential)) :
    build (count := count) parents = DependentProduct.ofFn parents
      (fun index => AtParent.build count (parents[index.val]'index.isLt)) := by
  unfold build
  rfl

/-- Each materialized entry retains the same original inspection factory at its exact parent occurrence. -/
theorem build_entry (parents : List (CenteredEdge curve differential)) (index : Fin parents.length) :
    (build (count := count) parents).entry index = AtParent.build count (parents[index.val]'index.isLt) :=
  DependentProduct.get_ofFn parents (fun index => AtParent.build count (parents[index.val]'index.isLt)) index

/-- Every actual retained occurrence must have its own successful containment certificate. -/
@[expose] def Ready : (parents : List (CenteredEdge curve differential)) → Inspection (count := count) parents → Prop
  | [], _ => True
  | _ :: parents, inspected => inspected.1.Ready ∧ Ready parents inspected.2

/-- Pointwise readiness of the SAME stored entries gives complete readiness in original list order. -/
theorem ready_of_entries : (parents : List (CenteredEdge curve differential)) →
    (inspected : Inspection (count := count) parents) →
    (∀ index, (inspected.entry index).Ready) → Ready parents inspected
  | [], _, _ => True.intro
  | _ :: parents, inspected, ready =>
      ⟨ready 0, ready_of_entries parents inspected.2 (fun index => ready index.succ)⟩

/-- Decide complete coverage from the actual stored outcomes, retaining the whole inspected product unchanged. -/
def readyDecision : (parents : List (CenteredEdge curve differential)) →
    (inspected : Inspection (count := count) parents) → Decidable (Ready parents inspected)
  | [], _ => .isTrue True.intro
  | _ :: parents, inspected =>
      match inspected.1.readyDecision with
      | .isFalse pending => .isFalse (fun ready => pending ready.1)
      | .isTrue first =>
          match readyDecision parents inspected.2 with
          | .isFalse pending => .isFalse (fun ready => pending ready.2)
          | .isTrue following => .isTrue ⟨first, following⟩

/-- Read the actual pending parent occurrences in their unchanged original order.

The bounded indices keep repeated parents distinct. Each index stores
failure of its SAME cached containment outcome; its original outside
witness and margin are returned by AtParent.request. No inspection is
repeated to enumerate requests.
-/
@[expose] def requests : (parents : List (CenteredEdge curve differential)) →
    (inspected : Inspection (count := count) parents) →
    List {index : Fin parents.length // ¬(inspected.entry index).Ready}
  | [], _ => []
  | _ :: parents, inspected =>
      let following := (requests parents inspected.2).map (fun pending => ⟨pending.val.succ, pending.property⟩)
      match inspected.1.readyDecision with
      | .isTrue _ => following
      | .isFalse pending => ⟨0, pending⟩ :: following

/-- An empty mapped request list has no original pending occurrences. -/
private theorem nil_of_map_nil {α β : Type} (function : α → β) (values : List α)
    (empty : values.map function = []) : values = [] := by
  cases values with
  | nil => rfl
  | cons => cases empty

/-- No pending occurrence means that every original cached box test supplied its own containment certificate. -/
theorem ready_of_requests_empty : (parents : List (CenteredEdge curve differential)) →
    (inspected : Inspection (count := count) parents) → requests parents inspected = [] → Ready parents inspected
  | [], _, _ => True.intro
  | parent :: parents, inspected, empty => by
      let liftRequest
          (pending : {index : Fin parents.length // ¬(entry (parents := parents) inspected.2 index).Ready}) :
          {index : Fin (parent :: parents).length // ¬(inspected.entry index).Ready} :=
        ⟨pending.val.succ, pending.property⟩
      change (match inspected.1.readyDecision with
        | .isTrue _ => (requests parents inspected.2).map liftRequest
        | .isFalse pending => ⟨0, pending⟩ :: (requests parents inspected.2).map liftRequest) = [] at empty
      cases same : inspected.1.readyDecision with
      | isFalse pending => rewrite [same] at empty; cases empty
      | isTrue first =>
          rewrite [same] at empty
          exact ⟨first, ready_of_requests_empty parents inspected.2 (nil_of_map_nil liftRequest _ empty)⟩

/-- Build coverage from the SAME successful original patches and their stored containment proofs.

Only the original covering constructors execute. The supplied inspection
retains every checked neighborhood for later source preparation; no patch,
seed, neighborhood, root or box inspection is rebuilt here.
-/
def coveredOfReady : (parents : List (CenteredEdge curve differential)) →
    (inspected : Inspection (count := count) parents) → Ready parents inspected → CoveredParents count parents
  | [], _, _ => .nil
  | _ :: parents, inspected, ready =>
      .cons inspected.1.patch (inspected.1.inside ready.1) (coveredOfReady parents inspected.2 ready.2)

/-- Coverage retains the exact original acquired patch at each same bounded parent occurrence. -/
theorem coveredOfReady_entry : (parents : List (CenteredEdge curve differential)) →
    (inspected : Inspection (count := count) parents) → (ready : Ready parents inspected) →
    (index : Fin parents.length) →
    ((coveredOfReady parents inspected ready).entry index).val = (inspected.entry index).patch
  | [], _, _, index => Fin.elim0 index
  | _ :: parents, inspected, ready, index =>
      Fin.cases rfl (fun following => coveredOfReady_entry parents inspected.2 ready.2 following) index

/-- A successful resolution contains only coverage derived from those exact already inspected patches. -/
@[expose] def Success {parents : List (CenteredEdge curve differential)}
    (inspected : Inspection (count := count) parents) :=
  {covered : CoveredParents count parents // ∃ ready : Ready parents inspected,
    covered = coveredOfReady parents inspected ready}

/-- All actual local refinement requests accompany their exact ordered enumeration and nonempty stopping reason. -/
@[expose] def Pending {parents : List (CenteredEdge curve differential)}
    (inspected : Inspection (count := count) parents) :=
  {pending : List {index : Fin parents.length // ¬(inspected.entry index).Ready} //
    pending = requests parents inspected ∧ pending ≠ []}

/-- Resolve the complete stored finite attempt into exact original coverage or all actual local refinement requests. -/
@[expose] def Resolution {parents : List (CenteredEdge curve differential)}
    (inspected : Inspection (count := count) parents) :=
  Success inspected ⊕ Pending inspected

/-- Resolve the complete original outcomes, retaining all actual local failures and the unchanged inspected tail. -/
def resolve (parents : List (CenteredEdge curve differential)) (inspected : Inspection (count := count) parents) :
    Resolution inspected :=
  match readyDecision parents inspected with
  | .isTrue ready => .inl ⟨coveredOfReady parents inspected ready, ⟨ready, rfl⟩⟩
  | .isFalse pending =>
      let outstanding := requests parents inspected
      .inr ⟨outstanding, rfl, fun empty => pending (ready_of_requests_empty parents inspected empty)⟩

/-- A successful resolution preserves the whole original inspected patch at every occurrence. -/
theorem Success.entry {parents : List (CenteredEdge curve differential)}
    {inspected : Inspection (count := count) parents}
    (success : Success inspected) (index : Fin parents.length) :
    (success.val.entry index).val = (inspected.entry index).patch := by
  rcases success.property with ⟨ready, same⟩
  exact (congrArg (fun covered : CoveredParents count parents => (covered.entry index).val) same).trans
    (coveredOfReady_entry parents inspected ready index)

end Inspection

/-- The complete original parent list, all stored inspections and their actual finite resolution.

The original list and every attempted patch/neighborhood/outcome remain
runtime data. Both whole construction equations certify the same finite
attempt. Failure requests refinement on those exact local boxes; it
asserts no global pole, divergence or canonical-cycle obstruction.
-/
@[expose] def InspectionAttempt (parents : List (CenteredEdge curve differential)) :=
  (_keptParents : {value : List (CenteredEdge curve differential) // value = parents}) ×
  (inspected : {value : Inspection (count := count) parents // value = Inspection.build parents}) ×
  {resolved : Inspection.Resolution inspected.val // resolved = Inspection.resolve parents inspected.val}

/-- Inspect every original occurrence once, then resolve only those retained outcomes. -/
def inspect (parents : List (CenteredEdge curve differential)) : InspectionAttempt (count := count) parents :=
  let inspected := Inspection.build parents
  let resolved := Inspection.resolve parents inspected
  ⟨⟨parents, rfl⟩, ⟨inspected, rfl⟩, ⟨resolved, rfl⟩⟩

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

end
