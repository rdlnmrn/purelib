module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.RootIsolation.Track.Accelerated
public import Purelib.RootIsolation.Track.Observation
-- Exposed cache append retains the owned structural membership certificate.
public import Purelib.Data.List.Membership
public import Purelib.RootIsolation.Subdivision.WindingOne
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Bounds.AccuracyRadius
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Accelerated numerical sources on original root channels

A paid original cache state initializes a distinct accelerated track with total
subdivision fallback. The original
root owner, payment and elimination cache remain retained beside the new track,
its actual root cache and the computed nested-root comparison. Transport uses
that comparison to present the new samples on the original coherent channel.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Data.List
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Data.Rat.Bounds.AccuracyRadius (accuracyRadius accuracyRadius_pos)

variable {polynomial : GaussianPolynomial} {ambient : Box}

namespace Accelerated

/-- The total dyadic proposal policy with subdivision fallback on the retained initial state. -/
@[expose] def dyadicTrack (input : FTA.Squarefree.Input polynomial)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate polynomial degreeBound)
    (initial : WindingOneState polynomial ambient) : WindingOneTrack polynomial ambient :=
  let clearances := Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider.AxisClearances.canonical elimination
  Track.Accelerated.fromDyadic elimination
    (Subdivision.WindingOne.ofInitial input elimination initial clearances) clearances

/-- The dyadic policy retains its complete supplied initial state. -/
theorem dyadicTrack_initial (input : FTA.Squarefree.Input polynomial)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate polynomial degreeBound)
    (initial : WindingOneState polynomial ambient) : (dyadicTrack input elimination initial).initial = initial :=
  (Track.Accelerated.fromDyadic_initial elimination
    (Subdivision.WindingOne.ofInitial input elimination initial)).trans
      (Subdivision.WindingOne.ofInitial_initial input elimination initial)

/-- Changing only an equal degree index preserves the complete dyadic program. -/
theorem dyadicTrack_castDegree (input : FTA.Squarefree.Input polynomial)
    {left right : Nat} (same : left = right) (elimination : AxisEliminationCertificate polynomial left)
    (initial : WindingOneState polynomial ambient) :
    dyadicTrack input (elimination.castDegree same) initial = dyadicTrack input elimination initial := by
  cases same
  rfl

/-- The cached bound and complete certificate retain the original input's whole dyadic program. -/
theorem dyadicTrack_original (input : FTA.Squarefree.Input polynomial)
    (elimination : Input.Elimination input) (initial : WindingOneState polynomial ambient) :
    dyadicTrack input elimination.certificate initial = dyadicTrack input input.elimination initial :=
  (dyadicTrack_castDegree input elimination.degree_eq elimination.certificate initial).symm.trans
    (congrArg (fun certificate => dyadicTrack input certificate initial) elimination.original_eq)

set_option genInjectivity false in
/-- Exact retained refinements covering a consecutive finite loaded of the same pure root policy.

Each requested index has an actual member with the complete original current
state and the exact positive quarter-schedule request. The length records
executed refinements, not a new bound on supported root indices.
-/
structure RefinementPrefix (track : WindingOneTrack polynomial ambient) (first count : Nat) where
  /-- The actual ordered complete refinement results. -/ entries : List (Track.Observation.CachedRefinement track)
  /-- Exactly the requested number of refinements was retained. -/ length_eq : entries.length = count
  /-- Every requested pure-policy successor has its exact retained current and epsilon. -/
  covers : ∀ index, first ≤ index → index < first + count →
    ∃ entry, entry ∈ entries ∧ entry.current = state track index ∧
      entry.epsilon = accuracyRadius (stepTarget track index)
  /-- The actual final loaded state, ready to seed only a missing suffix. -/
  current : {value : WindingOneState polynomial ambient // value = state track (first + count)}

constructive_injectivity RefinementPrefix

namespace RefinementPrefix

/-- Append a checked suffix while retaining the original complete entries and actual terminal state. -/
@[expose] def append {track : WindingOneTrack polynomial ambient} {first count extra : Nat}
    (loaded : RefinementPrefix track first count) (suffix : RefinementPrefix track (first + count) extra) :
    RefinementPrefix track first (count + extra) where
  entries := loaded.entries ++ suffix.entries
  length_eq := (List.length_append ..).trans (congrArg₂ Nat.add loaded.length_eq suffix.length_eq)
  covers := by
    intro index order bound
    if before : index < first + count then
      obtain ⟨entry, member, currentEq, epsilonEq⟩ := loaded.covers index order before
      exact ⟨entry, Membership.mem_append.mpr (Or.inl member), currentEq, epsilonEq⟩
    else
      have after : first + count ≤ index := Nat.le_of_not_gt before
      have last : index < (first + count) + extra := by
        rewrite [Nat.add_assoc]
        exact bound
      obtain ⟨entry, member, currentEq, epsilonEq⟩ := suffix.covers index after last
      exact ⟨entry, Membership.mem_append.mpr (Or.inr member), currentEq, epsilonEq⟩
  current := ⟨suffix.current.val, suffix.current.property.trans (congrArg (state track) (Nat.add_assoc ..))⟩

/-- Appending a loaded retains its exact original entry list as the left list operand. -/
theorem append_entries {track : WindingOneTrack polynomial ambient} {first count extra : Nat}
    (loaded : RefinementPrefix track first count) (suffix : RefinementPrefix track (first + count) extra) :
    (loaded.append suffix).entries = loaded.entries ++ suffix.entries := rfl

end RefinementPrefix

/-- Retaining checked refinements preserves every complete state of the same total policy.

The proof compares original states pointwise. It does not identify two
refinement functions or claim equality to a different Newton policy.
-/
theorem state_withRefinements (track : WindingOneTrack polynomial ambient)
    (entries : List (Track.Observation.CachedRefinement track)) (index : Nat) :
    state (Track.Observation.withRefinements track entries) index = state track index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change (Track.Observation.withRefinements track entries).refine _ _ _ = track.refine _ _ _
      rewrite [Track.Observation.withRefinements_refine, ih]
      rfl

end Accelerated

set_option genInjectivity false in
/-- A new accelerated root source compared with its retained original owner.

The paid state is an actual positive-index cache read from the original root.
It initializes the new track exactly. The supplied elimination cache is checked
against the same input, and both complete root caches remain comparison owners.
-/
structure Accelerated (input : FTA.Squarefree.Input polynomial)
    (track : WindingOneTrack polynomial ambient) (start : Nat) where
  /-- The complete original coherent root owner. -/
  original : CertifiedName track
  /-- The actual retained positive-index payment on that same original cache. -/
  paid : Refinement original (start + 1)
  /-- The supplied axis-elimination cache for the unchanged polynomial. -/
  elimination : Input.Elimination input
  /-- The actual whole refinements retained for the same dyadic total policy. -/
  refinements : List (Track.Observation.CachedRefinement
    (Accelerated.dyadicTrack input elimination.certificate paid.current))
  /-- The distinct total track with dyadic shortcuts and finite subdivision fallback. -/
  numericalTrack : WindingOneTrack polynomial ambient
  /-- The new track consumes that same retained payment and elimination cache. -/
  numericalTrack_eq : numericalTrack =
    Track.Observation.withRefinements (Accelerated.dyadicTrack input elimination.certificate paid.current) refinements
  /-- The actual retained root cache of the new numerical track. -/
  root : CertifiedName numericalTrack
  /-- The new cache is the certified construction on that same new track. -/
  root_eq : root = certifiedName numericalTrack original.degreePositive
  /-- The paid initial box lies strictly inside the original owner's initial box. -/
  nested : numericalTrack.initial.box.StrictInterior track.initial.box
  /-- The computed comparison between the original and new root channels. -/
  comparison : Equivalence.NamedEquivalent original.value.name root.value.name
  /-- The retained comparison consumes those same two owners and their strict nesting. -/
  comparison_eq : comparison = original.equivalent_nested input root nested

constructive_injectivity Accelerated

namespace Accelerated

variable {input : FTA.Squarefree.Input polynomial}
variable {track : WindingOneTrack polynomial ambient} {start : Nat}

/-- Use one paid original state as the initial state of a new accelerated source.

The original payment and supplied checked elimination cache are consumed
without another cache search or elimination construction. Subdivision supplies
the total fallback at every step. Positive paid index
proves strict original-owner nesting; the existing comparison computes both
index schedules rather than assuming a desired sample-distance inequality.
-/
@[expose] def ofRefinement (input : FTA.Squarefree.Input polynomial)
    (original : CertifiedName track) (start : Nat)
    (paid : Refinement original (start + 1))
    (elimination : Input.Elimination input)
    (refinements : List (Track.Observation.CachedRefinement
      (dyadicTrack input elimination.certificate paid.current)) := []) :
    Accelerated input track start :=
  let numericalTrack := Track.Observation.withRefinements
    (dyadicTrack input elimination.certificate paid.current) refinements
  let root := certifiedName numericalTrack original.degreePositive
  have nested : numericalTrack.initial.box.StrictInterior track.initial.box := by
    have positiveIndex : 0 < paid.index := (Nat.zero_lt_succ start).trans_le paid.index_ge
    have firstStrict : (state track 1).box.StrictInterior track.initial.box :=
      track.strict track.initial (accuracyRadius (stepTarget track 0))
        (accuracyRadius_pos (stepTarget_positive track 0))
    have contained := (Box.Refinement.StrictInterior.of_refines firstStrict)
      (state_refines_of_le track positiveIndex)
    change paid.current.box.StrictInterior track.initial.box
    rewrite [paid.current_eq, original.stateAt_eq]
    exact contained
  let comparison := original.equivalent_nested input root nested
  { original := original
    paid := paid
    elimination := elimination
    refinements := refinements
    numericalTrack := numericalTrack
    numericalTrack_eq := rfl
    root := root
    root_eq := rfl
    nested := nested
    comparison := comparison
    comparison_eq := rfl }

/-- The constructor retains the complete supplied original root owner. -/
theorem ofRefinement_original (input : FTA.Squarefree.Input polynomial)
    (original : CertifiedName track) (start : Nat)
    (paid : Refinement original (start + 1))
    (elimination : Input.Elimination input) :
    (ofRefinement input original start paid elimination).original = original := rfl

/-- The constructor retains the complete original payment, request and cache read. -/
theorem ofRefinement_paid (input : FTA.Squarefree.Input polynomial)
    (original : CertifiedName track) (start : Nat)
    (paid : Refinement original (start + 1))
    (elimination : Input.Elimination input) :
    (ofRefinement input original start paid elimination).paid = paid := rfl

/-- The constructor retains the exact supplied elimination cache. -/
theorem ofRefinement_elimination (input : FTA.Squarefree.Input polynomial)
    (original : CertifiedName track) (start : Nat)
    (paid : Refinement original (start + 1))
    (elimination : Input.Elimination input) :
    (ofRefinement input original start paid elimination).elimination = elimination := rfl

/-- The new numerical track begins at the exact retained original paid state. -/
theorem initial_eq (prepared : Accelerated input track start) :
    prepared.numericalTrack.initial = prepared.paid.current := by
  rewrite [prepared.numericalTrack_eq]
  rfl

/-- Attach the new root construction to the original channel through its same retained comparison.

The existing root sidecar retains the new track and actual cache. Its transport
retains that numerical program and the explicit comparison to the original
owner, independently of the old track's later states or checkpoint equations.
-/
@[expose] def algebraic (prepared : Accelerated input track start) :
    Algebraic.Sidecar prepared.original.value :=
  let sidecar := Algebraic.Sidecar.ofRoot
    (PolynomialRoot.Sidecar.ofIsolated prepared.root input.toPositive)
  sidecar.transport prepared.comparison

/-- The transported algebraic sidecar retains the unchanged original polynomial. -/
theorem algebraic_polynomial (prepared : Accelerated input track start) :
    prepared.algebraic.polynomial = polynomial := by
  unfold algebraic
  change (Algebraic.Sidecar.ofRoot
    (PolynomialRoot.Sidecar.ofIsolated prepared.root input.toPositive)).polynomial = polynomial
  rewrite [Algebraic.Sidecar.ofRoot_polynomial]
  exact PolynomialRoot.Sidecar.ofIsolated_residual_polynomial prepared.root input.toPositive

/-- The transported algebraic sidecar reads the same actual new root cache at every index. -/
theorem algebraic_sample (prepared : Accelerated input track start) (index : Nat) :
    prepared.algebraic.residual.source.sample index = prepared.root.approximation.sample index := by
  unfold algebraic
  rewrite [Algebraic.Sidecar.transport_sample]
  exact (Algebraic.Sidecar.ofRoot_sample _ index).trans
    (PolynomialRoot.Sidecar.ofIsolated_residual_sample prepared.root input.toPositive index)

/-- The algebraic origin retains the actual new root and the same original-to-new comparison. -/
theorem algebraic_origin (prepared : Accelerated input track start) :
    prepared.algebraic.origin =
      .transport (.root (PolynomialRoot.Sidecar.ofIsolated prepared.root input.toPositive))
        prepared.comparison := rfl

set_option genInjectivity false in
/-- A loaded dyadic root compared with the same original initial owner.

The actual original certificate remains a field beside the retained
elimination and complete refinement cache. The numerical root consumes that
cache through the same total policy. Its computed initial-box comparison
requires no positive-index payment from the old track.
-/
structure Initial (input : FTA.Squarefree.Input polynomial) (track : WindingOneTrack polynomial ambient) where
  /-- The actual original coherent root owner. -/ original : CertifiedName track
  /-- The retained elimination cache for the same polynomial. -/
  elimination : Input.Elimination input
  /-- The largest successor index loaded before numerical root consumers run. -/ last : Nat
  /-- The new positive state required by the comparison belongs to this loaded loaded. -/ first_covered : 1 ≤ last
  /-- The complete actual refinement loaded, with exact request coverage. -/
  loaded : RefinementPrefix (dyadicTrack input elimination.certificate track.initial) 0 last
  /-- The root cache uses the same initial owner and every retained checked refinement. -/
  root : CertifiedName (Track.Observation.withRefinements
    (dyadicTrack input elimination.certificate track.initial) loaded.entries)
  /-- The computed comparison retains both the original and loaded numerical channels. -/
  comparison : Equivalence.NamedEquivalent original.value.name root.value.name
  /-- The same-initial comparison pays only the retained new numerical source. -/
  comparison_eq : comparison = original.equivalent_initial input root rfl

constructive_injectivity Initial

namespace Initial

/-- The actual loaded numerical track, including its finite whole-refinement cache. -/
@[expose] def numericalTrack (prepared : Initial input track) : WindingOneTrack polynomial ambient :=
  Track.Observation.withRefinements
    (dyadicTrack input prepared.elimination.certificate track.initial) prepared.loaded.entries

/-- Loaded execution retains the complete original initial state literally. -/
theorem initial_eq (prepared : Initial input track) : prepared.numericalTrack.initial = track.initial := by
  unfold numericalTrack
  exact (Track.Observation.withRefinements_initial _ _).trans
    (dyadicTrack_initial input prepared.elimination.certificate track.initial)

/-- Every loaded-track refinement follows exactly the same dyadic total policy at the full original request. -/
theorem refine_eq (prepared : Initial input track) (current : WindingOneState polynomial ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    prepared.numericalTrack.refine current epsilon positive =
      (Track.Accelerated.dyadicRefinement prepared.elimination.certificate
        (Subdivision.WindingOne.ofInitial input prepared.elimination.certificate current)
        current epsilon positive).state :=
  Track.Observation.withRefinements_refine _ _ current epsilon positive

/-- Every loaded numerical state is the complete same-index state of the pure dyadic policy. -/
theorem stateAt_eq (prepared : Initial input track) (index : Nat) :
    prepared.root.stateAt index = state (dyadicTrack input prepared.elimination.certificate track.initial) index :=
  (prepared.root.stateAt_eq index).trans (state_withRefinements _ _ index)

/-- Loaded samples retain the exact same-index anchor of the pure dyadic policy. -/
theorem sample_eq (prepared : Initial input track) (index : Nat) :
    prepared.root.approximation.sample index =
      (state (dyadicTrack input prepared.elimination.certificate track.initial) index).box.anchor :=
  (prepared.root.sample_stateAt index).trans
    (congrArg (fun current : WindingOneState polynomial ambient => current.box.anchor) (prepared.stateAt_eq index))

/-- Refinement planning reads the unchanged initial scale without evaluating a positive root state. -/
theorem refineIndex_eq (prepared : Initial input track) (start : Nat) (target : Coordinate)
    (positive : 0 < target) :
    prepared.root.approximation.refineIndex start target positive =
      (certifiedName (dyadicTrack input prepared.elimination.certificate track.initial)
        input.degreePositive).approximation.refineIndex start target positive := by
  rewrite [prepared.root.approximation_cache]
  rfl

/-- Transport the loaded root samples onto the same retained original coherent channel. -/
@[expose] def algebraic (prepared : Initial input track) : Algebraic.Sidecar prepared.original.value :=
  (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated prepared.root input.toPositive)).transport
    prepared.comparison

/-- The transported loaded source retains the unchanged defining polynomial. -/
theorem algebraic_polynomial (prepared : Initial input track) : prepared.algebraic.polynomial = polynomial := by
  unfold algebraic
  change (Algebraic.Sidecar.ofRoot
    (PolynomialRoot.Sidecar.ofIsolated prepared.root input.toPositive)).polynomial = polynomial
  rewrite [Algebraic.Sidecar.ofRoot_polynomial]
  exact PolynomialRoot.Sidecar.ofIsolated_residual_polynomial prepared.root input.toPositive

/-- The transported source reads the same loaded numerical root cache. -/
theorem algebraic_sample (prepared : Initial input track) (index : Nat) :
    prepared.algebraic.residual.source.sample index = prepared.root.approximation.sample index := by
  unfold algebraic
  rewrite [Algebraic.Sidecar.transport_sample]
  exact (Algebraic.Sidecar.ofRoot_sample _ index).trans
    (PolynomialRoot.Sidecar.ofIsolated_residual_sample prepared.root input.toPositive index)

/-- The transport origin retains the actual loaded root and its original-owner comparison. -/
theorem algebraic_origin (prepared : Initial input track) :
    prepared.algebraic.origin =
      .transport (.root (PolynomialRoot.Sidecar.ofIsolated prepared.root input.toPositive)) prepared.comparison := rfl

end Initial

/-- Attach checked dyadic refinements before computing the original-to-new same-initial comparison.

The original owner is retained unchanged. The new root's cache uses actual
loaded results even outside its finite thunk loaded, and its total fallback
continues to support every positive request on an exact cache miss.
-/
@[expose] def fromInitial (input : FTA.Squarefree.Input polynomial) (original : CertifiedName track)
    (elimination : Input.Elimination input)
    (last : Nat) (firstCovered : 1 ≤ last)
    (loaded : RefinementPrefix (dyadicTrack input elimination.certificate track.initial) 0 last) :
    Initial input track :=
  let numericalTrack := Track.Observation.withRefinements
    (dyadicTrack input elimination.certificate track.initial) loaded.entries
  let root := certifiedName numericalTrack original.degreePositive
  { original := original
    elimination := elimination
    last := last
    first_covered := firstCovered
    loaded := loaded
    root := root
    comparison := original.equivalent_initial input root rfl
    comparison_eq := rfl }

/-- The same-initial attachment retains the exact original root owner. -/
theorem fromInitial_original (input : FTA.Squarefree.Input polynomial) (original : CertifiedName track)
    (elimination : Input.Elimination input)
    (last : Nat) (firstCovered : 1 ≤ last)
    (loaded : RefinementPrefix (dyadicTrack input elimination.certificate track.initial) 0 last) :
    (fromInitial input original elimination last firstCovered loaded).original = original := rfl

end Accelerated

end Purelib.Riemann.RootContinuation.CoherentRoot

end
