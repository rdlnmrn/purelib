module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Approximation
import Purelib.Approximation.Gaussian.Sequence.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
public import Purelib.Algebra.Ring.Normalization
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Search
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat.Bounds

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Geometric

/-!
# Coherent names from deterministic shrinking root tracks

The raw box bridge exposes a productive arithmetic cursor, but its process
state type also contains unrelated winding boxes.  Here we instead follow one
explicit recursive refinement chain.  Its anchors form a finite progressive
approximation because every later box refines every earlier box and its
diagonal is bounded by an explicit quarter-geometric allowance.  This yields
a genuine coherent CCL name without selecting a completed root.
-/

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Algebra.Ring

section
open Purelib.Data
/-- The rational scalar type for root error and residual bounds. -/
public abbrev Coordinate := Rat.Fraction.Rational
/-- The executable Gaussian rational sample type. -/
public abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Polynomial in
/-- The dense Gaussian polynomial type defining the root equation. -/
public abbrev GaussianPolynomial :=
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Geometry in
/-- The rational box type retaining the root track's enclosure. -/
public abbrev Box := Rational.Box
section
open Purelib.RootIsolation
/-- A certified winding-one root state inside its original ambient box. -/
public abbrev WindingOneState := State.WindingOne.Basic.WindingOneState
/-- The retained deterministic refinement track for one winding-one root state. -/
public abbrev WindingOneTrack := Track.Basic.WindingOneTrack
end

section
open Purelib.Approximation
/-- Finite Gaussian samples with explicit refinement and geometric error bounds. -/
public abbrev Approximation := Gaussian.Sequence.ApproximationData
/-- The coherent arithmetic CCL name type for the resulting approximation. -/
public abbrev CoherentNamed := Gaussian.Name.Coherent.CoherentNamed

end

/-- The initial root box's squared diagonal, used as the geometric error scale.

The original initial box supplies its squared diagonal. That same retained
quantity is the scalar factor in every quarter-geometric target. -/
@[expose] public def scale {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Coordinate :=
  track.initial.box.diagonalSq

open Purelib.Data in
/-- The initial proper box has strictly positive squared diagonal.

The retained initial box is proper, so its horizontal width square is
positive and its vertical width square nonnegative. Their original sum
therefore has a positive rational bound. -/
public theorem scale_positive {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : 0 < scale track := by
  rewrite [scale, Geometry.Rational.Box.diagonalSq_eq_original]
  have widthPositive : 0 < track.initial.box.widthX :=
    Arithmetic.sub_pos_direct track.initial.proper.1
  have widthSquarePositive : 0 < track.initial.box.widthX ^ 2 :=
    Arithmetic.pow_pos_direct widthPositive 2
  have heightSquareNonnegative :
      0 <= track.initial.box.widthY ^ 2 :=
    Arithmetic.sq_nonneg_direct _
  constructor
  · have sumNonnegative :=
      Arithmetic.add_le_add_direct
        (Arithmetic.le_of_lt_direct widthSquarePositive)
        heightSquareNonnegative
    have zeroIdentity : (0 : Coordinate) + 0 = 0 := by ring1
    rwa [zeroIdentity] at sumNonnegative
  · intro sumNonpositive
    apply widthSquarePositive.2
    have widthLeSum :=
      Arithmetic.add_le_add_direct (first :=
          track.initial.box.widthX ^ 2)
        (second := track.initial.box.widthX ^ 2) (third := 0)
        (fourth := track.initial.box.widthY ^ 2) le_rfl
        heightSquareNonnegative
    have widthIdentity :
        track.initial.box.widthX ^ 2 + (0 : Coordinate) =
          track.initial.box.widthX ^ 2 := by ring1
    rw [widthIdentity] at widthLeSum
    exact Basic.Compatibility.le_trans
      (track.initial.box.widthX ^ 2)
      (track.initial.box.widthX ^ 2 + track.initial.box.widthY ^ 2) 0
      widthLeSum sumNonpositive

section
open Purelib.Approximation
/-- The quarter-geometric error target assigned to the next recursive refinement.

The same initial diagonal scale is used at the successor index. This
retained quarter-geometric target determines the next refinement request. -/
@[expose] public def stepTarget {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) : Coordinate :=
  Basic.quarterRadius (scale track) (index + 1)

/-- Every recursive refinement target is strictly positive.

The retained initial diagonal scale is positive. Its original
quarter-geometric value at the successor index remains positive. -/
public theorem stepTarget_positive {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    0 < stepTarget track index :=
  Basic.quarterRadius_pos (scale_positive track) (index + 1)

end

section
open Purelib.Data
/-- The explicit recursive sequence of refined winding-one root states.

Start from the track's initial state and refine each predecessor using the corresponding positive accuracy radius. Every
state retains the original polynomial and ambient box. -/
@[expose] public def state {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Nat ->
      WindingOneState polynomial ambient
  | 0 => track.initial
  | index + 1 =>
      track.refine (state track index)
        (AccuracyRadius.accuracyRadius (stepTarget track index))
        (AccuracyRadius.accuracyRadius_pos
          (stepTarget_positive track index))

/-- Each successive root box refines its immediate predecessor.

The next state uses the original track refinement at the retained
accuracy radius. The track's nesting certificate links its exact box
to the same predecessor state. -/
public theorem state_succ_refines {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    (state track (index + 1)).box.Refines (state track index).box := by
  exact track.nested (state track index)
    (AccuracyRadius.accuracyRadius (stepTarget track index))
    (AccuracyRadius.accuracyRadius_pos
      (stepTarget_positive track index))

end

open Purelib.Geometry in
open Purelib.Data.Nat in
/-- A later root box refines every earlier box in the same deterministic track.

The supplied natural index ordering retains the original earlier and
later states. Their explicit difference counts successive refinements;
transitivity composes those exact box-nesting witnesses. -/
public theorem state_refines_of_le {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) {earlier later : Nat}
    (order : earlier <= later) :
    (state track later).box.Refines (state track earlier).box := by
  obtain ⟨extra, rfl⟩ : ∃ extra, later = earlier + extra :=
    ⟨later - earlier, (Subtraction.add_sub_of_le order).symm⟩
  clear order
  induction extra with
  | zero =>
      simpa only [Nat.add_zero] using
        Rational.Box.refines_refl (state track earlier).box
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact (state_succ_refines track (earlier + extra)).trans
        inductionHypothesis

open Purelib.Approximation in
open Purelib.Data in
/-- Each root box's squared diagonal is bounded by its quarter-geometric target.

The original initial box gives the zeroth bound. At a successor, the
track's accuracy certificate and the same retained accuracy-radius
square bound give the corresponding quarter-geometric target. -/
public theorem state_diagonal_le {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    (state track index).box.diagonalSq <=
      Basic.quarterRadius (scale track) index := by
  cases index with
  | zero =>
      change track.initial.box.diagonalSq <=
        Basic.quarterRadius track.initial.box.diagonalSq 0
      unfold Basic.quarterRadius
      rw [pow_zero]
      have divideOne : track.initial.box.diagonalSq / 1 =
          track.initial.box.diagonalSq := by
        apply Rat.Fraction.Field.mul_right_cancel_of_ne
          (show (1 : Coordinate) ≠ 0 by decide)
        calc
          (track.initial.box.diagonalSq / 1) * 1 =
              track.initial.box.diagonalSq :=
            Rat.Fraction.Field.div_mul_cancel_of_ne _ 1 (by decide)
          _ = track.initial.box.diagonalSq * 1 :=
            (Rat.Fraction.Field.mul_one_direct _).symm
      rw [divideOne]
  | succ index =>
      have accurate := track.accurate (state track index)
        (AccuracyRadius.accuracyRadius (stepTarget track index))
        (AccuracyRadius.accuracyRadius_pos
          (stepTarget_positive track index))
      have targetBound := AccuracyRadius.accuracyRadius_sq_lt
        (stepTarget_positive track index)
      exact accurate.trans targetBound.le

namespace StateCache

set_option genInjectivity false in
/-- A finite cache entry tied to the exact deterministic root state.

Its thunk is retained for reuse by the successor and repeated sample lookups, with an equality identifying the returned
state at the stored index. -/
public structure Entry {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) where
  /-- The natural index of the cached deterministic state. -/ index : Nat
  /-- The shared thunk retaining the root state computation. -/ value : Thunk (WindingOneState polynomial ambient)
  /-- The thunk returns the exact original root state at the retained index. -/ value_eq : value.get = state track index

constructive_injectivity Entry

/-- Cache the initial root state as the first shared thunk.

The original initial state is retained in a thunk at index zero. The
state equality certifies the same track and nominal initial state. -/
@[expose] public def first {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Entry track :=
  ⟨0, ⟨fun _ => track.initial⟩, rfl⟩

open Purelib.Data in
/-- Retain a checked complete original state as an actual stored cache entry.

The supplied equality identifies every original state field at that same
track and index. The thunk returns this literal retained state, so later
reads consume the completed data rather than repeat its original refinement.
-/
public def Entry.ofState {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat)
    (retained : WindingOneState polynomial ambient) (same : retained = state track index) : Entry track :=
  ⟨index, ⟨fun _ => retained⟩, same⟩

/-- A checked state cache entry retains its original index exactly. -/
public theorem Entry.ofState_index {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat)
    (retained : WindingOneState polynomial ambient) (same : retained = state track index) :
    (Entry.ofState track index retained same).index = index := by
  unfold Entry.ofState
  rfl

/-- Reading a checked state cache entry returns the literal supplied complete state. -/
public theorem Entry.ofState_get {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat)
    (retained : WindingOneState polynomial ambient) (same : retained = state track index) :
    (Entry.ofState track index retained same).value.get = retained := by
  unfold Entry.ofState
  rfl

/-- Build the next original entry, optionally consuming a checked retained state at that exact next index.

The thunk keeps the original predecessor and total refinement on a cache
miss. A successful ordered lookup reads the supplied entry's literal stored
state. Neither lookup nor refinement is forced while constructing the thunk;
the original index and complete deterministic state equation are preserved.
-/
@[expose] public def Entry.next {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (entry : Entry track)
    (cached : Option (List (Entry track)) := none) : Entry track where
  index := entry.index + 1
  value := ⟨fun _ =>
    match cached.bind (fun entries => entries.find? (fun candidate => decide (candidate.index = entry.index + 1))) with
    | none => track.refine entry.value.get
        (AccuracyRadius.accuracyRadius (stepTarget track entry.index))
        (AccuracyRadius.accuracyRadius_pos (stepTarget_positive track entry.index))
    | some retained => retained.value.get⟩
  value_eq := by
    cases cached with
    | none =>
        change track.refine entry.value.get _ _ = state track (entry.index + 1)
        rw [state, entry.value_eq]
    | some entries =>
        cases found : entries.find? (fun candidate => decide (candidate.index = entry.index + 1)) with
        | none =>
            change (match entries.find? (fun candidate => decide (candidate.index = entry.index + 1)) with
              | none => track.refine entry.value.get _ _
              | some retained => retained.value.get) = state track (entry.index + 1)
            rewrite [found]
            rw [state, entry.value_eq]
        | some retained =>
            have accepted := Purelib.Data.List.Search.find?_eq_some_accepts_certificate found
            have index := of_decide_eq_true accepted
            change (match entries.find? (fun candidate => decide (candidate.index = entry.index + 1)) with
              | none => track.refine entry.value.get _ _
              | some retained => retained.value.get) = state track (entry.index + 1)
            rewrite [found]
            exact retained.value_eq.trans (congrArg (state track) index)

/-- A successful ordered successor lookup consumes the literal retained complete state.

The lookup remains inside the original lazy thunk. Once that thunk is read,
the supplied successful first match is returned directly; neither its
predecessor nor the original refinement is evaluated on this branch.
-/
public theorem Entry.next_get_of_find {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (entry : Entry track)
    (entries : List (Entry track)) (retained : Entry track)
    (found : entries.find? (fun candidate => decide (candidate.index = entry.index + 1)) = some retained) :
    (entry.next (some entries)).value.get = retained.value.get := by
  change (match entries.find? (fun candidate => decide (candidate.index = entry.index + 1)) with
    | none => track.refine entry.value.get _ _
    | some retained => retained.value.get) = retained.value.get
  rewrite [found]
  rfl

/-- The absent cache retains the whole previous lazy successor entry and original refinement operation. -/
public theorem Entry.next_none {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (entry : Entry track) :
    entry.next none =
      { index := entry.index + 1
        value := ⟨fun _ => track.refine entry.value.get
          (AccuracyRadius.accuracyRadius (stepTarget track entry.index))
          (AccuracyRadius.accuracyRadius_pos (stepTarget_positive track entry.index))⟩
        value_eq := by
          change track.refine entry.value.get _ _ = state track (entry.index + 1)
          rw [state, entry.value_eq] } := rfl

/-- Any checked retained bank preserves the whole original successor thunk, index and specification.

The successor thunk is constant in its Unit argument. The scalar original
state equation therefore transports its complete function by congrArg;
no function extensionality or reading-only owner identification is needed.
-/
public theorem Entry.next_cached_eq_default {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (entry : Entry track) (cached : Option (List (Entry track))) :
    entry.next cached = entry.next none := by
  have scalar := (entry.next cached).value_eq.trans (entry.next none).value_eq.symm
  have values : (entry.next cached).value = (entry.next none).value := by
    change (⟨fun _ => (entry.next cached).value.get⟩ : Thunk (WindingOneState polynomial ambient)) =
      (⟨fun _ => (entry.next none).value.get⟩ : Thunk (WindingOneState polynomial ambient))
    exact congrArg (fun value : WindingOneState polynomial ambient => (⟨fun _ => value⟩ : Thunk _)) scalar
  cases left : entry.next cached with
  | mk leftIndex leftValue leftEq =>
      cases right : entry.next none with
      | mk rightIndex rightValue rightEq =>
          have indices : leftIndex = rightIndex :=
            (congrArg Entry.index left).symm.trans (congrArg Entry.index right)
          rewrite [left, right] at values
          exact (Entry.mk.injEq leftIndex leftValue leftEq rightIndex rightValue rightEq).mpr ⟨indices, values⟩

/-- Construct a finite prefix of shared root-state thunks.

Building the list does not execute root refinements; each successor retains its predecessor's thunk and exact state
equality. -/
@[expose] public def buildPrefix {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (count : Nat) (entry : Entry track)
    (cached : Option (List (Entry track)) := none) : List (Entry track) :=
  match count with
  | 0 => []
  | count + 1 => entry :: buildPrefix count (entry.next cached) cached

/-- Every checked retained bank preserves the entire original ordered thunk prefix.

The original first entry remains literal. Each successor consumes the same
retained bank and retains its whole default-entry equality; structural list
congruence preserves every original index, thunk and suffix in order.
-/
public theorem buildPrefix_cached_eq_default {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (count : Nat) (entry : Entry track)
    (cached : Option (List (Entry track))) : buildPrefix count entry cached = buildPrefix count entry none := by
  induction count generalizing entry with
  | zero => rfl
  | succ count inductionHypothesis =>
      change entry :: buildPrefix count (entry.next cached) cached =
        entry :: buildPrefix count (entry.next none) none
      have tail := (inductionHypothesis (entry.next cached)).trans
        (congrArg (fun first => buildPrefix count first none) (entry.next_cached_eq_default cached))
      exact congrArg (List.cons entry) tail

/-- The finite thunk prefix has exactly the requested length.

Each positive count adds the original retained entry and recursively
builds its successor prefix. Structural induction counts those entries
without executing the retained state thunks. -/
@[simp] public theorem prefix_length {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (count : Nat) (entry : Entry track) :
    (buildPrefix count entry).length = count := by
  induction count generalizing entry with
  | zero => rfl
  | succ count ih =>
      change Nat.succ ((buildPrefix count entry.next).length) = Nat.succ count
      exact congrArg Nat.succ (ih entry.next)

/-- Read a matching retained thunk or compute the original state on a cache miss.

The finite cache controls execution reuse only; every natural sample index remains supported by the original total
calculation. -/
@[expose] public def read {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    List (Entry track) → WindingOneState polynomial ambient
  | [] => state track index
  | entry :: remaining =>
      if entry.index = index then entry.value.get else read track index remaining

/-- Every cache read equals the original deterministic state at the requested index.

A matching retained entry returns the state at its stored equal index.
On a miss, structural recursion reads the same remaining cache; the
empty-cache branch runs the original total state calculation. -/
public theorem read_eq {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) (entries : List (Entry track)) :
    read track index entries = state track index := by
  induction entries with
  | nil => rfl
  | cons entry remaining ih =>
      simp only [read]
      split
      · rename_i equal
        exact entry.value_eq.trans (congrArg (state track) equal)
      · exact ih

section
open Purelib.Approximation

/-- Build an anchor approximation using the actual retained original root-state cache.

Every sample reads the supplied original cache. Its entries retain their
original-track state equations; a cache miss uses the same total track
calculation. The geometric refinement and error guarantees are unchanged.
-/
@[expose] public def approximation {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (cache : List (Entry track)) : Approximation :=
  { sample := fun index => (read track index cache).box.anchor
    radiusSq := fun index =>
      Basic.quarterRadius (scale track) index
    radiusSq_nonneg := fun index =>
      Basic.quarterRadius_nonneg
        (scale_positive track).le index
    later_close := by
      intro earlier later order
      simpa only [read_eq] using
        ((state track earlier).box.normSq_sub_le_diagonalSq
          ((state_refines_of_le track order).contains
            (state track later).box.contains_anchor)
          (state track earlier).box.contains_anchor).trans
            (state_diagonal_le track earlier)
    refineIndex := fun current target _ =>
      Search.firstQuarterBelow (scale track) current target
    refineIndex_ge := fun current target _ =>
      Search.firstQuarterBelow_ge (scale track) current target
    refineIndex_accurate := fun current target positive =>
      Search.firstQuarterBelow_accurate (scale track)
        (scale_positive track).le current target positive
    centerBound := ambient.normSqBound
    centerBound_nonneg := ambient.normSqBound_nonneg
    sample_bounded := by
      intro index
      simpa only [read_eq] using ambient.normSq_le_normSqBound
        ((state track index).refinesAmbient.contains
          (state track index).box.contains_anchor) }

end

end StateCache

section
open Purelib.Approximation
/-- Construct the anchor approximation with its explicit geometric squared-error bound.

A shared 64-entry thunk prefix reuses refinement work. The retained boxes certify later-sample closeness and ambient
bounds, and finite quarter-radius search supplies refinement indices. -/
@[expose] public def approximation {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Approximation :=
  let cache := StateCache.buildPrefix 64 (StateCache.first track)
  StateCache.approximation track cache

/-- Convert the deterministic root-track approximation to a coherent arithmetic CCL name.

The original approximation, including its retained shared thunk cache,
is passed to the existing coherent-name construction. No completed
root or replacement sample sequence is selected. -/
@[expose] public def named {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : CoherentNamed :=
  Gaussian.Name.Coherent.CoherentNamed.ofApproximation
    (approximation track)

end

/-- Each approximation sample is the anchor of the root box at that exact index.

Every retained cache entry identifies the original state at its index,
and a miss evaluates that same total state program. Taking the box
anchor therefore preserves the displayed sample exactly. -/
@[simp] public theorem approximation_sample {polynomial : GaussianPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    (index : Nat) :
    (approximation track).sample index = (state track index).box.anchor := by
  change (StateCache.read track index _).box.anchor = _
  rw [StateCache.read_eq]

section
open Purelib.Polynomial
/-- Every state retains quadrupled boundary winding four for the original polynomial.

Every original state retains its winding-one certificate for the same
polynomial and box. Its raw quadrupled winding is consequently four
at every natural state index. -/
public theorem state_winding {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    Winding.Box.Basic.quadrupledBoxWinding polynomial (state track index).box = 4 :=
  (state track index).rawWindingFour

/-- Multiply the coefficient-computed ambient Lipschitz bound by the initial squared diagonal.

The original ambient Lipschitz bound multiplies the initial squared
diagonal scale. Those same polynomial and box observations determine
the retained quarter-geometric residual allowance. -/
@[expose] public def residualScale (polynomial : GaussianPolynomial) (ambient : Box)
    (track : WindingOneTrack polynomial ambient) : Coordinate :=
  Box.denseLipschitzBound polynomial ambient * scale track

end

open Purelib.Data in
open Purelib.Polynomial in
/-- The geometric polynomial-residual scale is nonnegative.

Both the original ambient Lipschitz bound and initial diagonal scale
are positive. Their original rational product is therefore nonnegative. -/
public theorem residualScale_nonneg (polynomial : GaussianPolynomial) (ambient : Box)
    (track : WindingOneTrack polynomial ambient) :
    0 <= residualScale polynomial ambient track :=
  Arithmetic.mul_nonneg_direct
    (Box.denseLipschitzBound_pos polynomial ambient).le
    (scale_positive track).le

open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Every finite anchor sample has a geometrically shrinking polynomial residual.

For a positive-degree polynomial, retained winding and nested-box certificates bound the sample's evaluation quadrance
by the ambient residual scale times quarter-geometric decay. -/
public theorem sample_residual_le {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient)
    (degreePositive : 0 < polynomial.natDegree) (index : Nat) :
    Gaussian.Norm.Basic.normSq
        (polynomial.eval ((approximation track).sample index)) <=
      Basic.quarterRadius
        (residualScale polynomial ambient track) index := by
  have residual :=
    Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      polynomial degreePositive (state track index).refinesAmbient
      (state track index).proper (by
        rw [(state track index).rawWindingFour]
        decide)
  have scaledDiagonal :
      Box.denseLipschitzBound polynomial ambient *
          (state track index).box.diagonalSq <=
        Box.denseLipschitzBound polynomial ambient *
          Basic.quarterRadius (scale track) index :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (state_diagonal_le track index)
      (Box.denseLipschitzBound_pos
        polynomial ambient).le
  calc
    Gaussian.Norm.Basic.normSq
        (polynomial.eval ((approximation track).sample index)) <=
        Box.Residual.anchorResidualBound polynomial ambient
          (state track index).box := by
      simpa only [approximation_sample] using residual
    _ <= Box.denseLipschitzBound polynomial ambient *
          Basic.quarterRadius (scale track) index :=
      scaledDiagonal
    _ = Basic.quarterRadius
          (residualScale polynomial ambient track) index := by
      rw [Basic.quarterRadius_eq_mul_pow,
        Basic.quarterRadius_eq_mul_pow]
      unfold residualScale
      ring1

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational

open Purelib.Approximation in
open Purelib.Data in
set_option genInjectivity false in
/-- A coherent root name with its exact track identity and finite residual certificate.

The positive degree and pointwise geometric evaluation bound certify the displayed samples without selecting a completed
root. -/
public structure CertifiedName {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) where
  /-- The actual shared original root-state thunk prefix consumed by the approximation. -/
  stateCache : List (StateCache.Entry track)
  /-- The retained prefix is the original deterministic 64-entry cache construction. -/
  stateCache_eq : stateCache = StateCache.buildPrefix 64 (StateCache.first track)
  /-- The actual retained anchor approximation and its shared root-state cache. -/
  approximation : Approximation
  /-- The approximation reads the same actual retained original state cache. -/
  approximation_cache : approximation = StateCache.approximation track stateCache
  /-- The retained approximation is the original deterministic root-track construction. -/
  approximation_eq : approximation = CoherentRoot.approximation track
  /-- The retained coherent arithmetic name. -/ value : CoherentNamed
  /-- The original name consumes this exact retained approximation. -/
  value_approximation : value = CoherentNamed.ofApproximation approximation
  /-- The retained name is exactly the name built from this root track. -/ value_eq : value = named track
  /-- The defining polynomial has strictly positive natural degree. -/ degreePositive : 0 < polynomial.natDegree
  /-- Every finite sample satisfies the displayed quarter-geometric polynomial-residual bound. -/ residual : forall
    index,
    Gaussian.Norm.Basic.normSq
        (polynomial.eval ((CoherentRoot.approximation track).sample index)) <=
      Geometric.Basic.quarterRadius
        (residualScale polynomial ambient track) index

constructive_injectivity CertifiedName

/-- Construct the complete original root from a retained whole-identical cache prefix.

The exact prefix equality transports the original approximation and coherent
name records. All stored fields consume that same actual cache, with the
original positive degree and pointwise residual certificate retained. -/
@[expose] public def CertifiedName.ofCache {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (degreePositive : 0 < polynomial.natDegree)
    (cached : {entries : List (StateCache.Entry track) //
      entries = StateCache.buildPrefix 64 (StateCache.first track)}) : CertifiedName track :=
  let retained := StateCache.approximation track cached.val
  have approximationEq : retained = CoherentRoot.approximation track :=
    congrArg (StateCache.approximation track) cached.property
  { stateCache := cached.val
    stateCache_eq := cached.property
    approximation := retained
    approximation_cache := rfl
    approximation_eq := approximationEq
    value := CoherentNamed.ofApproximation retained
    value_approximation := rfl
    value_eq := congrArg CoherentNamed.ofApproximation approximationEq
    degreePositive := degreePositive
    residual := sample_residual_le track degreePositive }

/-- Package the original root using its lazy prefix and an optional checked completed-state bank.

The same original prefix builder consumes the supplied actual entries. A
cache miss retains the original lazy refinement, while whole prefix equality
keeps every original root, channel and residual owner unchanged.
-/
@[expose] public def certifiedName {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (degreePositive : 0 < polynomial.natDegree)
    (cached : Option (List (StateCache.Entry track)) := none) : CertifiedName track :=
  CertifiedName.ofCache track degreePositive
    ⟨StateCache.buildPrefix 64 (StateCache.first track) cached,
      StateCache.buildPrefix_cached_eq_default 64 (StateCache.first track) cached⟩

/-- A checked retained bank preserves the complete original certified root, channel and cache prefix.

The actual stored bank is consumed by the original prefix builder. Its whole
prefix equality transports the full approximation and coherent-name records,
retaining every original parent, state equation and residual certificate.
-/
public theorem certifiedName_cached_eq_default {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (degreePositive : 0 < polynomial.natDegree)
    (cached : Option (List (StateCache.Entry track))) :
    certifiedName track degreePositive cached = certifiedName track degreePositive none := by
  unfold certifiedName
  apply congrArg (CertifiedName.ofCache track degreePositive)
  apply Subtype.ext
  exact StateCache.buildPrefix_cached_eq_default 64 (StateCache.first track) cached

/-- The absent retained bank preserves every field of the original root construction. -/
public theorem certifiedName_none {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (degreePositive : 0 < polynomial.natDegree) :
    certifiedName track degreePositive none =
      (let stateCache := StateCache.buildPrefix 64 (StateCache.first track)
       let retained := StateCache.approximation track stateCache
       { stateCache := stateCache
         stateCache_eq := rfl
         approximation := retained
         approximation_cache := rfl
         approximation_eq := rfl
         value := CoherentNamed.ofApproximation retained
         value_approximation := rfl
         value_eq := rfl
         degreePositive := degreePositive
         residual := sample_residual_le track degreePositive }) := rfl

namespace CertifiedName

/-- Read the exact original approximation index represented by an actual original root-name process state.

The complete channel-defining equality transports only the process-state
type. No index is inferred from a numerical reading or operational agreement,
and the original supplied process state is consumed literally.
-/
public def stateIndex {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track)
    (actual : certificate.value.name.process.State) : Nat :=
  Eq.mp (congrArg (fun value : CoherentNamed => value.name.process.State) certificate.value_approximation) actual

/-- Equality to an original sequence-backed channel transports its scalar refinement-index bound. -/
private theorem stateIndex_refine_ge_of_eq (approximation : Approximation) (channel : CoherentNamed)
    (same : channel = CoherentNamed.ofApproximation approximation)
    (current : channel.name.process.State) (target : Coordinate) (positive : 0 < target) :
    (show Nat from Eq.mp (congrArg (fun value : CoherentNamed => value.name.process.State) same) current) ≤
      (show Nat from Eq.mp (congrArg (fun value : CoherentNamed => value.name.process.State) same)
        (channel.name.process.refine current target positive)) := by
  cases same
  exact approximation.refineIndex_ge current target positive

/-- Refining the actual original root-name state preserves its retained raw-index floor.

The original whole-channel equation transports the exact supplied state and
refinement. The original approximation's scalar refinement bound then applies
without identifying channels from numerical readings.
-/
public theorem stateIndex_refine_ge {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track)
    (current : certificate.value.name.process.State) (target : Coordinate) (positive : 0 < target) :
    certificate.stateIndex current ≤
      certificate.stateIndex (certificate.value.name.process.refine current target positive) :=
  stateIndex_refine_ge_of_eq certificate.approximation certificate.value certificate.value_approximation
    current target positive

/-- Read an original root state from the certificate's actual shared cache. -/
@[expose] public def stateAt {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) (index : Nat) :
    WindingOneState polynomial ambient :=
  StateCache.read track index certificate.stateCache

/-- A retained cache read is the original deterministic root state at the requested index. -/
public theorem stateAt_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) (index : Nat) :
    certificate.stateAt index = state track index := StateCache.read_eq track index certificate.stateCache

/-- The actual retained approximation sample is the anchor of its same cached original state. -/
public theorem sample_stateAt {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) (index : Nat) :
    certificate.approximation.sample index = (certificate.stateAt index).box.anchor := by
  rewrite [certificate.approximation_cache]
  rfl

/-- Every sample of the retained original root approximation lies in its original ambient box. -/
public theorem sample_inside {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) (index : Nat) :
    ambient.Contains (certificate.approximation.sample index) := by
  rewrite [certificate.approximation_eq, approximation_sample]
  exact (state track index).refinesAmbient.contains (state track index).box.contains_anchor

/-- Every actual cached root sample remains inside its same original initial owner box.

The deterministic state refines the original initial state. Its anchor is
the retained approximation reading, so the same refinement transports its
containment without rebuilding the root cache.
-/
public theorem sample_initial_inside {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) (index : Nat) :
    track.initial.box.Contains (certificate.approximation.sample index) := by
  rewrite [certificate.approximation_eq, approximation_sample]
  exact (state_refines_of_le track (Nat.zero_le index)).contains (state track index).box.contains_anchor

/-- Every possible reading at the original root name belongs to its same original initial box.

The defining whole-channel equality identifies the original sequence-backed
process. Its possibility witness is an actual later retained approximation
sample, whose deterministic state refines that original initial box.
-/
public theorem possible_initial_inside {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) {value : Gaussian}
    (possible : certificate.value.name.process.Possible certificate.value.name.state value) :
    track.initial.box.Contains value := by
  rewrite [certificate.value_approximation] at possible
  change certificate.approximation.Possible 0 value at possible
  rcases possible with ⟨later, _order, rfl⟩
  exact certificate.sample_initial_inside later

/-- Evaluate the defining polynomial using the certificate's actual retained root approximation.

The original root-state cache remains the input to every evaluation sample and
refinement. Coefficient-derived bounds supply the polynomial output allowance.
-/
@[expose] public def evaluation {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) : Approximation :=
  Polynomial.Dense.Gaussian.Approximation.evaluate polynomial ambient certificate.approximation
    certificate.sample_inside

/-- The defining polynomial's retained evaluation is operationally zero at every requested tolerance.

The existing original-track residual certificate supplies the geometric scale.
The comparison computes finite later indices for both independent starts and
bounds every permitted later sample; no sample is claimed to be an exact root.
-/
@[expose] public def evaluation_zero {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (certificate : CertifiedName track) :
    Equivalence.NamedEquivalent certificate.evaluation.toNamed
      (CoherentNamed.Coherence.exact 0).name := by
  have residual : ∀ index, Purelib.Data.Gaussian.Norm.Basic.normSq
      (certificate.evaluation.sample index - 0) ≤
        Geometric.Basic.quarterRadius (residualScale polynomial ambient track) index := by
    intro index
    change Purelib.Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (certificate.approximation.sample index) - 0) ≤ _
    rewrite [Normalization.sub_zero, certificate.approximation_eq]
    exact certificate.residual index
  exact Equivalence.NamedEquivalent.trans
    (Equivalence.Equivalent.toNamed
      (Sequence.Equivalence.equivalent_constant certificate.evaluation 0
        (residualScale polynomial ambient track) (residualScale_nonneg polynomial ambient track) residual))
    (Equivalence.NamedEquivalent.symm
      (Sequence.Name.Exact.exact_toConstantNamed 0))

end CertifiedName

end Purelib.Riemann.RootContinuation.CoherentRoot
