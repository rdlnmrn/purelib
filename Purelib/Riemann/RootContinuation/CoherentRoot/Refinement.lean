module

public import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Paid refinement bounds at the actual retained coherent-root cache -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Approximation.Rational
open Purelib.Data.Rat

namespace CertifiedName

/-- An already accurate original radius leaves the original refiner at the requested starting stage.

The same retained approximation exposes its original bounded quarter-radius
search; no root state or numerical observation is rebuilt.
-/
theorem refineIndex_eq_of_lt {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq)
    (accurate : root.approximation.radiusSq start < targetSq) :
    root.approximation.refineIndex start targetSq positive = start := by
  rewrite [root.approximation_cache] at accurate ⊢
  exact Geometric.Search.firstQuarterBelow_eq_of_lt (scale track) start targetSq accurate

/-- Every later original cached state meets an already paid squared-diagonal refinement request. -/
theorem stateAt_diagonal_lt_of_refineIndex_le {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq)
    {later : Nat} (order : root.approximation.refineIndex start targetSq positive ≤ later) :
    (root.stateAt later).box.diagonalSq < targetSq := by
  let index := root.approximation.refineIndex start targetSq positive
  have accurate : root.approximation.radiusSq index < targetSq :=
    root.approximation.refineIndex_accurate start targetSq positive
  have radiusEq : root.approximation.radiusSq index = Geometric.Basic.quarterRadius (scale track) index := by
    rewrite [root.approximation_eq]
    rfl
  rewrite [radiusEq] at accurate
  have bound := state_diagonal_le track later
  rewrite [← root.stateAt_eq later] at bound
  exact bound.trans_lt ((Geometric.Basic.quarterRadius_antitone (scale_positive track).le order).trans_lt accurate)

/-- The actual cached state at the original refiner's selected index meets its squared-diagonal request. -/
theorem stateAt_refineIndex_diagonal_lt {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq) :
    (root.stateAt (root.approximation.refineIndex start targetSq positive)).box.diagonalSq < targetSq := by
  exact root.stateAt_diagonal_lt_of_refineIndex_le start targetSq positive (Nat.le_refl _)

end CertifiedName

set_option genInjectivity false in
/-- One paid original root-refinement request with its actual retained cache state.

The squared request, original start, computed index and cache read retain their
defining identities. The same actual state meets that same positive request.
-/
structure Refinement {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat) where
  /-- The retained original squared-diagonal request. -/
  targetSq : Coordinate
  /-- The same original request is strictly positive. -/
  positive : 0 < targetSq
  /-- The stage returned by the original approximation refiner. -/
  index : Nat
  /-- The original approximation computes a sufficient finite upper stage for this same request. -/
  maxIndex : Nat
  /-- The retained upper stage is the original refiner's result on the same start and request. -/
  maxIndex_eq : maxIndex = root.approximation.refineIndex start targetSq positive
  /-- The actual selected cache stage is no later than that same sufficient upper stage. -/
  index_le : index ≤ maxIndex
  /-- The actual stage follows the caller's original start. -/
  index_ge : start ≤ index
  /-- The actual retained state read from the original root cache. -/
  current : WindingOneState polynomial ambient
  /-- The same actual state is the original cache read at that same selected index. -/
  current_eq : current = root.stateAt index
  /-- The retained cache state meets the same original request. -/
  diagonal_lt : current.box.diagonalSq < targetSq

constructive_injectivity Refinement

namespace Refinement

/-- Two complete original paid refinements, each retaining its own requested floor and root owner. -/
abbrev Pair {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) :=
  ((start : Nat) × Refinement first start) × ((start : Nat) × Refinement second start)

/-- Read original cached states until the same squared request is met, within its retained sufficient upper stage.

The actual original state is read once at each inspected index. A successful
diagonal comparison retains that same state. The final allowed index meets
the request by the original refiner's accuracy law, proving finite stopping.
-/
@[expose] def search {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) (maxIndex : Nat)
    (maxIndexEq : maxIndex = root.approximation.refineIndex start targetSq positive) :
    (remaining index : Nat) → start ≤ index → index + remaining = maxIndex → Refinement root start
  | 0, index, indexGe, balance =>
      let current := root.stateAt index
      have indexEq : index = root.approximation.refineIndex start targetSq positive := balance.trans maxIndexEq
      have accurate : current.box.diagonalSq < targetSq := by
        change (root.stateAt index).box.diagonalSq < targetSq
        rewrite [indexEq]
        exact root.stateAt_refineIndex_diagonal_lt start targetSq positive
      ⟨targetSq, positive, index, maxIndex, maxIndexEq, balance.le, indexGe, current, rfl, accurate⟩
  | remaining + 1, index, indexGe, balance =>
      let current := root.stateAt index
      if accurate : current.box.diagonalSq < targetSq then
        ⟨targetSq, positive, index, maxIndex, maxIndexEq,
          (Nat.le_add_right index (remaining + 1)).trans_eq balance, indexGe, current, rfl, accurate⟩
      else
        search root start targetSq positive maxIndex maxIndexEq remaining (index + 1)
          (indexGe.trans (Nat.le_succ index))
          ((Nat.add_right_comm index 1 remaining).trans balance)

/-- Every bounded original-cache search retains exactly the squared request it was given. -/
theorem search_targetSq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) (maxIndex : Nat)
    (maxIndexEq : maxIndex = root.approximation.refineIndex start targetSq positive)
    (remaining index : Nat) (indexGe : start ≤ index) (balance : index + remaining = maxIndex) :
    (search root start targetSq positive maxIndex maxIndexEq remaining index indexGe balance).targetSq = targetSq := by
  induction remaining generalizing index with
  | zero => rfl
  | succ remaining previous =>
      dsimp only [search]
      split
      · rfl
      · exact previous _ _ _

/-- Compute a sufficient original upper stage and retain the first already accurate original cache state.

The original refiner supplies the finite bound. The same actual cache states
are inspected from the caller's start, so an already accurate box incurs no
additional root refinement. All request, index and cache identities remain.
-/
@[expose] def ofTarget {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) : Refinement root start :=
  let maxIndex := root.approximation.refineIndex start targetSq positive
  have order := root.approximation.refineIndex_ge start targetSq positive
  search root start targetSq positive maxIndex rfl (maxIndex - start) start (Nat.le_refl start)
    (Nat.add_sub_of_le order)

/-- Retain an accurate original cache state with its exact paid request and stage bounds.

The original sufficient upper stage, requested start and selected index remain
unchanged. The supplied state replaces only execution of that original cache
read; its complete equality and strict diagonal bound certify the payment.
-/
@[expose] def atState {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (maxIndex : Nat) (maxIndexEq : maxIndex = root.approximation.refineIndex start targetSq positive)
    (index : Nat) (indexGe : start ≤ index) (indexLe : index ≤ maxIndex)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt index)
    (accurate : current.box.diagonalSq < targetSq) : Refinement root start :=
  { targetSq := targetSq
    positive := positive
    index := index
    maxIndex := maxIndex
    maxIndex_eq := maxIndexEq
    index_le := indexLe
    index_ge := indexGe
    current := current
    current_eq := same
    diagonal_lt := accurate }

/-- An accurate retained state gives the complete original search result at its current stage.

Both branches of the original remaining-stage calculation retain the same
request, upper stage, selected index and exact cache state. The original
search stops at this accurate stage, with all retained records preserved.
-/
theorem atState_eq_search {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (maxIndex : Nat) (maxIndexEq : maxIndex = root.approximation.refineIndex start targetSq positive)
    (remaining index : Nat) (indexGe : start ≤ index) (balance : index + remaining = maxIndex)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt index)
    (accurate : current.box.diagonalSq < targetSq) :
    atState root start targetSq positive maxIndex maxIndexEq index indexGe
      ((Nat.le_add_right index remaining).trans_eq balance) current same accurate =
      search root start targetSq positive maxIndex maxIndexEq remaining index indexGe balance := by
  cases same
  cases remaining with
  | zero => rfl
  | succ remaining =>
      dsimp only [search]
      rewrite [dif_pos accurate]
      rfl

/-- Retain an accurate exact state at the original requested starting index. -/
@[expose] def ofTargetFromState {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt start)
    (accurate : current.box.diagonalSq < targetSq) : Refinement root start :=
  atState root start targetSq positive _ rfl start (Nat.le_refl start)
    (root.approximation.refineIndex_ge start targetSq positive) current same accurate

/-- An accurate exact starting state retains the complete original paid refinement. -/
theorem ofTargetFromState_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt start)
    (accurate : current.box.diagonalSq < targetSq) :
    ofTargetFromState root start targetSq positive current same accurate =
      ofTarget root start targetSq positive :=
  atState_eq_search root start targetSq positive _ rfl _ start _ _ current same accurate

/-- Retain an actual original cache state at its same requested floor with a certified sufficient original radius.

The request is the same original radius plus one. The original bounded search
returns this exact starting stage, so the retained state supplies the paid
request without a fresh root-state computation or a copied owner.
-/
@[expose] def atFloor {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt start) : Refinement root start := by
  let target := root.approximation.radiusSq start + 1
  have positive : 0 < target := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (root.approximation.radiusSq_nonneg start) (by decide)
  have accurate : root.approximation.radiusSq start < target := by
    have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
      (show (0 : Coordinate) < 1 by decide) (root.approximation.radiusSq start)
    rewrite [Fraction.Field.add_comm (root.approximation.radiusSq start) 0,
      Fraction.Field.zero_add] at translated
    exact translated
  have indexEq := root.refineIndex_eq_of_lt start target positive accurate
  have diagonal := root.stateAt_refineIndex_diagonal_lt start target positive
  rewrite [indexEq, ← same] at diagonal
  exact atState root start target positive start indexEq.symm start (Nat.le_refl _) (Nat.le_refl _)
    current same diagonal

/-- A floor receipt retains the complete literal original state supplied to its construction. -/
theorem atFloor_current {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt start) :
    (atFloor root start current same).current = current := rfl

/-- A floor receipt pays exactly its original requested starting index. -/
theorem atFloor_index {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt start) :
    (atFloor root start current same).index = start := rfl

/-- The original bounded-search upper index is this same paid starting floor. -/
theorem atFloor_maxIndex {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (current : WindingOneState polynomial ambient) (same : current = root.stateAt start) :
    (atFloor root start current same).maxIndex = start := rfl

/-- Reuse this actual retained state for a compatible new request, with the original refinement as fallback.

Only the same requested starting index and a checked strict diagonal bound
permit reuse. The supplied complete state is passed to the original
`ofTargetFromState`; other requests use the original `ofTarget` procedure.
-/
@[expose] def atRequest {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {oldStart : Nat}
    (retained : Refinement root oldStart) (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq) :
    Refinement root start :=
  if atStart : start = retained.index then
    if accurate : retained.current.box.diagonalSq < targetSq then
      ofTargetFromState root start targetSq positive retained.current
        (retained.current_eq.trans (congrArg root.stateAt atStart).symm) accurate
    else ofTarget root start targetSq positive
  else ofTarget root start targetSq positive

/-- A compatible request passes the same complete stored state to the original exact-state builder. -/
theorem atRequest_cached {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {oldStart : Nat}
    (retained : Refinement root oldStart) (targetSq : Coordinate) (positive : 0 < targetSq)
    (accurate : retained.current.box.diagonalSq < targetSq) :
    retained.atRequest retained.index targetSq positive =
      ofTargetFromState root retained.index targetSq positive retained.current retained.current_eq accurate := by
  unfold atRequest
  rewrite [dif_pos rfl, dif_pos accurate]
  rfl

/-- Every retained-state request has the complete original requested refinement as its result. -/
theorem atRequest_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {oldStart : Nat}
    (retained : Refinement root oldStart) (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq) :
    retained.atRequest start targetSq positive = ofTarget root start targetSq positive := by
  unfold atRequest
  split
  · split
    · exact ofTargetFromState_eq root start targetSq positive _ _ _
    · rfl
  · rfl

/-- A compatible retained-state request preserves its exact original squared target. -/
theorem atRequest_targetSq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {oldStart : Nat}
    (retained : Refinement root oldStart) (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq) :
    (retained.atRequest start targetSq positive).targetSq = targetSq :=
  (congrArg Refinement.targetSq (retained.atRequest_eq start targetSq positive)).trans
    (search_targetSq root start targetSq positive _ rfl _ _ _ _)

/-- The actual retained cache-state request is the same squared target supplied to its constructor. -/
theorem ofTarget_targetSq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (start : Nat)
    (targetSq : Coordinate) (positive : 0 < targetSq) : (ofTarget root start targetSq positive).targetSq = targetSq :=
  search_targetSq root start targetSq positive _ _ _ _ _ _

/-- Every later original cached sample lies inside the same retained paid-request box. -/
theorem sample_inside {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {start : Nat}
    (refinement : Refinement root start) {later : Nat} (order : refinement.index ≤ later) :
    refinement.current.box.Contains (root.approximation.sample later) := by
  have nested := state_refines_of_le track order
  rewrite [← root.stateAt_eq refinement.index, ← refinement.current_eq, ← root.stateAt_eq later] at nested
  rewrite [root.sample_stateAt later]
  exact nested.contains (root.stateAt later).box.contains_anchor

/-- Every later original state keeps the same paid cache request's squared-diagonal bound. -/
theorem later_diagonal_lt {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {start : Nat}
    (refinement : Refinement root start) {later : Nat} (order : refinement.index ≤ later) :
    (state track later).box.diagonalSq < refinement.targetSq := by
  have nested := state_refines_of_le track order
  rewrite [← root.stateAt_eq refinement.index, ← refinement.current_eq] at nested
  exact (Purelib.Geometry.Rational.Box.diagonalSq_le_of_refines nested).trans_lt refinement.diagonal_lt

end Refinement

end Purelib.Riemann.RootContinuation.CoherentRoot

end
