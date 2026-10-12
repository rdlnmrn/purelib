module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
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
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity

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
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
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
  have widthPositive : 0 < track.initial.box.widthX :=
    Rat.Fraction.Order.Arithmetic.sub_pos_direct track.initial.proper.1
  have widthSquarePositive : 0 < track.initial.box.widthX ^ 2 :=
    Rat.Fraction.Order.Arithmetic.pow_pos_direct widthPositive 2
  have heightSquareNonnegative :
      0 <= track.initial.box.widthY ^ 2 :=
    Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _
  constructor
  · have sumNonnegative :=
      Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (Rat.Fraction.Order.Arithmetic.le_of_lt_direct widthSquarePositive)
        heightSquareNonnegative
    have zeroIdentity : (0 : Coordinate) + 0 = 0 := by ring1
    rwa [zeroIdentity] at sumNonnegative
  · intro sumNonpositive
    apply widthSquarePositive.2
    have widthLeSum :=
      Rat.Fraction.Order.Arithmetic.add_le_add_direct (first :=
          track.initial.box.widthX ^ 2)
        (second := track.initial.box.widthX ^ 2) (third := 0)
        (fourth := track.initial.box.widthY ^ 2) le_rfl
        heightSquareNonnegative
    have widthIdentity :
        track.initial.box.widthX ^ 2 + (0 : Coordinate) =
          track.initial.box.widthX ^ 2 := by ring1
    rw [widthIdentity] at widthLeSum
    exact Rat.Fraction.Order.Basic.Compatibility.le_trans
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
  Rational.Geometric.Basic.quarterRadius (scale track) (index + 1)

/-- Every recursive refinement target is strictly positive.

The retained initial diagonal scale is positive. Its original
quarter-geometric value at the successor index remains positive. -/
public theorem stepTarget_positive {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    0 < stepTarget track index :=
  Rational.Geometric.Basic.quarterRadius_pos (scale_positive track) (index + 1)

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
        (Rat.Bounds.AccuracyRadius.accuracyRadius (stepTarget track index))
        (Rat.Bounds.AccuracyRadius.accuracyRadius_pos
          (stepTarget_positive track index))

/-- Each successive root box refines its immediate predecessor.

The next state uses the original track refinement at the retained
accuracy radius. The track's nesting certificate links its exact box
to the same predecessor state. -/
public theorem state_succ_refines {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) (index : Nat) :
    (state track (index + 1)).box.Refines (state track index).box := by
  exact track.nested (state track index)
    (Rat.Bounds.AccuracyRadius.accuracyRadius (stepTarget track index))
    (Rat.Bounds.AccuracyRadius.accuracyRadius_pos
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
      Rational.Geometric.Basic.quarterRadius (scale track) index := by
  cases index with
  | zero =>
      change track.initial.box.diagonalSq <=
        Rational.Geometric.Basic.quarterRadius track.initial.box.diagonalSq 0
      unfold Rational.Geometric.Basic.quarterRadius
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
        (Rat.Bounds.AccuracyRadius.accuracyRadius (stepTarget track index))
        (Rat.Bounds.AccuracyRadius.accuracyRadius_pos
          (stepTarget_positive track index))
      have targetBound := Rat.Bounds.AccuracyRadius.accuracyRadius_sq_lt
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
/-- Build the next cache entry by refining the retained predecessor thunk.

The index increases by one, and the readback proof identifies this computation with the original recursive state. -/
@[expose] public def Entry.next {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (entry : Entry track) : Entry track where
  index := entry.index + 1
  value := ⟨fun _ => track.refine entry.value.get
    (Rat.Bounds.AccuracyRadius.accuracyRadius (stepTarget track entry.index))
    (Rat.Bounds.AccuracyRadius.accuracyRadius_pos (stepTarget_positive track entry.index))⟩
  value_eq := by
    change track.refine entry.value.get _ _ = state track (entry.index + 1)
    rw [state, entry.value_eq]

/-- Construct a finite prefix of shared root-state thunks.

Building the list does not execute root refinements; each successor retains its predecessor's thunk and exact state
equality. -/
@[expose] public def buildPrefix {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} : Nat → Entry track → List (Entry track)
  | 0, _ => []
  | count + 1, entry => entry :: buildPrefix count entry.next

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

end StateCache

section
open Purelib.Approximation
/-- Construct the anchor approximation with its explicit geometric squared-error bound.

A shared 64-entry thunk prefix reuses refinement work. The retained boxes certify later-sample closeness and ambient
bounds, and finite quarter-radius search supplies refinement indices. -/
@[expose] public def approximation {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) : Approximation :=
  let cache := StateCache.buildPrefix 64 (StateCache.first track)
  { sample := fun index => (StateCache.read track index cache).box.anchor
    radiusSq := fun index =>
      Rational.Geometric.Basic.quarterRadius (scale track) index
    radiusSq_nonneg := fun index =>
      Rational.Geometric.Basic.quarterRadius_nonneg
        (scale_positive track).le index
    later_close := by
      intro earlier later order
      simpa only [StateCache.read_eq] using
        ((state track earlier).box.normSq_sub_le_diagonalSq
          ((state_refines_of_le track order).contains
            (state track later).box.contains_anchor)
          (state track earlier).box.contains_anchor).trans
            (state_diagonal_le track earlier)
    refineIndex := fun current target _ =>
      Rational.Geometric.Search.firstQuarterBelow (scale track) current target
    refineIndex_ge := fun current target _ =>
      Rational.Geometric.Search.firstQuarterBelow_ge (scale track) current target
    refineIndex_accurate := fun current target positive =>
      Rational.Geometric.Search.firstQuarterBelow_accurate (scale track)
        (scale_positive track).le current target positive
    centerBound := ambient.normSqBound
    centerBound_nonneg := ambient.normSqBound_nonneg
    sample_bounded := by
      intro index
      simpa only [StateCache.read_eq] using ambient.normSq_le_normSqBound
        ((state track index).refinesAmbient.contains
          (state track index).box.contains_anchor) }

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
  Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient * scale track

end

open Purelib.Data in
open Purelib.Polynomial in
/-- The geometric polynomial-residual scale is nonnegative.

Both the original ambient Lipschitz bound and initial diagonal scale
are positive. Their original rational product is therefore nonnegative. -/
public theorem residualScale_nonneg (polynomial : GaussianPolynomial) (ambient : Box)
    (track : WindingOneTrack polynomial ambient) :
    0 <= residualScale polynomial ambient track :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos polynomial ambient).le
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
    Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval ((approximation track).sample index)) <=
      Rational.Geometric.Basic.quarterRadius
        (residualScale polynomial ambient track) index := by
  have residual :=
    Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      polynomial degreePositive (state track index).refinesAmbient
      (state track index).proper (by
        rw [(state track index).rawWindingFour]
        decide)
  have scaledDiagonal :
      Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient *
          (state track index).box.diagonalSq <=
        Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient *
          Rational.Geometric.Basic.quarterRadius (scale track) index :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (state_diagonal_le track index)
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos
        polynomial ambient).le
  calc
    Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval ((approximation track).sample index)) <=
        Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound polynomial ambient
          (state track index).box := by
      simpa only [approximation_sample] using residual
    _ <= Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient *
          Rational.Geometric.Basic.quarterRadius (scale track) index :=
      scaledDiagonal
    _ = Rational.Geometric.Basic.quarterRadius
          (residualScale polynomial ambient track) index := by
      rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
      unfold residualScale
      ring1

open Purelib.Approximation in
open Purelib.Data in
set_option genInjectivity false in
/-- A coherent root name with its exact track identity and finite residual certificate.

The positive degree and pointwise geometric evaluation bound certify the displayed samples without selecting a completed
root. -/
public structure CertifiedName {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient) where
  /-- The retained coherent arithmetic name. -/ value : CoherentNamed
  /-- The retained name is exactly the name built from this root track. -/ value_eq : value = named track
  /-- The defining polynomial has strictly positive natural degree. -/ degreePositive : 0 < polynomial.natDegree
  /-- Every finite sample satisfies the displayed quarter-geometric polynomial-residual bound. -/ residual : forall
    index,
    Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval ((approximation track).sample index)) <=
      Rational.Geometric.Basic.quarterRadius
        (residualScale polynomial ambient track) index

constructive_injectivity CertifiedName

/-- Package the track's coherent name, positive degree and geometric residual proof.

The retained coherent name is exactly the name constructed from the
same track. Its positive-degree witness and every finite sample
residual certificate are stored with that original name. -/
@[expose] public def certifiedName {polynomial : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack polynomial ambient)
    (degreePositive : 0 < polynomial.natDegree) : CertifiedName track where
  value := named track
  value_eq := rfl
  degreePositive := degreePositive
  residual := sample_residual_le track degreePositive

end Purelib.Riemann.RootContinuation.CoherentRoot
