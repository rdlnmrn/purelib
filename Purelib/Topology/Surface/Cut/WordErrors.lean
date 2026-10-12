module
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Ring.Multiplication
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.SignedWord
public import Purelib.Topology.Surface.Cut.WordArea
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite word errors from actual paired occurrences

The signed model uses the retained generator increments. Forward letters
therefore have zero error, and reversed letters have precisely the original
paired increment mismatch. Error sums retain both finite count factors.
No primitive descent or vanishing chord jump is assumed.
-/

namespace Purelib.Topology.Surface.Cut.WordErrors

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Gaussian.Basic

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryWord

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)
open Purelib.Data.Vector.Basic (vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutWordEntry)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)

attribute [local instance high] Group.Negation.subNegZeroMonoid SubNegMonoid.toNeg

/-- A signed coefficient row evaluates to the retained generator point or its componentwise negative.

The original bounded generator index selects exactly one integer coefficient. Its Boolean orientation determines the
displayed sign; direct casts and finite-sum readback preserve the same two Gaussian primitive coordinates. -/
theorem SignedGenerator.linear_eq {count : Nat} (letter : SignedWord.SignedGenerator count) (values : Fin count →
  Stokes.PrimitivePoint) :
    Pairing.linear letter.coefficients values =
      if letter.reversed then (PrimitivePoint.sub PrimitivePoint.zero) (values letter.index) else values letter.index :=
        by
  have component (value : Fin count → Gaussian.Basic.Canonical) :
      FiniteSum.Fin.sumFin (fun index => (letter.coefficients index : Gaussian.Basic.Canonical) * value index) =
        (if letter.reversed then -1 else 1 : Gaussian.Basic.Canonical) * value letter.index := by
    apply (FiniteSum.Fin.sumFin_congr (right := fun index => if index = letter.index then
      (if letter.reversed then -1 else 1 : Gaussian.Basic.Canonical) * value index else 0) ?_).trans
        (FiniteSum.Fin.sumFin_ite_eq letter.index _)
    intro index
    rw [SignedGenerator.coefficients, Data.Vector.Basic.vectorOfFn_apply]
    by_cases same : index = letter.index
    · rw [if_pos same, if_pos same]
      cases letter.reversed with
      | false =>
          have unequal : false ≠ true := by intro impossible; cases impossible
          rw [if_neg unequal, if_neg unequal, Int.cast_one]
      | true =>
          rw [if_pos rfl, if_pos rfl]
          change ((Int.negSucc 0 : Int) : Canonical) * value index = -(1 : Canonical) * value index
          rw [Ring.IntCast.cast_negSucc, Nat.cast_one]
    · rw [if_neg same, if_neg same, Ring.IntCast.cast_zero, Gaussian.Basic.zero_mul]
  unfold Pairing.linear
  rw [component, component]
  cases letter.reversed with
  | false =>
      have unequal : false ≠ true := by intro impossible; cases impossible
      rw [if_neg unequal, if_neg unequal, Gaussian.Basic.one_mul, Gaussian.Basic.one_mul]
  | true =>
      rw [if_pos rfl, if_pos rfl]
      rw [Ring.Multiplication.neg_mul, Ring.Multiplication.neg_mul,
        Gaussian.Basic.one_mul, Gaussian.Basic.one_mul]
      change (⟨-(values letter.index).left, -(values letter.index).right⟩ : Stokes.PrimitivePoint) =
        ⟨0 - (values letter.index).left, 0 - (values letter.index).right⟩
      rw [Gaussian.Basic.zero_sub, Gaussian.Basic.zero_sub]

namespace PrimitivePoint

/-- Adding two conjugate primitive points preserves the coordinate conjugacy relation. -/
theorem add_conjugate {first last : Stokes.PrimitivePoint} (left : (PrimitivePoint.Conjugate first)) (right :
  (PrimitivePoint.Conjugate last)) :
    (PrimitivePoint.Conjugate (first.add last)) := by
  change first.left + last.left = Canonical.conj (first.right + last.right)
  rw [left, right]
  apply Gaussian.Basic.ext
  · rfl
  · simp only [Canonical.conj, Gaussian.Basic.add_im]; ring1

/-- Enlarge a primitive point's common coordinate magnitude bound. -/
theorem Bounded.mono {point : Stokes.PrimitivePoint} {first last : PrimitiveAreaBounds.AreaCoordinate}
    (bounded : (PrimitivePoint.Bounded point) first) (order : first ≤ last) : (PrimitivePoint.Bounded point) last :=
  ⟨bounded.1.trans order, bounded.2.trans order⟩

end PrimitivePoint

namespace CutWordArea

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea (Step steps errorTotal steps_entries errorTotal_eq word)

variable {source target count : Nat} {labels : Fin source → Fin target}
  {generators : Data.Vector (Stokes.OrientedEdge source) count}
  {primitive : Fin source → Stokes.PrimitivePoint} {values : Fin count → Stokes.PrimitivePoint}

/-- Every original cut entry's actual increment differs from its signed-generator model by the supplied coordinate
bound. -/
@[expose] def ErrorsBounded (primitive : Fin source → Stokes.PrimitivePoint) (values : Fin count →
  Stokes.PrimitivePoint)
    (entries : List (BoundaryWord.CutWordEntry labels generators)) (bound : PrimitiveAreaBounds.AreaCoordinate) : Prop
      :=
  ∀ entry ∈ entries, (PrimitivePoint.Bounded ((PrimitivePoint.sub ((PrimitivePoint.sub (primitive entry.edge.finish))
    (primitive entry.edge.start)))
    (Pairing.linear entry.letter.coefficients values))) bound

section
open Purelib.Topology.Surface.Cut.WordErrors
/-- Original pair provenance and paired-increment bounds control every signed-word increment error. -/
theorem errors_of_pairing {pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)} {entries : List
  (BoundaryWord.CutWordEntry labels generators)}
    {bound : PrimitiveAreaBounds.AreaCoordinate} (nonnegative : 0 ≤ bound)
    (provenance : ∀ entry ∈ entries, entry.PairProvenance pairs)
    (values_eq : ∀ index, values index = (PrimitivePoint.sub (primitive (generators index).finish)) (primitive
      (generators index).start))
    (paired : ∀ pair ∈ pairs,
      (PrimitivePoint.Bounded (((PrimitivePoint.sub (primitive pair.first.finish)) (primitive pair.first.start)).add
        ((PrimitivePoint.sub (primitive pair.second.finish)) (primitive pair.second.start)))) bound) :
    ErrorsBounded primitive values entries bound := by
  intro entry member
  have actual := provenance entry member
  rw [SignedGenerator.linear_eq]
  unfold CutWordEntry.PairProvenance at actual
  split at actual
  · rename_i reversed
    rw [if_pos reversed, values_eq]
    obtain ⟨pair, pairMember, generatorEq, edgeEq⟩ := actual
    rw [generatorEq, edgeEq]
    have equal : ((PrimitivePoint.sub ((PrimitivePoint.sub (primitive pair.second.finish)) (primitive
      pair.second.start)))
        ((PrimitivePoint.sub PrimitivePoint.zero) ((PrimitivePoint.sub (primitive pair.first.finish)) (primitive
          pair.first.start)))) =
          ((PrimitivePoint.sub (primitive pair.first.finish)) (primitive pair.first.start)).add
            ((PrimitivePoint.sub (primitive pair.second.finish)) (primitive pair.second.start)) := by
      simp only [PrimitivePoint.zero, PrimitivePoint.sub, PrimitivePoint.add]
      congr 1 <;> ring1
    rw [equal]
    exact paired pair pairMember
  · rename_i forward
    rw [if_neg forward, values_eq, actual]
    constructor <;> simpa only [PrimitivePoint.sub, Gaussian.Basic.sub_self, Canonical.normSq, Gaussian.Basic.zero_re,
      Gaussian.Basic.zero_im, Fraction.Field.zero_mul_direct, _root_.add_zero] using nonnegative

/-- The generated step bank preserves the supplied error bound for every original entry.

Membership follows the same retained step-list spine. Its head keeps the current entry error, while the original tail
uses the specialized entry bound without a second scan or altered step data. -/
theorem steps_errors_bounded {entries : List (BoundaryWord.CutWordEntry labels generators)} {bound :
  PrimitiveAreaBounds.AreaCoordinate}
    (bounded : ErrorsBounded primitive values entries bound) (start : Stokes.PrimitivePoint) :
    ∀ step ∈ CutWordArea.steps primitive values start entries, (PrimitivePoint.Bounded step.error) bound := by
  induction entries generalizing start with
  | nil => intro step member; exact (List.not_mem_nil member).elim
  | cons entry entries ih =>
      intro step member
      rcases Membership.mem_cons.mp member with same | member
      · cases same; exact bounded entry List.mem_cons_self
      · exact ih (fun entry member => bounded entry (List.mem_cons_of_mem _ member)) _ step member

end

/-- The retained step bank has the same length as the original cut-entry list.

The step-entry readback certificate identifies the materialized source entries. Mapping preserves that original finite
length, so each retained step accounts for exactly one cut-entry occurrence. -/
theorem steps_length (entries : List (BoundaryWord.CutWordEntry labels generators)) (start : Stokes.PrimitivePoint) :
    (CutWordArea.steps primitive values start entries).length = entries.length := by
  have equal := congrArg List.length (CutWordArea.steps_entries primitive values entries start)
  rw [Map.length_map] at equal
  exact equal

/-- The left total-error coordinate is the Gaussian sum of the retained left step errors. -/
theorem errorTotal_left (samples : List (CutWordArea.Step (labels := labels) (generators := generators) primitive
  values)) :
    (CutWordArea.errorTotal samples).left = Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.map (fun step =>
      step.error.left)) := by
  induction samples with
  | nil => rfl
  | cons step samples ih => exact congrArg (step.error.left + ·) ih

/-- The right total-error coordinate is the Gaussian sum of the retained right step errors. -/
theorem errorTotal_right (samples : List (CutWordArea.Step (labels := labels) (generators := generators) primitive
  values)) :
    (CutWordArea.errorTotal samples).right = Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.map (fun step =>
      step.error.right)) := by
  induction samples with
  | nil => rfl
  | cons step samples ih => exact congrArg (step.error.right + ·) ih

section
open Purelib.Topology.Surface.Cut.WordErrors
/-- Uniform step-error bounds give a squared-count bound on the complete retained error sum.

Both primitive coordinates use the same retained step list and its complete count. The Gaussian sum bound therefore
keeps both count factors and the supplied local magnitude bound. -/
theorem errorTotal_bounded (samples : List (CutWordArea.Step (labels := labels) (generators := generators) primitive
  values))
    {bound : PrimitiveAreaBounds.AreaCoordinate} (bounded : ∀ step ∈ samples, (PrimitivePoint.Bounded step.error) bound)
      :
    (PrimitivePoint.Bounded (CutWordArea.errorTotal samples)) ((samples.length : PrimitiveAreaBounds.AreaCoordinate) *
      ((samples.length : PrimitiveAreaBounds.AreaCoordinate) * bound)) := by
  have component (value : CutWordArea.Step (labels := labels) (generators := generators) primitive values →
    Gaussian.Basic.Canonical)
      (bounded : ∀ step ∈ samples, Canonical.normSq (value step) ≤ bound) :
      Canonical.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.map value)) ≤ (samples.length :
        PrimitiveAreaBounds.AreaCoordinate) * ((samples.length : PrimitiveAreaBounds.AreaCoordinate) * bound) := by
    have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le (samples.map value) bound (by
      intro value member
      obtain ⟨step, member, same⟩ := Map.mem_map.mp member
      rw [← same]
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bounded step member)
    rw [Map.length_map, Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
    exact estimate
  constructor
  · rw [errorTotal_left]; exact component _ (fun step member => (bounded step member).1)
  · rw [errorTotal_right]; exact component _ (fun step member => (bounded step member).2)

/-- Bound the generated total error by the square of the original entry count times the local bound. -/
theorem steps_errorTotal_bounded {entries : List (BoundaryWord.CutWordEntry labels generators)} {bound :
  PrimitiveAreaBounds.AreaCoordinate}
    (bounded : ErrorsBounded primitive values entries bound) (start : Stokes.PrimitivePoint) :
    (PrimitivePoint.Bounded (CutWordArea.errorTotal (CutWordArea.steps primitive values start entries)))
      ((entries.length : PrimitiveAreaBounds.AreaCoordinate) * ((entries.length : PrimitiveAreaBounds.AreaCoordinate) *
        bound)) := by
  have estimate := errorTotal_bounded _ (steps_errors_bounded bounded start)
  simpa only [steps_length] using estimate

end

open Purelib.Topology.Surface.Cut.WordErrors in
open Purelib.Topology.Surface.Cut.WordErrors.PrimitivePoint in
/-- A supplied upper bound on entry count controls the generated total error with both count factors retained. -/
theorem steps_errorTotal_bounded_of_length {entries : List (BoundaryWord.CutWordEntry labels generators)} {bound :
  PrimitiveAreaBounds.AreaCoordinate}
    (bounded : ErrorsBounded primitive values entries bound) (nonnegative : 0 ≤ bound)
    (start : Stokes.PrimitivePoint) (lengthBound : Nat) (length_le : entries.length ≤ lengthBound) :
    (PrimitivePoint.Bounded (CutWordArea.errorTotal (CutWordArea.steps primitive values start entries)))
      ((lengthBound : PrimitiveAreaBounds.AreaCoordinate) * ((lengthBound : PrimitiveAreaBounds.AreaCoordinate) *
        bound)) := by
  apply Bounded.mono (steps_errorTotal_bounded bounded start)
  have countLe := Cast.Order.natCast_le_direct length_le
  exact Fraction.Order.Arithmetic.mul_le_mul_direct countLe
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct countLe nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Cast.Order.natCast_le_direct (Nat.zero_le _)) nonnegative)
    (Cast.Order.natCast_le_direct (Nat.zero_le _))

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
open Purelib.Topology.Surface.Cut.WordErrors in
/-- The modeled endpoint of any actual prefix differs by its accumulated local error.

The retained prefix path and concatenation equation identify the actual source entries. Their local errors are bounded
using the complete word count, with the same modeled endpoint and accumulated error sum. -/
theorem prefix_drift_bounded {entries first last : List (BoundaryWord.CutWordEntry labels generators)} {bound :
  PrimitiveAreaBounds.AreaCoordinate}
    (bounded : ErrorsBounded primitive values entries bound) (nonnegative : 0 ≤ bound)
    (equal : first ++ last = entries) {start finish : Fin source}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish
      (first.map CutWordEntry.edge) start finish) :
    (PrimitivePoint.Bounded ((PrimitivePoint.sub (primitive finish)) ((primitive start).add (Pairing.linear
      (Pairing.totalAt (word first)) values))))
      ((entries.length : PrimitiveAreaBounds.AreaCoordinate) * ((entries.length : PrimitiveAreaBounds.AreaCoordinate) *
        bound)) := by
  have included : ErrorsBounded primitive values first bound := by
    intro entry member
    apply bounded entry
    rw [← equal]
    exact Membership.mem_append.mpr (Or.inl member)
  have lengthLe : first.length ≤ entries.length := by rw [← equal, Append.length_append]; exact Nat.le_add_right _ _
  have estimate := steps_errorTotal_bounded_of_length included nonnegative (primitive start) entries.length
    lengthLe
  rw [CutWordArea.errorTotal_eq primitive values first path] at estimate
  have endpoint : (PrimitivePoint.sub (primitive finish)) ((primitive start).add (Pairing.linear (Pairing.totalAt (word
    first)) values)) =
      (PrimitivePoint.sub ((PrimitivePoint.sub (primitive finish)) (primitive start))) (Pairing.linear (Pairing.totalAt
        (word first)) values) := by
    simp only [PrimitivePoint.add, PrimitivePoint.sub]
    congr 1 <;> ring1
  rw [endpoint]
  exact estimate

end CutWordArea

namespace CutBoundaryWord.AreaSample

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open Purelib.Topology.Surface.Cut.WordArea.CutBoundaryWord (AreaSample generatorValues)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {primitive : Fin source → Stokes.PrimitivePoint} {start :
    Stokes.PrimitivePoint}

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
/-- Each cached generator value is its original representative edge's primitive increment. -/
theorem values_apply (sample : CutBoundaryWord.AreaSample word primitive start) (index : Fin word.alphabet.count) :
    sample.values index = (PrimitivePoint.sub (primitive (word.alphabet.generators index).finish))
      (primitive (word.alphabet.generators index).start) := by
  rw [sample.values_eq, CutBoundaryWord.generatorValues, Data.Vector.Basic.vectorOfFn_apply]

open Purelib.Topology.Surface.Cut.WordArea.CutWordArea in
open Purelib.Topology.Surface.Cut.WordErrors in
/-- Bound the sample's retained total error using the complete boundary length.

The cached step and entry readback equations identify the original edge-list count. Transporting that scalar length
retains the same total error coordinates and both multiplicative count factors. -/
theorem errorTotal_bounded (sample : CutBoundaryWord.AreaSample word primitive start) {bound :
  PrimitiveAreaBounds.AreaCoordinate}
    (bounded : CutWordArea.ErrorsBounded primitive sample.values word.alphabet.entries bound) :
    (PrimitivePoint.Bounded sample.errorTotal) ((edges.length : PrimitiveAreaBounds.AreaCoordinate) * ((edges.length :
      PrimitiveAreaBounds.AreaCoordinate) * bound)) := by
  rw [sample.errorTotal_eq, sample.steps_eq]
  have estimate := CutWordArea.steps_errorTotal_bounded bounded start
  have lengthEq := congrArg List.length word.alphabet.edges_eq
  rw [Map.length_map] at lengthEq
  rw [lengthEq] at estimate
  exact estimate

end CutBoundaryWord.AreaSample
end Purelib.Topology.Surface.Cut.WordErrors
