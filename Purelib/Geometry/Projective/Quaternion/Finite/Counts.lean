module
import Purelib.Data.List.Append
import Purelib.Data.List.FilterMap
import Purelib.Data.Bool.Decide
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Division
import Purelib.Data.List.Flatten
import Purelib.Data.List.Fold
import Purelib.Data.List.Filter
public import Purelib.Algebra.Field.Finite.Odd.SquareClasses
import Purelib.Geometry.Quadratic.Finite.Fibers
import Purelib.Data.List.Bijection
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Data.List.CountWhere
import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Quaternion.Finite.Enumeration
public import Purelib.Geometry.Quadratic.Finite.NullDirections
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Algebra.Field.Finite.Odd.SquareFibers
import Purelib.Tactic.Ring

section
public section

/-!
# Certified rotation and projective occurrence counts

The displayed odd-field presentation retains its original finite scalar and
vector enumerations. Boolean filters and explicit bijections count canonical
projective representatives and the corresponding rotation strata.
-/

namespace Purelib.Algebra.Field.Finite.Odd.Presentation

open Purelib
open Purelib.Algebra.Field.Finite.Odd
open Purelib.Algebra.Field.Finite.Odd.Presentation
open Purelib.Algebra.Field.Finite.Odd.SquareClasses
open Purelib.Algebra.Quadratic
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Data.List
open Purelib.Data.List.Bijection
open Purelib.LinearAlgebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace FiniteOddFieldPresentation

variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The certified nonzero scalar carrier has `q - 1` entries for carrier length `q`. -/
theorem nonzeroScalarWitnesses_length :
    presentation.nonzeroScalarWitnesses.length =
      presentation.carrier.length - 1 := by
  calc
    presentation.nonzeroScalarWitnesses.length =
        presentation.nonzeroScalars.length :=
      ListBijection.length_eq
        presentation.nonzeroScalarWitnessValueBijection
        presentation.nonzeroScalarWitnesses_nodup
        presentation.nonzeroScalars_nodup
    _ = presentation.carrier.length - 1 :=
      presentation.nonzeroScalars_length

/-- The orbit-coordinate list has `(q - 1)` times as many entries as the canonical non-null carrier. -/
theorem scaleOrbitCoordinates_length :
    presentation.scaleOrbitCoordinates.length =
      (presentation.carrier.length - 1) *
        presentation.nonNullProjectiveRepresentatives.length := by
  unfold FiniteOddFieldPresentation.scaleOrbitCoordinates
  rw [Flatten.flatMap_map_length, presentation.nonzeroScalarWitnesses_length]

/-- Counting the raw non-null four-tuples by their explicit scale orbits. -/
theorem allNonNullProportionRepresentatives_length :
    presentation.allNonNullProportionRepresentatives.length =
      (presentation.carrier.length - 1) *
        presentation.nonNullProjectiveRepresentatives.length := by
  calc
    presentation.allNonNullProportionRepresentatives.length =
        presentation.scaleOrbitCoordinates.length :=
      ListBijection.length_eq presentation.nonNullScaleOrbitBijection
        presentation.allNonNullProportionRepresentatives_nodup
        presentation.scaleOrbitCoordinates_nodup
    _ = (presentation.carrier.length - 1) *
        presentation.nonNullProjectiveRepresentatives.length :=
      presentation.scaleOrbitCoordinates_length

/-- Count one fixed-`t` slice of a Boolean property on affine vectors. -/
@[expose] public def vectorSliceCountWhere (t : K) (predicate : Coordinates3.Vector K → Bool) : Nat :=
  (presentation.carrier.map fun r =>
    CountWhere.listCountWhere (presentation.carrier.map fun s => ⟨t, r, s⟩)
      predicate).foldr Nat.add 0

/-- At first coordinate `t`, ternary quadrance `value` reduces to two-square value `value - t²`. -/
theorem vectorSliceQuadranceCount_eq_twoSquareCount (t value : K) :
    presentation.vectorSliceCountWhere t (fun vector =>
      @decide (vector.quadrance = value)
        (presentation.eqDecidable vector.quadrance value)) =
    presentation.twoSquareCount (value - t ^ 2) := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.vectorSliceCountWhere FiniteOddFieldPresentation.twoSquareCount
    FiniteOddFieldPresentation.twoSquareFiber FiniteOddFieldPresentation.scalarPairs
  change
    (presentation.carrier.map fun r =>
      CountWhere.listCountWhere
        (presentation.carrier.map fun s => (⟨t, r, s⟩ : Coordinates3.Vector K))
        (fun vector => decide (vector.quadrance = value))).foldr Nat.add 0 =
      CountWhere.listCountWhere
        (presentation.carrier.flatMap fun r =>
          presentation.carrier.map fun s => (⟨r, s⟩ : Quadratic.Pair K (1 : K)))
        (fun pair => decide (pair.quadrance = value - t ^ 2))
  rw [CountWhere.listCountWhere_flatMap]
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply Map.map_congr_left
  intro r _
  rw [CountWhere.listCountWhere_map, CountWhere.listCountWhere_map]
  apply CountWhere.listCountWhere_congr
  intro s _
  apply Purelib.Data.Bool.Decide.eq_of_true_iff
  constructor
  · intro accepted
    apply decide_eq_true
    have equation := of_decide_eq_true accepted
    unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot at equation
    unfold Quadratic.Pair.quadrance
    calc
      r ^ 2 + s ^ 2 =
          (t * t + r * r + s * s) - t ^ 2 := by ring1
      _ = value - t ^ 2 := by rw [equation]
  · intro accepted
    apply decide_eq_true
    have equation := of_decide_eq_true accepted
    unfold Quadratic.Pair.quadrance at equation
    unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
    calc
      t * t + r * r + s * s = t ^ 2 + (r ^ 2 + s ^ 2) := by ring1
      _ = t ^ 2 + (value - t ^ 2) := by rw [equation]
      _ = value := by ring1

/-- Count a Boolean property over the displayed affine vector carrier without first flattening its three nested loops.
Each fixed-`t` slice is reduced separately, keeping concrete regression certificates within the ordinary kernel
recursion limit. -/
@[expose] public def vectorCountWhere (predicate : Coordinates3.Vector K → Bool) : Nat :=
  (presentation.carrier.map fun t =>
    presentation.vectorSliceCountWhere t predicate).foldr Nat.add 0

/-- Pointwise equal Boolean predicates have equal finite vector counts. -/
theorem vectorCountWhere_congr (left right : Coordinates3.Vector K → Bool)
    (pointwise : ∀ vector : Coordinates3.Vector K, left vector = right vector) :
    presentation.vectorCountWhere left = presentation.vectorCountWhere right := by
  unfold FiniteOddFieldPresentation.vectorCountWhere FiniteOddFieldPresentation.vectorSliceCountWhere
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply Map.map_congr_left
  intro t _
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply Map.map_congr_left
  intro r _
  apply CountWhere.listCountWhere_congr
  intro vector _
  exact pointwise vector

/-- Count one fixed-`r` line in the first chart at infinity. -/
@[expose] public def infinityTSliceCountWhere (r : K)
    (predicate : Projective.Basic.Proportion K → Bool) : Nat :=
  CountWhere.listCountWhere (presentation.carrier.map fun s => ⟨0, ⟨1, r, s⟩⟩)
    predicate

/-- Count a Boolean property over the four canonical projective charts, again retaining the nested chart loops rather
than reducing one long list. -/
@[expose] public def projectiveCountWhere (predicate : Projective.Basic.Proportion K → Bool) : Nat :=
  let affine := presentation.vectorCountWhere fun vector =>
    predicate ⟨1, vector⟩
  let infinityT := (presentation.carrier.map fun r =>
    presentation.infinityTSliceCountWhere r predicate).foldr Nat.add 0
  let infinityR := CountWhere.listCountWhere
    (presentation.carrier.map fun s => ⟨0, ⟨0, 1, s⟩⟩) predicate
  let infinityS := if predicate FiniteOddFieldPresentation.infinitySRepresentative then 1 else 0
  affine + infinityT + infinityR + infinityS

/-- A projective predicate supported only in the scalar-one chart counts the same objects as its displayed affine-vector
predicate. -/
theorem projectiveCountWhere_eq_vectorCountWhere_of_infinity_rejected
    (predicate : Projective.Basic.Proportion K → Bool) (affinePredicate : Coordinates3.Vector K → Bool)
    (affine : ∀ vector : Coordinates3.Vector K,
      predicate ⟨1, vector⟩ = affinePredicate vector)
    (infinity : ∀ raw : Projective.Basic.Proportion K, raw.scalar = 0 → predicate raw = false) :
    presentation.projectiveCountWhere predicate =
      presentation.vectorCountWhere affinePredicate := by
  unfold FiniteOddFieldPresentation.projectiveCountWhere FiniteOddFieldPresentation.infinityTSliceCountWhere
  have affineEqual := presentation.vectorCountWhere_congr
    (fun vector => predicate ⟨1, vector⟩) affinePredicate affine
  rw [affineEqual]
  have infinityTZero : ∀ r : K,
      CountWhere.listCountWhere
        (presentation.carrier.map fun s =>
          (⟨0, ⟨1, r, s⟩⟩ : Projective.Basic.Proportion K)) predicate = 0 := by
    intro r
    apply CountWhere.listCountWhere_eq_zero_of_reject
    intro raw member
    rcases Map.mem_map.mp member with ⟨s, _, equal⟩
    rw [← equal]
    exact infinity ⟨0, ⟨1, r, s⟩⟩ rfl
  have infinityTMap :
      presentation.carrier.map (fun r =>
        CountWhere.listCountWhere
          (presentation.carrier.map fun s =>
            (⟨0, ⟨1, r, s⟩⟩ : Projective.Basic.Proportion K)) predicate) =
        presentation.carrier.map fun _ => 0 := by
    apply Map.map_congr_left
    intro r _
    exact infinityTZero r
  rw [infinityTMap, Fold.foldr_add_map_zero]
  have infinityRZero :
      CountWhere.listCountWhere
        (presentation.carrier.map fun s =>
          (⟨0, ⟨0, 1, s⟩⟩ : Projective.Basic.Proportion K)) predicate = 0 := by
    apply CountWhere.listCountWhere_eq_zero_of_reject
    intro raw member
    rcases Map.mem_map.mp member with ⟨s, _, equal⟩
    rw [← equal]
    exact infinity ⟨0, ⟨0, 1, s⟩⟩ rfl
  rw [infinityRZero, infinity FiniteOddFieldPresentation.infinitySRepresentative rfl]
  rfl

/-- The nested slice counter equals the count on its flattened two-coordinate list. -/
private theorem vectorSliceCountWhere_eq (t : K)
    (predicate : Coordinates3.Vector K → Bool) :
    presentation.vectorSliceCountWhere t predicate =
      CountWhere.listCountWhere
        (presentation.carrier.flatMap fun r =>
          presentation.carrier.map fun s => ⟨t, r, s⟩) predicate := by
  unfold FiniteOddFieldPresentation.vectorSliceCountWhere
  exact (CountWhere.listCountWhere_flatMap presentation.carrier
    (fun r => presentation.carrier.map fun s => ⟨t, r, s⟩)
    predicate).symm

/-- The vector counter equals the length of the filtered explicit vector carrier. -/
theorem vectorCountWhere_eq_length_filter (predicate : Coordinates3.Vector K → Bool) :
    presentation.vectorCountWhere predicate =
      (presentation.vectors.filter predicate).length := by
  change presentation.vectorCountWhere predicate =
    CountWhere.listCountWhere presentation.vectors predicate
  unfold FiniteOddFieldPresentation.vectorCountWhere FiniteOddFieldPresentation.vectors
  rw [CountWhere.listCountWhere_flatMap]
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply Map.map_congr_left
  intro t _
  exact presentation.vectorSliceCountWhere_eq t predicate

/-- A predicate rejecting every displayed vector has count zero. -/
public theorem vectorCountWhere_eq_zero_of_reject
    (predicate : Coordinates3.Vector K → Bool)
    (reject : ∀ vector ∈ presentation.vectors, predicate vector = false) :
    presentation.vectorCountWhere predicate = 0 := by
  rw [presentation.vectorCountWhere_eq_length_filter]
  exact CountWhere.listCountWhere_eq_zero_of_reject presentation.vectors predicate reject

/-- The vector-loop count equals the filtered count in the scalar-one projective chart. -/
private theorem affineCountWhere_eq (predicate : Projective.Basic.Proportion K → Bool) :
    presentation.vectorCountWhere (fun vector => predicate ⟨1, vector⟩) =
      CountWhere.listCountWhere presentation.affineProportionRepresentatives
        predicate := by
  unfold FiniteOddFieldPresentation.affineProportionRepresentatives
  rw [CountWhere.listCountWhere_map]
  exact presentation.vectorCountWhere_eq_length_filter _

/-- The nested first-infinity-chart counter equals the count of its listed representatives. -/
private theorem infinityTCountWhere_eq
    (predicate : Projective.Basic.Proportion K → Bool) :
    (presentation.carrier.map fun r =>
      presentation.infinityTSliceCountWhere r predicate).foldr Nat.add 0 =
      CountWhere.listCountWhere presentation.infinityTRepresentatives predicate := by
  unfold FiniteOddFieldPresentation.infinityTRepresentatives
  rw [CountWhere.listCountWhere_flatMap]
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply Map.map_congr_left
  intro r _
  rfl

/-- The second-infinity-chart counter is the count of its listed representatives. -/
private theorem infinityRCountWhere_eq
    (predicate : Projective.Basic.Proportion K → Bool) :
    CountWhere.listCountWhere
        (presentation.carrier.map fun s => ⟨0, ⟨0, 1, s⟩⟩) predicate =
      CountWhere.listCountWhere presentation.infinityRRepresentatives predicate := by
  rfl

/-- The final chart contributes one exactly when its unique representative is accepted. -/
private theorem infinitySCountWhere_eq
    (_presentation : Presentation.FiniteOddFieldPresentation K)
    (predicate : Projective.Basic.Proportion K → Bool) :
    (if predicate FiniteOddFieldPresentation.infinitySRepresentative then 1 else 0) =
      CountWhere.listCountWhere [FiniteOddFieldPresentation.infinitySRepresentative] predicate := by
  unfold CountWhere.listCountWhere
  cases accepted : predicate FiniteOddFieldPresentation.infinitySRepresentative with
  | false =>
      rw [Filter.filter_cons, accepted]
      have falseNeTrue : ¬ false = true := by
        intro impossible
        exact Bool.noConfusion impossible
      rw [if_neg falseNeTrue, if_neg falseNeTrue]
      rfl
  | true =>
      rw [Filter.filter_cons, accepted]
      rw [if_pos rfl, if_pos rfl]
      rfl

/-- The chart-efficient counter is exactly the length of the corresponding filter of the canonical projective list. -/
theorem projectiveCountWhere_eq_length_filter
    (predicate : Projective.Basic.Proportion K → Bool) :
    presentation.projectiveCountWhere predicate =
      (presentation.projectiveRepresentatives.filter predicate).length := by
  change presentation.projectiveCountWhere predicate =
    CountWhere.listCountWhere presentation.projectiveRepresentatives predicate
  unfold FiniteOddFieldPresentation.projectiveCountWhere FiniteOddFieldPresentation.projectiveRepresentatives
  rw [presentation.affineCountWhere_eq,
    presentation.infinityTCountWhere_eq,
    presentation.infinityRCountWhere_eq,
    presentation.infinitySCountWhere_eq]
  rw [CountWhere.listCountWhere_append, CountWhere.listCountWhere_append,
    CountWhere.listCountWhere_append]

/-- Pointwise equal Boolean predicates have equal four-chart projective counts. -/
theorem projectiveCountWhere_congr (left right : Projective.Basic.Proportion K → Bool)
    (pointwise : ∀ raw : Projective.Basic.Proportion K, left raw = right raw) :
    presentation.projectiveCountWhere left =
      presentation.projectiveCountWhere right := by
  rw [presentation.projectiveCountWhere_eq_length_filter,
    presentation.projectiveCountWhere_eq_length_filter]
  exact CountWhere.listCountWhere_congr presentation.projectiveRepresentatives
    left right (fun raw _ => pointwise raw)

/-- Decide nonvanishing of a raw proportion's norm using the presentation's equality decision. -/
@[expose] public def normNonzeroAccepted (raw : Projective.Basic.Proportion K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (raw.norm ≠ 0)

/-- Non-null certification succeeds exactly when the Boolean norm test accepts. -/
public theorem certifyNonNull_isSome_eq_normNonzeroAccepted
    (raw : Projective.Basic.Proportion K) :
    (presentation.certifyNonNull raw).isSome =
      presentation.normNonzeroAccepted raw := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.certifyNonNull FiniteOddFieldPresentation.normNonzeroAccepted
  split
  next normZero =>
    rw [decide_eq_false (fun normNonzero => normNonzero normZero)]
    rfl
  next normNonzero =>
    rw [decide_eq_true normNonzero]
    rfl

/-- Counting certified proportions with square norm equals the raw nonzero-and-square norm count.

Non-null certification retains the original coordinates, so both filters inspect the same norm. -/
public theorem certifiedSquareFilter_length_eq_rawCount :
    ∀ values : List (Projective.Basic.Proportion K),
      ((values.filterMap presentation.certifyNonNull).filter fun proportion =>
          (FiniteOddFieldPresentation.isSquare presentation) proportion.toProportion.norm).length =
        CountWhere.listCountWhere values fun raw =>
          presentation.normNonzeroAccepted raw &&
            (FiniteOddFieldPresentation.isSquare presentation) raw.norm
  | [] => rfl
  | head :: tail => by
      cases certified : presentation.certifyNonNull head with
      | none =>
          have isSomeFalse :
              (presentation.certifyNonNull head).isSome = false :=
            congrArg Option.isSome certified
          have nonzeroFalse :
              presentation.normNonzeroAccepted head = false := by
            calc
              presentation.normNonzeroAccepted head =
                  (presentation.certifyNonNull head).isSome :=
                (presentation.certifyNonNull_isSome_eq_normNonzeroAccepted
                  head).symm
              _ = false := isSomeFalse
          rw [FilterMap.filterMap_cons_none certified]
          unfold CountWhere.listCountWhere
          rw [Filter.filter_cons, nonzeroFalse, Bool.false_and]
          exact
            certifiedSquareFilter_length_eq_rawCount
            tail
      | some result =>
          have isSomeTrue :
              (presentation.certifyNonNull head).isSome = true :=
            congrArg Option.isSome certified
          have nonzeroTrue :
              presentation.normNonzeroAccepted head = true := by
            calc
              presentation.normNonzeroAccepted head =
                  (presentation.certifyNonNull head).isSome :=
                (presentation.certifyNonNull_isSome_eq_normNonzeroAccepted
                  head).symm
              _ = true := isSomeTrue
          rw [FilterMap.filterMap_cons_some certified]
          unfold CountWhere.listCountWhere
          rw [Filter.filter_cons, Filter.filter_cons, nonzeroTrue,
            Bool.true_and,
            (FiniteOddFieldPresentation.certifyNonNull_eq_some_toProportion presentation) certified]
          cases square : (FiniteOddFieldPresentation.isSquare presentation) head.norm with
          | false =>
              rw [if_neg (fun impossible => Bool.noConfusion impossible)]
              exact
                certifiedSquareFilter_length_eq_rawCount
                tail
          | true =>
              exact congrArg Nat.succ

                  (certifiedSquareFilter_length_eq_rawCount
                  tail)

/-- Non-null points in the first chart of the projective plane at infinity. -/
@[expose] public def infinityTNonNullCount : Nat := by
  exact CountWhere.listCountWhere presentation.scalarPairs fun pair =>
    presentation.normNonzeroAccepted
      ⟨0, ⟨1, pair.re, pair.im⟩⟩

/-- Non-null points in the second chart of the projective plane at infinity. -/
@[expose] public def infinityRNonNullCount : Nat := by
  exact CountWhere.listCountWhere presentation.carrier fun s =>
    presentation.normNonzeroAccepted ⟨0, ⟨0, 1, s⟩⟩

/-- Non-null proportions in the scalar-one affine chart. -/
@[expose] public def affineNonNullCount : Nat :=
  presentation.vectorCountWhere fun vector =>
    presentation.normNonzeroAccepted ⟨1, vector⟩

/-- Rejecting nonzeroness of `1 + value` is exactly accepting `value = -1`. -/
private theorem complement_one_add_nonzero (value : K) :
    letI : DecidableEq K := presentation.eqDecidable
    (!decide ((1 : K) + value ≠ 0)) = decide (value = -1) := by
  letI : DecidableEq K := presentation.eqDecidable
  apply Purelib.Data.Bool.Decide.eq_of_true_iff
  constructor
  · intro accepted
    apply decide_eq_true
    have nonzeroDecideFalse := Purelib.Data.Bool.Decide.not_true_iff _ |>.mp accepted
    have notNonzero := decide_eq_false_iff_not.mp nonzeroDecideFalse
    have sumZero := FiniteOddFieldPresentation.eq_zero_of_not_ne presentation.eqDecidable notNonzero
    calc
      value = (1 + value) - 1 := by ring1
      _ = -1 := by rw [sumZero]; ring1
  · intro accepted
    have valueNegativeOne := of_decide_eq_true accepted
    apply Purelib.Data.Bool.Decide.not_true_iff _ |>.mpr
    apply decide_eq_false
    intro sumNonzero
    apply sumNonzero
    rw [valueNegativeOne]
    ring1

/-- The scalar-pair carrier has the square of the scalar carrier length. -/
private theorem scalarPairs_length :
    presentation.scalarPairs.length =
      presentation.carrier.length * presentation.carrier.length := by
  unfold FiniteOddFieldPresentation.scalarPairs
  exact Flatten.flatMap_map_length presentation.carrier presentation.carrier
    (fun first second => (⟨first, second⟩ : Quadratic.Pair K (1 : K)))

/-- The three-coordinate vector carrier has the cube of the scalar carrier length. -/
private theorem vectors_length :
    presentation.vectors.length = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length) := by
  unfold FiniteOddFieldPresentation.vectors
  apply Flatten.flatMap_length_of_constant presentation.carrier
    (fun t => presentation.carrier.flatMap fun r =>
      presentation.carrier.map fun s => (⟨t, r, s⟩ : Coordinates3.Vector K))
    (presentation.carrier.length * presentation.carrier.length)
  intro t _
  exact Flatten.flatMap_map_length presentation.carrier presentation.carrier
    (fun r s => (⟨t, r, s⟩ : Coordinates3.Vector K))

/-- Accepted affine representatives and the excluded quadrance-minus-one locus partition the `q³` vectors. -/
theorem affineNonNullCount_add_excludedAnchorQuadric :
    presentation.affineNonNullCount +
      presentation.excludedAnchorQuadric.length =
        presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length) := by
  letI : DecidableEq K := presentation.eqDecidable
  have partition := CountWhere.listCountWhere_add_complementary presentation.vectors
    (fun vector => presentation.normNonzeroAccepted ⟨1, vector⟩)
    (fun vector => decide (vector.quadrance = (-1 : K))) (by
      intro vector _
      unfold FiniteOddFieldPresentation.normNonzeroAccepted
      have normEquation :
          Proportion.norm (⟨1, vector⟩ : Projective.Basic.Proportion K) =
            1 + vector.quadrance := by
        unfold Proportion.norm
        ring1
      rw [normEquation]
      exact presentation.complement_one_add_nonzero vector.quadrance)
  have affineAsList : presentation.affineNonNullCount =
      CountWhere.listCountWhere presentation.vectors (fun vector =>
        presentation.normNonzeroAccepted ⟨1, vector⟩) := by
    unfold FiniteOddFieldPresentation.affineNonNullCount CountWhere.listCountWhere
    exact presentation.vectorCountWhere_eq_length_filter _
  calc
    presentation.affineNonNullCount +
        presentation.excludedAnchorQuadric.length =
      CountWhere.listCountWhere presentation.vectors (fun vector =>
          presentation.normNonzeroAccepted ⟨1, vector⟩) +
        CountWhere.listCountWhere presentation.vectors (fun vector =>
          decide (vector.quadrance = (-1 : K))) := by
            rw [affineAsList]
            rfl
    _ = presentation.vectors.length := partition
    _ = presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length) :=
      presentation.vectors_length

/-- The first infinity chart partitions into non-null representatives and two-square value-minus-one solutions. -/
theorem infinityTNonNullCount_add_twoSquareCount_minus_one :
    presentation.infinityTNonNullCount +
      presentation.twoSquareCount (-1) =
        presentation.carrier.length * presentation.carrier.length := by
  letI : DecidableEq K := presentation.eqDecidable
  have partition := CountWhere.listCountWhere_add_complementary
    presentation.scalarPairs
    (fun pair => presentation.normNonzeroAccepted
      ⟨0, ⟨1, pair.re, pair.im⟩⟩)
    (fun pair => decide (pair.quadrance = (-1 : K))) (by
      intro pair _
      unfold FiniteOddFieldPresentation.normNonzeroAccepted
      have normEquation :
          Proportion.norm (⟨0, ⟨1, pair.re, pair.im⟩⟩ :
            Projective.Basic.Proportion K) = 1 + pair.quadrance := by
        unfold Proportion.norm Quadratic.Pair.quadrance Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        ring1
      rw [normEquation]
      exact presentation.complement_one_add_nonzero pair.quadrance)
  change presentation.infinityTNonNullCount +
      presentation.twoSquareCount (-1) =
        presentation.scalarPairs.length at partition
  rw [presentation.scalarPairs_length] at partition
  exact partition

/-- The second infinity chart partitions into non-null representatives and square roots of minus one. -/
theorem infinityRNonNullCount_add_squareRootCount_minus_one :
    presentation.infinityRNonNullCount +
      presentation.squareRootCount (-1) = presentation.carrier.length := by
  letI : DecidableEq K := presentation.eqDecidable
  have partition := CountWhere.listCountWhere_add_complementary presentation.carrier
    (fun s => presentation.normNonzeroAccepted ⟨0, ⟨0, 1, s⟩⟩)
    (fun s => decide (s ^ 2 = (-1 : K))) (by
      intro s _
      unfold FiniteOddFieldPresentation.normNonzeroAccepted
      have normEquation :
          Proportion.norm (⟨0, ⟨0, 1, s⟩⟩ : Projective.Basic.Proportion K) =
            1 + s ^ 2 := by
        unfold Proportion.norm Coordinates3.Vector.quadrance Coordinates3.Vector.dot
        ring1
      rw [normEquation]
      exact presentation.complement_one_add_nonzero (s ^ 2))
  change presentation.infinityRNonNullCount +
      presentation.squareRootCount (-1) = presentation.carrier.length at partition
  exact partition

/-- Efficient executable count of one affine ternary quadrance fiber. -/
@[expose] public def vectorQuadranceCount (value : K) : Nat := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectorCountWhere fun vector =>
    decide (vector.quadrance = value)

/-- The executable vector quadrance count equals the sum of the retained two-square slice counts. -/
theorem vectorQuadranceCount_eq_ternaryQuadranceSlicedCount (value : K) :
    presentation.vectorQuadranceCount value =
      presentation.ternaryQuadranceSlicedCount value := by
  unfold FiniteOddFieldPresentation.vectorQuadranceCount FiniteOddFieldPresentation.vectorCountWhere
    FiniteOddFieldPresentation.ternaryQuadranceSlicedCount
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply Map.map_congr_left
  intro t _
  exact presentation.vectorSliceQuadranceCount_eq_twoSquareCount t value

/-- Exactly `q²` displayed vectors have zero quadrance in an odd field with `q` elements. -/
theorem vectorQuadranceCount_zero :
    presentation.vectorQuadranceCount 0 =
      presentation.carrier.length * presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_zero

/-- A nonzero square has `q² + q` ternary representations when minus one is a displayed square. -/
theorem vectorQuadranceCount_of_split_square
    (value minusOneRoot valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_split_square
    value minusOneRoot valueRoot valueNonzero minusOneSquare valueSquare

/-- A nonsquare has `q² - q` ternary representations when minus one is a displayed square. -/
theorem vectorQuadranceCount_of_split_nonsquare
    (value minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_split_nonsquare
    value minusOneRoot minusOneSquare valueNoRoot

/-- A nonzero square has `q² - q` ternary representations when minus one has no square root. -/
theorem vectorQuadranceCount_of_nonsplit_square
    (value valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_nonsplit_square
    value valueRoot valueNonzero minusOneNoRoot valueSquare

/-- A nonsquare has `q² + q` ternary representations when minus one has no square root. -/
theorem vectorQuadranceCount_of_nonsplit_nonsquare
    (value : K) (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_nonsplit_nonsquare
    value minusOneNoRoot valueNoRoot

/-- The enumerated zero-quadrance vectors contain no duplicates. -/
theorem nullVectors_nodup : presentation.nullVectors.Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.nullVectors
  exact Filter.pairwise_filter _ presentation.vectors_nodup

/-- The zero vector occurs in the finite null-vector carrier. -/
theorem zero_mem_nullVectors :
    (Coordinates3.Vector.zero : Coordinates3.Vector K) ∈ presentation.nullVectors := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.nullVectors
  apply Filter.mem_filter.mpr
  constructor
  · exact presentation.vectors_complete Coordinates3.Vector.zero
  · apply decide_eq_true
    unfold Coordinates3.Vector.zero Coordinates3.Vector.quadrance Coordinates3.Vector.dot
    ring1

/-- The nonzero null-vector list is the null-vector list with zero filtered out. -/
theorem nonzeroNullVectors_eq_filter_nullVectors :
    presentation.nonzeroNullVectors = by
      letI : DecidableEq K := presentation.eqDecidable
      exact presentation.nullVectors.filter fun vector => vector ≠ Coordinates3.Vector.zero := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.nonzeroNullVectors FiniteOddFieldPresentation.nullVectors
  exact Filter.filter_and_eq_filter_filter presentation.vectors
    (fun vector => decide (vector.quadrance = 0))
    (fun vector => decide (vector ≠ Coordinates3.Vector.zero))

/-- Removing the unique zero vector reduces the null-vector count by one. -/
theorem nonzeroNullVectors_length_add_one :
    presentation.nonzeroNullVectors.length + 1 =
      presentation.nullVectors.length := by
  letI : DecidableEq K := presentation.eqDecidable
  rw [presentation.nonzeroNullVectors_eq_filter_nullVectors]
  exact Filter.filter_ne_target_length_add_one
    (inferInstanceAs (DecidableEq (Coordinates3.Vector K))) Coordinates3.Vector.zero
    presentation.nullVectors_nodup presentation.zero_mem_nullVectors

/-- The null-vector list length is the executable count of quadrance zero. -/
theorem nullVectors_length_eq_vectorQuadranceCount_zero :
    presentation.nullVectors.length = presentation.vectorQuadranceCount 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.nullVectors FiniteOddFieldPresentation.vectorQuadranceCount
  rw [presentation.vectorCountWhere_eq_length_filter]

/-- The excluded affine anchor locus is counted by ternary quadrance minus one. -/
theorem excludedAnchorQuadric_length_eq_vectorQuadranceCount :
    presentation.excludedAnchorQuadric.length =
      presentation.vectorQuadranceCount (-1) := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.excludedAnchorQuadric FiniteOddFieldPresentation.vectorQuadranceCount
  rw [presentation.vectorCountWhere_eq_length_filter]

/-- Minus one is nonzero in the displayed odd-field presentation. -/
private theorem minus_one_ne_zero
    (presentation : Presentation.FiniteOddFieldPresentation K) : (-1 : K) ≠ 0 := by
  intro minusOneZero
  apply FiniteOddFieldPresentation.one_ne_zero presentation
  calc
    (1 : K) = -(-1) := by ring1
    _ = 0 := by rw [minusOneZero]; ring1

/-- The excluded affine anchor quadric has `q² + q` displayed points. -/
theorem excludedAnchorQuadric_length :
    presentation.excludedAnchorQuadric.length =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  rw [presentation.excludedAnchorQuadric_length_eq_vectorQuadranceCount]
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      exact presentation.vectorQuadranceCount_of_split_square
        (-1) root root (Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.minus_one_ne_zero presentation)
          rootSquare rootSquare
  | nonsquare minusOneNoRoot =>
      exact presentation.vectorQuadranceCount_of_nonsplit_nonsquare
        (-1) minusOneNoRoot minusOneNoRoot

/-- The excluded projective norm quadric, counted chart by chart: the affine piece `Q(v) = -1`, followed by the two null
charts at infinity. The final infinity point has norm one and contributes nothing. -/
@[expose] public def excludedProjectiveQuadricCount : Nat :=
  presentation.excludedAnchorQuadric.length +
    presentation.twoSquareCount (-1) + presentation.squareRootCount (-1)

/-- The two null charts at infinity together have `q + 1` displayed representatives. -/
private theorem infinityNullQuadricCount :
    presentation.twoSquareCount (-1) +
        presentation.squareRootCount (-1) =
      presentation.carrier.length + 1 := by
  have minusOneNonzero := Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.minus_one_ne_zero
    presentation
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      rw [presentation.twoSquareCount_of_minus_one_square_of_ne_zero
          (-1) root rootSquare minusOneNonzero,
        presentation.squareRootCount_of_nonzero_square
          (-1) root minusOneNonzero rootSquare]
      have oneLe : 1 ≤ presentation.carrier.length :=
        List.length_pos_of_mem (presentation.carrierComplete 0)
      calc
        presentation.carrier.length - 1 + 2 =
            (presentation.carrier.length - 1 + 1) + 1 := by ring1
        _ = presentation.carrier.length + 1 := by
          rw [Purelib.Data.Nat.Subtraction.sub_add_cancel oneLe]
  | nonsquare minusOneNoRoot =>
      rw [presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
          (-1) minusOneNonzero minusOneNoRoot,
        presentation.squareRootCount_of_nonsquare (-1) minusOneNoRoot,
        Nat.add_zero]

/-- The projective null conic has exactly `q+1` canonical displayed directions, independently of the square class of
`-1`. -/
theorem nullDirectionRepresentatives_length :
    presentation.nullDirectionRepresentatives.length =
      presentation.carrier.length + 1 := by
  unfold FiniteOddFieldPresentation.nullDirectionRepresentatives
  rw [Append.length_append, Map.length_map, Map.length_map]
  change presentation.twoSquareCount (-1) +
      presentation.squareRootCount (-1) = presentation.carrier.length + 1
  exact presentation.infinityNullQuadricCount

/-- The excluded projective norm quadric has `(q + 1)²` canonical representatives. -/
theorem excludedProjectiveQuadricCount_formula :
    presentation.excludedProjectiveQuadricCount =
      (presentation.carrier.length + 1) *
        (presentation.carrier.length + 1) := by
  unfold FiniteOddFieldPresentation.excludedProjectiveQuadricCount
  rw [presentation.excludedAnchorQuadric_length]
  calc
    presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length +
          presentation.twoSquareCount (-1) +
        presentation.squareRootCount (-1) =
      (presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length) +
        (presentation.twoSquareCount (-1) +
          presentation.squareRootCount (-1)) := by ring1
    _ = (presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length) +
        (presentation.carrier.length + 1) := by
      rw [presentation.infinityNullQuadricCount]
    _ = (presentation.carrier.length + 1) *
        (presentation.carrier.length + 1) := by ring1

/-- Recover a finite count by subtracting the complementary count from their total. -/
public theorem nat_eq_sub_of_add_eq_counting
    {left subtracted total : Nat} (added : left + subtracted = total) :
    left = total - subtracted := by
  calc
    left = (left + subtracted) - subtracted :=
      (Purelib.Data.Nat.Subtraction.add_sub_cancel_right left subtracted).symm
    _ = total - subtracted :=
      congrArg (fun count => count - subtracted) added

end FiniteOddFieldPresentation

/-!
# Certified rotation and projective occurrence counts

The displayed odd-field presentation retains its original finite scalar and
vector enumerations. Boolean filters and explicit bijections count canonical
projective representatives and the corresponding rotation strata.
-/

end Purelib.Algebra.Field.Finite.Odd.Presentation

end
