module

public import Purelib.Data.List.Bijection
public import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Addition
-- The exposed cardinality classifier retains these quotient and product certificates.
public import Purelib.Data.Nat.Division
public import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Remainder

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field
open Purelib.Data.List
open Purelib.Data.Nat
open scoped Purelib.Data.Nat Purelib.Data.List.Membership

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Algebra.Field.Finite.Odd

open Purelib.Data.List.Bijection

@[expose] public section

/-!
# Constructive square classes of a displayed odd finite field

This module proves that the nonzero elements of an explicit finite odd field
have exactly two square classes.  All carriers and maps are displayed lists.
In particular, the proof that a product of two nonsquares is a square uses a
finite list enumeration, not a cyclic multiplicative group or a selected
generator.
-/

namespace Purelib.Algebra.Field.Finite.Odd.SquareClasses

variable {K : Type*} [ExplicitField K]

variable (presentation : Presentation.FiniteOddFieldPresentation K)

/-- Test membership in the retained square-value table.

The Boolean computation uses the presentation's executable equality decision. -/
def FiniteOddFieldPresentation.isSquare (value : K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (value ∈ presentation.squareValues)

open FiniteOddFieldPresentation

/-- Filter the complete carrier for its square values.

Membership is checked against the retained square table while preserving carrier order. -/
def FiniteOddFieldPresentation.squareCarrierValues : List K :=
  presentation.carrier.filter (SquareClasses.FiniteOddFieldPresentation.isSquare presentation)

/-- Filter the complete carrier for its nonsquare values.

The complementary square-table test preserves carrier order and excludes zero. -/
def FiniteOddFieldPresentation.nonsquareValues : List K :=
  presentation.carrier.filter fun value => !(SquareClasses.FiniteOddFieldPresentation.isSquare presentation) value

/-- Filter the retained square table to remove zero.

The presentation's equality decision preserves the order of all nonzero square values. -/
def FiniteOddFieldPresentation.nonzeroSquareValues : List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.squareValues.filter fun value => value ≠ 0

/-- Zero belongs to the retained square table through its zero root.

Completeness of the displayed square table includes the square of zero, which
is zero for the retained field operations. -/
theorem FiniteOddFieldPresentation.zero_mem_squareValues : (0 : K) ∈ presentation.squareValues := by
  have squareMember := presentation.squareValuesComplete (0 : K)
  rw [show (0 : K) ^ 2 = 0 by rw [pow_two, MulZeroClass.mul_zero]]
    at squareMember
  exact squareMember

/-- The carrier square filter contains exactly the retained square-table values.

Carrier completeness supplies the source occurrence for every table member.
The original executable membership decision supplies the filter certificate. -/
theorem FiniteOddFieldPresentation.mem_squareCarrierValues_iff (value : K) :
    value ∈ (SquareClasses.FiniteOddFieldPresentation.squareCarrierValues presentation) ↔
      value ∈ presentation.squareValues := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold SquareClasses.FiniteOddFieldPresentation.squareCarrierValues SquareClasses.FiniteOddFieldPresentation.isSquare
  constructor
  · intro member
    exact of_decide_eq_true (Filter.mem_filter.mp member).2
  · intro member
    exact Filter.mem_filter.mpr ⟨presentation.carrierComplete value, decide_eq_true member⟩

/-- A value occurs in the nonsquare list exactly when it has no square root.

The complete carrier and certified square table make the finite test exhaustive. -/
theorem FiniteOddFieldPresentation.mem_nonsquareValues_iff (value : K) :
    value ∈ (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation) ↔
      ∀ root : K, root ^ 2 ≠ value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold SquareClasses.FiniteOddFieldPresentation.nonsquareValues SquareClasses.FiniteOddFieldPresentation.isSquare
  constructor
  · intro member root rootSquare
    have rejected := (Filter.mem_filter.mp member).2
    have valueMember := rootSquare ▸ presentation.squareValuesComplete root
    rw [decide_eq_true valueMember]
      at rejected
    nomatch rejected
  · intro noRoot
    apply Filter.mem_filter.mpr
    refine ⟨presentation.carrierComplete value, ?_⟩
    have rejected : ¬ value ∈ presentation.squareValues := by
      intro valueMember
      exact noRoot (presentation.squareRoot value)
        (presentation.squareRoot_spec value valueMember)
    rw [decide_eq_false rejected]
    rfl

/-- A scalar with no square root is nonzero.

Zero has its own zero square root. The supplied rejection certificate therefore
excludes equality of the scalar with zero. -/
theorem FiniteOddFieldPresentation.nonsquare_ne_zero {value : K}
    (noRoot : ∀ root : K, root ^ 2 ≠ value) : value ≠ 0 := by
  intro valueZero
  exact noRoot 0 (by rw [valueZero, pow_two, MulZeroClass.mul_zero])

/-- The nonzero-square list contains exactly the nonzero values having square roots.

Filtering the retained square table removes zero, and the presentation
certificates identify its remaining members with their explicit square roots. -/
theorem FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff (value : K) :
    value ∈ (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation) ↔
      value ≠ 0 ∧ Presentation.FiniteOddFieldPresentation.HasSquareRoot value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues
  constructor
  · intro member
    have retained := Filter.mem_filter.mp member
    exact ⟨of_decide_eq_true retained.2,
      (presentation.mem_squareValues_iff_hasSquareRoot value).mp retained.1⟩
  · intro data
    exact Filter.mem_filter.mpr
      ⟨(presentation.mem_squareValues_iff_hasSquareRoot value).mpr data.2,
        decide_eq_true data.1⟩

/-- The carrier square filter has no repeated values.

Every retained filtered occurrence belongs to the original complete carrier,
whose pairwise distinctness certificate is preserved by filtering. -/
theorem FiniteOddFieldPresentation.squareCarrierValues_nodup :
    (SquareClasses.FiniteOddFieldPresentation.squareCarrierValues presentation).Nodup := by
  unfold SquareClasses.FiniteOddFieldPresentation.squareCarrierValues
  exact Filter.pairwise_filter _ presentation.carrierNodup

/-- The retained nonsquare list has no repeated values.

The original carrier has distinct occurrences. Applying the complementary
Boolean test retains that certificate for the surviving entries. -/
theorem FiniteOddFieldPresentation.nonsquareValues_nodup : (SquareClasses.FiniteOddFieldPresentation.nonsquareValues
  presentation).Nodup := by
  unfold SquareClasses.FiniteOddFieldPresentation.nonsquareValues
  exact Filter.pairwise_filter _ presentation.carrierNodup

/-- The nonzero-square list has no repeated values.

The retained square table already has distinct occurrences, and removing zero
preserves their original pairwise distinctness certificate. -/
theorem FiniteOddFieldPresentation.nonzeroSquareValues_nodup :
    (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues
  exact Filter.pairwise_filter _ presentation.squareValuesNodup

/-- Identify the carrier square filter with the cached square table.

Both directions are identity maps preserving the displayed scalar values. -/
def FiniteOddFieldPresentation.squareCarrierBijection : ListBijection
    (SquareClasses.FiniteOddFieldPresentation.squareCarrierValues presentation) presentation.squareValues where
  forward := fun value => value
  backward := fun value => value
  forward_mem := by
    intro value member
    exact ((SquareClasses.FiniteOddFieldPresentation.mem_squareCarrierValues_iff presentation) value).1 member
  backward_mem := by
    intro value member
    exact ((SquareClasses.FiniteOddFieldPresentation.mem_squareCarrierValues_iff presentation) value).2 member
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

/-- The carrier square filter and cached square table have the same length. -/
theorem FiniteOddFieldPresentation.squareCarrierValues_length :
    (SquareClasses.FiniteOddFieldPresentation.squareCarrierValues presentation).length =
      presentation.squareValues.length := by
  exact ListBijection.length_eq (SquareClasses.FiniteOddFieldPresentation.squareCarrierBijection presentation)
    (SquareClasses.FiniteOddFieldPresentation.squareCarrierValues_nodup presentation) presentation.squareValuesNodup

/-- The square-table and nonsquare-list lengths add to the complete carrier length. -/
theorem FiniteOddFieldPresentation.squareValues_length_add_nonsquareValues_length :
    presentation.squareValues.length + (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length =
      presentation.carrier.length := open Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  have partition := Filter.filter_bool_add_complement_length
    presentation.carrier
    (SquareClasses.FiniteOddFieldPresentation.isSquare presentation)
  change (SquareClasses.FiniteOddFieldPresentation.squareCarrierValues presentation).length +
      (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length = presentation.carrier.length
        at partition
  rw [(SquareClasses.FiniteOddFieldPresentation.squareCarrierValues_length presentation)]
    at partition
  exact partition

/-- Removing zero shortens the certified square table by exactly one. -/
theorem FiniteOddFieldPresentation.nonzeroSquareValues_length_add_one :
    (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1 =
      presentation.squareValues.length := open Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  unfold SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues
  exact Filter.filter_ne_target_length_add_one presentation.eqDecidable 0
    presentation.squareValuesNodup (SquareClasses.FiniteOddFieldPresentation.zero_mem_squareValues presentation)

/-- The nonzero-square and nonsquare lists have equal length.

The retained odd-size count and the single zero square account for the two equal nonzero classes. -/
theorem FiniteOddFieldPresentation.nonzeroSquareValues_length_eq_nonsquareValues_length :
    (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length =
      (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length := by
  have squarePartition :=
    (SquareClasses.FiniteOddFieldPresentation.squareValues_length_add_nonsquareValues_length presentation)
  have squareCount := presentation.squareCount
  have nonsquarePlusOne : (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length + 1 =
      presentation.squareValues.length := by
    apply Addition.add_left_cancel
      (common := presentation.squareValues.length)
    calc
      presentation.squareValues.length +
          ((SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length + 1) =
        (presentation.squareValues.length +
          (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length) + 1 := by
            rw [Nat.add_assoc]
      _ = presentation.carrier.length + 1 := by rw [squarePartition]
      _ = presentation.squareValues.length +
          presentation.squareValues.length := squareCount.symm
  apply Addition.add_right_cancel
  exact calc
    (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1 =
        presentation.squareValues.length :=
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_add_one presentation)
    _ = (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length + 1 := nonsquarePlusOne.symm

section
open Purelib.Algebra.Field.Finite.Odd.SquareClasses.FiniteOddFieldPresentation
/-- The nonzero-square count is even when negative one has a displayed square root.

Negation pairs the finite nonzero-square list without fixed points. -/
theorem FiniteOddFieldPresentation.nonzeroSquareValues_length_even_of_minus_one_square
    (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1) :
    ∃ half : Nat,
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length = half + half := open
        Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  apply Nodup.fixedPointFreeInvolution_length_even presentation.eqDecidable
    (fun value : K => -value) (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation)
    (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_nodup presentation)
  · intro value member
    rcases ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) value).1 member with
      ⟨valueNonzero, valueRoot, valueSquare⟩
    apply ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) (-value)).2
    constructor
    · intro negativeZero
      apply valueNonzero
      calc
        value = -(-value) := by ring1
        _ = -0 := by rw [negativeZero]
        _ = 0 := by ring1
    · refine ⟨minusOneRoot * valueRoot, ?_⟩
      calc
        (minusOneRoot * valueRoot) ^ 2 =
            minusOneRoot ^ 2 * valueRoot ^ 2 := by ring1
        _ = (-1 : K) * value := by rw [minusOneSquare, valueSquare]
        _ = -value := by ring1
  · intro value _
    ring1
  · intro value member fixed
    have valueNonzero :=
      (((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) value).1 member).1
    have twiceZero : (2 : K) * value = 0 := by
      calc
        (2 : K) * value = value - (-value) := by ring1
        _ = 0 := by rw [fixed]; ring1
    apply valueNonzero
    have cancel := ExplicitField.mul_inv_cancel (2 : K)
      presentation.twoNonzero
    calc
      value = (2 * (2 : K)⁻¹) * value := by rw [cancel, one_mul]
      _ = (2 * value) * (2 : K)⁻¹ := by ring1
      _ = 0 := by rw [twiceZero, zero_mul]

/-- The nonzero-square count is odd when negative one has no square root.

Inversion pairs every retained nonzero square except one without fixed points. -/
theorem FiniteOddFieldPresentation.nonzeroSquareValues_length_odd_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    ∃ half : Nat,
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length = half + half + 1 := open
        Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  letI : DecidableEq K := presentation.eqDecidable
  let withoutOne := (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).filter
    fun value => value ≠ 1
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneZero
    apply presentation.twoNonzero
    calc
      (2 : K) = 1 + 1 := by ring1
      _ = 0 := by rw [oneZero, zero_add]
  have oneMember : (1 : K) ∈ (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation) :=
    ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) 1).2
      ⟨oneNonzero, ⟨1, by ring1⟩⟩
  have withoutOneNodup : withoutOne.Nodup :=
    Filter.pairwise_filter _
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_nodup presentation)
  have withoutOneClosed : ∀ value ∈ withoutOne, value⁻¹ ∈ withoutOne := by
    intro value member
    have memberData := Filter.mem_filter.mp member
    have valueNotOne : value ≠ 1 := of_decide_eq_true memberData.2
    rcases ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) value).1 memberData.1
      with
      ⟨valueNonzero, valueRoot, valueSquare⟩
    have rootNonzero : valueRoot ≠ 0 := by
      intro rootZero
      apply valueNonzero
      calc
        value = valueRoot ^ 2 := valueSquare.symm
        _ = 0 := by rw [rootZero, pow_two, MulZeroClass.mul_zero]
    have rootCancel := ExplicitField.mul_inv_cancel valueRoot rootNonzero
    have inverseSquare : valueRoot⁻¹ ^ 2 = value⁻¹ := by
      apply ExplicitField.eq_of_mul_eq_mul_right valueNonzero
      calc
        valueRoot⁻¹ ^ 2 * value = 1 := by
          rw [← valueSquare]
          calc
            valueRoot⁻¹ ^ 2 * valueRoot ^ 2 =
                (valueRoot * valueRoot⁻¹) ^ 2 := by ring1
            _ = 1 := by rw [rootCancel]; ring1
        _ = value⁻¹ * value := by
          rw [mul_comm, ExplicitField.mul_inv_cancel value valueNonzero]
    apply Filter.mem_filter.mpr
    constructor
    · apply ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) value⁻¹).2
      exact ⟨ExplicitField.inv_ne_zero valueNonzero,
        ⟨valueRoot⁻¹, inverseSquare⟩⟩
    · apply decide_eq_true
      intro inverseOne
      apply valueNotOne
      calc
        value = 1 * value := by ring1
        _ = value⁻¹ * value := by rw [inverseOne]
        _ = 1 := by
          rw [mul_comm, ExplicitField.mul_inv_cancel value valueNonzero]
  have withoutOneInvolutive :
      ∀ value ∈ withoutOne, (value⁻¹)⁻¹ = value := by
    intro value member
    have originalMember := (Filter.mem_filter.mp member).1
    have valueNonzero :=
      (((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) value).1 originalMember).1
    have inverseNonzero := ExplicitField.inv_ne_zero valueNonzero
    apply ExplicitField.eq_of_mul_eq_mul_right inverseNonzero
    calc
      (value⁻¹)⁻¹ * value⁻¹ = 1 := by
        rw [mul_comm,
          ExplicitField.mul_inv_cancel value⁻¹ inverseNonzero]
      _ = value * value⁻¹ :=
        (ExplicitField.mul_inv_cancel value valueNonzero).symm
  have withoutOneFixedPointFree :
      ∀ value ∈ withoutOne, value⁻¹ ≠ value := by
    intro value member fixed
    have memberData := Filter.mem_filter.mp member
    have valueNotOne : value ≠ 1 := of_decide_eq_true memberData.2
    rcases ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) value).1 memberData.1
      with
      ⟨valueNonzero, valueRoot, valueSquare⟩
    have squareOne : value ^ 2 = 1 := by
      calc
        value ^ 2 = value * value := by ring1
        _ = value⁻¹ * value := by rw [fixed]
        _ = 1 := by
          rw [mul_comm, ExplicitField.mul_inv_cancel value valueNonzero]
    have differenceNonzero : value - 1 ≠ 0 := by
      intro differenceZero
      apply valueNotOne
      calc
        value = (value - 1) + 1 := by ring1
        _ = 1 := by rw [differenceZero, zero_add]
    have productZero : (value - 1) * (value + 1) = 0 := by
      calc
        (value - 1) * (value + 1) = value ^ 2 - 1 := by ring1
        _ = 0 := by rw [squareOne]; ring1
    have sumZero := ExplicitField.eq_zero_of_mul_eq_zero_left
      differenceNonzero productZero
    have valueMinusOne : value = -1 := by
      calc
        value = (value + 1) - 1 := by ring1
        _ = -1 := by rw [sumZero]; ring1
    exact minusOneNoRoot valueRoot (valueSquare.trans valueMinusOne)
  rcases Nodup.fixedPointFreeInvolution_length_even presentation.eqDecidable
      (fun value : K => value⁻¹) withoutOne withoutOneNodup
      withoutOneClosed withoutOneInvolutive withoutOneFixedPointFree with
    ⟨half, halfEquation⟩
  have withoutOneLength : withoutOne.length + 1 =
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length :=
    Filter.filter_ne_target_length_add_one presentation.eqDecidable 1
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_nodup presentation) oneMember
  refine ⟨half, ?_⟩
  calc
    (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length = withoutOne.length + 1 :=
      withoutOneLength.symm
    _ = half + half + 1 := by rw [halfEquation]

end

/-- The full carrier has twice the nonzero-square count plus one element. -/
private theorem
  FiniteOddFieldPresentation.carrier_length_eq_twice_nonzeroSquares_add_one
  :
    presentation.carrier.length =
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length +
        (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1 := by
  calc
    presentation.carrier.length = presentation.squareValues.length +
        (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length :=
      (SquareClasses.FiniteOddFieldPresentation.squareValues_length_add_nonsquareValues_length presentation).symm
    _ = ((SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1) +
        (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length := by
      rw [(SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_add_one presentation),
        (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_eq_nonsquareValues_length presentation)]
    _ = (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length +
        (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1 := by ring1

/-- A displayed square root of negative one gives carrier size four times a natural number plus one.

The natural witness comes from explicit pairing of the nonzero-square list. -/
theorem FiniteOddFieldPresentation.carrier_length_eq_four_mul_add_one_of_minus_one_square
    (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1) :
    ∃ quarter : Nat,
      presentation.carrier.length = 4 * quarter + 1 := open Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  rcases (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_even_of_minus_one_square presentation)
      minusOneRoot minusOneSquare with ⟨quarter, squareLength⟩
  refine ⟨quarter, ?_⟩
  rw [(FiniteOddFieldPresentation.carrier_length_eq_twice_nonzeroSquares_add_one presentation),
    squareLength]
  ring1

/-- Absence of a square root of negative one gives carrier size four times a natural number plus three.

The natural witness comes from explicit inversion pairing away from one. -/
theorem FiniteOddFieldPresentation.carrier_length_eq_four_mul_add_three_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    ∃ quarter : Nat,
      presentation.carrier.length = 4 * quarter + 3 := open Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  rcases (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_odd_of_minus_one_nonsquare presentation)
      minusOneNoRoot with ⟨quarter, squareLength⟩
  refine ⟨quarter, ?_⟩
  rw [(FiniteOddFieldPresentation.carrier_length_eq_twice_nonzeroSquares_add_one presentation),
    squareLength]
  ring1

set_option genInjectivity false in
/-- Classify negative one together with the exact corresponding carrier-size formula.

The square branch retains a root and size four times a quarter plus one; the nonsquare branch retains a no-root proof
and size four times a quarter plus three. -/
inductive FiniteOddFieldPresentation.MinusOneCardinalityClassification where
  /-- Retain a root of negative one and the carrier-size formula four times the quarter plus one. -/ | square (root : K)
    (rootSquare : root ^ 2 = -1) (quarter : Nat)
      (cardinality : presentation.carrier.length = 4 * quarter + 1)
  /-- Retain a no-root proof for negative one and the carrier-size formula four times the quarter plus three. -/ |
    nonsquare (noRoot : ∀ root : K, root ^ 2 ≠ -1) (quarter : Nat)
      (cardinality : presentation.carrier.length = 4 * quarter + 3)

constructive_injectivity FiniteOddFieldPresentation.MinusOneCardinalityClassification

open Purelib.Algebra.Field.Finite.Odd.SquareClasses.FiniteOddFieldPresentation in
/-- Compute the negative-one square alternative and its certified carrier-size formula.

The retained square table chooses the branch, and the nonzero-square count computes the quarter witness. -/
def FiniteOddFieldPresentation.classifyMinusOneCardinality :
    (MinusOneCardinalityClassification presentation) := by
  have carrierLength :
      presentation.carrier.length =
        (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length +
          (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1 := by
    calc
      presentation.carrier.length = presentation.squareValues.length +
          (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation).length :=
        (SquareClasses.FiniteOddFieldPresentation.squareValues_length_add_nonsquareValues_length presentation).symm
      _ = ((SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1) +
          (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length := by
        rw [(SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_add_one presentation),
          (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_eq_nonsquareValues_length presentation)]
      _ = (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length +
          (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length + 1 := by ring1
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      refine MinusOneCardinalityClassification.square root rootSquare
        ((SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length / 2) ?_
      rcases (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_even_of_minus_one_square presentation)
          root rootSquare with ⟨quarter, squareLength⟩
      have doubled : quarter + quarter = 2 * quarter := by
        rw [Nat.succ_mul, Nat.one_mul]
      rw [carrierLength, squareLength, doubled,
        Division.mul_div_cancel_left quarter (by decide : 0 < 2)]
      rw [show (4 : Nat) = 2 + 2 from rfl, Multiplication.right_distrib]
  | nonsquare noRoot =>
      refine MinusOneCardinalityClassification.nonsquare noRoot
        ((SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).length / 2) ?_
      rcases (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_odd_of_minus_one_nonsquare
        presentation)
          noRoot with ⟨quarter, squareLength⟩
      have doubled : quarter + quarter = 2 * quarter := by
        rw [Nat.succ_mul, Nat.one_mul]
      have retainedQuarter : (quarter + quarter + 1) / 2 = quarter := by
        rw [doubled, Division.mul_add_div (by decide : 0 < 2),
          show 1 / 2 = 0 from by decide, Nat.add_zero]
      rw [carrierLength, squareLength, retainedQuarter, doubled]
      rw [show (4 : Nat) = 2 + 2 from rfl, Multiplication.right_distrib,
        Nat.succ_add]
      repeat first | rw [Nat.add_succ] | rw [Nat.add_zero]

/-- A displayed square root of negative one makes the carrier length congruent to one modulo four.

The certified carrier length is four times its retained quarter plus one.
Removing that displayed multiple leaves remainder one. -/
theorem FiniteOddFieldPresentation.carrier_length_mod_four_eq_one_of_minus_one_square
    (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1) :
    presentation.carrier.length % 4 = 1 := by
  rcases (SquareClasses.FiniteOddFieldPresentation.carrier_length_eq_four_mul_add_one_of_minus_one_square presentation)
      minusOneRoot minusOneSquare with ⟨quarter, cardinality⟩
  rw [cardinality, Remainder.mul_add_mod]

/-- Absence of a square root of negative one makes the carrier length congruent to three modulo four.

The certified carrier length is four times its retained quarter plus three.
Removing that displayed multiple leaves remainder three. -/
theorem FiniteOddFieldPresentation.carrier_length_mod_four_eq_three_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.carrier.length % 4 = 3 := by
  rcases (SquareClasses.FiniteOddFieldPresentation.carrier_length_eq_four_mul_add_three_of_minus_one_nonsquare
    presentation)
      minusOneNoRoot with ⟨quarter, cardinality⟩
  rw [cardinality, Remainder.mul_add_mod]

/-- Negative one has a square root exactly when the retained carrier length is one modulo four.

The square-table classification makes both directions constructive. -/
theorem FiniteOddFieldPresentation.minusOne_hasSquareRoot_iff_carrier_length_mod_four_eq_one :
    Presentation.FiniteOddFieldPresentation.HasSquareRoot (-1 : K) ↔ presentation.carrier.length % 4 = 1 := by
  constructor
  · rintro ⟨root, rootSquare⟩
    exact (SquareClasses.FiniteOddFieldPresentation.carrier_length_mod_four_eq_one_of_minus_one_square presentation)
      root rootSquare
  · intro cardinalityModFour
    cases presentation.classifyMinusOne with
    | square root rootSquare => exact ⟨root, rootSquare⟩
    | nonsquare noRoot =>
        have nonsquareModFour :=
          (SquareClasses.FiniteOddFieldPresentation.carrier_length_mod_four_eq_three_of_minus_one_nonsquare
            presentation)
            noRoot
        exact False.elim ((by decide : (1 : Nat) ≠ 3)
          (cardinalityModFour.symm.trans nonsquareModFour))

/-- Negative one has no square root exactly when the retained carrier length is three modulo four.

The square-table classification makes both directions constructive. -/
theorem FiniteOddFieldPresentation.minusOne_noRoot_iff_carrier_length_mod_four_eq_three :
    (∀ root : K, root ^ 2 ≠ -1) ↔ presentation.carrier.length % 4 = 3 := by
  constructor
  · exact (SquareClasses.FiniteOddFieldPresentation.carrier_length_mod_four_eq_three_of_minus_one_nonsquare
      presentation)
  · intro cardinalityModFour
    cases presentation.classifyMinusOne with
    | square root rootSquare =>
        have squareModFour :=
          (SquareClasses.FiniteOddFieldPresentation.carrier_length_mod_four_eq_one_of_minus_one_square presentation)
            root rootSquare
        exact False.elim ((by decide : (1 : Nat) ≠ 3)
          (squareModFour.symm.trans cardinalityModFour))
    | nonsquare noRoot => exact noRoot

set_option genInjectivity false in
/-- A retained scalar with a certificate that no square root exists.

The scalar is executable data and is necessarily nonzero. -/
structure FiniteOddFieldPresentation.NonsquareWitness where
  /-- The retained nonsquare scalar. -/ value : K
  /-- No scalar square equals the retained value. -/ noRoot : ∀ root : K, root ^ 2 ≠ value

constructive_injectivity FiniteOddFieldPresentation.NonsquareWitness

open Purelib.Algebra.Field.Finite.Odd.SquareClasses.FiniteOddFieldPresentation in
/-- Select the first value in the retained nonsquare list.

The equal nonzero-square and nonsquare counts and the displayed square one certify that this finite list is nonempty. -/
def FiniteOddFieldPresentation.chosenNonsquare : NonsquareWitness (K := K) := by
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneZero
    apply presentation.twoNonzero
    calc
      (2 : K) = 1 + 1 := by ring1
      _ = 0 := by rw [oneZero, zero_add]
  have oneMember : (1 : K) ∈ (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation) :=
    ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) 1).2
      ⟨oneNonzero, ⟨1, by ring1⟩⟩
  have equalLengths :=
    (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_eq_nonsquareValues_length presentation)
  cases valuesEquation : (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation) with
  | nil =>
      have positive := List.length_pos_of_mem oneMember
      rw [equalLengths, valuesEquation] at positive
      exact False.elim (Nat.lt_irrefl 0 positive)
  | cons head tail =>
      refine ⟨head, ?_⟩
      apply ((SquareClasses.FiniteOddFieldPresentation.mem_nonsquareValues_iff presentation) head).1
      rw [valuesEquation]
      exact List.mem_cons_self

/-- Multiply each retained nonzero square by a fixed scalar.

The mapped list keeps the original square-table order. -/
def FiniteOddFieldPresentation.scaledNonzeroSquareValues (factor : K) : List K :=
  (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation).map fun value => factor * value

/-- Scaling the nonzero-square list by a nonzero factor preserves distinctness. -/
theorem FiniteOddFieldPresentation.scaledNonzeroSquareValues_nodup (factor : K)
    (factorNonzero : factor ≠ 0) :
    ((SquareClasses.FiniteOddFieldPresentation.scaledNonzeroSquareValues presentation) factor).Nodup := open Purelib in
      by
  unfold SquareClasses.FiniteOddFieldPresentation.scaledNonzeroSquareValues
  apply Data.List.Nodup.nodup_map_of_injective
  · intro left right equal
    change factor * left = factor * right at equal
    have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
    calc
      left = (factor * factor⁻¹) * left := by rw [cancel, one_mul]
      _ = factor⁻¹ * (factor * left) := by ring1
      _ = factor⁻¹ * (factor * right) := by rw [equal]
      _ = (factor * factor⁻¹) * right := by ring1
      _ = right := by rw [cancel, one_mul]
  · exact (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_nodup presentation)

/-- Multiplying a nonzero square by a nonsquare yields a retained nonsquare.

A hypothetical product root divided by the square root would contradict the supplied factor obstruction. -/
theorem FiniteOddFieldPresentation.scaledNonzeroSquareValues_contained_in_nonsquares
    (factor : K) (factorNoRoot : ∀ root : K, root ^ 2 ≠ factor) :
    ∀ value ∈ (SquareClasses.FiniteOddFieldPresentation.scaledNonzeroSquareValues presentation) factor,
      value ∈ (SquareClasses.FiniteOddFieldPresentation.nonsquareValues presentation) := open
        Purelib.Algebra.Field.Finite.Odd.SquareClasses in open Purelib in by
  intro value member
  rcases Data.List.Map.mem_map.mp member with
    ⟨squareValue, squareMember, equal⟩
  rcases ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) squareValue).1
      squareMember with ⟨squareNonzero, squareRoot, squareEquation⟩
  apply ((SquareClasses.FiniteOddFieldPresentation.mem_nonsquareValues_iff presentation) value).2
  intro productRoot productEquation
  apply factorNoRoot (productRoot / squareRoot)
  apply Squares.quotient_square_of_product_square squareNonzero squareEquation
  calc
    productRoot ^ 2 = value := productEquation
    _ = factor * squareValue := equal.symm

/-- Every nonsquare is a fixed nonsquare times a retained nonzero square.

The scaled square list is duplicate-free, contained in the nonsquare list and has the same finite length. -/
theorem FiniteOddFieldPresentation.nonsquare_mem_scaledNonzeroSquareValues
    (factor : K) (factorNoRoot : ∀ root : K, root ^ 2 ≠ factor)
    {value : K} (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    value ∈ (SquareClasses.FiniteOddFieldPresentation.scaledNonzeroSquareValues presentation) factor := open
      Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  have factorNonzero := SquareClasses.FiniteOddFieldPresentation.nonsquare_ne_zero factorNoRoot
  apply Nodup.mem_of_nodup_contained_length_eq presentation.eqDecidable
    ((SquareClasses.FiniteOddFieldPresentation.scaledNonzeroSquareValues_nodup presentation) factor factorNonzero)
    (SquareClasses.FiniteOddFieldPresentation.nonsquareValues_nodup presentation)
    ((SquareClasses.FiniteOddFieldPresentation.scaledNonzeroSquareValues_contained_in_nonsquares presentation)
      factor factorNoRoot)
  · unfold SquareClasses.FiniteOddFieldPresentation.scaledNonzeroSquareValues
    rw [Map.length_map,
      (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues_length_eq_nonsquareValues_length presentation)]
  · exact ((SquareClasses.FiniteOddFieldPresentation.mem_nonsquareValues_iff presentation) value).2 valueNoRoot

section
open Purelib.Algebra.Field.Finite.Odd.SquareClasses.FiniteOddFieldPresentation
/-- Search a finite list for the first scalar whose product with the factor is the target.

The left-to-right search uses supplied decidable equality and returns none precisely when the displayed candidates
contain no match. -/
def FiniteOddFieldPresentation.scaledPreimage? (eqDecidable : DecidableEq K)
    (factor target : K) : List K → Option K
  | [] => none
  | head :: tail =>
      match eqDecidable (factor * head) target with
      | isTrue _ => some head
      | isFalse _ => scaledPreimage? eqDecidable factor target tail

/-- A target belonging to the scaled candidate list makes the finite preimage search succeed. -/
theorem FiniteOddFieldPresentation.scaledPreimage?_ne_none_of_mem
    (eqDecidable : DecidableEq K) (factor target : K) :
    ∀ values : List K, target ∈ values.map (fun value => factor * value) →
      scaledPreimage? eqDecidable factor target values ≠ none
  | [], impossible => by nomatch impossible
  | head :: tail, member => by
      unfold scaledPreimage?
      rcases Membership.mem_cons.mp member with headEqual | tailMember
      · cases equal : eqDecidable (factor * head) target with
        | isTrue _ =>
            intro impossible
            nomatch impossible
        | isFalse headDifferent =>
            exact False.elim (headDifferent headEqual.symm)
      · cases equal : eqDecidable (factor * head) target with
        | isTrue _ =>
            intro impossible
            nomatch impossible
        | isFalse _ =>
            exact scaledPreimage?_ne_none_of_mem eqDecidable factor
              target tail tailMember

/-- A successful scaled preimage search returns a retained candidate satisfying the target product equation. -/
theorem FiniteOddFieldPresentation.scaledPreimage?_eq_some_spec
    (eqDecidable : DecidableEq K) (factor target selected : K) :
    ∀ values : List K,
      scaledPreimage? eqDecidable factor target values = some selected →
        selected ∈ values ∧ factor * selected = target
  | [], impossible => by nomatch impossible
  | head :: tail, found => by
      unfold scaledPreimage? at found
      cases equal : eqDecidable (factor * head) target with
      | isTrue headEqual =>
          rw [equal]
            at found
          injection found with selectedEqual
          exact ⟨Membership.mem_cons.mpr (Or.inl selectedEqual.symm),
            selectedEqual ▸ headEqual⟩
      | isFalse headDifferent =>
          rw [equal] at found
          rcases scaledPreimage?_eq_some_spec eqDecidable factor target
              selected tail found with ⟨member, product⟩
          exact ⟨List.mem_cons_of_mem head member, product⟩

end

set_option genInjectivity false in
/-- A retained scalar root with its exact indexed square equation. -/
structure FiniteOddFieldPresentation.SquareRootWitness (value : K) where
  /-- The retained square root. -/ root : K
  /-- The retained root squares to the indexed value. -/ equation : root ^ 2 = value

constructive_injectivity FiniteOddFieldPresentation.SquareRootWitness

open Purelib.Algebra.Field.Finite.Odd.SquareClasses.FiniteOddFieldPresentation in
open Purelib.Algebra.Field.Finite.Odd.SquareClasses.FiniteOddFieldPresentation in
/-- Construct a square root of the product of two certified nonsquares.

A finite scaled-preimage search locates a nonzero square value, whose cached root gives the returned product root. -/
def FiniteOddFieldPresentation.nonsquareMulNonsquareSquareWitness
    (presentation : Presentation.FiniteOddFieldPresentation K)
    (left right : K) (leftNoRoot : ∀ root : K, root ^ 2 ≠ left)
    (rightNoRoot : ∀ root : K, root ^ 2 ≠ right) :
    SquareRootWitness (left * right) := by
  let values := (SquareClasses.FiniteOddFieldPresentation.nonzeroSquareValues presentation)
  let found := scaledPreimage? presentation.eqDecidable left right values
  have rightMember := SquareClasses.FiniteOddFieldPresentation.nonsquare_mem_scaledNonzeroSquareValues presentation
    left leftNoRoot rightNoRoot
  have foundNonempty : found ≠ none := by
    exact scaledPreimage?_ne_none_of_mem presentation.eqDecidable
      left right values rightMember
  cases foundEquation : found with
  | none => exact False.elim (foundNonempty foundEquation)
  | some squareValue =>
      have foundSpec := scaledPreimage?_eq_some_spec
        presentation.eqDecidable left right squareValue values foundEquation
      have squareData :=
        ((SquareClasses.FiniteOddFieldPresentation.mem_nonzeroSquareValues_iff presentation) squareValue).1 foundSpec.1
      let root := presentation.squareRoot squareValue
      have rootSquare : root ^ 2 = squareValue := by
        exact presentation.squareRoot_spec squareValue
          ((presentation.mem_squareValues_iff_hasSquareRoot squareValue).2
            squareData.2)
      refine ⟨left * root, ?_⟩
      calc
        (left * root) ^ 2 = left * (left * squareValue) := by
          rw [← rootSquare]
          ring1
        _ = left * right := by rw [foundSpec.2]

/-- The product of two certified nonsquares has a displayed square root.

The root is read from the finite search construction and its retained equation. -/
theorem FiniteOddFieldPresentation.nonsquare_mul_nonsquare_hasSquareRoot
    (presentation : Presentation.FiniteOddFieldPresentation K)
    (left right : K) (leftNoRoot : ∀ root : K, root ^ 2 ≠ left)
    (rightNoRoot : ∀ root : K, root ^ 2 ≠ right) :
    Presentation.FiniteOddFieldPresentation.HasSquareRoot (left * right) := by
  let witness := (SquareClasses.FiniteOddFieldPresentation.nonsquareMulNonsquareSquareWitness presentation)
    left right leftNoRoot rightNoRoot
  exact ⟨witness.root, witness.equation⟩

/-- A nonzero displayed square times a nonsquare has no square root.

Any proposed product root divided by the supplied nonzero square root would produce a forbidden nonsquare root. -/
theorem FiniteOddFieldPresentation.square_mul_nonsquare_noRoot
    (squareValue squareRoot nonsquare : K)
    (squareNonzero : squareValue ≠ 0)
    (squareEquation : squareRoot ^ 2 = squareValue)
    (nonsquareNoRoot : ∀ root : K, root ^ 2 ≠ nonsquare) :
    ∀ root : K, root ^ 2 ≠ squareValue * nonsquare := open Purelib.Algebra.Field.Finite.Odd.SquareClasses in by
  intro productRoot productEquation
  apply nonsquareNoRoot (productRoot / squareRoot)
  apply Squares.quotient_square_of_product_square squareNonzero squareEquation
  calc
    productRoot ^ 2 = squareValue * nonsquare := productEquation
    _ = nonsquare * squareValue := by ring1

end Purelib.Algebra.Field.Finite.Odd.SquareClasses
