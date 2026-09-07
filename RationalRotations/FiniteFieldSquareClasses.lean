import RationalRotations.FiniteFieldQuadrics

/-!
# Constructive square classes of a displayed odd finite field

This module proves that the nonzero elements of an explicit finite odd field
have exactly two square classes.  All carriers and maps are displayed lists.
In particular, the proof that a product of two nonsquares is a square uses a
finite list enumeration, not a cyclic multiplicative group or a selected
generator.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

namespace FiniteOddFieldPresentation

variable (presentation : FiniteOddFieldPresentation K)

/-- Executable square-membership test against the cached square table. -/
def isSquare (value : K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (value ∈ presentation.squareValues)

/-- The elements of the complete carrier that occur in the square table. -/
def squareCarrierValues : List K :=
  presentation.carrier.filter presentation.isSquare

/-- The displayed nonsquares.  Zero is absent because it occurs in the square
table through the displayed root zero. -/
def nonsquareValues : List K :=
  presentation.carrier.filter fun value => !presentation.isSquare value

/-- The displayed nonzero square values. -/
def nonzeroSquareValues : List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.squareValues.filter fun value => value ≠ 0

theorem zero_mem_squareValues : (0 : K) ∈ presentation.squareValues := by
  have squareMember := presentation.squareValuesComplete (0 : K)
  rw [show (0 : K) ^ 2 = 0 by ring1] at squareMember
  exact squareMember

theorem mem_squareCarrierValues_iff (value : K) :
    value ∈ presentation.squareCarrierValues ↔
      value ∈ presentation.squareValues := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold squareCarrierValues isSquare
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  exact and_iff_right (presentation.carrierComplete value)

theorem mem_nonsquareValues_iff (value : K) :
    value ∈ presentation.nonsquareValues ↔
      ∀ root : K, root ^ 2 ≠ value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonsquareValues isSquare
  rw [List.mem_filter]
  constructor
  · intro member root rootSquare
    have notSquare : decide (value ∈ presentation.squareValues) = false :=
      Eq.mp (Bool.not_eq_true' _) member.2
    have valueMember := rootSquare ▸ presentation.squareValuesComplete root
    exact (decide_eq_false_iff_not.mp notSquare) valueMember
  · intro noRoot
    constructor
    · exact presentation.carrierComplete value
    · apply Eq.mpr (Bool.not_eq_true' _)
      apply decide_eq_false
      intro valueMember
      exact noRoot (presentation.squareRoot value)
        (presentation.squareRoot_spec value valueMember)

theorem nonsquare_ne_zero {value : K}
    (noRoot : ∀ root : K, root ^ 2 ≠ value) : value ≠ 0 := by
  intro valueZero
  exact noRoot 0 (by rw [valueZero]; ring1)

theorem mem_nonzeroSquareValues_iff (value : K) :
    value ∈ presentation.nonzeroSquareValues ↔
      value ≠ 0 ∧ HasSquareRoot value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroSquareValues
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · intro member
    exact ⟨member.2,
      (presentation.mem_squareValues_iff_hasSquareRoot value).1 member.1⟩
  · intro data
    exact ⟨(presentation.mem_squareValues_iff_hasSquareRoot value).2 data.2,
      data.1⟩

theorem squareCarrierValues_nodup :
    presentation.squareCarrierValues.Nodup := by
  unfold squareCarrierValues
  exact presentation.carrierNodup.filter _

theorem nonsquareValues_nodup : presentation.nonsquareValues.Nodup := by
  unfold nonsquareValues
  exact presentation.carrierNodup.filter _

theorem nonzeroSquareValues_nodup :
    presentation.nonzeroSquareValues.Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroSquareValues
  exact presentation.squareValuesNodup.filter _

/-- The square entries of the carrier and the cached square table are the
same displayed set, with identity maps in both directions. -/
def squareCarrierBijection : FiniteListBijection
    presentation.squareCarrierValues presentation.squareValues where
  forward := fun value => value
  backward := fun value => value
  forward_mem := by
    intro value member
    exact (presentation.mem_squareCarrierValues_iff value).1 member
  backward_mem := by
    intro value member
    exact (presentation.mem_squareCarrierValues_iff value).2 member
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

theorem squareCarrierValues_length :
    presentation.squareCarrierValues.length =
      presentation.squareValues.length := by
  exact FiniteListBijection.length_eq presentation.squareCarrierBijection
    presentation.squareCarrierValues_nodup presentation.squareValuesNodup

private theorem filter_bool_add_complement_length {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) :
    (values.filter predicate).length +
      (values.filter fun value => !predicate value).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.filter_cons, List.filter_cons]
      cases accepted : predicate head with
      | false =>
          rw [Bool.not_false]
          change (tail.filter predicate).length +
              Nat.succ (tail.filter fun value => !predicate value).length =
            Nat.succ tail.length
          rw [Nat.add_succ, inductionHypothesis]
      | true =>
          rw [Bool.not_true]
          change Nat.succ (tail.filter predicate).length +
              (tail.filter fun value => !predicate value).length =
            Nat.succ tail.length
          rw [Nat.succ_add, inductionHypothesis]

theorem squareValues_length_add_nonsquareValues_length :
    presentation.squareValues.length + presentation.nonsquareValues.length =
      presentation.carrier.length := by
  have partition := filter_bool_add_complement_length presentation.carrier
    presentation.isSquare
  change presentation.squareCarrierValues.length +
      presentation.nonsquareValues.length = presentation.carrier.length at partition
  rw [presentation.squareCarrierValues_length] at partition
  exact partition

private theorem filter_ne_target_eq_self {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (target : Alpha) :
    ∀ {values : List Alpha}, (∀ value ∈ values, value ≠ target) →
      (letI : DecidableEq Alpha := eqDecidable
       values.filter fun value => value ≠ target) = values
  | [], _ => rfl
  | head :: tail, allNonzero => by
      letI : DecidableEq Alpha := eqDecidable
      rw [List.filter_cons_of_pos
        (p := fun value : Alpha => decide (value ≠ target))
        (decide_eq_true (allNonzero head List.mem_cons_self))]
      rw [filter_ne_target_eq_self eqDecidable target (fun value member =>
        allNonzero value (List.mem_cons_of_mem head member))]

private theorem filter_ne_target_length_add_one {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (target : Alpha) :
    ∀ {values : List Alpha}, values.Nodup → target ∈ values →
      (letI : DecidableEq Alpha := eqDecidable
       (values.filter fun value => value ≠ target).length + 1) = values.length
  | [], _, impossible => nomatch impossible
  | head :: tail, nodup, targetMember => by
      letI : DecidableEq Alpha := eqDecidable
      cases eqDecidable head target with
      | isTrue headZero =>
          have tailNonzero : ∀ value ∈ tail, value ≠ target := by
            intro value member valueZero
            apply (List.pairwise_cons.mp nodup).1 value member
            exact headZero.trans valueZero.symm
          rw [List.filter_cons_of_neg
            (p := fun value : Alpha => decide (value ≠ target))
            (fun accepted => (of_decide_eq_true accepted) headZero)]
          have unchanged := filter_ne_target_eq_self eqDecidable target tailNonzero
          rw [unchanged, List.length_cons]
      | isFalse headNonzero =>
          rw [List.filter_cons_of_pos
            (p := fun value : Alpha => decide (value ≠ target))
            (decide_eq_true headNonzero)]
          have tailZero : target ∈ tail := by
            rcases List.mem_cons.mp targetMember with headZero | member
            · exact False.elim (headNonzero headZero.symm)
            · exact member
          have induction := filter_ne_target_length_add_one eqDecidable target
            (List.pairwise_cons.mp nodup).2 tailZero
          exact congrArg Nat.succ induction

/-- A displayed duplicate-free carrier with a fixed-point-free involution can
be consumed in explicit pairs.  The proof recursively removes the mate of the
head, so it uses neither a quotient nor a chosen orbit representative. -/
private theorem fixedPointFreeInvolution_length_even {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (involution : Alpha → Alpha)
    (values : List Alpha) (nodup : values.Nodup)
    (closed : ∀ value ∈ values, involution value ∈ values)
    (involutive : ∀ value ∈ values, involution (involution value) = value)
    (fixedPointFree : ∀ value ∈ values, involution value ≠ value) :
    ∃ half : Nat, values.length = half + half := by
  letI : DecidableEq Alpha := eqDecidable
  cases values with
  | nil => exact ⟨0, rfl⟩
  | cons head tail =>
      let mate := involution head
      let remainder := tail.filter fun value => value ≠ mate
      have headMember : head ∈ head :: tail := List.mem_cons_self
      have mateMember : mate ∈ head :: tail := closed head headMember
      have mateDifferent : mate ≠ head := fixedPointFree head headMember
      have mateTail : mate ∈ tail := by
        rcases List.mem_cons.mp mateMember with mateHead | member
        · exact False.elim (mateDifferent mateHead)
        · exact member
      have tailNodup : tail.Nodup := (List.pairwise_cons.mp nodup).2
      have remainderNodup : remainder.Nodup := tailNodup.filter _
      have remainderClosed :
          ∀ value ∈ remainder, involution value ∈ remainder := by
        intro value member
        have memberData := List.mem_filter.mp member
        have valueTail : value ∈ tail := memberData.1
        have valueDifferentMate : value ≠ mate :=
          of_decide_eq_true memberData.2
        have valueMember : value ∈ head :: tail :=
          List.mem_cons_of_mem head valueTail
        have imageMember := closed value valueMember
        have imageDifferentHead : involution value ≠ head := by
          intro imageHead
          apply valueDifferentMate
          calc
            value = involution (involution value) :=
              (involutive value valueMember).symm
            _ = involution head := congrArg involution imageHead
            _ = mate := rfl
        have imageTail : involution value ∈ tail := by
          rcases List.mem_cons.mp imageMember with imageHead | member
          · exact False.elim (imageDifferentHead imageHead)
          · exact member
        apply List.mem_filter.mpr
        constructor
        · exact imageTail
        · apply decide_eq_true
          intro imageMate
          have headEqual : value = head := by
            calc
              value = involution (involution value) :=
                (involutive value valueMember).symm
              _ = involution mate := congrArg involution imageMate
              _ = head := by
                exact involutive head headMember
          exact (List.pairwise_cons.mp nodup).1 value valueTail headEqual.symm
      have remainderInvolutive :
          ∀ value ∈ remainder, involution (involution value) = value := by
        intro value member
        exact involutive value
          (List.mem_cons_of_mem head (List.mem_filter.mp member).1)
      have remainderFixedPointFree :
          ∀ value ∈ remainder, involution value ≠ value := by
        intro value member
        exact fixedPointFree value
          (List.mem_cons_of_mem head (List.mem_filter.mp member).1)
      have remainderShorter : remainder.length < (head :: tail).length :=
        Nat.lt_succ_of_le (List.length_filter_le _ _)
      have induction := fixedPointFreeInvolution_length_even
        eqDecidable involution remainder remainderNodup remainderClosed
        remainderInvolutive remainderFixedPointFree
      rcases induction with ⟨half, halfEquation⟩
      have remainderLength : remainder.length + 1 = tail.length :=
        filter_ne_target_length_add_one eqDecidable mate tailNodup mateTail
      refine ⟨half + 1, ?_⟩
      rw [List.length_cons, ← remainderLength, halfEquation]
      ring1
termination_by values.length
decreasing_by
  simp_all only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem nonzeroSquareValues_length_add_one :
    presentation.nonzeroSquareValues.length + 1 =
      presentation.squareValues.length := by
  unfold nonzeroSquareValues
  exact filter_ne_target_length_add_one presentation.eqDecidable 0
    presentation.squareValuesNodup presentation.zero_mem_squareValues

/-- The nonzero squares and nonsquares have equal displayed cardinality. -/
theorem nonzeroSquareValues_length_eq_nonsquareValues_length :
    presentation.nonzeroSquareValues.length =
      presentation.nonsquareValues.length := by
  have squarePartition :=
    presentation.squareValues_length_add_nonsquareValues_length
  have squareCount := presentation.squareCount
  have nonsquarePlusOne : presentation.nonsquareValues.length + 1 =
      presentation.squareValues.length := by
    apply Nat.add_left_cancel
      (n := presentation.squareValues.length)
    calc
      presentation.squareValues.length +
          (presentation.nonsquareValues.length + 1) =
        (presentation.squareValues.length +
          presentation.nonsquareValues.length) + 1 := by
            rw [Nat.add_assoc]
      _ = presentation.carrier.length + 1 := by rw [squarePartition]
      _ = presentation.squareValues.length +
          presentation.squareValues.length := squareCount.symm
  apply Nat.add_right_cancel
  exact calc
    presentation.nonzeroSquareValues.length + 1 =
        presentation.squareValues.length :=
      presentation.nonzeroSquareValues_length_add_one
    _ = presentation.nonsquareValues.length + 1 := nonsquarePlusOne.symm

private theorem eq_of_mul_right_eq {left right factor : K}
    (factorNonzero : factor ≠ 0) (equal : left * factor = right * factor) :
    left = right := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * (factor * factor⁻¹) := by rw [cancel, mul_one]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [equal]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [cancel, mul_one]

private theorem eq_zero_of_nonzero_mul_eq_zero {factor value : K}
    (factorNonzero : factor ≠ 0) (productZero : factor * value = 0) :
    value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

/-- If `-1` is a displayed square, negation pairs the displayed nonzero
squares without fixed points. -/
theorem nonzeroSquareValues_length_even_of_minus_one_square
    (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1) :
    ∃ half : Nat,
      presentation.nonzeroSquareValues.length = half + half := by
  apply fixedPointFreeInvolution_length_even presentation.eqDecidable
    (fun value : K => -value) presentation.nonzeroSquareValues
    presentation.nonzeroSquareValues_nodup
  · intro value member
    rcases (presentation.mem_nonzeroSquareValues_iff value).1 member with
      ⟨valueNonzero, valueRoot, valueSquare⟩
    apply (presentation.mem_nonzeroSquareValues_iff (-value)).2
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
      ((presentation.mem_nonzeroSquareValues_iff value).1 member).1
    have twiceZero : (2 : K) * value = 0 := by
      calc
        (2 : K) * value = value - (-value) := by ring1
        _ = 0 := by rw [fixed]; ring1
    apply valueNonzero
    have cancel := RFAP.ExplicitField.mul_inv_cancel (2 : K)
      presentation.twoNonzero
    calc
      value = (2 * (2 : K)⁻¹) * value := by rw [cancel, one_mul]
      _ = (2 * value) * (2 : K)⁻¹ := by ring1
      _ = 0 := by rw [twiceZero, zero_mul]

/-- If `-1` is a nonsquare, inversion pairs all displayed nonzero squares
except `1`. -/
theorem nonzeroSquareValues_length_odd_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    ∃ half : Nat,
      presentation.nonzeroSquareValues.length = half + half + 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  let withoutOne := presentation.nonzeroSquareValues.filter
    fun value => value ≠ 1
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneZero
    apply presentation.twoNonzero
    calc
      (2 : K) = 1 + 1 := by ring1
      _ = 0 := by rw [oneZero, zero_add]
  have oneMember : (1 : K) ∈ presentation.nonzeroSquareValues :=
    (presentation.mem_nonzeroSquareValues_iff 1).2
      ⟨oneNonzero, ⟨1, by ring1⟩⟩
  have withoutOneNodup : withoutOne.Nodup :=
    presentation.nonzeroSquareValues_nodup.filter _
  have withoutOneClosed : ∀ value ∈ withoutOne, value⁻¹ ∈ withoutOne := by
    intro value member
    have memberData := List.mem_filter.mp member
    have valueNotOne : value ≠ 1 := of_decide_eq_true memberData.2
    rcases (presentation.mem_nonzeroSquareValues_iff value).1 memberData.1 with
      ⟨valueNonzero, valueRoot, valueSquare⟩
    have rootNonzero : valueRoot ≠ 0 := by
      intro rootZero
      apply valueNonzero
      calc
        value = valueRoot ^ 2 := valueSquare.symm
        _ = 0 := by rw [rootZero]; ring1
    have rootCancel := RFAP.ExplicitField.mul_inv_cancel valueRoot rootNonzero
    have inverseSquare : valueRoot⁻¹ ^ 2 = value⁻¹ := by
      apply eq_of_mul_right_eq valueNonzero
      calc
        valueRoot⁻¹ ^ 2 * value = 1 := by
          rw [← valueSquare]
          calc
            valueRoot⁻¹ ^ 2 * valueRoot ^ 2 =
                (valueRoot * valueRoot⁻¹) ^ 2 := by ring1
            _ = 1 := by rw [rootCancel]; ring1
        _ = value⁻¹ * value := by
          rw [mul_comm, RFAP.ExplicitField.mul_inv_cancel value valueNonzero]
    apply List.mem_filter.mpr
    constructor
    · apply (presentation.mem_nonzeroSquareValues_iff value⁻¹).2
      exact ⟨RFAP.ExplicitField.inv_ne_zero valueNonzero,
        ⟨valueRoot⁻¹, inverseSquare⟩⟩
    · apply decide_eq_true
      intro inverseOne
      apply valueNotOne
      calc
        value = 1 * value := by ring1
        _ = value⁻¹ * value := by rw [inverseOne]
        _ = 1 := by
          rw [mul_comm, RFAP.ExplicitField.mul_inv_cancel value valueNonzero]
  have withoutOneInvolutive :
      ∀ value ∈ withoutOne, (value⁻¹)⁻¹ = value := by
    intro value member
    have originalMember := (List.mem_filter.mp member).1
    have valueNonzero :=
      ((presentation.mem_nonzeroSquareValues_iff value).1 originalMember).1
    have inverseNonzero := RFAP.ExplicitField.inv_ne_zero valueNonzero
    apply eq_of_mul_right_eq inverseNonzero
    calc
      (value⁻¹)⁻¹ * value⁻¹ = 1 := by
        rw [mul_comm,
          RFAP.ExplicitField.mul_inv_cancel value⁻¹ inverseNonzero]
      _ = value * value⁻¹ :=
        (RFAP.ExplicitField.mul_inv_cancel value valueNonzero).symm
  have withoutOneFixedPointFree :
      ∀ value ∈ withoutOne, value⁻¹ ≠ value := by
    intro value member fixed
    have memberData := List.mem_filter.mp member
    have valueNotOne : value ≠ 1 := of_decide_eq_true memberData.2
    rcases (presentation.mem_nonzeroSquareValues_iff value).1 memberData.1 with
      ⟨valueNonzero, valueRoot, valueSquare⟩
    have squareOne : value ^ 2 = 1 := by
      calc
        value ^ 2 = value * value := by ring1
        _ = value⁻¹ * value := by rw [fixed]
        _ = 1 := by
          rw [mul_comm, RFAP.ExplicitField.mul_inv_cancel value valueNonzero]
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
    have sumZero := eq_zero_of_nonzero_mul_eq_zero
      differenceNonzero productZero
    have valueMinusOne : value = -1 := by
      calc
        value = (value + 1) - 1 := by ring1
        _ = -1 := by rw [sumZero]; ring1
    exact minusOneNoRoot valueRoot (valueSquare.trans valueMinusOne)
  rcases fixedPointFreeInvolution_length_even presentation.eqDecidable
      (fun value : K => value⁻¹) withoutOne withoutOneNodup
      withoutOneClosed withoutOneInvolutive withoutOneFixedPointFree with
    ⟨half, halfEquation⟩
  have withoutOneLength : withoutOne.length + 1 =
      presentation.nonzeroSquareValues.length :=
    filter_ne_target_length_add_one presentation.eqDecidable 1
      presentation.nonzeroSquareValues_nodup oneMember
  refine ⟨half, ?_⟩
  calc
    presentation.nonzeroSquareValues.length = withoutOne.length + 1 :=
      withoutOneLength.symm
    _ = half + half + 1 := by rw [halfEquation]

private theorem carrier_length_eq_twice_nonzeroSquares_add_one :
    presentation.carrier.length =
      presentation.nonzeroSquareValues.length +
        presentation.nonzeroSquareValues.length + 1 := by
  calc
    presentation.carrier.length = presentation.squareValues.length +
        presentation.nonsquareValues.length :=
      presentation.squareValues_length_add_nonsquareValues_length.symm
    _ = (presentation.nonzeroSquareValues.length + 1) +
        presentation.nonzeroSquareValues.length := by
      rw [presentation.nonzeroSquareValues_length_add_one,
        presentation.nonzeroSquareValues_length_eq_nonsquareValues_length]
    _ = presentation.nonzeroSquareValues.length +
        presentation.nonzeroSquareValues.length + 1 := by ring1

/-- The square branch of the constructive `q mod 4` theorem. -/
theorem carrier_length_eq_four_mul_add_one_of_minus_one_square
    (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1) :
    ∃ quarter : Nat,
      presentation.carrier.length = 4 * quarter + 1 := by
  rcases presentation.nonzeroSquareValues_length_even_of_minus_one_square
      minusOneRoot minusOneSquare with ⟨quarter, squareLength⟩
  refine ⟨quarter, ?_⟩
  rw [presentation.carrier_length_eq_twice_nonzeroSquares_add_one,
    squareLength]
  ring1

/-- The nonsquare branch of the constructive `q mod 4` theorem. -/
theorem carrier_length_eq_four_mul_add_three_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    ∃ quarter : Nat,
      presentation.carrier.length = 4 * quarter + 3 := by
  rcases presentation.nonzeroSquareValues_length_odd_of_minus_one_nonsquare
      minusOneNoRoot with ⟨quarter, squareLength⟩
  refine ⟨quarter, ?_⟩
  rw [presentation.carrier_length_eq_twice_nonzeroSquares_add_one,
    squareLength]
  ring1

/-- Executable cardinality classification accompanying the square test for
`-1`.  Each branch stores both the field witness and the corresponding exact
natural-number formula. -/
inductive MinusOneCardinalityClassification where
  | square (root : K) (rootSquare : root ^ 2 = -1) (quarter : Nat)
      (cardinality : presentation.carrier.length = 4 * quarter + 1)
  | nonsquare (noRoot : ∀ root : K, root ^ 2 ≠ -1) (quarter : Nat)
      (cardinality : presentation.carrier.length = 4 * quarter + 3)

/-- Compute the exact `q = 4m+1` or `q = 4m+3` alternative by finite square
tables and explicit involution pairings. -/
def classifyMinusOneCardinality :
    presentation.MinusOneCardinalityClassification := by
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      refine MinusOneCardinalityClassification.square root rootSquare
        (presentation.nonzeroSquareValues.length / 2) ?_
      rcases presentation.nonzeroSquareValues_length_even_of_minus_one_square
          root rootSquare with ⟨quarter, squareLength⟩
      rw [presentation.carrier_length_eq_twice_nonzeroSquares_add_one,
        squareLength]
      omega
  | nonsquare noRoot =>
      refine MinusOneCardinalityClassification.nonsquare noRoot
        (presentation.nonzeroSquareValues.length / 2) ?_
      rcases presentation.nonzeroSquareValues_length_odd_of_minus_one_nonsquare
          noRoot with ⟨quarter, squareLength⟩
      rw [presentation.carrier_length_eq_twice_nonzeroSquares_add_one,
        squareLength]
      omega

/-- Literal modulo-four form of the square branch. -/
theorem carrier_length_mod_four_eq_one_of_minus_one_square
    (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1) :
    presentation.carrier.length % 4 = 1 := by
  rcases presentation.carrier_length_eq_four_mul_add_one_of_minus_one_square
      minusOneRoot minusOneSquare with ⟨quarter, cardinality⟩
  rw [cardinality]
  omega

/-- Literal modulo-four form of the nonsquare branch. -/
theorem carrier_length_mod_four_eq_three_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.carrier.length % 4 = 3 := by
  rcases presentation.carrier_length_eq_four_mul_add_three_of_minus_one_nonsquare
      minusOneNoRoot with ⟨quarter, cardinality⟩
  rw [cardinality]
  omega

/-- In a displayed odd finite field, `-1` is a square exactly in the
`q ≡ 1 (mod 4)` branch. -/
theorem minusOne_hasSquareRoot_iff_carrier_length_mod_four_eq_one :
    HasSquareRoot (-1 : K) ↔ presentation.carrier.length % 4 = 1 := by
  constructor
  · rintro ⟨root, rootSquare⟩
    exact presentation.carrier_length_mod_four_eq_one_of_minus_one_square
      root rootSquare
  · intro cardinalityModFour
    cases presentation.classifyMinusOne with
    | square root rootSquare => exact ⟨root, rootSquare⟩
    | nonsquare noRoot =>
        have nonsquareModFour :=
          presentation.carrier_length_mod_four_eq_three_of_minus_one_nonsquare
            noRoot
        exact False.elim (by omega)

/-- Equivalently, `-1` is a nonsquare exactly in the `q ≡ 3 (mod 4)`
branch. -/
theorem minusOne_noRoot_iff_carrier_length_mod_four_eq_three :
    (∀ root : K, root ^ 2 ≠ -1) ↔ presentation.carrier.length % 4 = 3 := by
  constructor
  · exact presentation.carrier_length_mod_four_eq_three_of_minus_one_nonsquare
  · intro cardinalityModFour
    cases presentation.classifyMinusOne with
    | square root rootSquare =>
        have squareModFour :=
          presentation.carrier_length_mod_four_eq_one_of_minus_one_square
            root rootSquare
        exact False.elim (by omega)
    | nonsquare noRoot => exact noRoot

private theorem one_ne_zero
    (presentation : FiniteOddFieldPresentation K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply presentation.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

/-- Cached executable representative of the unique nontrivial nonzero square
class. -/
structure NonsquareWitness where
  value : K
  noRoot : ∀ root : K, root ^ 2 ≠ value

/-- Select the first displayed nonsquare.  Nonemptiness follows from the
equal-size square/nonsquare tables and the displayed nonzero square one. -/
def chosenNonsquare : NonsquareWitness (K := K) := by
  have oneMember : (1 : K) ∈ presentation.nonzeroSquareValues :=
    (presentation.mem_nonzeroSquareValues_iff 1).2
      ⟨one_ne_zero presentation, ⟨1, by ring1⟩⟩
  have equalLengths :=
    presentation.nonzeroSquareValues_length_eq_nonsquareValues_length
  cases valuesEquation : presentation.nonsquareValues with
  | nil =>
      have positive := List.length_pos_of_mem oneMember
      rw [equalLengths, valuesEquation] at positive
      exact False.elim (Nat.lt_irrefl 0 positive)
  | cons head tail =>
      refine ⟨head, ?_⟩
      apply (presentation.mem_nonsquareValues_iff head).1
      rw [valuesEquation]
      exact List.mem_cons_self

private theorem root_ne_zero_of_nonzero_square {value root : K}
    (valueNonzero : value ≠ 0) (rootSquare : root ^ 2 = value) : root ≠ 0 := by
  intro rootZero
  apply valueNonzero
  calc
    value = root ^ 2 := rootSquare.symm
    _ = 0 := by rw [rootZero]; ring1

private theorem quotient_square_of_product_square
    {factor squareValue squareRoot productRoot : K}
    (squareNonzero : squareValue ≠ 0)
    (squareEquation : squareRoot ^ 2 = squareValue)
    (productEquation : productRoot ^ 2 = factor * squareValue) :
    (productRoot / squareRoot) ^ 2 = factor := by
  have rootNonzero := root_ne_zero_of_nonzero_square squareNonzero squareEquation
  have cancel := RFAP.ExplicitField.mul_inv_cancel squareRoot rootNonzero
  rw [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (productRoot * squareRoot⁻¹) ^ 2 =
        productRoot ^ 2 * squareRoot⁻¹ ^ 2 := by ring1
    _ = (factor * squareValue) * squareRoot⁻¹ ^ 2 := by
      rw [productEquation]
    _ = (factor * squareRoot ^ 2) * squareRoot⁻¹ ^ 2 := by
      rw [squareEquation]
    _ =
        factor * (squareRoot * squareRoot⁻¹) ^ 2 := by ring1
    _ = factor := by rw [cancel]; ring1

/-- Multiplying the nonzero square table by one displayed factor. -/
def scaledNonzeroSquareValues (factor : K) : List K :=
  presentation.nonzeroSquareValues.map fun value => factor * value

theorem scaledNonzeroSquareValues_nodup (factor : K)
    (factorNonzero : factor ≠ 0) :
    (presentation.scaledNonzeroSquareValues factor).Nodup := by
  unfold scaledNonzeroSquareValues
  apply QuotientFreeList.nodup_map_of_injective
  · intro left right equal
    change factor * left = factor * right at equal
    have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
    calc
      left = (factor * factor⁻¹) * left := by rw [cancel, one_mul]
      _ = factor⁻¹ * (factor * left) := by ring1
      _ = factor⁻¹ * (factor * right) := by rw [equal]
      _ = (factor * factor⁻¹) * right := by ring1
      _ = right := by rw [cancel, one_mul]
  · exact presentation.nonzeroSquareValues_nodup

theorem scaledNonzeroSquareValues_contained_in_nonsquares
    (factor : K) (factorNoRoot : ∀ root : K, root ^ 2 ≠ factor) :
    ∀ value ∈ presentation.scaledNonzeroSquareValues factor,
      value ∈ presentation.nonsquareValues := by
  intro value member
  rcases QuotientFreeList.mem_map.mp member with
    ⟨squareValue, squareMember, equal⟩
  rcases (presentation.mem_nonzeroSquareValues_iff squareValue).1
      squareMember with ⟨squareNonzero, squareRoot, squareEquation⟩
  apply (presentation.mem_nonsquareValues_iff value).2
  intro productRoot productEquation
  apply factorNoRoot (productRoot / squareRoot)
  apply quotient_square_of_product_square squareNonzero squareEquation
  calc
    productRoot ^ 2 = value := productEquation
    _ = factor * squareValue := equal.symm

private theorem mem_of_nodup_contained_length_eq {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha)
    {selected carrier : List Alpha} (selectedNodup : selected.Nodup)
    (carrierNodup : carrier.Nodup)
    (contained : ∀ value ∈ selected, value ∈ carrier)
    (lengthEqual : selected.length = carrier.length)
    {value : Alpha} (valueMember : value ∈ carrier) : value ∈ selected := by
  letI : DecidableEq Alpha := eqDecidable
  by_cases selectedMember : value ∈ selected
  · exact selectedMember
  · have extendedNodup : (value :: selected).Nodup := by
      apply List.pairwise_cons.mpr
      constructor
      · intro other otherMember equal
        exact selectedMember (equal ▸ otherMember)
      · exact selectedNodup
    have extendedContained : ∀ other ∈ value :: selected, other ∈ carrier := by
      intro other member
      rcases List.mem_cons.mp member with equal | selectedOther
      · exact equal ▸ valueMember
      · exact contained other selectedOther
    have bound := QuotientFreeList.nodup_length_le_of_mem extendedNodup
      carrierNodup extendedContained
    rw [List.length_cons, lengthEqual] at bound
    exact False.elim (Nat.not_succ_le_self carrier.length bound)

/-- Multiplication by a nonsquare enumerates all nonsquares from the nonzero
square table. -/
theorem nonsquare_mem_scaledNonzeroSquareValues
    (factor : K) (factorNoRoot : ∀ root : K, root ^ 2 ≠ factor)
    {value : K} (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    value ∈ presentation.scaledNonzeroSquareValues factor := by
  have factorNonzero := nonsquare_ne_zero factorNoRoot
  apply mem_of_nodup_contained_length_eq presentation.eqDecidable
    (presentation.scaledNonzeroSquareValues_nodup factor factorNonzero)
    presentation.nonsquareValues_nodup
    (presentation.scaledNonzeroSquareValues_contained_in_nonsquares
      factor factorNoRoot)
  · unfold scaledNonzeroSquareValues
    rw [List.length_map,
      presentation.nonzeroSquareValues_length_eq_nonsquareValues_length]
  · exact (presentation.mem_nonsquareValues_iff value).2 valueNoRoot

/-- Search a displayed list for a square value whose product with `factor` is
the requested target. -/
private def firstScaledPreimage? (eqDecidable : DecidableEq K)
    (factor target : K) : List K → Option K
  | [] => none
  | head :: tail =>
      match eqDecidable (factor * head) target with
      | isTrue _ => some head
      | isFalse _ => firstScaledPreimage? eqDecidable factor target tail

private theorem firstScaledPreimage?_ne_none_of_mem
    (eqDecidable : DecidableEq K) (factor target : K) :
    ∀ values : List K, target ∈ values.map (fun value => factor * value) →
      firstScaledPreimage? eqDecidable factor target values ≠ none
  | [], impossible => by nomatch impossible
  | head :: tail, member => by
      unfold firstScaledPreimage?
      rcases List.mem_cons.mp member with headEqual | tailMember
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
            exact firstScaledPreimage?_ne_none_of_mem eqDecidable factor
              target tail tailMember

private theorem firstScaledPreimage?_eq_some_spec
    (eqDecidable : DecidableEq K) (factor target selected : K) :
    ∀ values : List K,
      firstScaledPreimage? eqDecidable factor target values = some selected →
        selected ∈ values ∧ factor * selected = target
  | [], impossible => by nomatch impossible
  | head :: tail, found => by
      unfold firstScaledPreimage? at found
      cases equal : eqDecidable (factor * head) target with
      | isTrue headEqual =>
          rw [equal] at found
          injection found with selectedEqual
          exact ⟨List.mem_cons.mpr (Or.inl selectedEqual.symm),
            selectedEqual ▸ headEqual⟩
      | isFalse headDifferent =>
          rw [equal] at found
          rcases firstScaledPreimage?_eq_some_spec eqDecidable factor target
              selected tail found with ⟨member, product⟩
          exact ⟨List.mem_cons_of_mem head member, product⟩

/-- Cached executable root of one square value. -/
structure SquareRootWitness (value : K) where
  root : K
  equation : root ^ 2 = value

/-- Compute a square root of the product of two nonsquares through the
displayed nonzero-square table. -/
def nonsquareMulNonsquareSquareWitness
    (presentation : FiniteOddFieldPresentation K)
    (left right : K) (leftNoRoot : ∀ root : K, root ^ 2 ≠ left)
    (rightNoRoot : ∀ root : K, root ^ 2 ≠ right) :
    SquareRootWitness (left * right) := by
  let values := presentation.nonzeroSquareValues
  let found := firstScaledPreimage? presentation.eqDecidable left right values
  have rightMember := nonsquare_mem_scaledNonzeroSquareValues presentation
    left leftNoRoot rightNoRoot
  have foundNonempty : found ≠ none := by
    exact firstScaledPreimage?_ne_none_of_mem presentation.eqDecidable
      left right values rightMember
  cases foundEquation : found with
  | none => exact False.elim (foundNonempty foundEquation)
  | some squareValue =>
      have foundSpec := firstScaledPreimage?_eq_some_spec
        presentation.eqDecidable left right squareValue values foundEquation
      have squareData :=
        (presentation.mem_nonzeroSquareValues_iff squareValue).1 foundSpec.1
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

/-- Proposition-level corollary of the cached executable witness. -/
theorem nonsquare_mul_nonsquare_hasSquareRoot
    (presentation : FiniteOddFieldPresentation K)
    (left right : K) (leftNoRoot : ∀ root : K, root ^ 2 ≠ left)
    (rightNoRoot : ∀ root : K, root ^ 2 ≠ right) :
    HasSquareRoot (left * right) := by
  let witness := presentation.nonsquareMulNonsquareSquareWitness
    left right leftNoRoot rightNoRoot
  exact ⟨witness.root, witness.equation⟩

/-- A nonzero square times a nonsquare remains a nonsquare. -/
theorem square_mul_nonsquare_noRoot
    (squareValue squareRoot nonsquare : K)
    (squareNonzero : squareValue ≠ 0)
    (squareEquation : squareRoot ^ 2 = squareValue)
    (nonsquareNoRoot : ∀ root : K, root ^ 2 ≠ nonsquare) :
    ∀ root : K, root ^ 2 ≠ squareValue * nonsquare := by
  intro productRoot productEquation
  apply nonsquareNoRoot (productRoot / squareRoot)
  apply quotient_square_of_product_square squareNonzero squareEquation
  calc
    productRoot ^ 2 = squareValue * nonsquare := productEquation
    _ = nonsquare * squareValue := by ring1

end FiniteOddFieldPresentation

end RationalRotations
