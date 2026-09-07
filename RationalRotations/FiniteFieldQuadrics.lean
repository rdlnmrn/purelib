import RationalRotations.NullVectors

/-!
# Constructive finite-field quadrics

Displayed scalar pairs and their two-square norm supply the finite conics used
in the counting solution to Problem 69.  The carrier is always the explicit
list in `FiniteOddFieldPresentation`; no finiteness typeclass or quotient is
used.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- Explicit mutually inverse maps between two displayed finite lists. -/
structure FiniteListBijection {Alpha Beta : Type*}
    (source : List Alpha) (target : List Beta) where
  forward : Alpha → Beta
  backward : Beta → Alpha
  forward_mem : ∀ value ∈ source, forward value ∈ target
  backward_mem : ∀ value ∈ target, backward value ∈ source
  backward_forward : ∀ value ∈ source, backward (forward value) = value
  forward_backward : ∀ value ∈ target, forward (backward value) = value

namespace FiniteListBijection

private theorem nodup_map_of_injective_on
    {Alpha Beta : Type*} {values : List Alpha} (function : Alpha → Beta)
    (injectiveOn : ∀ left ∈ values, ∀ right ∈ values,
      function left = function right → left = right)
    (valuesNodup : values.Nodup) : (values.map function).Nodup := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rw [List.map_cons]
      apply List.pairwise_cons.mpr
      constructor
      · intro mapped mappedMember equal
        rcases QuotientFreeList.mem_map.mp mappedMember with
          ⟨source, sourceMember, sourceEqual⟩
        apply (List.pairwise_cons.mp valuesNodup).1 source sourceMember
        apply injectiveOn head List.mem_cons_self source
          (List.mem_cons_of_mem head sourceMember)
        exact equal.trans sourceEqual.symm
      · apply inductionHypothesis
        · intro left leftMember right rightMember equal
          exact injectiveOn left (List.mem_cons_of_mem head leftMember)
            right (List.mem_cons_of_mem head rightMember) equal
        · exact (List.pairwise_cons.mp valuesNodup).2

/-- A displayed finite bijection identifies list lengths without cardinal
types or quotient cardinality. -/
theorem length_eq {Alpha Beta : Type*} {source : List Alpha}
    {target : List Beta} (bijection : FiniteListBijection source target)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup) :
    source.length = target.length := by
  have forwardNodup : (source.map bijection.forward).Nodup :=
    nodup_map_of_injective_on bijection.forward (by
      intro left leftMember right rightMember equal
      calc
        left = bijection.backward (bijection.forward left) :=
          (bijection.backward_forward left leftMember).symm
        _ = bijection.backward (bijection.forward right) :=
          congrArg bijection.backward equal
        _ = right := bijection.backward_forward right rightMember)
      sourceNodup
  have forwardContained : ∀ value ∈ source.map bijection.forward,
      value ∈ target := by
    intro value member
    rcases QuotientFreeList.mem_map.mp member with
      ⟨sourceValue, sourceMember, equal⟩
    exact equal ▸ bijection.forward_mem sourceValue sourceMember
  have sourceLeTarget : source.length ≤ target.length := by
    rw [← List.length_map (as := source) bijection.forward]
    exact QuotientFreeList.nodup_length_le_of_mem forwardNodup targetNodup
      forwardContained
  have backwardNodup : (target.map bijection.backward).Nodup :=
    nodup_map_of_injective_on bijection.backward (by
      intro left leftMember right rightMember equal
      calc
        left = bijection.forward (bijection.backward left) :=
          (bijection.forward_backward left leftMember).symm
        _ = bijection.forward (bijection.backward right) :=
          congrArg bijection.forward equal
        _ = right := bijection.forward_backward right rightMember)
      targetNodup
  have backwardContained : ∀ value ∈ target.map bijection.backward,
      value ∈ source := by
    intro value member
    rcases QuotientFreeList.mem_map.mp member with
      ⟨targetValue, targetMember, equal⟩
    exact equal ▸ bijection.backward_mem targetValue targetMember
  have targetLeSource : target.length ≤ source.length := by
    rw [← List.length_map (as := target) bijection.backward]
    exact QuotientFreeList.nodup_length_le_of_mem backwardNodup sourceNodup
      backwardContained
  exact Nat.le_antisymm sourceLeTarget targetLeSource

end FiniteListBijection

/-- One displayed point of the affine two-square plane. -/
@[ext]
structure ScalarPair (K : Type*) where
  first : K
  second : K
deriving DecidableEq

namespace ScalarPair

/-- The binary quadrance `x² + y²`. -/
def quadrance (pair : ScalarPair K) : K :=
  pair.first ^ 2 + pair.second ^ 2

/-- Complex-style multiplication on displayed scalar pairs. -/
def mul (left right : ScalarPair K) : ScalarPair K :=
  ⟨left.first * right.first - left.second * right.second,
    left.first * right.second + left.second * right.first⟩

/-- Conjugation of a displayed scalar pair. -/
def conjugate (pair : ScalarPair K) : ScalarPair K :=
  ⟨pair.first, -pair.second⟩

/-- Coordinatewise scaling. -/
def scale (factor : K) (pair : ScalarPair K) : ScalarPair K :=
  ⟨factor * pair.first, factor * pair.second⟩

/-- The binary Euler identity. -/
theorem quadrance_mul (left right : ScalarPair K) :
    (mul left right).quadrance = left.quadrance * right.quadrance := by
  unfold mul quadrance
  ring1

theorem quadrance_conjugate (pair : ScalarPair K) :
    pair.conjugate.quadrance = pair.quadrance := by
  unfold conjugate quadrance
  ring1

theorem mul_conjugate (pair : ScalarPair K) :
    mul pair pair.conjugate = ⟨pair.quadrance, 0⟩ := by
  apply ScalarPair.ext <;> unfold mul conjugate quadrance <;> ring1

theorem quadrance_scale (factor : K) (pair : ScalarPair K) :
    (scale factor pair).quadrance = factor ^ 2 * pair.quadrance := by
  unfold scale quadrance
  ring1

/-- The split coordinates `(x + iy, x - iy)`. -/
def split (root : K) (pair : ScalarPair K) : ScalarPair K :=
  ⟨pair.first + root * pair.second,
    pair.first - root * pair.second⟩

/-- The inverse linear coordinates, written using only the displayed inverse
of two and of `i`. -/
def unsplit (root : K) (pair : ScalarPair K) : ScalarPair K :=
  ⟨(pair.first + pair.second) / 2,
    ((pair.first - pair.second) * root⁻¹) / 2⟩

theorem product_split (root : K) (rootSquare : root ^ 2 = -1)
    (pair : ScalarPair K) :
    (split root pair).first * (split root pair).second = pair.quadrance := by
  change (pair.first + root * pair.second) *
      (pair.first - root * pair.second) =
    pair.first ^ 2 + pair.second ^ 2
  have rootProduct : root * root = -1 := by
    simpa only [pow_two] using rootSquare
  calc
    (pair.first + root * pair.second) *
        (pair.first - root * pair.second) =
      pair.first ^ 2 - (root * root) * pair.second ^ 2 := by ring1
    _ = pair.first ^ 2 + pair.second ^ 2 := by rw [rootProduct]; ring1

private theorem inverse_mul (value : K) (nonzero : value ≠ 0) :
    value⁻¹ * value = 1 := by
  calc
    value⁻¹ * value = value * value⁻¹ := by ring1
    _ = 1 := RFAP.ExplicitField.mul_inv_cancel value nonzero

theorem unsplit_split (root : K) (rootNonzero : root ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (pair : ScalarPair K) :
    unsplit root (split root pair) = pair := by
  have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have rootCancel := RFAP.ExplicitField.mul_inv_cancel root rootNonzero
  apply ScalarPair.ext
  · change ((pair.first + root * pair.second) +
        (pair.first - root * pair.second)) / 2 = pair.first
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      ((pair.first + root * pair.second) +
          (pair.first - root * pair.second)) * (2 : K)⁻¹ =
        pair.first * (2 * (2 : K)⁻¹) := by ring1
      _ = pair.first := by rw [twoCancel, mul_one]
  · change ((((pair.first + root * pair.second) -
        (pair.first - root * pair.second)) * root⁻¹) / 2) = pair.second
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      ((pair.first + root * pair.second -
          (pair.first - root * pair.second)) * root⁻¹) * (2 : K)⁻¹ =
        pair.second * (root * root⁻¹) * (2 * (2 : K)⁻¹) := by ring1
      _ = pair.second := by rw [rootCancel, twoCancel]; ring1

theorem split_unsplit (root : K) (rootNonzero : root ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (pair : ScalarPair K) :
    split root (unsplit root pair) = pair := by
  have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have rootCancel := RFAP.ExplicitField.mul_inv_cancel root rootNonzero
  apply ScalarPair.ext
  · change (pair.first + pair.second) / 2 +
      root * (((pair.first - pair.second) * root⁻¹) / 2) = pair.first
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (pair.first + pair.second) * (2 : K)⁻¹ +
          root * ((pair.first - pair.second) * root⁻¹ * (2 : K)⁻¹) =
        ((pair.first + pair.second) +
          (pair.first - pair.second) * (root * root⁻¹)) * (2 : K)⁻¹ := by
            ring1
      _ = pair.first * (2 * (2 : K)⁻¹) := by rw [rootCancel]; ring1
      _ = pair.first := by rw [twoCancel, mul_one]
  · change (pair.first + pair.second) / 2 -
      root * (((pair.first - pair.second) * root⁻¹) / 2) = pair.second
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (pair.first + pair.second) * (2 : K)⁻¹ -
          root * ((pair.first - pair.second) * root⁻¹ * (2 : K)⁻¹) =
        ((pair.first + pair.second) -
          (pair.first - pair.second) * (root * root⁻¹)) * (2 : K)⁻¹ := by
            ring1
      _ = pair.second * (2 * (2 : K)⁻¹) := by rw [rootCancel]; ring1
      _ = pair.second := by rw [twoCancel, mul_one]

/-- The affine part of the rational parametrization of the unit circle. -/
def circleParameter (parameter : K) : ScalarPair K :=
  ⟨(1 - parameter ^ 2) / (1 + parameter ^ 2),
    (2 * parameter) / (1 + parameter ^ 2)⟩

/-- The single point omitted by the affine unit-circle parametrization. -/
def circleInfinity : ScalarPair K := ⟨-1, 0⟩

theorem circleDenominator_ne_zero
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    1 + parameter ^ 2 ≠ 0 := by
  intro denominatorZero
  apply minusOneNoRoot parameter
  calc
    parameter ^ 2 = (1 + parameter ^ 2) - 1 := by ring1
    _ = -1 := by rw [denominatorZero]; ring1

theorem quadrance_circleParameter
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).quadrance = 1 := by
  have denominatorNonzero :=
    circleDenominator_ne_zero minusOneNoRoot parameter
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  unfold circleParameter quadrance
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    ((1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹) ^ 2 +
        (2 * parameter * (1 + parameter ^ 2)⁻¹) ^ 2 =
      ((1 + parameter ^ 2) * (1 + parameter ^ 2)) *
        ((1 + parameter ^ 2)⁻¹ * (1 + parameter ^ 2)⁻¹) := by
          ring1
    _ = ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹) *
        ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹) := by ring1
    _ = 1 := by rw [denominatorCancel]; ring1

theorem circleInfinity_quadrance : (circleInfinity : ScalarPair K).quadrance = 1 := by
  unfold circleInfinity quadrance
  ring1

theorem circleParameter_first_add_one
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).first + 1 =
      2 / (1 + parameter ^ 2) := by
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2)
    (circleDenominator_ne_zero minusOneNoRoot parameter)
  unfold circleParameter
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹ + 1 =
        (1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹ +
          (1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹ := by
            rw [denominatorCancel]
    _ = 2 * (1 + parameter ^ 2)⁻¹ := by ring1

theorem circleParameter_first_add_one_ne_zero
    (twoNonzero : (2 : K) ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).first + 1 ≠ 0 := by
  rw [circleParameter_first_add_one minusOneNoRoot parameter]
  exact RFAP.ExplicitField.div_ne_zero twoNonzero
    (circleDenominator_ne_zero minusOneNoRoot parameter)

theorem circleParameter_ne_infinity
    (twoNonzero : (2 : K) ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    circleParameter parameter ≠ circleInfinity := by
  intro equal
  apply circleParameter_first_add_one_ne_zero twoNonzero minusOneNoRoot parameter
  calc
    (circleParameter parameter).first + 1 =
        circleInfinity.first + 1 := congrArg (fun pair => pair.first + 1) equal
    _ = 0 := by unfold circleInfinity; ring1

theorem circleParameter_inverse
    (twoNonzero : (2 : K) ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).second /
        ((circleParameter parameter).first + 1) = parameter := by
  have denominatorNonzero :=
    circleDenominator_ne_zero minusOneNoRoot parameter
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  have firstAdd := circleParameter_first_add_one minusOneNoRoot parameter
  have firstAddNonzero := circleParameter_first_add_one_ne_zero
    twoNonzero minusOneNoRoot parameter
  have secondRelation : (circleParameter parameter).second =
      parameter * ((circleParameter parameter).first + 1) := by
    rw [firstAdd]
    unfold circleParameter
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  rw [secondRelation, RFAP.ExplicitField.div_eq_mul_inv]
  calc
    parameter * ((circleParameter parameter).first + 1) *
        ((circleParameter parameter).first + 1)⁻¹ =
      parameter * (((circleParameter parameter).first + 1) *
        ((circleParameter parameter).first + 1)⁻¹) := by ring1
    _ = parameter := by
      rw [RFAP.ExplicitField.mul_inv_cancel _ firstAddNonzero, mul_one]

theorem eq_zero_of_square_eq_zero (eqDecidable : DecidableEq K)
    (value : K) (squareZero : value ^ 2 = 0) : value = 0 := by
  cases eqDecidable value 0 with
  | isTrue equal => exact equal
  | isFalse nonzero =>
      apply False.elim
      apply RFAP.ExplicitField.mul_ne_zero nonzero nonzero
      simpa only [pow_two] using squareZero

theorem first_add_one_ne_zero_of_quadrance_one_of_ne_infinity
    (eqDecidable : DecidableEq K) (pair : ScalarPair K)
    (quadranceOne : pair.quadrance = 1) (notInfinity : pair ≠ circleInfinity) :
    pair.first + 1 ≠ 0 := by
  intro firstAddZero
  have firstNegOne : pair.first = -1 := by
    calc
      pair.first = (pair.first + 1) - 1 := by ring1
      _ = -1 := by rw [firstAddZero]; ring1
  have secondSquareZero : pair.second ^ 2 = 0 := by
    unfold quadrance at quadranceOne
    calc
      pair.second ^ 2 =
          (pair.first ^ 2 + pair.second ^ 2) - pair.first ^ 2 := by ring1
      _ = 1 - (-1 : K) ^ 2 := by rw [quadranceOne, firstNegOne]
      _ = 0 := by ring1
  have secondZero :=
    eq_zero_of_square_eq_zero eqDecidable pair.second secondSquareZero
  apply notInfinity
  apply ScalarPair.ext
  · exact firstNegOne
  · exact secondZero

/-- Every nonexceptional point of the unit circle is recovered from the
rational parameter `y / (x + 1)`. -/
theorem circleParameter_complete (eqDecidable : DecidableEq K)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (pair : ScalarPair K)
    (quadranceOne : pair.quadrance = 1) (notInfinity : pair ≠ circleInfinity) :
    circleParameter (pair.second / (pair.first + 1)) = pair := by
  have firstAddNonzero :=
    first_add_one_ne_zero_of_quadrance_one_of_ne_infinity
      eqDecidable pair quadranceOne notInfinity
  have firstAddCancel := RFAP.ExplicitField.mul_inv_cancel
    (pair.first + 1) firstAddNonzero
  have secondSquare : pair.second ^ 2 = 1 - pair.first ^ 2 := by
    unfold quadrance at quadranceOne
    calc
      pair.second ^ 2 =
          (pair.first ^ 2 + pair.second ^ 2) - pair.first ^ 2 := by ring1
      _ = 1 - pair.first ^ 2 := by rw [quadranceOne]
  have parameterSquare :
      (pair.second / (pair.first + 1)) ^ 2 =
        (1 - pair.first) * (pair.first + 1)⁻¹ := by
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (pair.second * (pair.first + 1)⁻¹) ^ 2 =
          pair.second ^ 2 * ((pair.first + 1)⁻¹ ^ 2) := by ring1
      _ = (1 - pair.first ^ 2) * ((pair.first + 1)⁻¹ ^ 2) := by
        rw [secondSquare]
      _ = (1 - pair.first) *
          ((pair.first + 1) * (pair.first + 1)⁻¹) *
            (pair.first + 1)⁻¹ := by ring1
      _ = (1 - pair.first) * (pair.first + 1)⁻¹ := by
        rw [firstAddCancel]
        ring1
  have firstNumerator :
      1 - (pair.second / (pair.first + 1)) ^ 2 =
        pair.first * (1 + (pair.second / (pair.first + 1)) ^ 2) := by
    rw [parameterSquare]
    calc
      1 - (1 - pair.first) * (pair.first + 1)⁻¹ =
          pair.first *
              (1 + (1 - pair.first) * (pair.first + 1)⁻¹) +
            (1 - pair.first) *
              (1 - (pair.first + 1) * (pair.first + 1)⁻¹) := by
                ring1
      _ = pair.first *
          (1 + (1 - pair.first) * (pair.first + 1)⁻¹) := by
        rw [firstAddCancel]
        ring1
  have secondNumerator :
      2 * (pair.second / (pair.first + 1)) =
        pair.second * (1 + (pair.second / (pair.first + 1)) ^ 2) := by
    rw [parameterSquare, RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * (pair.second * (pair.first + 1)⁻¹) =
          pair.second *
              (1 + (1 - pair.first) * (pair.first + 1)⁻¹) +
            pair.second *
              ((pair.first + 1) * (pair.first + 1)⁻¹ - 1) := by
                ring1
      _ = pair.second *
          (1 + (1 - pair.first) * (pair.first + 1)⁻¹) := by
        rw [firstAddCancel]
        ring1
  have denominatorNonzero := circleDenominator_ne_zero minusOneNoRoot
    (pair.second / (pair.first + 1))
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + (pair.second / (pair.first + 1)) ^ 2) denominatorNonzero
  apply ScalarPair.ext
  · change (1 - (pair.second / (pair.first + 1)) ^ 2) /
        (1 + (pair.second / (pair.first + 1)) ^ 2) = pair.first
    rw [firstNumerator, RFAP.ExplicitField.div_eq_mul_inv]
    calc
      pair.first * (1 + (pair.second / (pair.first + 1)) ^ 2) *
          (1 + (pair.second / (pair.first + 1)) ^ 2)⁻¹ =
        pair.first * ((1 + (pair.second / (pair.first + 1)) ^ 2) *
          (1 + (pair.second / (pair.first + 1)) ^ 2)⁻¹) := by ring1
      _ = pair.first := by rw [denominatorCancel, mul_one]
  · change (2 * (pair.second / (pair.first + 1))) /
        (1 + (pair.second / (pair.first + 1)) ^ 2) = pair.second
    rw [secondNumerator, RFAP.ExplicitField.div_eq_mul_inv]
    calc
      pair.second * (1 + (pair.second / (pair.first + 1)) ^ 2) *
          (1 + (pair.second / (pair.first + 1)) ^ 2)⁻¹ =
        pair.second * ((1 + (pair.second / (pair.first + 1)) ^ 2) *
          (1 + (pair.second / (pair.first + 1)) ^ 2)⁻¹) := by ring1
      _ = pair.second := by rw [denominatorCancel, mul_one]

theorem eq_zero_of_quadrance_eq_zero_of_minus_one_nonsquare
    (eqDecidable : DecidableEq K)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (pair : ScalarPair K)
    (quadranceZero : pair.quadrance = 0) : pair = ⟨0, 0⟩ := by
  have secondZero : pair.second = 0 := by
    cases eqDecidable pair.second 0 with
    | isTrue equal => exact equal
    | isFalse secondNonzero =>
        have secondCancel := RFAP.ExplicitField.mul_inv_cancel
          pair.second secondNonzero
        have firstSquare : pair.first ^ 2 = -(pair.second ^ 2) := by
          unfold quadrance at quadranceZero
          calc
            pair.first ^ 2 =
                (pair.first ^ 2 + pair.second ^ 2) - pair.second ^ 2 := by ring1
            _ = -(pair.second ^ 2) := by rw [quadranceZero]; ring1
        apply False.elim
        apply minusOneNoRoot (pair.first / pair.second)
        rw [RFAP.ExplicitField.div_eq_mul_inv]
        calc
          (pair.first * pair.second⁻¹) ^ 2 =
              pair.first ^ 2 * (pair.second⁻¹ ^ 2) := by ring1
          _ = -(pair.second ^ 2) * (pair.second⁻¹ ^ 2) := by
            rw [firstSquare]
          _ = -((pair.second * pair.second⁻¹) *
              (pair.second * pair.second⁻¹)) := by ring1
          _ = -1 := by rw [secondCancel]; ring1
  have firstSquareZero : pair.first ^ 2 = 0 := by
    unfold quadrance at quadranceZero
    calc
      pair.first ^ 2 =
          (pair.first ^ 2 + pair.second ^ 2) - pair.second ^ 2 := by ring1
      _ = 0 := by rw [quadranceZero, secondZero]; ring1
  have firstZero := eq_zero_of_square_eq_zero eqDecidable
    pair.first firstSquareZero
  apply ScalarPair.ext
  · exact firstZero
  · exact secondZero

/-- Divide complex-style by a pair of nonzero quadrance `value`, using its
conjugate and the explicitly supplied scalar inverse. -/
def divideMul (value : K) (divisor pair : ScalarPair K) : ScalarPair K :=
  scale value⁻¹ (mul divisor.conjugate pair)

theorem divideMul_mul (value : K) (valueNonzero : value ≠ 0)
    (divisor pair : ScalarPair K) (divisorQuadrance : divisor.quadrance = value) :
    divideMul value divisor (mul divisor pair) = pair := by
  have valueCancel : value⁻¹ * value = 1 := inverse_mul value valueNonzero
  apply ScalarPair.ext
  · calc
      (divideMul value divisor (mul divisor pair)).first =
          value⁻¹ * (divisor.quadrance * pair.first) := by
            unfold divideMul scale mul conjugate quadrance
            ring1
      _ = value⁻¹ * (value * pair.first) := by rw [divisorQuadrance]
      _ = pair.first := by
        calc
          value⁻¹ * (value * pair.first) =
              (value⁻¹ * value) * pair.first := by ring1
          _ = pair.first := by rw [valueCancel, one_mul]
  · calc
      (divideMul value divisor (mul divisor pair)).second =
          value⁻¹ * (divisor.quadrance * pair.second) := by
            unfold divideMul scale mul conjugate quadrance
            ring1
      _ = value⁻¹ * (value * pair.second) := by rw [divisorQuadrance]
      _ = pair.second := by
        calc
          value⁻¹ * (value * pair.second) =
              (value⁻¹ * value) * pair.second := by ring1
          _ = pair.second := by rw [valueCancel, one_mul]

theorem mul_divideMul (value : K) (valueNonzero : value ≠ 0)
    (divisor pair : ScalarPair K) (divisorQuadrance : divisor.quadrance = value) :
    mul divisor (divideMul value divisor pair) = pair := by
  have valueCancel : value⁻¹ * value = 1 := inverse_mul value valueNonzero
  apply ScalarPair.ext
  · calc
      (mul divisor (divideMul value divisor pair)).first =
          value⁻¹ * (divisor.quadrance * pair.first) := by
            unfold divideMul scale mul conjugate quadrance
            ring1
      _ = value⁻¹ * (value * pair.first) := by rw [divisorQuadrance]
      _ = pair.first := by
        calc
          value⁻¹ * (value * pair.first) =
              (value⁻¹ * value) * pair.first := by ring1
          _ = pair.first := by rw [valueCancel, one_mul]
  · calc
      (mul divisor (divideMul value divisor pair)).second =
          value⁻¹ * (divisor.quadrance * pair.second) := by
            unfold divideMul scale mul conjugate quadrance
            ring1
      _ = value⁻¹ * (value * pair.second) := by rw [divisorQuadrance]
      _ = pair.second := by
        calc
          value⁻¹ * (value * pair.second) =
              (value⁻¹ * value) * pair.second := by ring1
          _ = pair.second := by rw [valueCancel, one_mul]

theorem quadrance_divideMul (value : K) (valueNonzero : value ≠ 0)
    (divisor pair : ScalarPair K) (divisorQuadrance : divisor.quadrance = value)
    (pairQuadrance : pair.quadrance = value) :
    (divideMul value divisor pair).quadrance = 1 := by
  have valueCancel : value⁻¹ * value = 1 := inverse_mul value valueNonzero
  rw [divideMul, quadrance_scale, quadrance_mul, quadrance_conjugate,
    divisorQuadrance, pairQuadrance]
  calc
    value⁻¹ ^ 2 * (value * value) =
        (value⁻¹ * value) * (value⁻¹ * value) := by ring1
    _ = 1 := by rw [valueCancel]; ring1

end ScalarPair

namespace FiniteOddFieldPresentation

variable (presentation : FiniteOddFieldPresentation K)

/-- The complete displayed affine pair carrier. -/
def scalarPairs : List (ScalarPair K) :=
  presentation.carrier.flatMap fun first =>
    presentation.carrier.map fun second => ⟨first, second⟩

/-- One two-square affine quadric fiber. -/
def twoSquareFiber (value : K) : List (ScalarPair K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.scalarPairs.filter fun pair => pair.quadrance = value

/-- Executable cardinality of one two-square fiber. -/
def twoSquareCount (value : K) : Nat :=
  (presentation.twoSquareFiber value).length

/-- The factorized hyperbola fiber `uv = value`. -/
def productFiber (value : K) : List (ScalarPair K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.scalarPairs.filter fun pair =>
    pair.first * pair.second = value

private theorem one_ne_zero
    (presentation : FiniteOddFieldPresentation K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply presentation.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

theorem root_ne_zero (presentation : FiniteOddFieldPresentation K)
    {root : K} (rootSquare : root ^ 2 = -1) :
    root ≠ 0 := by
  intro rootZero
  apply one_ne_zero presentation
  have minusOneZero : (-1 : K) = 0 := by
    calc
      (-1 : K) = root ^ 2 := rootSquare.symm
      _ = 0 := by rw [rootZero]; ring1
  calc
    (1 : K) = -(-1) := by ring1
    _ = 0 := by rw [minusOneZero]; ring1

/-- The displayed nonzero field carrier, computed by a direct finite filter. -/
def nonzeroScalars : List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.carrier.filter fun value => value ≠ 0

theorem nonzeroScalars_nodup : presentation.nonzeroScalars.Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroScalars
  exact presentation.carrierNodup.filter _

theorem mem_nonzeroScalars_iff (value : K) :
    value ∈ presentation.nonzeroScalars ↔
      value ≠ 0 ∧ value ∈ presentation.carrier := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroScalars
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨member, nonzero⟩
    exact ⟨nonzero, member⟩
  · rintro ⟨nonzero, member⟩
    exact ⟨member, nonzero⟩

private theorem filter_nonzero_eq_self (eqDecidable : DecidableEq K) :
    ∀ {values : List K}, (∀ value ∈ values, value ≠ 0) →
      (letI : DecidableEq K := eqDecidable
       values.filter fun value => value ≠ 0) = values
  | [], _ => rfl
  | head :: tail, allNonzero => by
      letI : DecidableEq K := eqDecidable
      rw [List.filter_cons_of_pos
        (p := fun value : K => decide (value ≠ 0))
        (decide_eq_true (allNonzero head List.mem_cons_self))]
      rw [filter_nonzero_eq_self eqDecidable (fun value member =>
        allNonzero value (List.mem_cons_of_mem head member))]

private theorem filter_nonzero_length_add_one (eqDecidable : DecidableEq K) :
    ∀ {values : List K}, values.Nodup → 0 ∈ values →
      (letI : DecidableEq K := eqDecidable
       (values.filter fun value => value ≠ 0).length + 1) = values.length
  | [], _, impossible => nomatch impossible
  | head :: tail, nodup, zeroMember => by
      letI : DecidableEq K := eqDecidable
      cases eqDecidable head 0 with
      | isTrue headZero =>
          have tailNonzero : ∀ value ∈ tail, value ≠ 0 := by
            intro value member valueZero
            apply (List.pairwise_cons.mp nodup).1 value member
            exact headZero.trans valueZero.symm
          rw [List.filter_cons_of_neg
            (p := fun value : K => decide (value ≠ 0))
            (fun accepted => (of_decide_eq_true accepted) headZero)]
          rw [filter_nonzero_eq_self eqDecidable tailNonzero]
          rfl
      | isFalse headNonzero =>
          have tailMember : 0 ∈ tail := by
            rcases List.mem_cons.mp zeroMember with headMember | member
            · exact False.elim (headNonzero headMember.symm)
            · exact member
          rw [List.filter_cons_of_pos
            (p := fun value : K => decide (value ≠ 0))
            (decide_eq_true headNonzero)]
          have induction := filter_nonzero_length_add_one eqDecidable
            (List.pairwise_cons.mp nodup).2 tailMember
          exact congrArg Nat.succ induction

theorem nonzeroScalars_length :
    presentation.nonzeroScalars.length = presentation.carrier.length - 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroScalars
  have count := filter_nonzero_length_add_one presentation.eqDecidable
    presentation.carrierNodup (presentation.carrierComplete 0)
  calc
    (presentation.carrier.filter fun value => value ≠ 0).length =
        ((presentation.carrier.filter fun value => value ≠ 0).length + 1) - 1 := by
      rw [Nat.add_sub_cancel]
    _ = presentation.carrier.length - 1 := congrArg (fun length => length - 1) count

theorem scalarPairs_complete (pair : ScalarPair K) :
    pair ∈ presentation.scalarPairs := by
  unfold scalarPairs
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨pair.first, presentation.carrierComplete pair.first, ?_⟩
  exact QuotientFreeList.mem_map.mpr
    ⟨pair.second, presentation.carrierComplete pair.second, rfl⟩

private theorem scalarPairs_nodup_flatMap
    (presentation : FiniteOddFieldPresentation K) :
    ∀ {values : List K}, values.Nodup →
      (values.flatMap fun first =>
        presentation.carrier.map fun second =>
          (⟨first, second⟩ : ScalarPair K)).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      rw [List.flatMap_cons]
      apply QuotientFreeList.nodup_append
      · apply QuotientFreeList.nodup_map_of_injective
        · intro left right equal
          exact congrArg ScalarPair.second equal
        · exact presentation.carrierNodup
      · exact scalarPairs_nodup_flatMap presentation
          (List.pairwise_cons.mp nodup).2
      · intro left leftMember right rightMember equal
        rcases QuotientFreeList.mem_map.mp leftMember with
          ⟨leftSecond, _, leftEqual⟩
        rcases QuotientFreeList.mem_flatMap.mp rightMember with
          ⟨rightFirst, rightFirstMember, rightSecondMember⟩
        rcases QuotientFreeList.mem_map.mp rightSecondMember with
          ⟨rightSecond, _, rightEqual⟩
        apply (List.pairwise_cons.mp nodup).1 rightFirst rightFirstMember
        calc
          head = left.first := congrArg ScalarPair.first leftEqual
          _ = right.first := congrArg ScalarPair.first equal
          _ = rightFirst :=
            (congrArg ScalarPair.first rightEqual).symm

theorem scalarPairs_nodup : presentation.scalarPairs.Nodup := by
  unfold scalarPairs
  exact scalarPairs_nodup_flatMap presentation presentation.carrierNodup

theorem twoSquareFiber_nodup (value : K) :
    (presentation.twoSquareFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold twoSquareFiber
  exact presentation.scalarPairs_nodup.filter _

theorem productFiber_nodup (value : K) :
    (presentation.productFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold productFiber
  exact presentation.scalarPairs_nodup.filter _

theorem mem_twoSquareFiber_iff (value : K) (pair : ScalarPair K) :
    pair ∈ presentation.twoSquareFiber value ↔ pair.quadrance = value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold twoSquareFiber
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  exact and_iff_right (presentation.scalarPairs_complete pair)

theorem mem_productFiber_iff (value : K) (pair : ScalarPair K) :
    pair ∈ presentation.productFiber value ↔
      pair.first * pair.second = value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold productFiber
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  exact and_iff_right (presentation.scalarPairs_complete pair)

/-- When `-1` has the displayed square root `root`, split coordinates give a
constructive bijection from the two-square conic to the product hyperbola. -/
def twoSquareProductBijection (value root : K) (rootSquare : root ^ 2 = -1) :
    FiniteListBijection (presentation.twoSquareFiber value)
      (presentation.productFiber value) where
  forward := ScalarPair.split root
  backward := ScalarPair.unsplit root
  forward_mem := by
    intro pair member
    apply (presentation.mem_productFiber_iff value _).2
    rw [ScalarPair.product_split root rootSquare pair]
    exact (presentation.mem_twoSquareFiber_iff value pair).1 member
  backward_mem := by
    intro pair member
    apply (presentation.mem_twoSquareFiber_iff value _).2
    have splitProduct := ScalarPair.product_split root rootSquare
      (ScalarPair.unsplit root pair)
    rw [ScalarPair.split_unsplit root
      (root_ne_zero presentation rootSquare) presentation.twoNonzero pair]
      at splitProduct
    exact splitProduct.symm.trans
      ((presentation.mem_productFiber_iff value pair).1 member)
  backward_forward := by
    intro pair _
    exact ScalarPair.unsplit_split root
      (root_ne_zero presentation rootSquare) presentation.twoNonzero pair
  forward_backward := by
    intro pair _
    exact ScalarPair.split_unsplit root
      (root_ne_zero presentation rootSquare) presentation.twoNonzero pair

theorem twoSquareCount_eq_productFiber_length (value root : K)
    (rootSquare : root ^ 2 = -1) :
    presentation.twoSquareCount value =
      (presentation.productFiber value).length := by
  unfold twoSquareCount
  exact FiniteListBijection.length_eq
    (presentation.twoSquareProductBijection value root rootSquare)
    (presentation.twoSquareFiber_nodup value)
    (presentation.productFiber_nodup value)

private theorem first_ne_zero_of_product_eq {value : K}
    (valueNonzero : value ≠ 0) (pair : ScalarPair K)
    (product : pair.first * pair.second = value) : pair.first ≠ 0 := by
  intro firstZero
  apply valueNonzero
  calc
    value = pair.first * pair.second := product.symm
    _ = 0 := by rw [firstZero, zero_mul]

/-- A nonzero product fiber is parametrized by its nonzero first coordinate. -/
def nonzeroProductBijection (value : K) (valueNonzero : value ≠ 0) :
    FiniteListBijection (presentation.productFiber value)
      presentation.nonzeroScalars where
  forward := ScalarPair.first
  backward := fun first => ⟨first, value / first⟩
  forward_mem := by
    intro pair member
    apply (presentation.mem_nonzeroScalars_iff pair.first).2
    exact ⟨first_ne_zero_of_product_eq valueNonzero pair
      ((presentation.mem_productFiber_iff value pair).1 member),
      presentation.carrierComplete pair.first⟩
  backward_mem := by
    intro first member
    apply (presentation.mem_productFiber_iff value _).2
    have firstNonzero :=
      (presentation.mem_nonzeroScalars_iff first).1 member |>.1
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      first * (value * first⁻¹) =
          value * (first * first⁻¹) := by ring1
      _ = value := by
        rw [RFAP.ExplicitField.mul_inv_cancel first firstNonzero, mul_one]
  backward_forward := by
    intro pair member
    have product := (presentation.mem_productFiber_iff value pair).1 member
    have firstNonzero :=
      first_ne_zero_of_product_eq valueNonzero pair product
    apply ScalarPair.ext
    · rfl
    · change value / pair.first = pair.second
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        value * pair.first⁻¹ =
            (pair.first * pair.second) * pair.first⁻¹ := by rw [product]
        _ = pair.second * (pair.first * pair.first⁻¹) := by ring1
        _ = pair.second := by
          rw [RFAP.ExplicitField.mul_inv_cancel pair.first firstNonzero,
            mul_one]
  forward_backward := by
    intro _ _
    rfl

theorem productFiber_length_of_ne_zero (value : K) (valueNonzero : value ≠ 0) :
    (presentation.productFiber value).length =
      presentation.nonzeroScalars.length := by
  exact FiniteListBijection.length_eq
    (presentation.nonzeroProductBijection value valueNonzero)
    (presentation.productFiber_nodup value)
    presentation.nonzeroScalars_nodup

theorem twoSquareCount_of_minus_one_square_of_ne_zero
    (value root : K) (rootSquare : root ^ 2 = -1)
    (valueNonzero : value ≠ 0) :
    presentation.twoSquareCount value =
      presentation.carrier.length - 1 := by
  rw [presentation.twoSquareCount_eq_productFiber_length value root rootSquare,
    presentation.productFiber_length_of_ne_zero value valueNonzero,
    presentation.nonzeroScalars_length]

/-- The zero product fiber, with the origin included only on the vertical
axis and the horizontal axis restricted to nonzero first coordinates. -/
def zeroProductPoints : List (ScalarPair K) :=
  presentation.carrier.map (fun second => ⟨0, second⟩) ++
    presentation.nonzeroScalars.map (fun first => ⟨first, 0⟩)

theorem zeroProductPoints_nodup : presentation.zeroProductPoints.Nodup := by
  unfold zeroProductPoints
  apply QuotientFreeList.nodup_append
  · apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      exact congrArg ScalarPair.second equal
    · exact presentation.carrierNodup
  · apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      exact congrArg ScalarPair.first equal
    · exact presentation.nonzeroScalars_nodup
  · intro left leftMember right rightMember equal
    rcases QuotientFreeList.mem_map.mp leftMember with
      ⟨leftSecond, _, leftEqual⟩
    rcases QuotientFreeList.mem_map.mp rightMember with
      ⟨rightFirst, rightFirstMember, rightEqual⟩
    have rightNonzero :=
      (presentation.mem_nonzeroScalars_iff rightFirst).1 rightFirstMember |>.1
    apply rightNonzero
    calc
      rightFirst = right.first := congrArg ScalarPair.first rightEqual
      _ = left.first := (congrArg ScalarPair.first equal).symm
      _ = 0 := (congrArg ScalarPair.first leftEqual).symm

theorem mem_zeroProductPoints_iff (pair : ScalarPair K) :
    pair ∈ presentation.zeroProductPoints ↔
      pair.first * pair.second = 0 := by
  constructor
  · intro member
    rcases List.mem_append.mp member with vertical | horizontal
    · rcases QuotientFreeList.mem_map.mp vertical with
        ⟨second, _, equal⟩
      rw [← equal]
      exact zero_mul second
    · rcases QuotientFreeList.mem_map.mp horizontal with
        ⟨first, _, equal⟩
      rw [← equal]
      exact mul_zero first
  · intro product
    cases presentation.eqDecidable pair.first 0 with
    | isTrue firstZero =>
        apply List.mem_append.mpr
        left
        apply QuotientFreeList.mem_map.mpr
        refine ⟨pair.second, presentation.carrierComplete pair.second, ?_⟩
        apply ScalarPair.ext
        · exact firstZero.symm
        · rfl
    | isFalse firstNonzero =>
        have secondZero : pair.second = 0 := by
          cases presentation.eqDecidable pair.second 0 with
          | isTrue equal => exact equal
          | isFalse secondNonzero =>
              exact False.elim
                (RFAP.ExplicitField.mul_ne_zero firstNonzero secondNonzero product)
        apply List.mem_append.mpr
        right
        apply QuotientFreeList.mem_map.mpr
        refine ⟨pair.first,
          (presentation.mem_nonzeroScalars_iff pair.first).2
            ⟨firstNonzero, presentation.carrierComplete pair.first⟩, ?_⟩
        apply ScalarPair.ext
        · rfl
        · exact secondZero.symm

/-- The zero hyperbola fiber and its explicit two-axis display contain the
same points. -/
def zeroProductBijection :
    FiniteListBijection (presentation.productFiber 0)
      presentation.zeroProductPoints where
  forward := fun pair => pair
  backward := fun pair => pair
  forward_mem := by
    intro pair member
    exact (presentation.mem_zeroProductPoints_iff pair).2
      ((presentation.mem_productFiber_iff 0 pair).1 member)
  backward_mem := by
    intro pair member
    exact (presentation.mem_productFiber_iff 0 pair).2
      ((presentation.mem_zeroProductPoints_iff pair).1 member)
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

theorem zeroProductPoints_length :
    presentation.zeroProductPoints.length =
      presentation.carrier.length + (presentation.carrier.length - 1) := by
  unfold zeroProductPoints
  rw [List.length_append, List.length_map, List.length_map,
    presentation.nonzeroScalars_length]

theorem productFiber_zero_length :
    (presentation.productFiber 0).length =
      presentation.carrier.length + (presentation.carrier.length - 1) := by
  calc
    (presentation.productFiber 0).length =
        presentation.zeroProductPoints.length :=
      FiniteListBijection.length_eq presentation.zeroProductBijection
        (presentation.productFiber_nodup 0)
        presentation.zeroProductPoints_nodup
    _ = presentation.carrier.length +
        (presentation.carrier.length - 1) :=
      presentation.zeroProductPoints_length

theorem twoSquareCount_zero_of_minus_one_square
    (root : K) (rootSquare : root ^ 2 = -1) :
    presentation.twoSquareCount 0 =
      presentation.carrier.length + (presentation.carrier.length - 1) := by
  rw [presentation.twoSquareCount_eq_productFiber_length 0 root rootSquare,
    presentation.productFiber_zero_length]

/-- The pair computed by the cached two-square search. -/
def representedPair (value : K) : ScalarPair K :=
  let representation := presentation.twoSquareRepresentation value
  ⟨representation.first, representation.second⟩

theorem representedPair_quadrance (value : K) :
    (presentation.representedPair value).quadrance = value := by
  unfold representedPair ScalarPair.quadrance
  exact (presentation.twoSquareRepresentation value).equation

/-- Multiplication by a computed representation of a nonzero value transports
the unit circle bijectively onto that value's two-square fiber. -/
def unitCircleToNonzeroFiberBijection (value : K) (valueNonzero : value ≠ 0) :
    FiniteListBijection (presentation.twoSquareFiber 1)
      (presentation.twoSquareFiber value) where
  forward := ScalarPair.mul (presentation.representedPair value)
  backward := ScalarPair.divideMul value (presentation.representedPair value)
  forward_mem := by
    intro pair member
    apply (presentation.mem_twoSquareFiber_iff value _).2
    rw [ScalarPair.quadrance_mul, presentation.representedPair_quadrance,
      (presentation.mem_twoSquareFiber_iff 1 pair).1 member, mul_one]
  backward_mem := by
    intro pair member
    apply (presentation.mem_twoSquareFiber_iff 1 _).2
    exact ScalarPair.quadrance_divideMul value valueNonzero
      (presentation.representedPair value) pair
      (presentation.representedPair_quadrance value)
      ((presentation.mem_twoSquareFiber_iff value pair).1 member)
  backward_forward := by
    intro pair _
    exact ScalarPair.divideMul_mul value valueNonzero
      (presentation.representedPair value) pair
      (presentation.representedPair_quadrance value)
  forward_backward := by
    intro pair _
    exact ScalarPair.mul_divideMul value valueNonzero
      (presentation.representedPair value) pair
      (presentation.representedPair_quadrance value)

theorem twoSquareCount_eq_one_of_ne_zero (value : K) (valueNonzero : value ≠ 0) :
    presentation.twoSquareCount value = presentation.twoSquareCount 1 := by
  unfold twoSquareCount
  exact (FiniteListBijection.length_eq
    (presentation.unitCircleToNonzeroFiberBijection value valueNonzero)
    (presentation.twoSquareFiber_nodup 1)
    (presentation.twoSquareFiber_nodup value)).symm

/-- The `q` affine parameters followed by the exceptional parameter at
infinity.  `Option` keeps the two pieces disjoint without a quotient. -/
def circleParameters : List (Option K) :=
  presentation.carrier.map some ++ [none]

theorem circleParameters_nodup : presentation.circleParameters.Nodup := by
  unfold circleParameters
  apply QuotientFreeList.nodup_append
  · apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      injection equal
    · exact presentation.carrierNodup
  · exact QuotientFreeList.nodup_singleton none
  · intro left leftMember right rightMember equal
    rcases QuotientFreeList.mem_map.mp leftMember with
      ⟨parameter, _, parameterEqual⟩
    rcases List.mem_cons.mp rightMember with rightEqual | impossible
    · have contradiction : some parameter = none :=
        parameterEqual.trans (equal.trans rightEqual)
      nomatch contradiction
    · nomatch impossible

theorem circleParameters_length :
    presentation.circleParameters.length = presentation.carrier.length + 1 := by
  unfold circleParameters
  rw [List.length_append, List.length_map]
  rfl

/-- If `-1` is nonsquare, the rational circle parametrization plus its
exceptional point is a complete constructive enumeration of `x²+y²=1`. -/
def unitCircleParameterBijection
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    FiniteListBijection (presentation.twoSquareFiber 1)
      presentation.circleParameters := by
  letI : DecidableEq K := presentation.eqDecidable
  exact
    { forward := fun pair =>
        if pair = ScalarPair.circleInfinity then none
        else some (pair.second / (pair.first + 1))
      backward := fun parameter => match parameter with
        | some value => ScalarPair.circleParameter value
        | none => ScalarPair.circleInfinity
      forward_mem := by
        intro pair member
        if infinity : pair = ScalarPair.circleInfinity then
          rw [if_pos infinity]
          unfold circleParameters
          exact List.mem_append.mpr (Or.inr List.mem_cons_self)
        else
          rw [if_neg infinity]
          unfold circleParameters
          apply List.mem_append.mpr
          left
          exact QuotientFreeList.mem_map.mpr
            ⟨pair.second / (pair.first + 1),
              presentation.carrierComplete _, rfl⟩
      backward_mem := by
        intro parameter _
        cases parameter with
        | none =>
            exact (presentation.mem_twoSquareFiber_iff 1 _).2
              ScalarPair.circleInfinity_quadrance
        | some value =>
            exact (presentation.mem_twoSquareFiber_iff 1 _).2
              (ScalarPair.quadrance_circleParameter minusOneNoRoot value)
      backward_forward := by
        intro pair member
        have quadranceOne :=
          (presentation.mem_twoSquareFiber_iff 1 pair).1 member
        if infinity : pair = ScalarPair.circleInfinity then
          rw [if_pos infinity]
          exact infinity.symm
        else
          rw [if_neg infinity]
          exact ScalarPair.circleParameter_complete
            presentation.eqDecidable minusOneNoRoot pair quadranceOne infinity
      forward_backward := by
        intro parameter _
        cases parameter with
        | none => rw [if_pos rfl]
        | some value =>
            rw [if_neg (ScalarPair.circleParameter_ne_infinity
              presentation.twoNonzero minusOneNoRoot value)]
            rw [ScalarPair.circleParameter_inverse presentation.twoNonzero
              minusOneNoRoot value] }

theorem twoSquareCount_one_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.twoSquareCount 1 = presentation.carrier.length + 1 := by
  unfold twoSquareCount
  calc
    (presentation.twoSquareFiber 1).length =
        presentation.circleParameters.length :=
      FiniteListBijection.length_eq
        (presentation.unitCircleParameterBijection minusOneNoRoot)
        (presentation.twoSquareFiber_nodup 1)
        presentation.circleParameters_nodup
    _ = presentation.carrier.length + 1 :=
      presentation.circleParameters_length

theorem twoSquareCount_of_minus_one_nonsquare_of_ne_zero
    (value : K) (valueNonzero : value ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.twoSquareCount value = presentation.carrier.length + 1 := by
  rw [presentation.twoSquareCount_eq_one_of_ne_zero value valueNonzero,
    presentation.twoSquareCount_one_of_minus_one_nonsquare minusOneNoRoot]

/-- In the nonsplit case, the zero conic contains only the origin. -/
def nonsplitZeroFiberBijection
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    FiniteListBijection (presentation.twoSquareFiber 0)
      [(⟨0, 0⟩ : ScalarPair K)] where
  forward := fun pair => pair
  backward := fun pair => pair
  forward_mem := by
    intro pair member
    have pairZero :=
      ScalarPair.eq_zero_of_quadrance_eq_zero_of_minus_one_nonsquare
        presentation.eqDecidable minusOneNoRoot pair
        ((presentation.mem_twoSquareFiber_iff 0 pair).1 member)
    rw [pairZero]
    exact List.mem_cons_self
  backward_mem := by
    intro pair member
    rcases List.mem_cons.mp member with pairZero | impossible
    · rw [pairZero]
      exact (presentation.mem_twoSquareFiber_iff 0 _).2 (by
        unfold ScalarPair.quadrance
        ring1)
    · nomatch impossible
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

theorem twoSquareCount_zero_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.twoSquareCount 0 = 1 := by
  unfold twoSquareCount
  exact FiniteListBijection.length_eq
    (presentation.nonsplitZeroFiberBijection minusOneNoRoot)
    (presentation.twoSquareFiber_nodup 0)
    (QuotientFreeList.nodup_singleton (⟨0, 0⟩ : ScalarPair K))

/-- Constructive exhaustive classification of every binary affine quadric
fiber.  This is the square-status form of the usual `q mod 4` dichotomy. -/
inductive TwoSquareCountClassification where
  | split (root : K) (rootSquare : root ^ 2 = -1)
      (zeroCount : presentation.twoSquareCount 0 =
        presentation.carrier.length + (presentation.carrier.length - 1))
      (nonzeroCount : ∀ value : K, value ≠ 0 →
        presentation.twoSquareCount value = presentation.carrier.length - 1)
  | nonsplit (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (zeroCount : presentation.twoSquareCount 0 = 1)
      (nonzeroCount : ∀ value : K, value ≠ 0 →
        presentation.twoSquareCount value = presentation.carrier.length + 1)

/-- Compute the binary-quadric count regime from the cached square table. -/
def classifyTwoSquareCounts :
    presentation.TwoSquareCountClassification :=
  match presentation.classifyMinusOne with
  | SquareClassification.square root rootSquare =>
      TwoSquareCountClassification.split root rootSquare
        (presentation.twoSquareCount_zero_of_minus_one_square root rootSquare)
        (fun value valueNonzero =>
          presentation.twoSquareCount_of_minus_one_square_of_ne_zero
            value root rootSquare valueNonzero)
  | SquareClassification.nonsquare minusOneNoRoot =>
      TwoSquareCountClassification.nonsplit minusOneNoRoot
        (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
        (fun value valueNonzero =>
          presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
            value valueNonzero minusOneNoRoot)

/-- Displayed roots of one scalar equation `root² = value`. -/
def squareRootFiber (value : K) : List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.carrier.filter fun root => root ^ 2 = value

/-- Executable number of displayed square roots. -/
def squareRootCount (value : K) : Nat :=
  (presentation.squareRootFiber value).length

/-- Displayed scalars that are not roots of `root² = value`. -/
def squareNonrootFiber (value : K) : List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.carrier.filter fun root => root ^ 2 ≠ value

def squareNonrootCount (value : K) : Nat :=
  (presentation.squareNonrootFiber value).length

theorem squareRootFiber_nodup (value : K) :
    (presentation.squareRootFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold squareRootFiber
  exact presentation.carrierNodup.filter _

theorem mem_squareRootFiber_iff (value root : K) :
    root ∈ presentation.squareRootFiber value ↔ root ^ 2 = value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold squareRootFiber
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  exact and_iff_right (presentation.carrierComplete root)

private theorem squareRoot_partition_length (eqDecidable : DecidableEq K)
    (value : K) : ∀ values : List K,
    (letI : DecidableEq K := eqDecidable
     (values.filter fun root => root ^ 2 = value).length +
       (values.filter fun root => root ^ 2 ≠ value).length) = values.length
  | [] => rfl
  | head :: tail => by
      letI : DecidableEq K := eqDecidable
      cases eqDecidable (head ^ 2) value with
      | isTrue equal =>
          rw [List.filter_cons_of_pos
              (p := fun root : K => decide (root ^ 2 = value))
              (decide_eq_true equal),
            List.filter_cons_of_neg
              (p := fun root : K => decide (root ^ 2 ≠ value))
              (fun accepted => (of_decide_eq_true accepted) equal)]
          simp only [List.length_cons]
          rw [Nat.succ_add]
          exact congrArg Nat.succ
            (squareRoot_partition_length eqDecidable value tail)
      | isFalse different =>
          rw [List.filter_cons_of_neg
              (p := fun root : K => decide (root ^ 2 = value))
              (fun accepted => different (of_decide_eq_true accepted)),
            List.filter_cons_of_pos
              (p := fun root : K => decide (root ^ 2 ≠ value))
              (decide_eq_true different)]
          simp only [List.length_cons]
          rw [Nat.add_succ]
          exact congrArg Nat.succ
            (squareRoot_partition_length eqDecidable value tail)

theorem squareRootCount_add_squareNonrootCount (value : K) :
    presentation.squareRootCount value +
      presentation.squareNonrootCount value = presentation.carrier.length := by
  unfold squareRootCount squareNonrootCount squareRootFiber squareNonrootFiber
  exact squareRoot_partition_length presentation.eqDecidable value
    presentation.carrier

theorem squareNonrootCount_eq_length_sub_squareRootCount (value : K) :
    presentation.squareNonrootCount value =
      presentation.carrier.length - presentation.squareRootCount value := by
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  calc
    presentation.squareNonrootCount value =
        (presentation.squareRootCount value +
          presentation.squareNonrootCount value) -
            presentation.squareRootCount value := by
      rw [Nat.add_sub_cancel_left]
    _ = presentation.carrier.length - presentation.squareRootCount value :=
      congrArg (fun count => count - presentation.squareRootCount value)
        partition

def zeroSquareRootBijection :
    FiniteListBijection (presentation.squareRootFiber 0) [(0 : K)] where
  forward := fun root => root
  backward := fun root => root
  forward_mem := by
    intro root member
    have rootZero := ScalarPair.eq_zero_of_square_eq_zero
      presentation.eqDecidable root
      ((presentation.mem_squareRootFiber_iff 0 root).1 member)
    rw [rootZero]
    exact List.mem_cons_self
  backward_mem := by
    intro root member
    rcases List.mem_cons.mp member with rootZero | impossible
    · rw [rootZero]
      exact (presentation.mem_squareRootFiber_iff 0 0).2 (by ring1)
    · nomatch impossible
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

theorem squareRootCount_zero : presentation.squareRootCount 0 = 1 := by
  unfold squareRootCount
  exact FiniteListBijection.length_eq presentation.zeroSquareRootBijection
    (presentation.squareRootFiber_nodup 0)
    (QuotientFreeList.nodup_singleton (0 : K))

private theorem root_ne_zero_of_square_ne_zero {value root : K}
    (valueNonzero : value ≠ 0) (rootSquare : root ^ 2 = value) : root ≠ 0 := by
  intro rootZero
  apply valueNonzero
  calc
    value = root ^ 2 := rootSquare.symm
    _ = 0 := by rw [rootZero]; ring1

private theorem root_ne_neg_root
    (presentation : FiniteOddFieldPresentation K)
    (root : K) (rootNonzero : root ≠ 0) :
    root ≠ -root := by
  intro equal
  have twiceZero : (2 : K) * root = 0 := by
    calc
      (2 : K) * root = root + root := by ring1
      _ = -root + root := congrArg (fun value => value + root) equal
      _ = 0 := by ring1
  exact (RFAP.ExplicitField.mul_ne_zero presentation.twoNonzero rootNonzero)
    twiceZero

/-- A displayed nonzero square has exactly its two opposite roots. -/
def nonzeroSquareRootBijection (value root : K) (rootSquare : root ^ 2 = value) :
    FiniteListBijection (presentation.squareRootFiber value) [root, -root] where
  forward := fun candidate => candidate
  backward := fun candidate => candidate
  forward_mem := by
    intro candidate member
    have candidateSquare :=
      (presentation.mem_squareRootFiber_iff value candidate).1 member
    have equalSquares : candidate ^ 2 = root ^ 2 :=
      candidateSquare.trans rootSquare.symm
    cases presentation.eqDecidable candidate root with
    | isTrue equal => exact List.mem_cons.mpr (Or.inl equal)
    | isFalse notRoot =>
        have firstFactorNonzero : candidate - root ≠ 0 := by
          intro differenceZero
          apply notRoot
          calc
            candidate = (candidate - root) + root := by ring1
            _ = root := by rw [differenceZero, zero_add]
        have productZero : (candidate - root) * (candidate + root) = 0 := by
          calc
            (candidate - root) * (candidate + root) =
                candidate ^ 2 - root ^ 2 := by ring1
            _ = 0 := by rw [equalSquares]; ring1
        have secondFactorZero : candidate + root = 0 := by
          cases presentation.eqDecidable (candidate + root) 0 with
          | isTrue equal => exact equal
          | isFalse secondFactorNonzero =>
              exact False.elim
                ((RFAP.ExplicitField.mul_ne_zero firstFactorNonzero
                  secondFactorNonzero) productZero)
        apply List.mem_cons.mpr
        right
        apply List.mem_cons.mpr
        left
        calc
          candidate = (candidate + root) - root := by ring1
          _ = -root := by rw [secondFactorZero]; ring1
  backward_mem := by
    intro candidate member
    rcases List.mem_cons.mp member with rootEqual | negativeMember
    · rw [rootEqual]
      exact (presentation.mem_squareRootFiber_iff value root).2 rootSquare
    · rcases List.mem_cons.mp negativeMember with negativeEqual | impossible
      · rw [negativeEqual]
        apply (presentation.mem_squareRootFiber_iff value (-root)).2
        calc
          (-root) ^ 2 = root ^ 2 := by ring1
          _ = value := rootSquare
      · nomatch impossible
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

theorem squareRootCount_of_nonzero_square (value root : K)
    (valueNonzero : value ≠ 0) (rootSquare : root ^ 2 = value) :
    presentation.squareRootCount value = 2 := by
  unfold squareRootCount
  exact FiniteListBijection.length_eq
    (presentation.nonzeroSquareRootBijection value root rootSquare)
    (presentation.squareRootFiber_nodup value)
    (QuotientFreeList.nodup_append
      (QuotientFreeList.nodup_singleton root)
      (QuotientFreeList.nodup_singleton (-root)) (by
        intro left leftMember right rightMember
        rcases List.mem_cons.mp leftMember with leftEqual | leftImpossible
        · rcases List.mem_cons.mp rightMember with
            rightEqual | rightImpossible
          · rw [leftEqual, rightEqual]
            exact root_ne_neg_root presentation root
              (root_ne_zero_of_square_ne_zero valueNonzero rootSquare)
          · nomatch rightImpossible
        · nomatch leftImpossible))

private theorem filter_squareRoot_eq_nil (eqDecidable : DecidableEq K)
    (value : K) (noRoot : ∀ root : K, root ^ 2 ≠ value) :
    ∀ values : List K,
      (letI : DecidableEq K := eqDecidable
       values.filter fun root => root ^ 2 = value) = []
  | [] => rfl
  | head :: tail => by
      letI : DecidableEq K := eqDecidable
      rw [List.filter_cons_of_neg
        (p := fun root : K => decide (root ^ 2 = value))
        (fun accepted => noRoot head (of_decide_eq_true accepted))]
      exact filter_squareRoot_eq_nil eqDecidable value noRoot tail

theorem squareRootFiber_eq_nil_of_nonsquare (value : K)
    (noRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.squareRootFiber value = [] := by
  unfold squareRootFiber
  exact filter_squareRoot_eq_nil presentation.eqDecidable value noRoot
    presentation.carrier

theorem squareRootCount_of_nonsquare (value : K)
    (noRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.squareRootCount value = 0 := by
  unfold squareRootCount
  rw [presentation.squareRootFiber_eq_nil_of_nonsquare value noRoot]
  rfl

/-- The ternary quadrance count expressed as the finite sum of its binary
slices `r²+s² = value-t²`. -/
def ternaryQuadranceSlicedCount (value : K) : Nat :=
  (presentation.carrier.map fun t =>
    presentation.twoSquareCount (value - t ^ 2)).foldr Nat.add 0

private theorem nat_add_swap_first (first second third : Nat) :
    first + (second + third) = second + (first + third) := by
  calc
    first + (second + third) = (first + second) + third :=
      (Nat.add_assoc first second third).symm
    _ = (second + first) + third :=
      congrArg (fun value => value + third) (Nat.add_comm first second)
    _ = second + (first + third) := Nat.add_assoc second first third

private theorem nat_add_swap_first_flat (first second third : Nat) :
    first + (second + third) = (second + first) + third := by
  calc
    first + (second + third) = (first + second) + third :=
      (Nat.add_assoc first second third).symm
    _ = (second + first) + third :=
      congrArg (fun value => value + third) (Nat.add_comm first second)

private theorem nat_add_rotate_first (first second third : Nat) :
    first + (second + third) = second + (third + first) := by
  calc
    first + (second + third) = second + (first + third) :=
      nat_add_swap_first first second third
    _ = second + (third + first) :=
      congrArg (fun value => second + value) (Nat.add_comm first third)

private theorem ternarySlice_partition
    (presentation : FiniteOddFieldPresentation K) (eqDecidable : DecidableEq K)
    (value : K) (zeroFiberSize nonzeroFiberSize : Nat)
    (zeroFiberCount : presentation.twoSquareCount 0 = zeroFiberSize)
    (nonzeroFiberCount : ∀ residual : K, residual ≠ 0 →
      presentation.twoSquareCount residual = nonzeroFiberSize) :
    ∀ values : List K,
      (values.map fun t =>
        presentation.twoSquareCount (value - t ^ 2)).foldr Nat.add 0 =
      (letI : DecidableEq K := eqDecidable
       (values.filter fun t => t ^ 2 = value).length * zeroFiberSize +
         (values.filter fun t => t ^ 2 ≠ value).length * nonzeroFiberSize)
  | [] => by
      change 0 = 0 * zeroFiberSize + 0 * nonzeroFiberSize
      rw [Nat.zero_mul, Nat.zero_mul, zero_add]
  | head :: tail => by
      letI : DecidableEq K := eqDecidable
      cases eqDecidable (head ^ 2) value with
      | isTrue equal =>
          have residualZero : value - head ^ 2 = 0 := by rw [equal]; ring1
          rw [List.map_cons, List.foldr_cons, residualZero, zeroFiberCount,
            List.filter_cons_of_pos
              (p := fun t : K => decide (t ^ 2 = value))
              (decide_eq_true equal),
            List.filter_cons_of_neg
              (p := fun t : K => decide (t ^ 2 ≠ value))
              (fun accepted => (of_decide_eq_true accepted) equal),
            List.length_cons,
            ternarySlice_partition presentation eqDecidable value
              zeroFiberSize nonzeroFiberSize zeroFiberCount nonzeroFiberCount tail,
            Nat.succ_mul]
          exact nat_add_swap_first_flat zeroFiberSize _ _
      | isFalse different =>
          have residualNonzero : value - head ^ 2 ≠ 0 := by
            intro residualZero
            apply different
            calc
              head ^ 2 = value - (value - head ^ 2) := by ring1
              _ = value := by rw [residualZero]; ring1
          rw [List.map_cons, List.foldr_cons,
            nonzeroFiberCount (value - head ^ 2) residualNonzero,
            List.filter_cons_of_neg
              (p := fun t : K => decide (t ^ 2 = value))
              (fun accepted => different (of_decide_eq_true accepted)),
            List.filter_cons_of_pos
              (p := fun t : K => decide (t ^ 2 ≠ value))
              (decide_eq_true different),
            List.length_cons,
            ternarySlice_partition presentation eqDecidable value
              zeroFiberSize nonzeroFiberSize zeroFiberCount nonzeroFiberCount tail,
            Nat.succ_mul]
          exact nat_add_rotate_first nonzeroFiberSize _ _

theorem ternaryQuadranceSlicedCount_eq_root_partition
    (value : K) (zeroFiberSize nonzeroFiberSize : Nat)
    (zeroFiberCount : presentation.twoSquareCount 0 = zeroFiberSize)
    (nonzeroFiberCount : ∀ residual : K, residual ≠ 0 →
      presentation.twoSquareCount residual = nonzeroFiberSize) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.squareRootCount value * zeroFiberSize +
        presentation.squareNonrootCount value * nonzeroFiberSize := by
  unfold ternaryQuadranceSlicedCount squareRootCount squareNonrootCount
    squareRootFiber squareNonrootFiber
  exact ternarySlice_partition presentation presentation.eqDecidable value
    zeroFiberSize nonzeroFiberSize zeroFiberCount nonzeroFiberCount
    presentation.carrier

/-- The ternary null cone has exactly `q²` affine points in every displayed
odd finite field, independently of the split/nonsplit binary regime. -/
theorem ternaryQuadranceSlicedCount_zero :
    presentation.ternaryQuadranceSlicedCount 0 =
      presentation.carrier.length * presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_zero
  have partition := presentation.squareRootCount_add_squareNonrootCount 0
  rw [rootCount] at partition
  have predecessor : presentation.carrier.length - 1 =
      presentation.squareNonrootCount 0 := by
    calc
      presentation.carrier.length - 1 =
          (1 + presentation.squareNonrootCount 0) - 1 := by rw [partition]
      _ = presentation.squareNonrootCount 0 := by
        rw [Nat.add_sub_cancel_left]
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
        0
        (presentation.carrier.length + (presentation.carrier.length - 1))
        (presentation.carrier.length - 1)
        (presentation.twoSquareCount_zero_of_minus_one_square root rootSquare)
        (fun residual residualNonzero =>
          presentation.twoSquareCount_of_minus_one_square_of_ne_zero
            residual root rootSquare residualNonzero)
      rw [rootCount, one_mul, predecessor] at sliced
      rw [← partition] at sliced ⊢
      exact sliced.trans (by ring1)
  | nonsquare minusOneNoRoot =>
      have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
        0 1 (presentation.carrier.length + 1)
        (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
        (fun residual residualNonzero =>
          presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
            residual residualNonzero minusOneNoRoot)
      rw [rootCount, one_mul] at sliced
      rw [← partition] at sliced ⊢
      exact sliced.trans (by ring1)

private theorem nat_eq_sub_of_add_eq {left subtracted total : Nat}
    (equal : left + subtracted = total) : left = total - subtracted := by
  calc
    left = (left + subtracted) - subtracted :=
      (Nat.add_sub_cancel left subtracted).symm
    _ = total - subtracted :=
      congrArg (fun value => value - subtracted) equal

private theorem carrier_predecessor (presentation : FiniteOddFieldPresentation K) :
    presentation.carrier.length - 1 =
      presentation.squareNonrootCount 0 := by
  have partition := presentation.squareRootCount_add_squareNonrootCount 0
  rw [presentation.squareRootCount_zero] at partition
  calc
    presentation.carrier.length - 1 =
        (1 + presentation.squareNonrootCount 0) - 1 := by rw [partition]
    _ = presentation.squareNonrootCount 0 := by
      rw [Nat.add_sub_cancel_left]

theorem ternaryQuadranceSlicedCount_of_split_square
    (value minusOneRoot valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonzero_square
    value valueRoot valueNonzero valueSquare
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount] at partition
  have partitionOne : 1 + (1 + presentation.squareNonrootCount value) =
      presentation.carrier.length := by
    calc
      1 + (1 + presentation.squareNonrootCount value) =
          2 + presentation.squareNonrootCount value := by ring1
      _ = presentation.carrier.length := partition
  have predecessor : presentation.carrier.length - 1 =
      1 + presentation.squareNonrootCount value := by
    calc
      presentation.carrier.length - 1 =
          (1 + (1 + presentation.squareNonrootCount value)) - 1 := by
        rw [partitionOne]
      _ = 1 + presentation.squareNonrootCount value := by
        rw [Nat.add_sub_cancel_left]
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value
    (presentation.carrier.length + (presentation.carrier.length - 1))
    (presentation.carrier.length - 1)
    (presentation.twoSquareCount_zero_of_minus_one_square
      minusOneRoot minusOneSquare)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_square_of_ne_zero
        residual minusOneRoot minusOneSquare residualNonzero)
  rw [rootCount, predecessor] at sliced
  rw [← partition] at sliced ⊢
  exact sliced.trans (by ring1)

theorem ternaryQuadranceSlicedCount_of_split_nonsquare
    (value minusOneRoot : K)
    (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonsquare value valueNoRoot
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount, zero_add] at partition
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value
    (presentation.carrier.length + (presentation.carrier.length - 1))
    (presentation.carrier.length - 1)
    (presentation.twoSquareCount_zero_of_minus_one_square
      minusOneRoot minusOneSquare)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_square_of_ne_zero
        residual minusOneRoot minusOneSquare residualNonzero)
  rw [rootCount, Nat.zero_mul, zero_add, partition] at sliced
  have zeroPartition := presentation.squareRootCount_add_squareNonrootCount 0
  rw [presentation.squareRootCount_zero] at zeroPartition
  have predecessor := carrier_predecessor presentation
  have added : presentation.ternaryQuadranceSlicedCount value +
      presentation.carrier.length =
        presentation.carrier.length * presentation.carrier.length := by
    calc
      presentation.ternaryQuadranceSlicedCount value +
          presentation.carrier.length =
        presentation.carrier.length * (presentation.carrier.length - 1) +
          presentation.carrier.length := congrArg
            (fun count => count + presentation.carrier.length) sliced
      _ = presentation.carrier.length * presentation.carrier.length := by
        rw [predecessor, ← zeroPartition]
        ring1
  exact nat_eq_sub_of_add_eq added

theorem ternaryQuadranceSlicedCount_of_nonsplit_square
    (value valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonzero_square
    value valueRoot valueNonzero valueSquare
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount] at partition
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value 1 (presentation.carrier.length + 1)
    (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
        residual residualNonzero minusOneNoRoot)
  rw [rootCount, Nat.mul_one] at sliced
  have added : presentation.ternaryQuadranceSlicedCount value +
      presentation.carrier.length =
        presentation.carrier.length * presentation.carrier.length := by
    rw [← partition] at sliced ⊢
    calc
      presentation.ternaryQuadranceSlicedCount value +
          (2 + presentation.squareNonrootCount value) =
        (2 + presentation.squareNonrootCount value *
          (2 + presentation.squareNonrootCount value + 1)) +
          (2 + presentation.squareNonrootCount value) :=
            congrArg (fun count => count +
              (2 + presentation.squareNonrootCount value)) sliced
      _ = (2 + presentation.squareNonrootCount value) *
          (2 + presentation.squareNonrootCount value) := by ring1
  exact nat_eq_sub_of_add_eq added

theorem ternaryQuadranceSlicedCount_of_nonsplit_nonsquare
    (value : K)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonsquare value valueNoRoot
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount, zero_add] at partition
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value 1 (presentation.carrier.length + 1)
    (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
        residual residualNonzero minusOneNoRoot)
  rw [rootCount, Nat.zero_mul, zero_add, partition] at sliced
  exact sliced.trans (by ring1)

/-- Exhaustive constructive classification of the ternary affine fibers.
The four nonzero cases expose exactly which two square classifications produce
the `q²+q` or `q²-q` result. -/
inductive TernaryQuadranceCountClassification (value : K) where
  | zero (valueZero : value = 0)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length)
  | splitSquare (valueNonzero : value ≠ 0)
      (minusOneRoot valueRoot : K)
      (minusOneSquare : minusOneRoot ^ 2 = -1)
      (valueSquare : valueRoot ^ 2 = value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)
  | splitNonsquare (valueNonzero : value ≠ 0)
      (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1)
      (valueNoRoot : ∀ root : K, root ^ 2 ≠ value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  | nonsplitSquare (valueNonzero : value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (valueRoot : K) (valueSquare : valueRoot ^ 2 = value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  | nonsplitNonsquare (valueNonzero : value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (valueNoRoot : ∀ root : K, root ^ 2 ≠ value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)

/-- Compute the exact ternary-fiber regime from the displayed equality and
square classifiers. -/
def classifyTernaryQuadranceCount (value : K) :
    presentation.TernaryQuadranceCountClassification value := by
  cases presentation.eqDecidable value 0 with
  | isTrue valueZero =>
      exact TernaryQuadranceCountClassification.zero valueZero (by
        rw [valueZero]
        exact presentation.ternaryQuadranceSlicedCount_zero)
  | isFalse valueNonzero =>
      cases presentation.classifyMinusOne with
      | square minusOneRoot minusOneSquare =>
          cases presentation.classifySquare value with
          | square valueRoot valueSquare =>
              exact TernaryQuadranceCountClassification.splitSquare
                valueNonzero minusOneRoot valueRoot minusOneSquare valueSquare
                (presentation.ternaryQuadranceSlicedCount_of_split_square
                  value minusOneRoot valueRoot valueNonzero minusOneSquare
                  valueSquare)
          | nonsquare valueNoRoot =>
              exact TernaryQuadranceCountClassification.splitNonsquare
                valueNonzero minusOneRoot minusOneSquare valueNoRoot
                (presentation.ternaryQuadranceSlicedCount_of_split_nonsquare
                  value minusOneRoot minusOneSquare valueNoRoot)
      | nonsquare minusOneNoRoot =>
          cases presentation.classifySquare value with
          | square valueRoot valueSquare =>
              exact TernaryQuadranceCountClassification.nonsplitSquare
                valueNonzero minusOneNoRoot valueRoot valueSquare
                (presentation.ternaryQuadranceSlicedCount_of_nonsplit_square
                  value valueRoot valueNonzero minusOneNoRoot valueSquare)
          | nonsquare valueNoRoot =>
              exact TernaryQuadranceCountClassification.nonsplitNonsquare
                valueNonzero minusOneNoRoot valueNoRoot
                (presentation.ternaryQuadranceSlicedCount_of_nonsplit_nonsquare
                  value minusOneNoRoot valueNoRoot)

end FiniteOddFieldPresentation

end RationalRotations
