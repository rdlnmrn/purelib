import mathlib.Tactic.QuotientFreeRing
import Mathlib.Algebra.Ring.MinimalAxioms
import mathlib.RFAP.CanonicalFractionArithmetic
import mathlib.RFAP.ExplicitField

/-!
# Field laws for canonical fractions

All laws are proved from explicit cross-multiplication certificates and the
uniqueness of reduced positive-denominator records.  No theorem is
transported through the former quotient-valued rational field.
-/

namespace RFAP.CanonicalFraction

/-- Plain common-denominator addition on arbitrary displays. -/
def plainAddRaw (left right : RawFraction) : RawFraction :=
  ⟨left.num * (right.den : Int) + right.num * (left.den : Int),
    left.den * right.den, Nat.mul_pos left.den_pos right.den_pos⟩

/-- Plain negation on an arbitrary display. -/
def plainNegRaw (source : RawFraction) : RawFraction :=
  ⟨-source.num, source.den, source.den_pos⟩

/-- Plain multiplication on arbitrary displays. -/
def plainMulRaw (left right : RawFraction) : RawFraction :=
  ⟨left.num * right.num, left.den * right.den,
    Nat.mul_pos left.den_pos right.den_pos⟩

theorem plainAddRaw_respects {left left' right right' : RawFraction}
    (leftEquivalent : Equivalent left left')
    (rightEquivalent : Equivalent right right') :
    Equivalent (plainAddRaw left right) (plainAddRaw left' right') := by
  dsimp only [Equivalent, plainAddRaw] at leftEquivalent rightEquivalent ⊢
  calc
    (left.num * (right.den : Int) + right.num * (left.den : Int)) *
          ((left'.den : Int) * (right'.den : Int)) =
        (left.num * (left'.den : Int)) *
            ((right.den : Int) * (right'.den : Int)) +
          (right.num * (right'.den : Int)) *
            ((left.den : Int) * (left'.den : Int)) := by ring1
    _ = (left'.num * (right'.den : Int) +
          right'.num * (left'.den : Int)) *
        ((left.den : Int) * (right.den : Int)) := by
      rw [leftEquivalent, rightEquivalent]
      ring1

theorem plainNegRaw_respects {left right : RawFraction}
    (equivalent : Equivalent left right) :
    Equivalent (plainNegRaw left) (plainNegRaw right) := by
  dsimp only [Equivalent, plainNegRaw] at equivalent ⊢
  rw [Int.neg_mul, Int.neg_mul, equivalent]

theorem plainMulRaw_respects {left left' right right' : RawFraction}
    (leftEquivalent : Equivalent left left')
    (rightEquivalent : Equivalent right right') :
    Equivalent (plainMulRaw left right) (plainMulRaw left' right') := by
  dsimp only [Equivalent, plainMulRaw] at leftEquivalent rightEquivalent ⊢
  calc
    left.num * right.num * ((left'.den : Int) * (right'.den : Int)) =
        (left.num * (left'.den : Int)) *
          (right.num * (right'.den : Int)) := by ring1
    _ = (left'.num * (left.den : Int)) *
          (right'.num * (right.den : Int)) := by
      rw [leftEquivalent, rightEquivalent]
    _ = left'.num * right'.num *
          ((left.den : Int) * (right.den : Int)) := by ring1

/-- Cross-equivalent canonical records are structurally equal. -/
theorem eq_of_equivalent {left right : Rational}
    (equivalent : Equivalent left.toRaw right.toRaw) : left = right :=
  eq_of_cross equivalent

theorem add_plain (left right : Rational) :
    Equivalent (left + right).toRaw
      (plainAddRaw left.toRaw right.toRaw) := by
  change Equivalent (add left right).toRaw
    (plainAddRaw left.toRaw right.toRaw)
  simpa only [plainAddRaw, referenceAddRaw, Rational.toRaw] using
    add_equivalent left right

theorem neg_plain (source : Rational) :
    Equivalent (-source).toRaw (plainNegRaw source.toRaw) := by
  rfl

theorem mul_plain (left right : Rational) :
    Equivalent (left * right).toRaw
      (plainMulRaw left.toRaw right.toRaw) := by
  change Equivalent (mul left right).toRaw
    (plainMulRaw left.toRaw right.toRaw)
  simpa only [plainMulRaw, referenceMulRaw, Rational.toRaw] using
    mul_equivalent left right

theorem add_comm (left right : Rational) : left + right = right + left := by
  apply eq_of_equivalent
  have plainCommutes :
      Equivalent (plainAddRaw left.toRaw right.toRaw)
        (plainAddRaw right.toRaw left.toRaw) := by
    dsimp only [Equivalent, plainAddRaw, Rational.toRaw]
    simp only [Int.natCast_mul]
    ring1
  exact equivalent_trans (add_plain left right)
    (equivalent_trans plainCommutes (add_plain right left).symm)

theorem add_assoc (first second third : Rational) :
    first + second + third = first + (second + third) := by
  apply eq_of_equivalent
  have leftExpanded :
      Equivalent (first + second + third).toRaw
        (plainAddRaw (plainAddRaw first.toRaw second.toRaw) third.toRaw) :=
    equivalent_trans (add_plain (first + second) third)
      (plainAddRaw_respects (add_plain first second)
        (equivalent_refl third.toRaw))
  have rightExpanded :
      Equivalent (first + (second + third)).toRaw
        (plainAddRaw first.toRaw
          (plainAddRaw second.toRaw third.toRaw)) :=
    equivalent_trans (add_plain first (second + third))
      (plainAddRaw_respects (equivalent_refl first.toRaw)
        (add_plain second third))
  have plainAssociates :
      Equivalent
        (plainAddRaw (plainAddRaw first.toRaw second.toRaw) third.toRaw)
        (plainAddRaw first.toRaw
          (plainAddRaw second.toRaw third.toRaw)) := by
    dsimp only [Equivalent, plainAddRaw, Rational.toRaw]
    simp only [Int.natCast_mul]
    ring1
  exact equivalent_trans leftExpanded
    (equivalent_trans plainAssociates rightExpanded.symm)

theorem zero_add (source : Rational) : 0 + source = source := by
  apply eq_of_equivalent
  have plainZero :
      Equivalent (plainAddRaw zero.toRaw source.toRaw) source.toRaw := by
    dsimp only [Equivalent, plainAddRaw, Rational.toRaw, zero]
    simp only [Nat.one_mul]
    ring1
  exact equivalent_trans (add_plain zero source) plainZero

theorem neg_add_cancel (source : Rational) : -source + source = 0 := by
  apply eq_of_equivalent
  have expanded :
      Equivalent (-source + source).toRaw
        (plainAddRaw (plainNegRaw source.toRaw) source.toRaw) :=
    equivalent_trans (add_plain (-source) source)
      (plainAddRaw_respects (neg_plain source)
        (equivalent_refl source.toRaw))
  have plainCancellation :
      Equivalent (plainAddRaw (plainNegRaw source.toRaw) source.toRaw)
        zero.toRaw := by
    dsimp only [Equivalent, plainAddRaw, plainNegRaw, Rational.toRaw, zero]
    simp only [Int.natCast_mul]
    simp only [Int.neg_mul, _root_.neg_add_cancel, Int.zero_mul]
  exact equivalent_trans expanded plainCancellation

theorem mul_comm (left right : Rational) : left * right = right * left := by
  apply eq_of_equivalent
  have plainCommutes :
      Equivalent (plainMulRaw left.toRaw right.toRaw)
        (plainMulRaw right.toRaw left.toRaw) := by
    dsimp only [Equivalent, plainMulRaw, Rational.toRaw]
    simp only [Int.natCast_mul]
    ring1
  exact equivalent_trans (mul_plain left right)
    (equivalent_trans plainCommutes (mul_plain right left).symm)

theorem mul_assoc (first second third : Rational) :
    first * second * third = first * (second * third) := by
  apply eq_of_equivalent
  have leftExpanded :
      Equivalent (first * second * third).toRaw
        (plainMulRaw (plainMulRaw first.toRaw second.toRaw) third.toRaw) :=
    equivalent_trans (mul_plain (first * second) third)
      (plainMulRaw_respects (mul_plain first second)
        (equivalent_refl third.toRaw))
  have rightExpanded :
      Equivalent (first * (second * third)).toRaw
        (plainMulRaw first.toRaw
          (plainMulRaw second.toRaw third.toRaw)) :=
    equivalent_trans (mul_plain first (second * third))
      (plainMulRaw_respects (equivalent_refl first.toRaw)
        (mul_plain second third))
  have plainAssociates :
      Equivalent
        (plainMulRaw (plainMulRaw first.toRaw second.toRaw) third.toRaw)
        (plainMulRaw first.toRaw
          (plainMulRaw second.toRaw third.toRaw)) := by
    dsimp only [Equivalent, plainMulRaw, Rational.toRaw]
    simp only [Int.natCast_mul]
    ring1
  exact equivalent_trans leftExpanded
    (equivalent_trans plainAssociates rightExpanded.symm)

theorem one_mul (source : Rational) : 1 * source = source := by
  apply eq_of_equivalent
  have plainOne :
      Equivalent (plainMulRaw one.toRaw source.toRaw) source.toRaw := by
    dsimp only [Equivalent, plainMulRaw, Rational.toRaw, one]
    simp only [Nat.one_mul]
    ring1
  exact equivalent_trans (mul_plain one source) plainOne

theorem left_distrib (first second third : Rational) :
    first * (second + third) = first * second + first * third := by
  apply eq_of_equivalent
  have leftExpanded :
      Equivalent (first * (second + third)).toRaw
        (plainMulRaw first.toRaw
          (plainAddRaw second.toRaw third.toRaw)) :=
    equivalent_trans (mul_plain first (second + third))
      (plainMulRaw_respects (equivalent_refl first.toRaw)
        (add_plain second third))
  have rightExpanded :
      Equivalent (first * second + first * third).toRaw
        (plainAddRaw
          (plainMulRaw first.toRaw second.toRaw)
          (plainMulRaw first.toRaw third.toRaw)) :=
    equivalent_trans (add_plain (first * second) (first * third))
      (plainAddRaw_respects (mul_plain first second)
        (mul_plain first third))
  have plainDistributes :
      Equivalent
        (plainMulRaw first.toRaw
          (plainAddRaw second.toRaw third.toRaw))
        (plainAddRaw
          (plainMulRaw first.toRaw second.toRaw)
          (plainMulRaw first.toRaw third.toRaw)) := by
    dsimp only [Equivalent, plainMulRaw, plainAddRaw, Rational.toRaw]
    simp only [Int.natCast_mul]
    ring1
  exact equivalent_trans leftExpanded
    (equivalent_trans plainDistributes rightExpanded.symm)

theorem mul_inv_cancel (source : Rational) (nonzero : source ≠ 0) :
    source * source⁻¹ = 1 := by
  apply eq_of_equivalent
  have productDisplay := mul_plain source source⁻¹
  by_cases zeroNumerator : source.num = 0
  · have sourceZero : source = zero := by
      apply eq_of_cross
      dsimp only [zero]
      simp only [zeroNumerator, Int.zero_mul]
    exact (nonzero sourceZero).elim
  · have plainCancellation :
        Equivalent (plainMulRaw source.toRaw (source⁻¹).toRaw) one.toRaw := by
      by_cases positiveNumerator : 0 < source.num
      · have numeratorMagnitude :
            (source.num.natAbs : Int) = source.num :=
          Int.natAbs_of_nonneg positiveNumerator.le
        simp only [Inv.inv, inv, zeroNumerator, positiveNumerator,
          ↓reduceDIte]
        dsimp only [Equivalent, plainMulRaw, Rational.toRaw, one]
        simp only [Int.natCast_mul]
        rw [numeratorMagnitude]
        simpa only [Int.natCast_one, _root_.mul_one, _root_.one_mul] using
          (_root_.mul_comm source.num (source.den : Int))
      · have negativeNumerator : source.num < 0 :=
          lt_of_le_of_ne (Int.le_of_not_gt positiveNumerator) zeroNumerator
        have numeratorMagnitude :
            (source.num.natAbs : Int) = -source.num :=
          Int.ofNat_natAbs_of_nonpos negativeNumerator.le
        simp only [Inv.inv, inv, zeroNumerator, positiveNumerator,
          ↓reduceDIte]
        dsimp only [Equivalent, plainMulRaw, Rational.toRaw, one]
        simp only [Int.natCast_mul]
        rw [numeratorMagnitude]
        simpa only [Int.natCast_one, Int.mul_neg, _root_.mul_one,
          _root_.one_mul] using
          congrArg (fun value : Int => -value)
            (_root_.mul_comm source.num (source.den : Int))
    exact equivalent_trans productDisplay plainCancellation

theorem inv_zero : (0 : Rational)⁻¹ = 0 := by
  change inv zero = zero
  simp only [inv, zero, ↓reduceDIte]

theorem zero_ne_one : (0 : Rational) ≠ 1 := by
  intro equal
  have numeratorEqual := congrArg Rational.num equal
  change (0 : Int) = 1 at numeratorEqual
  exact Int.zero_ne_one numeratorEqual

instance instCommRing : CommRing Rational :=
  { CommRing.ofMinimalAxioms
      add_assoc zero_add neg_add_cancel mul_assoc mul_comm one_mul left_distrib with
    sub := sub
    sub_eq_add_neg := fun _ _ => rfl }

theorem eq_zero_iff_num_zero (source : Rational) :
    source = 0 ↔ source.num = 0 := by
  constructor
  · intro sourceZero
    have numeratorEqual := congrArg Rational.num sourceZero
    exact numeratorEqual
  · intro numeratorZero
    apply eq_of_cross
    change source.num * (1 : Int) = (0 : Int) * (source.den : Int)
    simp only [numeratorZero, Int.zero_mul]

theorem numerator_zero_iff_of_equivalent {left right : RawFraction}
    (equivalent : Equivalent left right) :
    left.num = 0 ↔ right.num = 0 := by
  constructor
  · intro leftZero
    rw [Equivalent, leftZero, Int.zero_mul] at equivalent
    have productZero : right.num * (left.den : Int) = 0 := equivalent.symm
    have denominatorNonzero : (left.den : Int) ≠ 0 := by
      intro castZero
      have denominatorZero : left.den = 0 := Int.ofNat.inj castZero
      exact (Nat.ne_of_gt left.den_pos) denominatorZero
    exact (Int.mul_eq_zero.mp productZero).resolve_right denominatorNonzero
  · intro rightZero
    rw [Equivalent, rightZero, Int.zero_mul] at equivalent
    have denominatorNonzero : (right.den : Int) ≠ 0 := by
      intro castZero
      have denominatorZero : right.den = 0 := Int.ofNat.inj castZero
      exact (Nat.ne_of_gt right.den_pos) denominatorZero
    exact (Int.mul_eq_zero.mp equivalent).resolve_right denominatorNonzero

theorem mul_ne_zero {left right : Rational}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left * right ≠ 0 := by
  intro productZero
  have productNumeratorZero : (left * right).num = 0 :=
    (eq_zero_iff_num_zero (left * right)).mp productZero
  have rawNumeratorZero : (referenceMulRaw left right).num = 0 :=
    (numerator_zero_iff_of_equivalent (mul_equivalent left right)).mp
      productNumeratorZero
  change left.num * right.num = 0 at rawNumeratorZero
  rcases Int.mul_eq_zero.mp rawNumeratorZero with leftZero | rightZero
  · exact leftNonzero ((eq_zero_iff_num_zero left).mpr leftZero)
  · exact rightNonzero ((eq_zero_iff_num_zero right).mpr rightZero)

theorem inv_ne_zero {source : Rational} (sourceNonzero : source ≠ 0) :
    source⁻¹ ≠ 0 := by
  intro inverseZero
  have sourceNumeratorNonzero : source.num ≠ 0 := fun sourceNumeratorZero =>
    sourceNonzero ((eq_zero_iff_num_zero source).mpr sourceNumeratorZero)
  have inverseNumeratorZero : (source⁻¹).num = 0 :=
    (eq_zero_iff_num_zero source⁻¹).mp inverseZero
  by_cases positiveNumerator : 0 < source.num
  · simp only [Inv.inv, inv, sourceNumeratorNonzero, positiveNumerator,
      ↓reduceDIte] at inverseNumeratorZero
    have denominatorZero : source.den = 0 := Int.ofNat.inj inverseNumeratorZero
    exact (Nat.ne_of_gt source.den_pos) denominatorZero
  · simp only [Inv.inv, inv, sourceNumeratorNonzero, positiveNumerator,
      ↓reduceDIte, neg_eq_zero] at inverseNumeratorZero
    have denominatorZero : source.den = 0 := Int.ofNat.inj inverseNumeratorZero
    exact (Nat.ne_of_gt source.den_pos) denominatorZero

theorem mul_left_cancel_of_nonzero {factor left right : Rational}
    (factorNonzero : factor ≠ 0) (equalProducts : factor * left = factor * right) :
    left = right := by
  have inverseProduct : factor⁻¹ * factor = 1 := by
    rw [mul_comm, mul_inv_cancel factor factorNonzero]
  calc
    left = 1 * left := (one_mul left).symm
    _ = (factor⁻¹ * factor) * left := by rw [inverseProduct]
    _ = factor⁻¹ * (factor * left) := mul_assoc _ _ _
    _ = factor⁻¹ * (factor * right) := by rw [equalProducts]
    _ = (factor⁻¹ * factor) * right := (mul_assoc _ _ _).symm
    _ = 1 * right := by rw [inverseProduct]
    _ = right := one_mul right

theorem inv_neg (source : Rational) : (-source)⁻¹ = -(source⁻¹) := by
  by_cases sourceZero : source = 0
  · rw [sourceZero]
    change inv (neg zero) = neg (inv zero)
    rfl
  · have negativeNonzero : -source ≠ 0 := neg_ne_zero.mpr sourceZero
    apply mul_left_cancel_of_nonzero negativeNonzero
    calc
      (-source) * (-source)⁻¹ = 1 :=
        mul_inv_cancel (-source) negativeNonzero
      _ = source * source⁻¹ := (mul_inv_cancel source sourceZero).symm
      _ = (-source) * (-(source⁻¹)) := (neg_mul_neg source source⁻¹).symm

instance instExplicitField : RFAP.ExplicitField Rational where
  div_eq_mul_inv := fun _ _ => rfl
  mul_inv_cancel := mul_inv_cancel
  mul_ne_zero := mul_ne_zero
  inv_ne_zero := inv_ne_zero
  inv_neg := inv_neg

end RFAP.CanonicalFraction
