module
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

public import Mathlib.Algebra.Ring.MinimalAxioms
public import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.Arithmetic
-- Exposed field certificates retain the direct scalar arithmetic and sign laws.
import Purelib.Data.Int.Arithmetic
public import Purelib.Data.Int.Order
import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Ring.Multiplication
public import Purelib.Algebra.Ring.Basic
public import Purelib.Data.Nat.Order

-- Preserve the subtraction parent's operations with its direct zero certificate.
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
open scoped Purelib.Data.Nat

open Purelib.Data.Rat

open Purelib.Algebra

section
@[expose] public section

/-!
# Field laws for canonical fractions

All laws are proved from explicit cross-multiplication certificates and the
uniqueness of reduced positive-denominator records.  No theorem is
transported through the former quotient-valued rational field.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data.Int
open Purelib.Algebra

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

/-- Ordinary displayed addition preserves cross-product equivalence in both operands. -/
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

/-- Negating both numerators preserves cross-multiplication equivalence.

The denominators and their positivity witnesses remain the original ones;
the retained cross-product equality is transported through integer negation. -/
theorem plainNegRaw_respects {left right : RawFraction}
    (equivalent : Equivalent left right) :
    Equivalent (plainNegRaw left) (plainNegRaw right) := by
  dsimp only [Equivalent, plainNegRaw] at equivalent ⊢
  rw [Arithmetic.neg_mul, Arithmetic.neg_mul, equivalent]

/-- Ordinary displayed multiplication preserves cross-product equivalence in both operands. -/
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

/-- Canonical addition is cross-product equivalent to the ordinary displayed sum. -/
theorem add_plain (left right : Rational) :
    Equivalent (left + right).toRaw
      (plainAddRaw left.toRaw right.toRaw) := by
  change Equivalent (add left right).toRaw
    (plainAddRaw left.toRaw right.toRaw)
  simpa only [plainAddRaw, referenceAddRaw, Rational.toRaw] using
    add_equivalent left right

/-- Canonical negation is cross-product equivalent to negating the displayed numerator. -/
theorem neg_plain (source : Rational) :
    Equivalent (-source).toRaw (plainNegRaw source.toRaw) := by
  rfl

/-- Canonical multiplication is cross-product equivalent to the ordinary displayed product. -/
theorem mul_plain (left right : Rational) :
    Equivalent (left * right).toRaw
      (plainMulRaw left.toRaw right.toRaw) := by
  change Equivalent (mul left right).toRaw
    (plainMulRaw left.toRaw right.toRaw)
  simpa only [plainMulRaw, referenceMulRaw, Rational.toRaw] using
    mul_equivalent left right

/-- Canonical rational addition is commutative. -/
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

/-- Canonical rational addition is associative. -/
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

/-- Adding zero on the left preserves a canonical rational. -/
theorem zero_add (source : Rational) : 0 + source = source := by
  apply eq_of_equivalent
  have plainZero :
      Equivalent (plainAddRaw zero.toRaw source.toRaw) source.toRaw := by
    dsimp only [Equivalent, plainAddRaw, Rational.toRaw, zero]
    rw [Nat.one_mul, Int.natCast_one, Arithmetic.zero_mul, Arithmetic.mul_one,
      Arithmetic.zero_add]
  exact equivalent_trans (add_plain zero source) plainZero

/-- A canonical rational and its negation sum to zero.

Their common-denominator display has a zero numerator. Uniqueness of the
reduced positive-denominator record identifies the result with canonical zero. -/
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
    rw [Arithmetic.neg_mul, Arithmetic.neg_add_cancel, Arithmetic.zero_mul,
      Arithmetic.zero_mul]
  exact equivalent_trans expanded plainCancellation

/-- Canonical rational multiplication is commutative. -/
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

/-- Canonical rational multiplication is associative. -/
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

/-- Canonical one is a left identity for multiplication. -/
theorem one_mul (source : Rational) : 1 * source = source := by
  apply eq_of_equivalent
  have plainOne :
      Equivalent (plainMulRaw one.toRaw source.toRaw) source.toRaw := by
    dsimp only [Equivalent, plainMulRaw, Rational.toRaw, one]
    simp only [Nat.one_mul]
    ring1
  exact equivalent_trans (mul_plain one source) plainOne

/-- Canonical rational multiplication distributes over addition on the left. -/
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

/-- Multiplying a nonzero canonical rational by its reciprocal gives one.

The reciprocal retains the original denominator and numerator magnitude
with the numerator's sign. Their product display is equivalent to one. -/
theorem mul_inv_cancel (source : Rational) (nonzero : source ≠ 0) :
    source * source⁻¹ = 1 := by
  apply eq_of_equivalent
  have productDisplay := mul_plain source source⁻¹
  by_cases zeroNumerator : source.num = 0
  · have sourceZero : source = zero := by
      apply eq_of_cross
      dsimp only [zero]
      rw [zeroNumerator, Arithmetic.zero_mul, Arithmetic.zero_mul]
    exact (nonzero sourceZero).elim
  · have plainCancellation :
        Equivalent (plainMulRaw source.toRaw (source⁻¹).toRaw) one.toRaw := by
      by_cases positiveNumerator : 0 < source.num
      · have numeratorMagnitude :
            (source.num.natAbs : Int) = source.num :=
          Order.natAbs_of_pos positiveNumerator
        change Equivalent (plainMulRaw source.toRaw (inv source).toRaw) one.toRaw
        unfold inv
        rw [dif_neg zeroNumerator, dif_pos positiveNumerator]
        dsimp only [Equivalent, plainMulRaw, Rational.toRaw, one]
        simp only [Int.natCast_mul]
        rw [numeratorMagnitude]
        rw [Int.natCast_one, Arithmetic.mul_one, Int.one_mul, Arithmetic.mul_comm]
      · have numeratorMagnitude :
            (source.num.natAbs : Int) = -source.num :=
          Order.natAbs_of_not_pos positiveNumerator
        change Equivalent (plainMulRaw source.toRaw (inv source).toRaw) one.toRaw
        unfold inv
        rw [dif_neg zeroNumerator, dif_neg positiveNumerator]
        dsimp only [Equivalent, plainMulRaw, Rational.toRaw, one]
        simp only [Int.natCast_mul]
        rw [numeratorMagnitude]
        rw [Int.natCast_one, Arithmetic.mul_one, Int.one_mul,
          Arithmetic.mul_comm source.num (-(source.den : Int)), Arithmetic.neg_mul,
          Arithmetic.mul_comm (source.den : Int) (-source.num), Arithmetic.neg_mul,
          Arithmetic.mul_comm]
    exact equivalent_trans productDisplay plainCancellation

/-- The total reciprocal sends canonical zero to zero. -/
theorem inv_zero : (0 : Rational)⁻¹ = 0 := by
  change inv zero = zero
  unfold inv
  rw [dif_pos (show zero.num = 0 from rfl)]

/-- The canonical rational zero and one records are distinct. -/
theorem zero_ne_one : (0 : Rational) ≠ 1 := by
  intro equal
  have numeratorEqual := congrArg Rational.num equal
  change (0 : Int) = 1 at numeratorEqual
  exact Int.zero_ne_one numeratorEqual

/-- Multiplying canonical zero on the left gives canonical zero.

The plain product has a zero numerator and the original positive
denominator, so its cross-product agrees with canonical zero. -/
theorem zero_mul (source : Rational) : (0 : Rational) * source = 0 := by
  apply eq_of_equivalent
  have plainZero :
      Equivalent (plainMulRaw zero.toRaw source.toRaw) zero.toRaw := by
    dsimp only [Equivalent, plainMulRaw, Rational.toRaw, zero]
    rw [Arithmetic.zero_mul, Arithmetic.zero_mul, Arithmetic.zero_mul]
  exact equivalent_trans (mul_plain zero source) plainZero

/-- Canonical rational arithmetic forms a commutative ring.

Addition, multiplication, subtraction and negation retain their existing
operations. Powers, scalar multiplication and casts retain the same class
default recursions as the minimal-axiom construction. The displayed field
laws supply all ring certificates directly. -/
instance instCommRing : CommRing Rational :=
  Ring.commRingOfAxioms add_assoc zero_add neg_add_cancel mul_assoc mul_comm
    one_mul left_distrib sub (fun _ _ => rfl)

/-- A canonical rational is zero exactly when its stored numerator is zero.

Record equality supplies the forward implication. The reverse implication
uses the positive-denominator display's cross-product with canonical zero. -/
theorem eq_zero_iff_num_zero (source : Rational) :
    source = 0 ↔ source.num = 0 := by
  constructor
  · intro sourceZero
    have numeratorEqual := congrArg Rational.num sourceZero
    exact numeratorEqual
  · intro numeratorZero
    apply eq_of_cross
    change source.num * (1 : Int) = (0 : Int) * (source.den : Int)
    rw [numeratorZero, Arithmetic.zero_mul, Arithmetic.zero_mul]

/-- Equivalent positive-denominator displays have the same numerator zero test.

Each direction cancels the opposite display's nonzero denominator from
the retained cross-product equality. -/
theorem numerator_zero_iff_of_equivalent {left right : RawFraction}
    (equivalent : Equivalent left right) :
    left.num = 0 ↔ right.num = 0 := by
  constructor
  · intro leftZero
    rw [Equivalent, leftZero, Arithmetic.zero_mul] at equivalent
    have productZero : right.num * (left.den : Int) = 0 := equivalent.symm
    have denominatorNonzero : (left.den : Int) ≠ 0 := by
      intro castZero
      have denominatorZero : left.den = 0 := Int.ofNat.inj castZero
      exact (Nat.ne_of_gt left.den_pos) denominatorZero
    exact (Arithmetic.eq_zero_of_mul_eq_zero productZero).resolve_right denominatorNonzero
  · intro rightZero
    rw [Equivalent, rightZero, Arithmetic.zero_mul] at equivalent
    have denominatorNonzero : (right.den : Int) ≠ 0 := by
      intro castZero
      have denominatorZero : right.den = 0 := Int.ofNat.inj castZero
      exact (Nat.ne_of_gt right.den_pos) denominatorZero
    exact (Arithmetic.eq_zero_of_mul_eq_zero equivalent).resolve_right denominatorNonzero

/-- The product of two nonzero canonical rationals is nonzero.

Its plain display retains the two numerator factors. A zero product would
force one numerator, and hence one of the original rationals, to be zero. -/
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
  rcases Arithmetic.eq_zero_of_mul_eq_zero rawNumeratorZero with leftZero | rightZero
  · exact leftNonzero ((eq_zero_iff_num_zero left).mpr leftZero)
  · exact rightNonzero ((eq_zero_iff_num_zero right).mpr rightZero)

/-- The reciprocal of a nonzero canonical rational is nonzero.

Either nonzero reciprocal branch has the original positive denominator as
its numerator magnitude, excluding a zero stored numerator. -/
theorem inv_ne_zero {source : Rational} (sourceNonzero : source ≠ 0) :
    source⁻¹ ≠ 0 := by
  intro inverseZero
  have sourceNumeratorNonzero : source.num ≠ 0 := fun sourceNumeratorZero =>
    sourceNonzero ((eq_zero_iff_num_zero source).mpr sourceNumeratorZero)
  have inverseNumeratorZero : (source⁻¹).num = 0 :=
    (eq_zero_iff_num_zero source⁻¹).mp inverseZero
  change (inv source).num = 0 at inverseNumeratorZero
  unfold inv at inverseNumeratorZero
  rw [dif_neg sourceNumeratorNonzero] at inverseNumeratorZero
  by_cases positiveNumerator : 0 < source.num
  · rw [dif_pos positiveNumerator] at inverseNumeratorZero
    have denominatorZero : source.den = 0 := Int.ofNat.inj inverseNumeratorZero
    exact (Nat.ne_of_gt source.den_pos) denominatorZero
  · rw [dif_neg positiveNumerator] at inverseNumeratorZero
    change -(source.den : Int) = 0 at inverseNumeratorZero
    have denominatorCastZero : (source.den : Int) = 0 := by
      have negated := congrArg Int.neg inverseNumeratorZero
      change -(-(source.den : Int)) = (0 : Int) at negated
      rw [Int.neg_neg] at negated
      exact negated
    exact (Nat.ne_of_gt source.den_pos) (Int.ofNat.inj denominatorCastZero)

/-- Cancel a fixed nonzero rational factor from the left of an equality. -/
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

/-- Negating a canonical rational negates its reciprocal.

Zero follows the total reciprocal's zero branch. For a nonzero source,
multiplication cancellation identifies the two reciprocals of its negation. -/
theorem inv_neg (source : Rational) : (-source)⁻¹ = -(source⁻¹) := by
  by_cases sourceZero : source = 0
  · rw [sourceZero]
    change inv (neg zero) = neg (inv zero)
    rfl
  · have negativeNonzero : -source ≠ 0 := by
      intro negativeZero
      have numeratorZero := (eq_zero_iff_num_zero (-source)).mp negativeZero
      change -source.num = 0 at numeratorZero
      have originalNumeratorZero := congrArg (fun value : Int => -value) numeratorZero
      rw [Int.neg_neg] at originalNumeratorZero
      exact sourceZero ((eq_zero_iff_num_zero source).mpr originalNumeratorZero)
    apply mul_left_cancel_of_nonzero negativeNonzero
    calc
      (-source) * (-source)⁻¹ = 1 :=
        mul_inv_cancel (-source) negativeNonzero
      _ = source * source⁻¹ := (mul_inv_cancel source sourceZero).symm
      _ = (-source) * (-(source⁻¹)) :=
        (Ring.Multiplication.neg_mul_neg source source⁻¹).symm

/-- Equip the canonical rational ring with its original total inverse and explicit cancellation witnesses.

The supplied witnesses prove inverse cancellation, nonzero products, nonzero reciprocals and compatibility with
negation; the underlying operations are unchanged. -/
instance instExplicitField : Field.ExplicitField Rational where
  div_eq_mul_inv := fun _ _ => rfl
  mul_inv_cancel := mul_inv_cancel
  mul_ne_zero := mul_ne_zero
  inv_ne_zero := inv_ne_zero
  inv_neg := inv_neg

end Purelib.Data.Rat.Fraction

end

end

section
@[expose] public section

/-!
# Compatibility surface for canonical fractions

This module provides the compatibility operations now owned by
`Purelib.Data.Rat.Fraction.Compatibility` over the quotient-free rational carrier.  All operations use the canonical
structural rational carrier.

The signed-denominator `SignedFraction` record remains available as input syntax.
Its positivity proof makes conversion to the canonical natural-denominator
display total and executable.  Semantic rationals themselves are reduced
structural records; `representative` therefore exposes data already present
in the value rather than selecting a member of a quotient.
-/

namespace Purelib.Data.Rat.Fraction.Field

/-- Canonical rational addition is commutative. -/
theorem add_comm (left right : Fraction.Rational) : left + right = right + left
  :=
  _root_.add_comm left right

/-- Canonical rational addition is associative. -/
theorem add_assoc (first second third : Fraction.Rational) :
    first + second + third = first + (second + third) :=
  _root_.add_assoc first second third

/-- Canonical zero is a left identity for addition. -/
theorem zero_add (source : Fraction.Rational) : 0 + source = source :=
  _root_.zero_add source

/-- Adding a rational to its additive inverse gives canonical zero. -/
theorem neg_add_cancel (source : Fraction.Rational) : -source + source = 0 :=
  _root_.neg_add_cancel source

/-- Canonical rational multiplication is commutative. -/
theorem mul_comm (left right : Fraction.Rational) : left * right = right * left
  :=
  _root_.mul_comm left right

/-- Canonical rational multiplication is associative. -/
theorem mul_assoc (first second third : Fraction.Rational) :
    first * second * third = first * (second * third) :=
  _root_.mul_assoc first second third

/-- Canonical one is a left identity for multiplication. -/
theorem one_mul (source : Fraction.Rational) : 1 * source = source :=
  _root_.one_mul source

/-- Canonical rational multiplication distributes over addition on the left. -/
theorem left_distrib (first second third : Fraction.Rational) :
    first * (second + third) = first * second + first * third :=
  Fraction.left_distrib first second third

/-- A nonzero canonical rational multiplied by its total reciprocal gives one. -/
theorem mul_inv_cancel (source : Fraction.Rational) (nonzero : source ≠ 0) :
    source * source⁻¹ = 1 :=
  Fraction.mul_inv_cancel source nonzero

/-- The total canonical reciprocal sends zero to zero. -/
theorem inv_zero : (0 : Fraction.Rational)⁻¹ = 0 :=
  Fraction.inv_zero

/-- The canonical rational zero and one records are distinct. -/
theorem zero_ne_one : (0 : Fraction.Rational) ≠ 1 :=
  Fraction.zero_ne_one

/-- Reassociate four factors and exchange only the middle two. -/
theorem mul_pair_swap (first second third fourth : Fraction.Rational) :
    (first * second) * (third * fourth) =
      (first * third) * (second * fourth) := by
  ring1

/-- Multiplying a canonical rational by zero on the right gives zero. -/
theorem mul_zero_direct (source : Fraction.Rational) : source * 0 = 0 :=
  mul_zero source

/-- Multiplying a canonical rational by zero on the left gives zero. -/
theorem zero_mul_direct (source : Fraction.Rational) : 0 * source = 0 :=
  zero_mul source

/-- Canonical one is a right identity for multiplication. -/
theorem mul_one_direct (source : Fraction.Rational) : source * 1 = source :=
  _root_.mul_one source

/-- Division by canonical zero returns zero under the total reciprocal convention. -/
theorem div_zero_direct (source : Fraction.Rational) : source / 0 = 0 := by
  change source * (0 : Fraction.Rational)⁻¹ = 0
  rw [inv_zero, mul_zero_direct]

/-- Canonical zero divided by any rational is zero. -/
theorem zero_div_direct (source : Fraction.Rational) : 0 / source = 0 := by
  change 0 * source⁻¹ = 0
  exact zero_mul_direct _

/-- The reciprocal of a nonzero rational multiplied by that rational gives one. -/
theorem inv_mul_cancel (source : Fraction.Rational) (nonzero : source ≠ 0) :
    source⁻¹ * source = 1 := by
  rw [_root_.mul_comm]
  exact mul_inv_cancel source nonzero

/-- The product of two retained nonzero canonical rationals is nonzero. -/
theorem mul_ne_zero_direct {left right : Fraction.Rational}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left * right ≠ 0 :=
  Fraction.mul_ne_zero leftNonzero rightNonzero

/-- The reciprocal of a retained nonzero canonical rational is nonzero. -/
theorem inv_ne_zero_direct {source : Fraction.Rational} (nonzero : source ≠ 0) :
    source⁻¹ ≠ 0 :=
  Fraction.inv_ne_zero nonzero

/-- Negating a rational negates its total canonical reciprocal. -/
theorem inv_neg_direct (source : Fraction.Rational) : Fraction.inv (-source) =
  -Fraction.inv source :=
  Fraction.inv_neg source

/-- Canonical division is definitionally multiplication by total reciprocal. -/
theorem div_eq_mul_inv_direct (left right : Fraction.Rational) :
    left / right = left * right⁻¹ := rfl

/-- Multiplying a quotient by its retained nonzero denominator recovers the numerator. -/
theorem div_mul_cancel_of_ne (numerator denominator : Fraction.Rational)
    (denominatorNonzero : denominator ≠ 0) :
    (numerator / denominator) * denominator = numerator := by
  change (numerator * denominator⁻¹) * denominator = numerator
  calc
    (numerator * denominator⁻¹) * denominator =
        numerator * (denominator⁻¹ * denominator) := _root_.mul_assoc _ _ _
    _ = numerator * 1 := by rw [inv_mul_cancel denominator denominatorNonzero]
    _ = numerator := mul_one_direct _

/-- Two divisions with nonzero denominators agree when their displayed cross-products agree.  This is the direct
certificate form of equality of fractions; it does not compare quotient representatives. -/
theorem div_eq_div_of_cross_mul {firstNumerator firstDenominator
    secondNumerator secondDenominator : Fraction.Rational}
    (firstDenominatorNonzero : firstDenominator ≠ 0)
    (secondDenominatorNonzero : secondDenominator ≠ 0)
    (crossProduct :
      firstNumerator * secondDenominator =
        secondNumerator * firstDenominator) :
    firstNumerator / firstDenominator =
      secondNumerator / secondDenominator := by
  have productNonzero :
      firstDenominator * secondDenominator ≠ 0 :=
    mul_ne_zero_direct firstDenominatorNonzero secondDenominatorNonzero
  apply Fraction.mul_left_cancel_of_nonzero productNonzero
  calc
    (firstDenominator * secondDenominator) *
          (firstNumerator / firstDenominator) =
        (firstNumerator / firstDenominator) *
          (firstDenominator * secondDenominator) := by ring1
    _ = ((firstNumerator / firstDenominator) * firstDenominator) *
          secondDenominator := by rw [_root_.mul_assoc]
    _ = firstNumerator * secondDenominator := by
      rw [div_mul_cancel_of_ne _ _ firstDenominatorNonzero]
    _ = secondNumerator * firstDenominator := crossProduct
    _ = ((secondNumerator / secondDenominator) * secondDenominator) *
          firstDenominator := by
      rw [div_mul_cancel_of_ne _ _ secondDenominatorNonzero]
    _ = (firstDenominator * secondDenominator) *
          (secondNumerator / secondDenominator) := by ring1

/-- Cancel a fixed nonzero rational factor from the right of an equality. -/
theorem mul_right_cancel_of_ne {a b c : Fraction.Rational}
    (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have scaled := congrArg (fun value => value * c⁻¹) h
  simpa only [_root_.mul_assoc, mul_inv_cancel c hc,
    mul_one_direct] using scaled

/-- The total reciprocal of a product is the product of the total reciprocals. -/
theorem inv_mul_direct (left right : Fraction.Rational) :
    (left * right)⁻¹ = left⁻¹ * right⁻¹ := by
  by_cases leftZero : left = 0
  · subst left
    rw [zero_mul_direct, inv_zero, zero_mul_direct]
  · by_cases rightZero : right = 0
    · subst right
      rw [mul_zero_direct, inv_zero, mul_zero_direct]
    · have productNonzero := mul_ne_zero_direct leftZero rightZero
      apply mul_right_cancel_of_ne productNonzero
      calc
        (left * right)⁻¹ * (left * right) = 1 :=
          inv_mul_cancel _ productNonzero
        _ = (left⁻¹ * left) * (right⁻¹ * right) := by
          rw [inv_mul_cancel left leftZero, inv_mul_cancel right rightZero,
            mul_one_direct]
        _ = (left⁻¹ * right⁻¹) * (left * right) :=
          mul_pair_swap _ _ _ _

/-- Total rational reciprocal commutes with every natural power. -/
theorem inv_pow_direct (source : Fraction.Rational) : ∀ exponent : Nat,
    (source ^ exponent)⁻¹ = source⁻¹ ^ exponent
  | 0 => by
      change (1 : Fraction.Rational)⁻¹ = 1
      decide
  | exponent + 1 => by
      rw [pow_succ, inv_mul_direct, inv_pow_direct source exponent,
        pow_succ]

/-- The product of two canonical rational quotients is the quotient of the numerator and denominator products. -/
theorem div_mul_div_direct (first second third fourth : Fraction.Rational) :
    (first / second) * (third / fourth) =
      (first * third) / (second * fourth) := by
  change (first * second⁻¹) * (third * fourth⁻¹) =
    (first * third) * (second * fourth)⁻¹
  rw [inv_mul_direct]
  exact mul_pair_swap _ _ _ _

/-- Subtract two rational quotients by their cross-products over the product of the nonzero denominators. -/
theorem div_sub_div_direct (first second third fourth : Fraction.Rational)
    (secondNonzero : second ≠ 0) (fourthNonzero : fourth ≠ 0) :
    first / second - third / fourth =
      (first * fourth - third * second) / (second * fourth) := by
  change first * second⁻¹ - third * fourth⁻¹ =
    (first * fourth - third * second) * (second * fourth)⁻¹
  rw [inv_mul_direct]
  rw [Fraction.Arithmetic.sub_eq_add_neg_direct, Fraction.Arithmetic.sub_eq_add_neg_direct, _root_.add_mul,
    _root_.neg_mul]
  have firstReorder :
      (first * fourth) * (second⁻¹ * fourth⁻¹) =
        first * second⁻¹ := by
    calc
      (first * fourth) * (second⁻¹ * fourth⁻¹) =
          (first * second⁻¹) * (fourth * fourth⁻¹) :=
        mul_pair_swap _ _ _ _
      _ = (first * second⁻¹) * 1 := by
        rw [mul_inv_cancel fourth fourthNonzero]
      _ = first * second⁻¹ := mul_one_direct _
  have secondReorder :
      (third * second) * (second⁻¹ * fourth⁻¹) =
        third * fourth⁻¹ := by
    calc
      (third * second) * (second⁻¹ * fourth⁻¹) =
          (third * fourth⁻¹) * (second * second⁻¹) := by
        rw [_root_.mul_comm second⁻¹ fourth⁻¹]
        exact mul_pair_swap _ _ _ _
      _ = (third * fourth⁻¹) * 1 := by
        rw [mul_inv_cancel second secondNonzero]
      _ = third * fourth⁻¹ := mul_one_direct _
  rw [firstReorder, secondReorder]

/-- Cancel a common nonzero rational factor from the numerator and denominator of a quotient. -/
theorem mul_div_mul_left_direct (factor numerator denominator :
  Fraction.Rational)
    (factorNonzero : factor ≠ 0) :
    (factor * numerator) / (factor * denominator) =
      numerator / denominator := by
  change (factor * numerator) * (factor * denominator)⁻¹ =
    numerator * denominator⁻¹
  rw [inv_mul_direct]
  calc
    (factor * numerator) * (factor⁻¹ * denominator⁻¹) =
        (factor * factor⁻¹) * (numerator * denominator⁻¹) :=
      mul_pair_swap _ _ _ _
    _ = 1 * (numerator * denominator⁻¹) := by
      rw [mul_inv_cancel factor factorNonzero]
    _ = numerator * denominator⁻¹ := _root_.one_mul _
end Purelib.Data.Rat.Fraction.Field

end

end

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Data.Rat.Fraction.Field

/-- Multiplying an inverse by one half divides one by twice its denominator.

The identity uses the total reciprocal, so it also holds when the displayed
denominator is zero. No nonzero premise is required. -/
public theorem half_mul_inverse (value : Fraction.Rational) :
    (1 / 2 : Fraction.Rational) * value⁻¹ = 1 / (2 * value) := by
  have oneDiv : (1 / value : Fraction.Rational) = value⁻¹ := by
    change 1 * value⁻¹ = value⁻¹
    exact _root_.one_mul _
  calc
    (1 / 2 : Fraction.Rational) * value⁻¹ =
        (1 / 2) * (1 / value) := by rw [oneDiv]
    _ = (1 * 1) / (2 * value) :=
      div_mul_div_direct 1 2 1 value
    _ = 1 / (2 * value) := by
      apply congrArg (fun numerator : Fraction.Rational => numerator / (2 * value))
      exact mul_one_direct 1

end Purelib.Data.Rat.Fraction.Field

end

section
@[expose] public section

/-!
# Finite coherence certificates for progressive CCL processes

`Process` deliberately permits branching refinement strategies: it promises
that every requested branch becomes accurate, but does not by itself say that
two independently refined branches describe one operational value.  This
module adds exactly that missing, finite certificate.

A coherent process assigns a nonnegative rational squared allowance to every
finite state.  The current enclosure radius is no larger than that allowance,
every pair of explicitly possible Gaussian-rational readings is close at the
sum of their allowances, and one ordinary refinement makes the allowance
smaller than any requested positive rational target.  There is no completed
value, infinite carrier, limit, or choice of a value common to all states.
-/

namespace Purelib.Data.Rat.Fraction.Field

/-- Move a rational factor into the numerator of a quotient. -/
public theorem quotient_mul_reorder
    (numerator denominator factor : Fraction.Rational) :
    numerator / denominator * factor =
      (numerator * factor) / denominator := by
  change (numerator * denominator⁻¹) * factor =
    (numerator * factor) * denominator⁻¹
  calc
    (numerator * denominator⁻¹) * factor =
        numerator * (denominator⁻¹ * factor) :=
      _root_.mul_assoc _ _ _
    _ = numerator * (factor * denominator⁻¹) := by
      rw [_root_.mul_comm denominator⁻¹ factor]
    _ = (numerator * factor) * denominator⁻¹ :=
      (_root_.mul_assoc _ _ _).symm

end Purelib.Data.Rat.Fraction.Field

end

section
@[expose] public section

/-!
# Progressive finite enclosures for constructive CCL arithmetic

An arithmetic input is not a completed complex value.  It is a finite request
procedure: for each positive rational squared-error target it returns one
rational ball meeting that target.  A uniform rational bound on the squared
norm of the returned centres is carried explicitly.  This is the extra finite
side information needed by multiplication.

Division deliberately asks for one further side certificate: a fixed positive
lower bound for every realization of every requested denominator ball.  The
definitions below construct arbitrarily accurate output balls for all four
elementary operations.  Their error budgets are closed rational expressions,
so there is no unbounded search and no completed limit in the interface.
-/

namespace Purelib.CCL.Progressive.Enclosures
namespace Name

end Name

end Purelib.CCL.Progressive.Enclosures

end

section
@[expose] public section

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace Purelib.Data.Rat.Fraction.Field

/-- The two halves of a canonical rational sum to that rational. -/
public theorem two_halves (value : Fraction.Rational) : value / 2 + value / 2 =
  value := by
  calc
    value / 2 + value / 2 = (value / 2) * 2 := by ring1
    _ = value := div_mul_cancel_of_ne value 2
      (by decide)

end Purelib.Data.Rat.Fraction.Field

end

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Data.Rat.Fraction.Field

/-- Quotients with nonzero denominators are equal when their cross-products agree. -/
theorem div_eq_div_of_cross
    (leftNumerator leftDenominator rightNumerator rightDenominator : Fraction.Rational)
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (cross : leftNumerator * rightDenominator =
      rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator = rightNumerator / rightDenominator := by
  apply mul_right_cancel_of_ne
    (mul_ne_zero_direct leftNonzero rightNonzero)
  calc
    leftNumerator / leftDenominator *
          (leftDenominator * rightDenominator) =
        (leftNumerator / leftDenominator * leftDenominator) *
          rightDenominator := by ring1
    _ = leftNumerator * rightDenominator :=
      congrArg (fun value : Fraction.Rational => value * rightDenominator)
        (div_mul_cancel_of_ne
          leftNumerator leftDenominator leftNonzero)
    _ = rightNumerator * leftDenominator := cross
    _ = (rightNumerator / rightDenominator * rightDenominator) *
        leftDenominator :=
      congrArg (fun value : Fraction.Rational => value * leftDenominator)
        (div_mul_cancel_of_ne
          rightNumerator rightDenominator rightNonzero).symm
    _ = rightNumerator / rightDenominator *
        (leftDenominator * rightDenominator) := by ring1
end Purelib.Data.Rat.Fraction.Field

end

section
@[expose] public section

/-!
# Divine Proportions, Example 14.10

The rational exclusion is the finite Eisenstein-at-seven argument applied to
the computable gcd-reduced numerator and denominator.  The three decimal
displays are retained as exact rational sign-change brackets; no completed
decimal field, real root, or limit object is introduced.
-/

namespace Purelib.Data.Rat.Fraction.Field

/-- Canonical zero and one witness that the rational carrier is nontrivial. -/
private theorem rationalNontrivial : Nontrivial Fraction.Rational := by
  exact ⟨⟨0, 1, Fraction.zero_ne_one⟩⟩

end Purelib.Data.Rat.Fraction.Field

end

section
@[expose] public section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

namespace Purelib.Data.Rat.Fraction.Field

/-- Every natural power of a nonzero canonical rational is nonzero. -/
public theorem pow_ne_zero_direct (point : Fraction.Rational) (pointNonzero :
  point ≠ 0) :
    (exponent : Nat) → point ^ exponent ≠ 0
  | 0 => by
      change (1 : Fraction.Rational) ≠ 0
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact _root_.Purelib.Algebra.Field.ExplicitField.mul_ne_zero
        (pow_ne_zero_direct point pointNonzero exponent) pointNonzero

end Purelib.Data.Rat.Fraction.Field

end

namespace Purelib.Data.Rat.Fraction.Field

/-- Simultaneous negation preserves a rational affine interpolation equation.

Negating the supplied scalar equation recovers the original endpoints and
value. The interpolation parameter and its multiplication remain unchanged. -/
public theorem unneg_affine {first last parameter value : Rational}
    (equal : -first + parameter * (-last - -first) = -value) :
    first + parameter * (last - first) = value :=
  (show first + parameter * (last - first) = -(-first + parameter * (-last - -first)) by ring1).trans
    ((congrArg Neg.neg equal).trans (neg_neg value))

end Purelib.Data.Rat.Fraction.Field

namespace Purelib.Data.Rat.Fraction.Field

/-- Natural powers distribute over the product of two canonical rationals.

Induction preserves the original power operation; the successor step only
reassociates its four retained factors by the direct rational product law. -/
public theorem mul_pow_direct (left right : Rational) : ∀ exponent : Nat,
    (left * right) ^ exponent = left ^ exponent * right ^ exponent := by
  intro exponent
  induction exponent with
  | zero =>
      change (1 : Rational) = 1 * 1
      exact (one_mul 1).symm
  | succ exponent previous =>
      rewrite [pow_succ, previous, pow_succ, pow_succ]
      exact mul_pair_swap (left ^ exponent) (right ^ exponent) left right

end Purelib.Data.Rat.Fraction.Field

section

namespace Purelib.Data.Rat.Fraction.Field
/-- Distribute a weighted scale over a natural power of the sample square.

The scalar identity retains the leading coefficient, lower-term weight and
scale separately, with the same natural exponent on both sides. -/
public theorem weighted_scale_identity
    (leadingNorm sampleSq weight scale : Purelib.Data.Rat.Fraction.Rational) (exponent : Nat) :
    (leadingNorm * (sampleSq * scale) - weight) * sampleSq ^ exponent =
      (leadingNorm * (sampleSq ^ exponent * sampleSq)) * scale -
        weight * sampleSq ^ exponent := by
  ring1
end Purelib.Data.Rat.Fraction.Field
end
