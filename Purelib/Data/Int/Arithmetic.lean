module

public import Init.Data.Int.Lemmas
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Parity
import Purelib.Data.Nat.Subtraction

namespace Purelib.Data.Int.Arithmetic

/-- Adding zero on the left preserves an integer.

The identity holds for both natural and negative displayed integers. -/
public theorem zero_add (value : Int) : 0 + value = value := by
  cases value with
  | ofNat value => exact congrArg Int.ofNat (Nat.zero_add value)
  | negSucc value => rfl

/-- Multiplication by zero on the left gives zero.

The other integer factor has no sign or magnitude restriction. -/
public theorem zero_mul (value : Int) : 0 * value = 0 := by
  cases value with
  | ofNat value => exact congrArg Int.ofNat (Nat.zero_mul value)
  | negSucc value =>
      change Int.negOfNat (0 * (value + 1)) = 0
      rw [Nat.zero_mul]
      rfl

/-- Subtracting zero preserves an integer.

The identity uses ordinary integer subtraction for either sign. -/
public theorem sub_zero (value : Int) : value - 0 = value := by
  cases value <;> rfl

/-- Subtracting an integer from zero gives its negation. -/
public theorem zero_sub (value : Int) : 0 - value = -value :=
  zero_add (-value)

/-- Swapping the two displayed integer summands preserves their sum. -/
public theorem add_comm : ∀ left right : Int, left + right = right + left
  | .ofNat left, .ofNat right => congrArg Int.ofNat (Nat.add_comm left right)
  | .ofNat _, .negSucc _ => rfl
  | .negSucc _, .ofNat _ => rfl
  | .negSucc left, .negSucc right =>
      congrArg (fun value => Int.negSucc (Nat.succ value)) (Nat.add_comm left right)

/-- Swapping the two displayed integer factors preserves their product. -/
public theorem mul_comm : ∀ left right : Int, left * right = right * left
  | .ofNat left, .ofNat right => congrArg Int.ofNat (Nat.mul_comm left right)
  | .ofNat left, .negSucc right =>
      congrArg Int.negOfNat (Nat.mul_comm left (right + 1))
  | .negSucc left, .ofNat right =>
      congrArg Int.negOfNat (Nat.mul_comm (left + 1) right)
  | .negSucc left, .negSucc right =>
      congrArg Int.ofNat (Nat.mul_comm (left + 1) (right + 1))

/-- The absolute value of an integer product is the product of the absolute values.

The four displayed sign combinations reduce to natural multiplication.
Negative displayed products also include the possible zero magnitude. -/
public theorem natAbs_mul (left right : Int) :
    (left * right).natAbs = left.natAbs * right.natAbs := by
  cases left with
  | ofNat left =>
      cases right with
      | ofNat right => rfl
      | negSucc right => exact Int.natAbs_negOfNat (left * (right + 1))
  | negSucc left =>
      cases right with
      | ofNat right => exact Int.natAbs_negOfNat ((left + 1) * right)
      | negSucc right => rfl

/-- The magnitude of a nonzero integer is positive.

Both nonzero sign constructors have a successor natural magnitude. The
zero constructor is excluded by the retained nonzero proof. -/
public theorem natAbs_pos_of_ne_zero {value : Int} (nonzero : value ≠ 0) :
    0 < value.natAbs := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => exact (nonzero rfl).elim
      | succ value => exact Nat.zero_lt_succ value
  | negSucc value => exact Nat.zero_lt_succ value

/-- Adding an integer to its displayed negation gives zero. -/
public theorem neg_add_cancel (value : Int) : -value + value = 0 := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => rfl
      | succ value =>
          change Int.subNatNat (value + 1) (value + 1) = 0
          unfold Int.subNatNat
          rw [Nat.sub_self]
          rfl
  | negSucc value =>
      change Int.subNatNat (value + 1) (value + 1) = 0
      unfold Int.subNatNat
      rw [Nat.sub_self]
      rfl

/-- Equal integers have zero difference.

The retained equality identifies the two original operands. Their difference
then reduces to the displayed addition and negation cancellation identity. -/
public theorem sub_eq_zero_of_eq {left right : Int} (equal : left = right) :
    left - right = 0 := by
  cases equal
  change left + -left = 0
  exact (add_comm left (-left)).trans (neg_add_cancel left)

open Purelib.Data.Nat

/-- Multiplying a displayed negative natural by a natural preserves its sign. -/
private theorem negOfNat_mul_ofNat (left right : Nat) :
    Int.negOfNat left * Int.ofNat right = Int.negOfNat (left * right) := by
  rw [mul_comm, Int.ofNat_eq_natCast right, Int.ofNat_mul_negOfNat]
  exact congrArg Int.negOfNat (Nat.mul_comm right left)

/-- Multiplying a displayed negative natural by a negative successor gives a natural. -/
private theorem negOfNat_mul_negSucc (left right : Nat) :
    Int.negOfNat left * Int.negSucc right = Int.ofNat (left * (right + 1)) := by
  rw [mul_comm, Int.negSucc_mul_negOfNat]
  exact congrArg Int.ofNat (Nat.mul_comm (right + 1) left)

/-- Regrouping three displayed integer factors preserves their product.

Each sign combination reduces to the corresponding natural multiplication
identity, including products whose negative magnitude is zero. -/
public theorem mul_assoc (first second third : Int) :
    first * second * third = first * (second * third) := by
  cases first with
  | ofNat first =>
      cases second with
      | ofNat second =>
          cases third with
          | ofNat third =>
              exact congrArg Int.ofNat (Multiplication.mul_assoc first second third)
          | negSucc third =>
              change Int.negOfNat ((first * second) * (third + 1)) =
                Int.ofNat first * Int.negOfNat (second * (third + 1))
              rw [Int.ofNat_eq_natCast first, Int.ofNat_mul_negOfNat]
              exact congrArg Int.negOfNat (Multiplication.mul_assoc first second (third + 1))
      | negSucc second =>
          cases third with
          | ofNat third =>
              change Int.negOfNat (first * (second + 1)) * Int.ofNat third =
                Int.ofNat first * Int.negOfNat ((second + 1) * third)
              rw [negOfNat_mul_ofNat, Int.ofNat_eq_natCast first, Int.ofNat_mul_negOfNat]
              exact congrArg Int.negOfNat (Multiplication.mul_assoc first (second + 1) third)
          | negSucc third =>
              change Int.negOfNat (first * (second + 1)) * Int.negSucc third =
                Int.ofNat (first * ((second + 1) * (third + 1)))
              rw [negOfNat_mul_negSucc]
              exact congrArg Int.ofNat (Multiplication.mul_assoc first (second + 1) (third + 1))
  | negSucc first =>
      cases second with
      | ofNat second =>
          cases third with
          | ofNat third =>
              change Int.negOfNat ((first + 1) * second) * Int.ofNat third =
                Int.negOfNat ((first + 1) * (second * third))
              rw [negOfNat_mul_ofNat]
              exact congrArg Int.negOfNat (Multiplication.mul_assoc (first + 1) second third)
          | negSucc third =>
              change Int.negOfNat ((first + 1) * second) * Int.negSucc third =
                Int.negSucc first * Int.negOfNat (second * (third + 1))
              rw [negOfNat_mul_negSucc, Int.negSucc_mul_negOfNat]
              exact congrArg Int.ofNat (Multiplication.mul_assoc (first + 1) second (third + 1))
      | negSucc second =>
          cases third with
          | ofNat third =>
              change Int.ofNat (((first + 1) * (second + 1)) * third) =
                Int.negSucc first * Int.negOfNat ((second + 1) * third)
              rw [Int.negSucc_mul_negOfNat]
              exact congrArg Int.ofNat (Multiplication.mul_assoc (first + 1) (second + 1) third)
          | negSucc third =>
              exact congrArg Int.negOfNat
                (Multiplication.mul_assoc (first + 1) (second + 1) (third + 1))

/-- Multiplying a displayed integer by one on the right preserves it. -/
public theorem mul_one (value : Int) : value * 1 = value :=
  (mul_comm value 1).trans (Int.one_mul value)

/-- The zeroth power of a displayed integer is one. -/
public theorem pow_zero (value : Int) : value ^ 0 = 1 := by
  cases value <;> rfl

/-- Incrementing the natural exponent multiplies the displayed power by its base.

For negative bases, the two retained remainder cases determine the alternating
sign without changing the executable integer power operation. -/
public theorem pow_succ (value : Int) (exponent : Nat) :
    value ^ (exponent + 1) = value ^ exponent * value := by
  cases value with
  | ofNat value => rfl
  | negSucc value =>
      change (if (exponent + 1) % 2 = 0 then Int.ofNat ((value + 1) ^ (exponent + 1))
        else Int.negOfNat ((value + 1) ^ (exponent + 1))) =
        (if exponent % 2 = 0 then Int.ofNat ((value + 1) ^ exponent)
        else Int.negOfNat ((value + 1) ^ exponent)) * Int.negSucc value
      cases Parity.consecutive exponent with
      | inl even =>
          rw [even.1, even.2]
          change Int.negOfNat ((value + 1) ^ (exponent + 1)) =
            Int.negOfNat (((value + 1) ^ exponent) * (value + 1))
          exact congrArg Int.negOfNat (Nat.pow_succ (value + 1) exponent)
      | inr odd =>
          rw [odd.1, odd.2]
          change Int.ofNat ((value + 1) ^ (exponent + 1)) =
            Int.negOfNat ((value + 1) ^ exponent) * Int.negSucc value
          rw [negOfNat_mul_negSucc]
          exact congrArg Int.ofNat (Nat.pow_succ (value + 1) exponent)

/-- The power of a displayed negative natural has its magnitude and parity sign.

An even exponent gives the natural magnitude, and an odd exponent gives its
negation. This includes the zero base and preserves the integer power operation. -/
public theorem pow_negOfNat (value exponent : Nat) :
    Int.pow (Int.negOfNat value) exponent =
      if exponent % 2 = 0 then Int.ofNat (value ^ exponent)
      else Int.negOfNat (value ^ exponent) := by
  cases value with
  | zero =>
      cases exponent with
      | zero => rfl
      | succ exponent =>
          change (0 : Int) ^ (exponent + 1) =
            if (exponent + 1) % 2 = 0 then Int.ofNat (0 ^ (exponent + 1))
            else Int.negOfNat (0 ^ (exponent + 1))
          rw [pow_succ, mul_comm (0 ^ exponent) 0, zero_mul,
            Nat.pow_succ, Nat.mul_zero]
          split <;> rfl
  | succ value => rfl

/-- Incrementing both natural inputs preserves their signed difference. -/
public theorem subNatNat_succ_succ (left right : Nat) :
    Int.subNatNat (left + 1) (right + 1) = Int.subNatNat left right := by
  unfold Int.subNatNat
  rw [Nat.succ_sub_succ, Nat.succ_sub_succ]

/-- A bounded signed natural difference is the cast of its natural difference.

The retained inequality prevents the signed subtraction from taking a
negative branch, so the natural and integer displays coincide. -/
public theorem subNatNat_of_le {left right : Nat} (bound : right ≤ left) :
    Int.subNatNat left right = Int.ofNat (left - right) :=
  Int.subNatNat_of_sub_eq_zero (Subtraction.sub_eq_zero_of_le bound)

/-- A bounded natural subtraction casts to the same original integer difference.

The retained subtrahend bound prevents natural truncation. The original signed
subtraction and natural subtraction then retain the same displayed magnitude. -/
public theorem natCast_sub_of_le {value subtrahend : Nat} (bound : subtrahend ≤ value) :
    ((value - subtrahend : Nat) : Int) = (value : Int) - (subtrahend : Int) := by
  cases subtrahend with
  | zero => rfl
  | succ subtrahend =>
      change Int.ofNat (value - (subtrahend + 1)) =
        Int.subNatNat value (subtrahend + 1)
      exact (subNatNat_of_le bound).symm

/-- A signed difference has magnitude bounded by the sum of its inputs.

Removing a successor from both natural displays preserves the difference
and reduces the available bound. The zero-input cases are exact readbacks. -/
private theorem natAbs_subNatNat_le : ∀ left right : Nat,
    (Int.subNatNat left right).natAbs ≤ left + right
  | left, 0 => by
      unfold Int.subNatNat
      rw [Nat.zero_sub, Nat.sub_zero]
      change left ≤ left + 0
      rw [Nat.add_zero]
      exact Nat.le_refl left
  | 0, right + 1 => by
      unfold Int.subNatNat
      rw [Nat.sub_zero, Nat.zero_add]
      exact Nat.le_refl (right + 1)
  | left + 1, right + 1 => by
      rw [subNatNat_succ_succ]
      exact Nat.le_trans (natAbs_subNatNat_le left right)
        (Nat.add_le_add (Nat.le_succ left) (Nat.le_succ right))

/-- The magnitude of an integer sum does not exceed the summed magnitudes.

Equal signs give the exact sum of the displayed natural magnitudes. Opposite
signs give a signed difference bounded directly by those same magnitudes. -/
public theorem natAbs_add_le (left right : Int) :
    (left + right).natAbs ≤ left.natAbs + right.natAbs := by
  cases left with
  | ofNat left =>
      cases right with
      | ofNat right => exact Nat.le_refl (left + right)
      | negSucc right => exact natAbs_subNatNat_le left (right + 1)
  | negSucc left =>
      cases right with
      | ofNat right =>
          change (Int.subNatNat right (left + 1)).natAbs ≤ (left + 1) + right
          rw [Nat.add_comm (left + 1) right]
          exact natAbs_subNatNat_le right (left + 1)
      | negSucc right =>
          change left + right + 1 + 1 ≤ (left + 1) + (right + 1)
          rw [Nat.succ_add left (right + 1), Nat.add_succ left right]
          exact Nat.le_refl _

/-- Incrementing the minuend increments its signed difference. -/
private theorem subNatNat_succ_left : ∀ left right : Nat,
    Int.subNatNat (left + 1) right = Int.subNatNat left right + 1
  | left, 0 => by
      unfold Int.subNatNat
      rw [Nat.zero_sub, Nat.zero_sub, Nat.sub_zero, Nat.sub_zero]
      rfl
  | 0, right + 1 => rfl
  | left + 1, right + 1 => by
      rw [subNatNat_succ_succ, subNatNat_succ_succ]
      exact subNatNat_succ_left left right

/-- Incrementing a displayed natural summand increments its integer sum. -/
public theorem add_natural_succ (left : Nat) (right : Int) :
    (Int.ofNat left + right) + 1 = Int.ofNat (left + 1) + right := by
  cases right with
  | ofNat right => exact congrArg Int.ofNat (Nat.succ_add left right).symm
  | negSucc right => exact (subNatNat_succ_left left (right + 1)).symm

/-- A natural summand translates the minuend of a displayed signed difference. -/
private theorem subNatNat_add_natural : ∀ left right subtrahend : Nat,
    Int.subNatNat (left + right) subtrahend =
      Int.ofNat left + Int.subNatNat right subtrahend
  | 0, right, subtrahend => by
      rw [Nat.zero_add]
      exact (zero_add _).symm
  | left + 1, right, subtrahend => by
      rw [Nat.succ_add, subNatNat_succ_left,
        subNatNat_add_natural left right subtrahend, add_natural_succ]

/-- Two displayed natural summands associate with any displayed integer. -/
private theorem add_assoc_naturals (first second : Nat) (third : Int) :
    (Int.ofNat first + Int.ofNat second) + third =
      Int.ofNat first + (Int.ofNat second + third) := by
  cases third with
  | ofNat third => exact congrArg Int.ofNat (Nat.add_assoc first second third)
  | negSucc third => exact subNatNat_add_natural first second (third + 1)

/-- A signed difference with zero subtrahend is the displayed natural. -/
private theorem subNatNat_zero_right (value : Nat) :
    Int.subNatNat value 0 = Int.ofNat value := by
  unfold Int.subNatNat
  rw [Nat.zero_sub, Nat.sub_zero]

/-- Incrementing the subtrahend adds negative one to the signed difference. -/
private theorem subNatNat_succ_right : ∀ left right : Nat,
    Int.subNatNat left (right + 1) = Int.subNatNat left right + Int.negSucc 0
  | left, 0 => by
      rw [subNatNat_zero_right]
      rfl
  | 0, right + 1 => rfl
  | left + 1, right + 1 => by
      rw [subNatNat_succ_succ, subNatNat_succ_succ]
      exact subNatNat_succ_right left right

/-- Adding negative one increments the magnitude of a retained negative summand. -/
private theorem add_negative_succ (left : Int) (right : Nat) :
    (left + Int.negSucc right) + Int.negSucc 0 = left + Int.negSucc (right + 1) := by
  cases left with
  | ofNat left => exact (subNatNat_succ_right left (right + 1)).symm
  | negSucc left => rfl

/-- A negative successor translates the subtrahend of a signed difference. -/
private theorem subNatNat_add_negative : ∀ left right magnitude : Nat,
    Int.subNatNat left right + Int.negSucc magnitude =
      Int.subNatNat left (right + (magnitude + 1))
  | left, right, 0 => (subNatNat_succ_right left right).symm
  | left, right, magnitude + 1 => by
      rw [← add_negative_succ, subNatNat_add_negative left right magnitude,
        ← subNatNat_succ_right]
      exact congrArg (Int.subNatNat left) (Nat.add_assoc right (magnitude + 1) 1)

/-- Two negative successors associate with a displayed natural summand. -/
private theorem add_assoc_negatives (first second third : Nat) :
    (Int.negSucc first + Int.negSucc second) + Int.ofNat third =
      Int.negSucc first + (Int.negSucc second + Int.ofNat third) := by
  change Int.subNatNat third (first + second + 1 + 1) =
    Int.negSucc first + Int.subNatNat third (second + 1)
  rw [add_comm (Int.negSucc first), subNatNat_add_negative]
  apply congrArg (Int.subNatNat third)
  rw [Nat.succ_add second (first + 1)]
  exact congrArg (fun value => value + 1 + 1) (Nat.add_comm first second)

/-- Regrouping three displayed integer summands preserves their sum.

The mixed-sign cases use translations of the original signed natural
difference, retaining its ordinary addition operation. -/
public theorem add_assoc : ∀ first second third : Int,
    (first + second) + third = first + (second + third)
  | .ofNat first, .ofNat second, third => add_assoc_naturals first second third
  | .ofNat first, .negSucc second, .ofNat third => by
      rw [add_comm (Int.ofNat first + Int.negSucc second) (Int.ofNat third),
        ← add_assoc_naturals third first (Int.negSucc second),
        add_comm (Int.ofNat third) (Int.ofNat first),
        add_assoc_naturals first third (Int.negSucc second),
        add_comm (Int.ofNat third) (Int.negSucc second)]
  | .negSucc first, .ofNat second, .ofNat third => by
      rw [add_comm (Int.negSucc first) (Int.ofNat second),
        add_comm (Int.ofNat second + Int.negSucc first) (Int.ofNat third),
        ← add_assoc_naturals third second (Int.negSucc first),
        add_comm (Int.ofNat third + Int.ofNat second) (Int.negSucc first),
        add_comm (Int.ofNat third) (Int.ofNat second)]
  | .negSucc first, .negSucc second, .ofNat third =>
      add_assoc_negatives first second third
  | .negSucc first, .ofNat second, .negSucc third => by
      rw [add_comm (Int.negSucc first + Int.ofNat second) (Int.negSucc third),
        ← add_assoc_negatives third first second,
        add_comm (Int.negSucc third) (Int.negSucc first),
        add_assoc_negatives first third second,
        add_comm (Int.negSucc third) (Int.ofNat second)]
  | .ofNat first, .negSucc second, .negSucc third => by
      rw [add_comm (Int.ofNat first) (Int.negSucc second),
        add_comm (Int.negSucc second + Int.ofNat first) (Int.negSucc third),
        ← add_assoc_negatives third second first,
        add_comm (Int.negSucc third + Int.negSucc second) (Int.ofNat first),
        add_comm (Int.negSucc third) (Int.negSucc second)]
  | .negSucc first, .negSucc second, .negSucc third => by
      change Int.negSucc ((first + second + 1) + third + 1) =
        Int.negSucc (first + (second + third + 1) + 1)
      rw [Nat.succ_add (first + second) third]
      exact congrArg (fun value => Int.negSucc (value + 1 + 1))
        (Nat.add_assoc first second third)

/-- Four displayed summands can be grouped into their corresponding pairs. -/
private theorem add_four (first second third fourth : Int) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) := by
  rw [add_assoc, ← add_assoc second third fourth, add_comm second third,
    add_assoc third second fourth, ← add_assoc]

/-- A displayed additive inverse is the negation of the other summand.

The supplied equality says that the two original integers sum to zero.
Adding the displayed inverse of the first summand recovers the second. -/
public theorem neg_eq_of_add_eq_zero {left right : Int} (vanishes : left + right = 0) :
    -left = right := by
  calc
    -left = -left + 0 := (Int.add_zero _).symm
    _ = -left + (left + right) := congrArg (-left + ·) vanishes.symm
    _ = (-left + left) + right := (add_assoc _ _ _).symm
    _ = 0 + right := congrArg (· + right) (neg_add_cancel left)
    _ = right := zero_add right

/-- Negating an integer sum negates both displayed summands. -/
public theorem neg_add (left right : Int) : -(left + right) = -left + -right := by
  apply neg_eq_of_add_eq_zero
  rw [add_four, add_comm left (-left), neg_add_cancel,
    zero_add, add_comm right (-right), neg_add_cancel]

/-- Displayed negative naturals add by adding their natural magnitudes. -/
private theorem negOfNat_add : ∀ left right : Nat,
    Int.negOfNat left + Int.negOfNat right = Int.negOfNat (left + right)
  | 0, right => by
      rw [Nat.zero_add]
      exact zero_add _
  | left + 1, 0 => by
      rw [Nat.add_zero]
      exact Int.add_zero _
  | left + 1, right + 1 => by
      rw [Nat.succ_add]
      rfl

/-- Incrementing a natural integer factor adds one copy of the other factor. -/
public theorem ofNat_succ_mul (count : Nat) (value : Int) :
    Int.ofNat (count + 1) * value = Int.ofNat count * value + value := by
  cases value with
  | ofNat value => exact congrArg Int.ofNat (Nat.succ_mul count value)
  | negSucc value =>
      change Int.negOfNat ((count + 1) * (value + 1)) =
        Int.negOfNat (count * (value + 1)) + Int.negOfNat (value + 1)
      rw [negOfNat_add, Nat.succ_mul]

/-- A natural integer factor distributes over the two displayed summands. -/
private theorem ofNat_mul_add : ∀ count : Nat, ∀ left right : Int,
    Int.ofNat count * (left + right) =
      Int.ofNat count * left + Int.ofNat count * right
  | 0, left, right => by
      change (0 : Int) * (left + right) = 0 * left + 0 * right
      rw [zero_mul, zero_mul, zero_mul, Int.add_zero]
  | count + 1, left, right => by
      rw [ofNat_succ_mul, ofNat_mul_add count left right,
        ofNat_succ_mul, ofNat_succ_mul]
      exact add_four _ _ _ _

/-- A displayed negative natural factor negates its corresponding positive product. -/
private theorem negOfNat_mul (count : Nat) (value : Int) :
    Int.negOfNat count * value = -(Int.ofNat count * value) := by
  cases value with
  | ofNat value => exact negOfNat_mul_ofNat count value
  | negSucc value =>
      rw [negOfNat_mul_negSucc]
      change Int.ofNat (count * (value + 1)) = -(-Int.ofNat (count * (value + 1)))
      exact (Int.neg_neg _).symm

/-- Negating the left displayed factor negates the integer product. -/
public theorem neg_mul (left right : Int) : -left * right = -(left * right) := by
  cases left with
  | ofNat left => exact negOfNat_mul left right
  | negSucc left =>
      change Int.ofNat (left + 1) * right = -(Int.negOfNat (left + 1) * right)
      rw [negOfNat_mul]
      exact (Int.neg_neg _).symm

/-- Integer multiplication distributes over a sum in the right factor. -/
public theorem mul_add (factor left right : Int) :
    factor * (left + right) = factor * left + factor * right := by
  cases factor with
  | ofNat factor => exact ofNat_mul_add factor left right
  | negSucc factor =>
      change Int.negOfNat (factor + 1) * (left + right) =
        Int.negOfNat (factor + 1) * left + Int.negOfNat (factor + 1) * right
      rw [negOfNat_mul, negOfNat_mul, negOfNat_mul, ofNat_mul_add, neg_add]

/-- Integer multiplication distributes over a sum in the left factor. -/
public theorem add_mul (left right factor : Int) :
    (left + right) * factor = left * factor + right * factor := by
  rw [mul_comm (left + right) factor, mul_add,
    mul_comm factor left, mul_comm factor right]

/-- A zero displayed integer product has a displayed zero factor.

The two integer sign constructors and zero natural magnitudes distinguish
all possible products directly. Products of positive magnitudes cannot be zero. -/
public theorem eq_zero_of_mul_eq_zero {left right : Int} (vanishes : left * right = 0) :
    left = 0 ∨ right = 0 := by
  cases left with
  | ofNat left =>
      cases left with
      | zero => exact Or.inl rfl
      | succ left =>
          cases right with
          | ofNat right =>
              cases right with
              | zero => exact Or.inr rfl
              | succ right => cases vanishes
          | negSucc right => cases vanishes
  | negSucc left =>
      cases right with
      | ofNat right =>
          cases right with
          | zero => exact Or.inr rfl
          | succ right => cases vanishes
      | negSucc right => cases vanishes

/-- Equal displayed sums with a common right summand have equal left summands. -/
public theorem add_right_cancel {left right offset : Int}
    (same : left + offset = right + offset) : left = right := by
  have cancels : offset + -offset = 0 :=
    (add_comm _ _).trans (neg_add_cancel offset)
  calc
    left = left + 0 := (Int.add_zero _).symm
    _ = left + (offset + -offset) := congrArg (left + ·) cancels.symm
    _ = (left + offset) + -offset := (add_assoc _ _ _).symm
    _ = (right + offset) + -offset := congrArg (· + -offset) same
    _ = right + (offset + -offset) := add_assoc _ _ _
    _ = right + 0 := congrArg (right + ·) cancels
    _ = right := Int.add_zero _

/-- Cancelling a retained nonzero left integer factor preserves equality.

The product equality gives a zero product with the displayed additive
difference. The nonzero factor and additive cancellation determine the
equality of the other two integer factors. -/
public theorem eq_of_mul_eq_mul_left {factor left right : Int}
    (nonzero : factor ≠ 0) (same : factor * left = factor * right) : left = right := by
  have vanishes : factor * (left + -right) = 0 := by
    rw [mul_add, mul_comm factor (-right), neg_mul, mul_comm right factor, same,
      add_comm (factor * right), neg_add_cancel]
  cases eq_zero_of_mul_eq_zero vanishes with
  | inl factorZero => exact False.elim (nonzero factorZero)
  | inr differenceZero =>
      have rightCancels : right + -right = 0 :=
        (add_comm _ _).trans (neg_add_cancel right)
      exact add_right_cancel (differenceZero.trans rightCancels.symm)

/-- The absolute value of a displayed integer power is the corresponding magnitude power.

Structural induction follows the original integer power recurrence. Each
successor multiplies the retained magnitude by the same original base magnitude. -/
public theorem natAbs_pow (value : Int) : ∀ exponent : Nat,
    (value ^ exponent).natAbs = value.natAbs ^ exponent
  | 0 => by
      rewrite [pow_zero, Nat.pow_zero]
      exact Eq.refl _
  | exponent + 1 => by
      rewrite [pow_succ, natAbs_mul, natAbs_pow value exponent, Nat.pow_succ]
      exact Eq.refl _

/-- Squaring the original magnitude cast gives the square of the original integer.

Both displayed integer sign constructors reduce to the same natural square.
The equality retains the original integer power and magnitude algorithms,
including the zero magnitude. -/
public theorem natAbs_pow_two (value : Int) :
    (value.natAbs : Int) ^ 2 = value ^ 2 := by
  cases value <;> rfl

end Purelib.Data.Int.Arithmetic
