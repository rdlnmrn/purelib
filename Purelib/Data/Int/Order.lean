module

import Mathlib.Algebra.Order.Ring.Defs
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Subtraction

namespace Purelib.Data.Int.Order

open Purelib.Data.Nat

/-- A retained natural additive difference certifies a weak integer bound.

Adding the supplied natural difference to the lower integer gives the upper
integer. Cancellation identifies this difference with the order's displayed
nonnegative subtraction. -/
public theorem le_intro {left right : Int} (difference : Nat)
    (equation : left + (difference : Int) = right) : left ≤ right := by
  change Int.NonNeg (right - left)
  rw [← equation, Int.sub_eq_add_neg, Arithmetic.add_comm left (difference : Int),
    Arithmetic.add_assoc, Arithmetic.add_comm left (-left),
    Arithmetic.neg_add_cancel, Int.add_zero]
  exact Int.NonNeg.mk difference

/-- A weak integer bound retains a natural additive difference.

The nonnegative subtraction already contains the natural witness. Adding
the lower integer back recovers the upper integer without selecting data. -/
public theorem le_dest {left right : Int} (bound : left ≤ right) :
    ∃ difference : Nat, left + (difference : Int) = right := by
  obtain ⟨difference, equation⟩ := Int.NonNeg.elim bound
  refine ⟨difference, ?_⟩
  rw [← equation, Int.sub_eq_add_neg, Arithmetic.add_comm left (right + -left),
    Arithmetic.add_assoc, Arithmetic.neg_add_cancel, Int.add_zero]

/-- A weak integer bound makes its displayed subtraction nonnegative.

The original bound already retains a nonnegative witness for the upper
integer minus the lower integer. Subtracting zero preserves that same witness. -/
public theorem sub_nonneg_of_le {right left : Int} (bound : left ≤ right) :
    0 ≤ right - left := by
  change Int.NonNeg ((right - left) - 0)
  rw [Arithmetic.sub_zero]
  exact bound

/-- Integer casts preserve and reflect weak natural comparison.

The forward direction reads the retained natural additive difference of the
integer bound. The reverse direction uses the original bounded subtraction
as its explicit difference witness. -/
public theorem natCast_le_iff {left right : Nat} :
    (left : Int) ≤ (right : Int) ↔ left ≤ right := by
  constructor
  · intro bound
    obtain ⟨difference, equation⟩ := le_dest bound
    rw [← Int.natCast_add] at equation
    exact Nat.le.intro (Int.ofNat.inj equation)
  · intro bound
    apply le_intro (right - left)
    rw [← Int.natCast_add]
    exact congrArg Int.ofNat (Subtraction.add_sub_of_le bound)

/-- Integer casts preserve and reflect strict natural comparison.

Both displayed orders define strict comparison by the same successor step.
Their weak comparison equivalence applies after transporting that step
through the original natural cast. -/
public theorem natCast_lt_iff {left right : Nat} :
    (left : Int) < (right : Int) ↔ left < right := by
  constructor
  · intro strict
    apply natCast_le_iff.mp
    change ((left + 1 : Nat) : Int) ≤ (right : Int)
    rw [Int.natCast_add, Int.natCast_one]
    exact strict
  · intro strict
    have bound := natCast_le_iff.mpr strict
    change ((left + 1 : Nat) : Int) ≤ (right : Int) at bound
    rw [Int.natCast_add, Int.natCast_one] at bound
    exact bound

/-- A cast natural difference retains its bounded or truncated subtraction case.

When the subtrahend fits, the natural difference casts to the same signed
integer difference. Otherwise the original strict bound certifies truncation
to the displayed integer zero. Both cases use the original operands. -/
public theorem natCast_sub_dichotomy {left right : Nat} :
    right ≤ left ∧ ((left - right : Nat) : Int) = (left : Int) - (right : Int) ∨
      left < right ∧ ((left - right : Nat) : Int) = 0 := by
  by_cases bound : right ≤ left
  · exact Or.inl ⟨bound, Arithmetic.natCast_sub_of_le bound⟩
  · have strict : left < right := Nat.lt_of_not_ge bound
    have truncated : left - right = 0 := Subtraction.sub_eq_zero_of_le (Nat.le_of_lt strict)
    exact Or.inr ⟨strict, congrArg Int.ofNat truncated⟩

/-- Every integer is weakly bounded by itself. -/
public theorem le_refl (value : Int) : value ≤ value :=
  le_intro 0 (Int.add_zero value)

/-- Two retained weak integer bounds compose by adding their natural differences.

The sum uses the witnesses of the two supplied bounds, with the intermediate
integer eliminated by their original additive equations. -/
public theorem le_trans {first second third : Int}
    (firstSecond : first ≤ second) (secondThird : second ≤ third) : first ≤ third := by
  obtain ⟨firstDifference, firstEquation⟩ := le_dest firstSecond
  obtain ⟨secondDifference, secondEquation⟩ := le_dest secondThird
  apply le_intro (firstDifference + secondDifference)
  rw [Int.natCast_add, ← Arithmetic.add_assoc, firstEquation, secondEquation]

/-- Negating both integer endpoints reverses their retained weak bound.

The original natural additive difference is retained. Negating its endpoint
equation and cancelling the same difference gives the reversed bound. -/
public theorem neg_le_neg {left right : Int} (bound : left ≤ right) :
    -right ≤ -left := by
  obtain ⟨difference, equation⟩ := le_dest bound
  have reversed : -(left + (difference : Int)) = -right :=
    congrArg Int.neg equation
  rw [Arithmetic.neg_add] at reversed
  apply le_intro difference
  rw [← reversed, Arithmetic.add_assoc, Arithmetic.neg_add_cancel, Int.add_zero]

/-- Opposite weak integer bounds identify their endpoints.

Their retained natural differences sum to zero after scalar cancellation,
so the first additive equation has zero difference. -/
public theorem le_antisymm {left right : Int}
    (leftRight : left ≤ right) (rightLeft : right ≤ left) : left = right := by
  obtain ⟨firstDifference, firstEquation⟩ := le_dest leftRight
  obtain ⟨secondDifference, secondEquation⟩ := le_dest rightLeft
  have same : left + ((firstDifference : Int) + (secondDifference : Int)) =
      left + 0 := by
    rw [← Arithmetic.add_assoc, firstEquation, secondEquation, Int.add_zero]
  have sumZero : (firstDifference : Int) + (secondDifference : Int) = 0 :=
    Arithmetic.add_right_cancel
      ((Arithmetic.add_comm _ _).trans (same.trans (Arithmetic.add_comm _ _)))
  have naturalZero := Int.ofNat.inj sumZero
  have firstZero := (Nat.eq_zero_of_add_eq_zero naturalZero).1
  rw [firstZero, Int.natCast_zero, Int.add_zero] at firstEquation
  exact firstEquation

/-- Any two displayed integers are weakly ordered in one direction.

The sign constructor of their subtraction gives one nonnegative difference;
negating that difference gives the reverse bound in the negative case. -/
public theorem le_total (left right : Int) : left ≤ right ∨ right ≤ left := by
  have reverseDifference : left - right = -(right - left) := by
    rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Arithmetic.neg_add, Int.neg_neg,
      Arithmetic.add_comm]
  cases differenceEquation : right - left with
  | ofNat difference =>
      apply Or.inl
      change Int.NonNeg (right - left)
      rw [differenceEquation]
      exact Int.NonNeg.mk difference
  | negSucc difference =>
      apply Or.inr
      change Int.NonNeg (left - right)
      rw [reverseDifference, differenceEquation]
      exact Int.NonNeg.mk (difference + 1)

/-- Multiplying a weak integer bound by a nonnegative right factor preserves it.

The additive difference and the factor each retain a natural witness. Their
natural product is the additive difference of the scaled endpoints. -/
public theorem mul_le_mul_of_nonneg_right {left right factor : Int}
    (bound : left ≤ right) (factorNonnegative : 0 ≤ factor) :
    left * factor ≤ right * factor := by
  obtain ⟨difference, differenceEquation⟩ := le_dest bound
  obtain ⟨magnitude, magnitudeEquation⟩ := le_dest factorNonnegative
  rw [Arithmetic.zero_add] at magnitudeEquation
  rw [← magnitudeEquation]
  apply le_intro (difference * magnitude)
  rw [Int.natCast_mul, ← Arithmetic.add_mul, differenceEquation]

/-- Adding two weak integer bounds preserves their order.

The original natural additive differences are added. Scalar associativity and
commutativity identify their sum as the difference of the summed endpoints. -/
public theorem add_le_add {first second third fourth : Int}
    (firstBound : first ≤ second) (secondBound : third ≤ fourth) :
    first + third ≤ second + fourth := by
  obtain ⟨firstDifference, firstEquation⟩ := le_dest firstBound
  obtain ⟨secondDifference, secondEquation⟩ := le_dest secondBound
  apply le_intro (firstDifference + secondDifference)
  calc
    first + third + ((firstDifference + secondDifference : Nat) : Int) =
        (first + (firstDifference : Int)) +
          (third + (secondDifference : Int)) := by
      rw [Int.natCast_add, Arithmetic.add_assoc first third,
        ← Arithmetic.add_assoc third (firstDifference : Int),
        Arithmetic.add_comm third (firstDifference : Int),
        Arithmetic.add_assoc (firstDifference : Int) third,
        ← Arithmetic.add_assoc first (firstDifference : Int)]
    _ = second + fourth := congrArg₂ Int.add firstEquation secondEquation

/-- Multiplying a weak integer bound by a nonnegative left factor preserves it.

Scalar commutativity transports the original bound to multiplication on the
right, where the retained natural difference already gives its certificate. -/
public theorem mul_le_mul_of_nonneg_left {left right factor : Int}
    (bound : left ≤ right) (factorNonnegative : 0 ≤ factor) :
    factor * left ≤ factor * right := by
  calc
    factor * left = left * factor := Arithmetic.mul_comm _ _
    _ ≤ right * factor := mul_le_mul_of_nonneg_right bound factorNonnegative
    _ = factor * right := Arithmetic.mul_comm _ _

/-- Multiplying a weak integer bound by a nonpositive left factor reverses it.

The negated factor is nonnegative. Multiplication by that factor preserves the
original bound, and negating both products restores the original factor. -/
public theorem mul_le_mul_of_nonpos_left {left right factor : Int}
    (bound : left ≤ right) (factorNonpositive : factor ≤ 0) :
    factor * right ≤ factor * left := by
  have nonnegative := neg_le_neg factorNonpositive
  rw [Int.neg_zero] at nonnegative
  have multiplied := mul_le_mul_of_nonneg_left bound nonnegative
  have reversed := neg_le_neg multiplied
  rw [Arithmetic.neg_mul, Arithmetic.neg_mul, Int.neg_neg, Int.neg_neg] at reversed
  exact reversed

/-- A retained positive natural additive difference certifies a strict integer bound.

The successor difference consists of the order's unit step and the supplied
natural remainder. Their displayed sum identifies the upper integer. -/
public theorem lt_intro {left right : Int} {difference : Nat}
    (equation : left + ((difference + 1 : Nat) : Int) = right) : left < right := by
  change left + 1 ≤ right
  apply le_intro difference
  rw [Int.natCast_add, Int.natCast_one, Arithmetic.add_comm (difference : Int) 1,
    ← Arithmetic.add_assoc] at equation
  exact equation

/-- A strict integer bound retains a positive natural additive difference.

The order's unit step and its retained nonnegative remainder form the
successor natural difference between the endpoints. -/
public theorem lt_dest {left right : Int} (strict : left < right) :
    ∃ difference : Nat, left + ((difference + 1 : Nat) : Int) = right := by
  obtain ⟨difference, equation⟩ := le_dest strict
  refine ⟨difference, ?_⟩
  rw [Int.natCast_add, Int.natCast_one, Arithmetic.add_comm (difference : Int) 1,
    ← Arithmetic.add_assoc]
  exact equation

/-- An integer cannot be strictly bounded by itself.

Its retained successor difference would be zero after additive cancellation,
contradicting the distinct natural constructors. -/
public theorem lt_irrefl (value : Int) : ¬value < value := by
  intro strict
  obtain ⟨difference, equation⟩ := lt_dest strict
  have differenceZero : ((difference + 1 : Nat) : Int) = 0 :=
    Arithmetic.add_right_cancel
      ((Arithmetic.add_comm _ _).trans
        (equation.trans (Arithmetic.zero_add value).symm))
  exact Nat.noConfusion (Int.ofNat.inj differenceZero)

/-- Every strict integer bound also supplies a weak bound. -/
public theorem le_of_lt {left right : Int} (strict : left < right) : left ≤ right := by
  obtain ⟨difference, equation⟩ := lt_dest strict
  exact le_intro (difference + 1) equation

/-- Strict integer order is weak order with the reverse weak bound excluded.

A retained natural difference is zero exactly when the endpoints coincide;
its successor case supplies the defining strict unit step. -/
public theorem lt_iff_le_and_not_ge {left right : Int} :
    left < right ↔ left ≤ right ∧ ¬right ≤ left := by
  constructor
  · intro strict
    have bound := le_of_lt strict
    refine ⟨bound, ?_⟩
    intro reverse
    have same := le_antisymm bound reverse
    rw [same] at strict
    exact lt_irrefl right strict
  · intro bounds
    obtain ⟨difference, equation⟩ := le_dest bounds.1
    cases difference with
    | zero =>
        rw [Int.natCast_zero, Int.add_zero] at equation
        cases equation
        exact (bounds.2 (le_refl left)).elim
    | succ difference => exact lt_intro equation

/-- A weak integer bound between distinct endpoints is strict. -/
public theorem lt_of_le_of_ne {left right : Int}
    (bound : left ≤ right) (distinct : left ≠ right) : left < right :=
  lt_iff_le_and_not_ge.mpr ⟨bound, fun reverse => distinct (le_antisymm bound reverse)⟩

/-- Excluding a strict integer bound gives the reverse weak bound.

Weak totality retains an additive difference in one direction. If only the
forward weak bound is available, its zero difference identifies the endpoints;
a successor difference contradicts the supplied exclusion. -/
public theorem le_of_not_lt {left right : Int} (excluded : ¬left < right) :
    right ≤ left := by
  cases le_total right left with
  | inl reverse => exact reverse
  | inr forward =>
      obtain ⟨difference, equation⟩ := le_dest forward
      cases difference with
      | zero =>
          rw [Int.natCast_zero, Int.add_zero] at equation
          rewrite [← equation]
          exact le_refl left
      | succ difference => exact (excluded (lt_intro equation)).elim

/-- Excluding a weak integer bound gives the reverse strict bound.

Weak totality orders the original endpoints. The supplied exclusion rules out
one direction and certifies the strictness of the retained reverse comparison. -/
public theorem lt_of_not_le {left right : Int} (excluded : ¬left ≤ right) :
    right < left := by
  cases le_total right left with
  | inl reverse => exact lt_iff_le_and_not_ge.mpr ⟨reverse, excluded⟩
  | inr forward => exact (excluded forward).elim

/-- Distinct integers are strictly ordered in one direction.

Weak totality supplies an ordering of the original endpoints. Their retained
disequality excludes equality, so that same ordering is strict. -/
public theorem lt_or_gt_of_ne {left right : Int} (distinct : left ≠ right) :
    left < right ∨ right < left := by
  cases le_total left right with
  | inl ordered => exact Or.inl (lt_of_le_of_ne ordered distinct)
  | inr ordered =>
      exact Or.inr (lt_of_le_of_ne ordered (fun equal => distinct equal.symm))

/-- A positive integer subtraction is a strict bound between its endpoints.

The retained successor difference gives the same additive endpoint equation
on either side of the equivalence, after cancelling the lower integer. -/
public theorem sub_pos {left right : Int} : 0 < right - left ↔ left < right := by
  constructor
  · intro positive
    obtain ⟨difference, equation⟩ := lt_dest positive
    rw [Arithmetic.zero_add] at equation
    apply lt_intro (difference := difference)
    rw [equation, Int.sub_eq_add_neg,
      Arithmetic.add_comm left (right + -left), Arithmetic.add_assoc,
      Arithmetic.neg_add_cancel, Int.add_zero]
  · intro strict
    obtain ⟨difference, equation⟩ := lt_dest strict
    have differenceEquation : right - left = ((difference + 1 : Nat) : Int) := by
      rw [← equation, Int.sub_eq_add_neg,
        Arithmetic.add_comm left ((difference + 1 : Nat) : Int),
        Arithmetic.add_assoc, Arithmetic.add_comm left (-left),
        Arithmetic.neg_add_cancel, Int.add_zero]
    exact lt_intro ((Arithmetic.zero_add _).trans differenceEquation.symm)

/-- A positive natural number has a positive integer cast.

Its successor representation leaves a nonnegative displayed difference
after subtracting one, which is the definition of strict integer positivity. -/
public theorem natCast_pos {value : Nat} (positive : 0 < value) :
    0 < (value : Int) := by
  cases value with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ value =>
      change Int.NonNeg (Int.subNatNat (value + 1) 1)
      rw [Arithmetic.subNatNat_succ_succ value 0,
        Arithmetic.subNatNat_of_le (Nat.zero_le value)]
      exact Int.NonNeg.mk value

/-- A displayed negative integer cannot be positive. -/
public theorem negSucc_not_pos (value : Nat) : ¬0 < Int.negSucc value := by
  intro positive
  change Int.NonNeg (Int.negSucc (value + 1)) at positive
  cases positive

/-- A positive integer is the integer cast of its magnitude.

The negative constructor contradicts positivity. The natural constructor
already has the displayed magnitude as its integer representation. -/
public theorem natAbs_of_pos {value : Int} (positive : 0 < value) :
    (value.natAbs : Int) = value := by
  cases value with
  | ofNat value => rfl
  | negSucc value => exact (negSucc_not_pos value positive).elim

/-- A nonnegative integer is the integer cast of its magnitude.

The natural constructor retains this readback directly, including zero.
Nonnegativity excludes the negative successor constructor. -/
public theorem natAbs_of_nonneg {value : Int} (nonnegative : 0 ≤ value) :
    (value.natAbs : Int) = value := by
  cases value with
  | ofNat value => rfl
  | negSucc value => cases nonnegative

/-- The magnitude of an integer that is not positive is its negation.

Zero and the negative constructor have this equation directly. A nonzero
natural constructor would be positive, contradicting the supplied condition. -/
public theorem natAbs_of_not_pos {value : Int} (notPositive : ¬0 < value) :
    (value.natAbs : Int) = -value := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => rfl
      | succ value => exact (notPositive (natCast_pos (Nat.zero_lt_succ value))).elim
  | negSucc value => rfl

/-- The product of two positive displayed integers is positive.

Each strict bound retains a successor natural magnitude. Their product is
again a successor magnitude, giving its explicit positive integer sign. -/
public theorem mul_pos {left right : Int}
    (leftPositive : 0 < left) (rightPositive : 0 < right) : 0 < left * right := by
  obtain ⟨leftMagnitude, leftEquation⟩ := lt_dest leftPositive
  obtain ⟨rightMagnitude, rightEquation⟩ := lt_dest rightPositive
  rw [Arithmetic.zero_add] at leftEquation rightEquation
  rw [← leftEquation, ← rightEquation, ← Int.natCast_mul]
  apply natCast_pos
  rw [Nat.mul_succ, Nat.add_succ]
  exact Nat.zero_lt_succ _

/-- A positive integer product with a positive right factor has a positive left factor.

The zero left constructor gives a zero product. A negative left constructor
times the retained positive natural magnitude gives a negative successor;
only the positive natural constructor remains. -/
public theorem pos_of_mul_pos_left {left right : Int}
    (productPositive : 0 < left * right) (rightPositive : 0 < right) : 0 < left := by
  obtain ⟨rightMagnitude, rightEquation⟩ := lt_dest rightPositive
  rw [Arithmetic.zero_add] at rightEquation
  rw [← rightEquation] at productPositive
  cases left with
  | ofNat left =>
      cases left with
      | zero =>
          rw [Int.ofNat_eq_natCast, Int.ofNat_zero, Arithmetic.zero_mul] at productPositive
          exact (lt_irrefl 0 productPositive).elim
      | succ left => exact natCast_pos (Nat.zero_lt_succ left)
  | negSucc left =>
      change 0 < Int.negOfNat ((left + 1) * (rightMagnitude + 1)) at productPositive
      rw [Nat.mul_succ, Nat.add_succ] at productPositive
      exact (negSucc_not_pos _ productPositive).elim

/-- Adding two nonnegative integers preserves nonnegativity.

Their retained natural magnitudes add to the displayed magnitude of the sum. -/
public theorem add_nonneg {left right : Int}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) : 0 ≤ left + right := by
  obtain ⟨leftMagnitude, leftEquation⟩ := le_dest leftNonnegative
  obtain ⟨rightMagnitude, rightEquation⟩ := le_dest rightNonnegative
  rw [Arithmetic.zero_add] at leftEquation rightEquation
  rw [← leftEquation, ← rightEquation, ← Int.natCast_add]
  exact Int.natCast_nonneg _

/-- Multiplying two nonnegative integers preserves nonnegativity.

Their retained natural magnitudes multiply to the displayed magnitude of
the product, including either possible zero magnitude. -/
public theorem mul_nonneg {left right : Int}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) : 0 ≤ left * right := by
  obtain ⟨leftMagnitude, leftEquation⟩ := le_dest leftNonnegative
  obtain ⟨rightMagnitude, rightEquation⟩ := le_dest rightNonnegative
  rw [Arithmetic.zero_add] at leftEquation rightEquation
  rw [← leftEquation, ← rightEquation, ← Int.natCast_mul]
  exact Int.natCast_nonneg _

/-- A zero sum of two nonnegative integers has both addends zero.

The retained natural magnitudes sum to zero. Natural constructor disjointness
identifies each magnitude as zero and transports this to the original integers. -/
public theorem eq_zero_of_add_nonneg_eq_zero {left right : Int}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right)
    (sumZero : left + right = 0) : left = 0 ∧ right = 0 := by
  obtain ⟨leftMagnitude, leftEquation⟩ := le_dest leftNonnegative
  obtain ⟨rightMagnitude, rightEquation⟩ := le_dest rightNonnegative
  rw [Arithmetic.zero_add] at leftEquation rightEquation
  rw [← leftEquation, ← rightEquation, ← Int.natCast_add] at sumZero
  have magnitudesZero := Nat.eq_zero_of_add_eq_zero (Int.ofNat.inj sumZero)
  constructor
  · rw [← leftEquation, magnitudesZero.1, Int.natCast_zero]
  · rw [← rightEquation, magnitudesZero.2, Int.natCast_zero]

/-- The square of a nonzero displayed integer is positive.

The natural constructor has positive magnitude. The negative successor
constructor squares to a positive natural magnitude directly. -/
public theorem mul_self_pos {value : Int} (nonzero : value ≠ 0) : 0 < value * value := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => exact (nonzero rfl).elim
      | succ value =>
          exact mul_pos (natCast_pos (Nat.zero_lt_succ value))
            (natCast_pos (Nat.zero_lt_succ value))
  | negSucc value =>
      change 0 < (((value + 1) * (value + 1) : Nat) : Int)
      apply natCast_pos
      rw [Nat.mul_succ, Nat.add_succ]
      exact Nat.zero_lt_succ _

end Purelib.Data.Int.Order

@[expose] public section

/-!
# Casts and order for canonical fractions

Natural and integer casts are related directly to denominator-one canonical
records.  Weak order is sign-safe cross multiplication; strict order is its
constructive asymmetric part and is proved equivalent to strict integer
cross multiplication.
-/

namespace Purelib.Data.Int.Order

open Purelib.Data.Int

/-- A positive common right integer factor can be cancelled from a weak bound.

The scaled difference is nonnegative. A negative original difference would
have a negative product with the positive factor, so its displayed sign must
be natural and supplies the required weak bound. -/
theorem int_le_of_mul_le_mul_right {left right factor : Int}
    (factorPositive : 0 < factor)
    (scaled : left * factor ≤ right * factor) : left ≤ right := by
  have differenceProduct : (right - left) * factor = right * factor - left * factor := by
    rw [Int.sub_eq_add_neg, Arithmetic.add_mul, Arithmetic.neg_mul,
      Int.sub_eq_add_neg]
  change Int.NonNeg (right * factor - left * factor) at scaled
  rw [← differenceProduct] at scaled
  change Int.NonNeg (right - left)
  cases differenceEquation : right - left with
  | ofNat difference => exact Int.NonNeg.mk difference
  | negSucc difference =>
      rw [differenceEquation] at scaled
      cases factor with
      | ofNat factor =>
          cases factor with
          | zero => cases factorPositive
          | succ factor =>
              change Int.NonNeg (Int.negOfNat ((difference + 1) * (factor + 1))) at scaled
              rw [Nat.mul_succ, Nat.add_succ] at scaled
              cases scaled
      | negSucc factor => exact (negSucc_not_pos factor factorPositive).elim
end Purelib.Data.Int.Order

end

namespace Purelib.Data.Int.Order

/-- Multiplying an integer by itself gives a nonnegative integer.

A zero input retains zero as its product. A nonzero input has a strictly
positive square by the original signed multiplication certificate. -/
public theorem mul_self_nonneg (value : Int) : 0 ≤ value * value := by
  by_cases zero : value = 0
  · cases zero
    exact le_refl 0
  · exact le_of_lt (mul_self_pos zero)

end Purelib.Data.Int.Order
