module

public import Purelib.Algebra.Binomial.Gaussian
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Choose
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Bounded binomial expansions

The retained finite expansion reads ascending powers of its second input and
descending powers of its first input. Pascal's recurrence and the same bounded
prefix sums prove the general identity, its Gaussian row specialization and
the endpoint reduction when every interior coefficient is certified zero.
-/

namespace Purelib.Algebra.Binomial

open Purelib.Algebra
open Purelib.Algebra.FiniteSum
open Purelib.Data
open Purelib.Data.Nat

public section

variable {K : Type*} [CommRing K]

/-- Compute a bounded binomial expansion in descending first-input powers.

The sum includes exponent plus one terms, with ascending second-input powers and natural binomial coefficients cast into
the commutative ring. -/
@[expose] def binomialExpansion (exponent : Nat) (x y : K) : K :=
  Prefix.prefixSum (exponent + 1) (fun index =>
    y ^ index * x ^ (exponent - index) *
      (exponent.choose index : K))

/-- A natural power of a sum equals its bounded binomial expansion.

The identity holds over any commutative ring using the explicit finite prefix sum. -/
theorem binomial_theorem (exponent : Nat) (x y : K) :
    (x + y) ^ exponent = binomialExpansion exponent x y := by
  let term : Nat → Nat → K := fun row index =>
    y ^ index * x ^ (row - index) * (row.choose index : K)
  have firstTerm : ∀ row : Nat, term row 0 = x ^ row := by
    intro row
    dsimp only [term]
    rewrite [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one]
    exact (congrArg (fun value : K => value * 1) (_root_.one_mul (x ^ row))).trans
      (_root_.mul_one (x ^ row))
  have afterLastTerm : ∀ row : Nat, term row (row + 1) = 0 := by
    intro row
    dsimp only [term]
    rewrite [Nat.choose_succ_self, Nat.cast_zero]
    exact MulZeroClass.mul_zero _
  have pascalStep : ∀ row index : Nat, index ≤ row →
      term (row + 1) (index + 1) =
        y * term row index + x * term row (index + 1) := by
    intro row index indexBound
    dsimp only [term]
    rw [Nat.choose_succ_succ', NatCast.add, mul_add]
    apply congrArg₂ (fun first second : K => first + second)
    · rw [pow_succ y, Nat.succ_sub_succ]
      ring1
    · by_cases lastIndex : index = row
      · rw [lastIndex, Nat.choose_succ_self, Nat.cast_zero]
        ring1
      · have nextIndexBound : index + 1 ≤ row :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_ne indexBound lastIndex)
        have recovered :
            (index + 1) + ((row - (index + 1)) + 1) = row + 1 :=
          (Nat.add_assoc (index + 1) (row - (index + 1)) 1).symm.trans
            (congrArg (fun value : Nat => value + 1)
              (Subtraction.add_sub_of_le nextIndexBound))
        have subtractionIdentity :
            row + 1 - (index + 1) = (row - (index + 1)) + 1 :=
          (congrArg (fun value : Nat => value - (index + 1)) recovered.symm).trans
            (Subtraction.add_sub_cancel_left (index + 1) ((row - (index + 1)) + 1))
        rw [subtractionIdentity, pow_succ x]
        ring1
  induction exponent with
  | zero =>
      change (x + y) ^ 0 = term 0 0 + 0
      exact (pow_zero (x + y)).trans
        ((_root_.add_zero (term 0 0)).trans
          ((firstTerm 0).trans (pow_zero x))).symm
  | succ exponent inductionHypothesis =>
      have shiftedLast :
          Prefix.prefixSum (exponent + 1)
              (fun index => term exponent (index + 1)) =
            Prefix.prefixSum exponent
              (fun index => term exponent (index + 1)) := by
        rw [Prefix.prefixSum_succ_last,
          afterLastTerm exponent, add_zero]
      have previousExpansion :
          binomialExpansion exponent x y =
            x ^ exponent +
              Prefix.prefixSum exponent
                (fun index => term exponent (index + 1)) := by
        unfold binomialExpansion
        change Prefix.prefixSum (exponent + 1) (term exponent) = _
        rw [Prefix.prefixSum_succ, firstTerm]
      have previousSum :
          Prefix.prefixSum (exponent + 1) (term exponent) =
            binomialExpansion exponent x y := by
        unfold binomialExpansion
        rfl
      have nextExpansion :
          binomialExpansion (Nat.succ exponent) x y =
            x ^ Nat.succ exponent +
              y * Prefix.prefixSum (exponent + 1) (term exponent) +
              x * Prefix.prefixSum (exponent + 1)
                (fun index => term exponent (index + 1)) := by
        unfold binomialExpansion
        change Prefix.prefixSum (Nat.succ exponent + 1)
          (term (Nat.succ exponent)) = _
        rw [show Nat.succ exponent + 1 = (exponent + 1) + 1 by omega0,
          Prefix.prefixSum_succ, firstTerm]
        have summedPascal := Prefix.prefixSum_congr
          (K := K) (exponent + 1)
          (fun index => term (exponent + 1) (index + 1))
          (fun index =>
            y * term exponent index + x * term exponent (index + 1))
          (by
            intro index indexBound
            exact pascalStep exponent index (by omega0))
        rw [summedPascal, Prefix.prefixSum_add,
          Prefix.prefixSum_mul_left, Prefix.prefixSum_mul_left]
        ring1
      calc
        (x + y) ^ Nat.succ exponent =
            (x + y) ^ exponent * (x + y) := by
          rw [pow_succ]
        _ = binomialExpansion exponent x y * (x + y) := by
          rw [inductionHypothesis]
        _ = binomialExpansion (Nat.succ exponent) x y := by
          rw [nextExpansion, previousSum, previousExpansion, shiftedLast,
            pow_succ]
          ring1

/-- Expand a natural power of two ring elements as their bounded binomial sum.

The first exponent descends while the second ascends through the requested finite degree. -/
theorem example_2_7 (exponent : Nat) (x₁ x₂ : K) :
    (x₁ + x₂) ^ exponent =
      binomialExpansion exponent x₁ x₂ :=
  binomial_theorem exponent x₁ x₂

/-- A finite binomial power reduces to its two endpoints when all interior coefficients vanish.

The exponent is nonzero and each strictly interior natural binomial coefficient casts to zero in the commutative ring.
-/
theorem add_pow_eq_endpoints_of_interior_choose_cast_zero
    {S : Type*} [CommRing S]
    (exponent : Nat) (exponentNonzero : exponent ≠ 0)
    (interiorZero : ∀ index : Nat, index ≠ 0 → index < exponent →
      (exponent.choose index : S) = 0)
    (left right : S) :
    (left + right) ^ exponent = left ^ exponent + right ^ exponent := by
  obtain ⟨last, exponentEquation⟩ := Nat.exists_eq_succ_of_ne_zero
    exponentNonzero
  subst exponent
  let term : Nat → S := fun index =>
    right ^ index * left ^ (last + 1 - index) *
      ((last + 1).choose index : S)
  have firstTerm : term 0 = left ^ (last + 1) := by
    unfold term
    rewrite [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one]
    exact (congrArg (fun value : S => value * 1)
      (_root_.one_mul (left ^ (last + 1)))).trans
        (_root_.mul_one (left ^ (last + 1)))
  have lastTerm : term (last + 1) = right ^ (last + 1) := by
    unfold term
    rewrite [Nat.sub_self, pow_zero, Choose.choose_self, Nat.cast_one]
    exact (_root_.mul_one (right ^ (last + 1) * 1)).trans
      (_root_.mul_one (right ^ (last + 1)))
  have interiorTermZero (index : Nat) (indexBelow : index < last) :
      term (index + 1) = 0 := by
    have castZero : (((last + 1).choose (index + 1) : Nat) : S) = 0 :=
      interiorZero (index + 1) (by omega0) (by omega0)
    unfold term
    rw [castZero, mul_zero]
  have middleSumZero :
      Prefix.prefixSum last (fun index => term (index + 1)) = 0 := by
    calc
      Prefix.prefixSum last (fun index => term (index + 1)) =
          Prefix.prefixSum last (fun _ : Nat => (0 : S)) := by
            apply Prefix.prefixSum_congr
            intro index indexBelow
            exact interiorTermZero index indexBelow
      _ = 0 := Prefix.prefixSum_zero_values last
  rw [binomial_theorem]
  unfold binomialExpansion
  change Prefix.prefixSum (last + 1 + 1) term = _
  rw [Prefix.prefixSum_succ_last, Prefix.prefixSum_succ, firstTerm,
    middleSumZero, lastTerm]
  rewrite [_root_.add_zero]
  exact Eq.refl _

end

end Purelib.Algebra.Binomial
