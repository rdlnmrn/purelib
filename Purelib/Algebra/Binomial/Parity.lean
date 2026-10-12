module
import Purelib.Algebra.Binomial
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.FiniteSum.Prefix

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Data.Nat.Choose.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra.FiniteSum

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: the alternating binomial formula

Exercise 8.6 is proved by expanding the two finite powers in Theorem 59 and
pairing their even and odd terms.  Every sum below has an explicit natural
bound and is implemented by primitive recursion.
-/

namespace Purelib.Algebra.Binomial

variable {K : Type*} [ExplicitField K]

namespace Parity

/-- Negating a ring element leaves every displayed even power unchanged. -/
public theorem neg_pow_even {R : Type*} [CommRing R]
    (value : R) (half : Nat) :
    (-value) ^ (half + half) = value ^ (half + half) := by
  calc
    (-value) ^ (half + half) = (-value) ^ (2 * half) := by
      congr 1
      omega0
    _ = ((-value) ^ 2) ^ half := by rw [pow_mul]
    _ = (value ^ 2) ^ half := by
      congr 1
      ring1
    _ = value ^ (2 * half) := by rw [pow_mul]
    _ = value ^ (half + half) := by
      congr 1
      omega0

open Purelib.Algebra.Binomial in
/-- A displayed odd power of a negative ring element is the negative of the original power. -/
public theorem neg_pow_odd {R : Type*} [CommRing R]
    (value : R) (half : Nat) :
    (-value) ^ (half + half + 1) = -value ^ (half + half + 1) := by
  calc
    (-value) ^ (half + half + 1) =
        (-value) ^ (half + half) * (-value) := by rw [pow_succ]
    _ = value ^ (half + half) * (-value) := by rw [Parity.neg_pow_even]
    _ = -(value ^ (half + half) * value) := by ring1
    _ = -value ^ (half + half + 1) := by rw [pow_succ]

end Parity
/-- Compute one finite binomial term for a center and offset.

The offset has the selected index power and the center has the remaining exponent, multiplied by the cast natural
binomial coefficient. -/
public def binomialTerm {R : Type*} [CommRing R]
    (exponent : Nat) (center offset : R) (index : Nat) : R :=
  offset ^ index * center ^ (exponent - index) *
    (exponent.choose index : R)
namespace Parity

section
open Purelib.Algebra.Binomial
/-- Adding opposite-offset even-index terms doubles the original binomial term. -/
private theorem pairedBinomialTerm_even
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half) +
        binomialTerm exponent center (-offset) (half + half) =
      2 * binomialTerm exponent center offset (half + half) := by
  unfold binomialTerm
  rw [Parity.neg_pow_even]
  ring1

/-- Adding opposite-offset odd-index binomial terms gives zero. -/
private theorem pairedBinomialTerm_odd
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half + 1) +
        binomialTerm exponent center (-offset) (half + half + 1) = 0 := by
  unfold binomialTerm
  rw [Parity.neg_pow_odd]
  ring1

end

/-- The sum of two opposite-offset even powers retains only even-index binomial terms.

The explicit half-index gives the exponent, and the bounded sum contains half plus one terms, each doubled. -/
theorem symmetric_binomial_even
    {R : Type*} [CommRing R]
    (half : Nat) (center offset : R) :
    (center + offset) ^ (half + half) +
        (center - offset) ^ (half + half) =
      2 * Prefix.prefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half - (index + index)) *
          ((half + half).choose (index + index) : R)) := open Purelib.Algebra.Binomial in open Purelib.Algebra in by
  let exponent := half + half
  let combined := fun index : Nat =>
    binomialTerm exponent center offset index +
      binomialTerm exponent center (-offset) index
  let evenTerm := fun index : Nat =>
    binomialTerm exponent center offset (index + index)
  have expansion :
      (center + offset) ^ exponent + (center - offset) ^ exponent =
        Prefix.prefixSum (exponent + 1) combined := by
    calc
      (center + offset) ^ exponent + (center - offset) ^ exponent =
          (center + offset) ^ exponent +
            (center + -offset) ^ exponent := by
              congr 2
              ring1
      _ = Binomial.binomialExpansion exponent center offset +
          Binomial.binomialExpansion exponent center (-offset) := by
            rw [Binomial.binomial_theorem,
              Binomial.binomial_theorem]
      _ = Prefix.prefixSum (exponent + 1) combined := by
        unfold Binomial.binomialExpansion combined binomialTerm
        rw [Prefix.prefixSum_add]
  have grouped :
      Prefix.prefixSum half (fun index =>
          combined (index + index) + combined (index + index + 1)) =
        Prefix.prefixSum half (fun index => 2 * evenTerm index) := by
    apply Prefix.prefixSum_congr
    intro index indexBound
    unfold combined evenTerm
    rw [Parity.pairedBinomialTerm_even,
      Parity.pairedBinomialTerm_odd]
    ring1
  calc
    (center + offset) ^ (half + half) +
        (center - offset) ^ (half + half) =
      Prefix.prefixSum (exponent + 1) combined := expansion
    _ = Prefix.prefixSum half (fun index =>
          combined (index + index) + combined (index + index + 1)) +
        combined (half + half) := by
          unfold exponent
          rw [Prefix.prefixSum_pairs_and_last]
    _ = Prefix.prefixSum half (fun index => 2 * evenTerm index) +
        2 * evenTerm half := by
          rw [grouped]
          unfold combined evenTerm
          rw [Parity.pairedBinomialTerm_even]
    _ = 2 * Prefix.prefixSum half evenTerm +
        2 * evenTerm half := by
          rw [Prefix.prefixSum_mul_left]
    _ = 2 * Prefix.prefixSum (half + 1) evenTerm := by
          rw [Prefix.prefixSum_succ_last]
          ring1
    _ = 2 * Prefix.prefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half - (index + index)) *
          ((half + half).choose (index + index) : R)) := rfl

/-- The sum of two opposite-offset odd powers retains only even-index binomial terms.

The exponent is twice the supplied half-index plus one; the bounded sum contains half plus one doubled terms. -/
theorem symmetric_binomial_odd
    {R : Type*} [CommRing R]
    (half : Nat) (center offset : R) :
    (center + offset) ^ (half + half + 1) +
        (center - offset) ^ (half + half + 1) =
      2 * Prefix.prefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half + 1 - (index + index)) *
          ((half + half + 1).choose (index + index) : R)) := open Purelib.Algebra.Binomial in open Purelib.Algebra in by
  let exponent := half + half + 1
  let combined := fun index : Nat =>
    binomialTerm exponent center offset index +
      binomialTerm exponent center (-offset) index
  let evenTerm := fun index : Nat =>
    binomialTerm exponent center offset (index + index)
  have expansion :
      (center + offset) ^ exponent + (center - offset) ^ exponent =
        Prefix.prefixSum (exponent + 1) combined := by
    calc
      (center + offset) ^ exponent + (center - offset) ^ exponent =
          (center + offset) ^ exponent +
            (center + -offset) ^ exponent := by
              congr 2
              ring1
      _ = Binomial.binomialExpansion exponent center offset +
          Binomial.binomialExpansion exponent center (-offset) := by
            rw [Binomial.binomial_theorem,
              Binomial.binomial_theorem]
      _ = Prefix.prefixSum (exponent + 1) combined := by
        unfold Binomial.binomialExpansion combined binomialTerm
        rw [Prefix.prefixSum_add]
  have grouped :
      Prefix.prefixSum (half + 1) (fun index =>
          combined (index + index) + combined (index + index + 1)) =
        Prefix.prefixSum (half + 1)
          (fun index => 2 * evenTerm index) := by
    apply Prefix.prefixSum_congr
    intro index indexBound
    unfold combined evenTerm
    rw [Parity.pairedBinomialTerm_even,
      Parity.pairedBinomialTerm_odd]
    ring1
  calc
    (center + offset) ^ (half + half + 1) +
        (center - offset) ^ (half + half + 1) =
      Prefix.prefixSum (exponent + 1) combined := expansion
    _ = Prefix.prefixSum (half + 1) (fun index =>
        combined (index + index) + combined (index + index + 1)) := by
          unfold exponent
          rw [show half + half + 1 + 1 =
            (half + 1) + (half + 1) by omega0]
          rw [Prefix.prefixSum_pairs]
    _ = Prefix.prefixSum (half + 1)
        (fun index => 2 * evenTerm index) := grouped
    _ = 2 * Prefix.prefixSum (half + 1) evenTerm := by
          rw [Prefix.prefixSum_mul_left]
    _ = 2 * Prefix.prefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half + 1 - (index + index)) *
          ((half + half + 1).choose (index + index) : R)) := rfl

section
open Purelib.Algebra.Binomial
/-- Subtracting opposite-offset even-index binomial terms gives zero. -/
private theorem pairedBinomialTerm_even_difference
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half) -
        binomialTerm exponent center (-offset) (half + half) = 0 := by
  unfold binomialTerm
  rw [Parity.neg_pow_even]
  ring1

/-- Subtracting opposite-offset odd-index terms extracts twice the offset.

The remaining term has the preceding even offset power, unchanged center power and the original odd binomial
coefficient. -/
private theorem pairedBinomialTerm_odd_difference
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half + 1) -
        binomialTerm exponent center (-offset) (half + half + 1) =
      2 * offset *
        (offset ^ (half + half) *
          center ^ (exponent - (half + half + 1)) *
            (exponent.choose (half + half + 1) : R)) := by
  unfold binomialTerm
  rw [Parity.neg_pow_odd, pow_succ]
  ring1

end

/-- The difference of two opposite-offset odd powers retains only odd-index terms.

The finite expansion factors out twice the offset, leaving half plus one terms with even offset powers. -/
theorem antisymmetric_binomial_odd
    {R : Type*} [CommRing R]
    (half : Nat) (center offset : R) :
    (center + offset) ^ (half + half + 1) -
        (center - offset) ^ (half + half + 1) =
      2 * offset * Prefix.prefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half + 1 - (index + index + 1)) *
            ((half + half + 1).choose (index + index + 1) : R)) := open Purelib.Algebra.Binomial in open Purelib.Algebra
              in by
  let exponent := half + half + 1
  let difference := fun index : Nat =>
    binomialTerm exponent center offset index -
      binomialTerm exponent center (-offset) index
  let oddCore := fun index : Nat =>
    offset ^ (index + index) *
      center ^ (exponent - (index + index + 1)) *
        (exponent.choose (index + index + 1) : R)
  have expansion :
      (center + offset) ^ exponent - (center - offset) ^ exponent =
        Prefix.prefixSum (exponent + 1) difference := by
    calc
      (center + offset) ^ exponent - (center - offset) ^ exponent =
          (center + offset) ^ exponent -
            (center + -offset) ^ exponent := by
              congr 2
              ring1
      _ = Binomial.binomialExpansion exponent center offset -
          Binomial.binomialExpansion exponent center (-offset) := by
            rw [Binomial.binomial_theorem,
              Binomial.binomial_theorem]
      _ = Prefix.prefixSum (exponent + 1) difference := by
        unfold Binomial.binomialExpansion difference binomialTerm
        rw [Prefix.prefixSum_sub]
  have grouped :
      Prefix.prefixSum (half + 1) (fun index =>
          difference (index + index) + difference (index + index + 1)) =
        Prefix.prefixSum (half + 1)
          (fun index => 2 * offset * oddCore index) := by
    apply Prefix.prefixSum_congr
    intro index indexBound
    unfold difference oddCore
    rw [Parity.pairedBinomialTerm_even_difference,
      Parity.pairedBinomialTerm_odd_difference]
    ring1
  calc
    (center + offset) ^ (half + half + 1) -
        (center - offset) ^ (half + half + 1) =
      Prefix.prefixSum (exponent + 1) difference := expansion
    _ = Prefix.prefixSum (half + 1) (fun index =>
        difference (index + index) + difference (index + index + 1)) := by
          unfold exponent
          rw [show half + half + 1 + 1 =
            (half + 1) + (half + 1) by omega0]
          rw [Prefix.prefixSum_pairs]
    _ = Prefix.prefixSum (half + 1)
        (fun index => 2 * offset * oddCore index) := grouped
    _ = 2 * offset * Prefix.prefixSum (half + 1) oddCore := by
          rw [Prefix.prefixSum_mul_left]
    _ = 2 * offset * Prefix.prefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half + 1 - (index + index + 1)) *
            ((half + half + 1).choose (index + index + 1) : R)) := rfl

end Parity
end Purelib.Algebra.Binomial

end
