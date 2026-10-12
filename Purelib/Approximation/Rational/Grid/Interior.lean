module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Cast.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.Addition
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.List.OfFn.Nodup

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.List.OfFn
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Normalized rational interior grids

The original endpoint difference divided by the degree bound plus two supplies
a positive spacing. The retained Fin indices select exactly the displayed
interior points, and their original List.ofFn order materializes the grid.
-/

open Purelib
open Purelib.Data.List
open Purelib.Data.Rat
open Fraction.Order

namespace Purelib.Approximation.Rational.Grid.Interior

/-- Compute the normalized rational spacing for a finite interior grid.

The interval width is divided by the degree bound plus two, leaving a gap at each endpoint. -/
@[expose] public def interiorStep (a b : Fraction.Rational) (degreeBound : Nat) : Fraction.Rational :=
  Fraction.Arithmetic.normalizedDiv
    (Fraction.Arithmetic.normalizedSub b a)
    (degreeBound + 2 : Nat)

/-- Compute the indexed interior point using normalized rational arithmetic.

The index selects one of the degree bound plus one equally spaced points strictly between ordered endpoints. -/
@[expose] public def interiorCandidate (a b : Fraction.Rational) (degreeBound : Nat)
    (index : Fin (degreeBound + 1)) : Fraction.Rational :=
  Fraction.Arithmetic.normalizedAdd a
    (Fraction.Arithmetic.normalizedMul (index.val + 1 : Nat)
      (Approximation.Rational.Grid.Interior.interiorStep a b degreeBound))

/-- Enumerate all displayed interior grid points in index order.

The list is built from the original finite index type and contains exactly the degree bound plus one candidates. -/
@[expose] public def interiorCandidates (a b : Fraction.Rational) (degreeBound : Nat) :
    List Fraction.Rational :=
  List.ofFn (Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound)

/-- Strictly ordered endpoints give a positive interior-grid spacing.

The original endpoint difference is strictly positive. Dividing that
same normalized difference by the positive natural degree bound plus two
therefore gives a strictly positive retained spacing. -/
public theorem interiorStep_pos {a b : Fraction.Rational} (less : a < b)
    (degreeBound : Nat) : 0 < Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
  simp only [Approximation.Rational.Grid.Interior.interiorStep, Fraction.Arithmetic.normalizedDiv_eq,
    Fraction.Arithmetic.normalizedSub_eq]
  apply Fraction.Order.Field.div_pos_direct
  · exact Fraction.Order.Arithmetic.sub_pos_direct less
  · exact Purelib.Data.Rat.Cast.Order.natCast_pos (Nat.zero_lt_succ _)

/-- For strictly ordered endpoints, distinct finite indices give distinct interior candidates.

Both candidates use the same left endpoint and positive spacing.
Scalar additive and multiplicative cancellation identify their original
positive successor indices and hence the same bounded Fin entries. -/
public theorem interiorCandidate_injective {a b : Fraction.Rational} (less : a < b)
    (degreeBound : Nat) :
    Function.Injective (Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound) := by
  intro first second equal
  apply Fin.ext
  have productsEqual :
      ((first.val + 1 : Nat) : Fraction.Rational) * Approximation.Rational.Grid.Interior.interiorStep a b degreeBound =
        ((second.val + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
    change Fraction.Arithmetic.normalizedAdd a
        (Fraction.Arithmetic.normalizedMul (first.val + 1 : Nat)
          (Approximation.Rational.Grid.Interior.interiorStep a b degreeBound)) =
      Fraction.Arithmetic.normalizedAdd a
        (Fraction.Arithmetic.normalizedMul (second.val + 1 : Nat)
          (Approximation.Rational.Grid.Interior.interiorStep a b degreeBound)) at equal
    rw [Fraction.Arithmetic.normalizedAdd_eq,
      Fraction.Arithmetic.normalizedAdd_eq,
      Fraction.Arithmetic.normalizedMul_eq,
      Fraction.Arithmetic.normalizedMul_eq] at equal
    calc
      ((first.val + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound =
        (a + ((first.val + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound) - a := by ring1
      _ = (a + ((second.val + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound) - a :=
        congrArg (fun value : Fraction.Rational => value - a) equal
      _ = ((second.val + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by ring1
  have castsEqual := Fraction.Field.mul_right_cancel_of_ne
    (Approximation.Rational.Grid.Interior.interiorStep_pos less degreeBound).ne' productsEqual
  have sumsEqual : first.val + 1 = second.val + 1 := by
    exact Fraction.Cast.Compatibility.natCast_injective_direct castsEqual
  exact Data.Nat.Addition.add_right_cancel sumsEqual

/-- The interior-candidate list contains no duplicates when its endpoints are strictly ordered.

The original List.ofFn enumeration retains exactly the indexed candidate
function. Its injectivity for strictly ordered endpoints excludes repeated
entries without changing the table order. -/
public theorem interiorCandidates_nodup {a b : Fraction.Rational} (less : a < b)
    (degreeBound : Nat) : (Approximation.Rational.Grid.Interior.interiorCandidates a b degreeBound).Nodup :=
  OfFn.Nodup.nodup_ofFn_of_injective
    (function := Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound)
    (Approximation.Rational.Grid.Interior.interiorCandidate_injective less degreeBound)

/-- The interior grid contains exactly the degree bound plus one candidates.

The original Fin domain has size equal to the degree bound plus one.
Materializing that same indexed function with List.ofFn retains exactly
that many entries. -/
@[simp] public theorem interiorCandidates_length (a b : Fraction.Rational)
    (degreeBound : Nat) :
    (Approximation.Rational.Grid.Interior.interiorCandidates a b degreeBound).length = degreeBound + 1 := by
  exact OfFn.Basic.length_ofFn

/-- Multiplying the grid spacing by the degree bound plus two recovers the endpoint difference.

The original positive denominator is the natural degree bound plus two.
Multiplication cancels that nonzero denominator and recovers the same
normalized endpoint difference. -/
public theorem interiorStep_scaled (a b : Fraction.Rational) (degreeBound : Nat) :
    ((degreeBound + 2 : Nat) : Fraction.Rational) *
        Approximation.Rational.Grid.Interior.interiorStep a b degreeBound = b - a := by
  simp only [Approximation.Rational.Grid.Interior.interiorStep, Fraction.Arithmetic.normalizedDiv_eq,
    Fraction.Arithmetic.normalizedSub_eq]
  rw [Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (Purelib.Data.Rat.Cast.Order.natCast_pos (Nat.zero_lt_succ _)).ne'

/-- Every displayed interior candidate lies strictly between the ordered endpoints.

The retained index is positive after its successor increment and is
strictly below the degree bound plus two. Multiplying those comparisons
by the same positive spacing locates its original normalized point. -/
public theorem interiorCandidate_bounds {a b : Fraction.Rational} (less : a < b)
    (degreeBound : Nat) (index : Fin (degreeBound + 1)) :
    a < Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index ∧
      Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index < b := by
  have stepPositive := Approximation.Rational.Grid.Interior.interiorStep_pos less degreeBound
  have indexPositive :
      (0 : Fraction.Rational) < ((index.val + 1 : Nat) : Fraction.Rational) :=
    Purelib.Data.Rat.Cast.Order.natCast_pos (Nat.zero_lt_succ _)
  have offsetPositive : 0 <
      ((index.val + 1 : Nat) : Fraction.Rational) *
        Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
    exact Arithmetic.mul_pos_direct indexPositive stepPositive
  have indexLessNat : index.val + 1 < degreeBound + 2 :=
    Nat.add_lt_add_right index.isLt 1
  have indexLess :
      ((index.val + 1 : Nat) : Fraction.Rational) <
        ((degreeBound + 2 : Nat) : Fraction.Rational) := by
    exact Fraction.Cast.Order.natCast_lt_direct indexLessNat
  have offsetLess :
      ((index.val + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound < b - a := by
    have multiplied := Arithmetic.mul_lt_mul_of_pos_right_direct indexLess stepPositive
    rw [Approximation.Rational.Grid.Interior.interiorStep_scaled] at multiplied
    exact multiplied
  constructor
  · calc
      a = a + 0 := by ring1
      _ < a + ((index.val + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct offsetPositive a
      _ = Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index := by
        symm
        rw [Approximation.Rational.Grid.Interior.interiorCandidate,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedMul_eq]
  · calc
      Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index =
          a + ((index.val + 1 : Nat) : Fraction.Rational) *
            Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
        rw [Approximation.Rational.Grid.Interior.interiorCandidate,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedMul_eq]
      _ < a + (b - a) :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct offsetLess a
      _ = b := by ring1

/-- Each selected point leaves both subintervals no longer than `D+1` candidate spacings.

The original index lies between one and the degree bound plus one.
Its offset and the complementary endpoint difference are each bounded
by the same degree-scaled retained spacing. -/
public theorem interiorCandidate_contraction {a b : Fraction.Rational} (less : a < b)
    (degreeBound : Nat) (index : Fin (degreeBound + 1)) :
    Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index - a ≤
        ((degreeBound + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound ∧
      b - Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index ≤
        ((degreeBound + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
  have stepPositive := Approximation.Rational.Grid.Interior.interiorStep_pos less degreeBound
  have indexUpperNat : index.val + 1 ≤ degreeBound + 1 :=
    Nat.succ_le_iff.mpr index.isLt
  have indexUpper :
      ((index.val + 1 : Nat) : Fraction.Rational) ≤
        ((degreeBound + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct indexUpperNat
  have leftBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      indexUpper stepPositive.le
  have indexLowerNat : 1 ≤ index.val + 1 :=
    Nat.succ_le_succ (Nat.zero_le _)
  have indexLower : (1 : Fraction.Rational) ≤
      ((index.val + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct indexLowerNat
  have offsetLower :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      indexLower stepPositive.le
  have offsetLower' : Approximation.Rational.Grid.Interior.interiorStep a b degreeBound ≤
      ((index.val + 1 : Nat) : Fraction.Rational) *
        Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
    simpa only [one_mul] using offsetLower
  constructor
  · calc
      Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index - a =
          ((index.val + 1 : Nat) : Fraction.Rational) *
            Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
        rw [Approximation.Rational.Grid.Interior.interiorCandidate,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedMul_eq]
        ring1
      _ ≤ ((degreeBound + 1 : Nat) : Fraction.Rational) *
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := leftBound
  · calc
      b - Approximation.Rational.Grid.Interior.interiorCandidate a b degreeBound index =
          (b - a) - ((index.val + 1 : Nat) : Fraction.Rational) *
            Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
        rw [Approximation.Rational.Grid.Interior.interiorCandidate,
          Fraction.Arithmetic.normalizedAdd_eq,
          Fraction.Arithmetic.normalizedMul_eq]
        ring1
      _ ≤ (b - a) - Approximation.Rational.Grid.Interior.interiorStep a b degreeBound :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct offsetLower' (b - a)
      _ = ((degreeBound + 2 : Nat) : Fraction.Rational) *
            Approximation.Rational.Grid.Interior.interiorStep a b degreeBound -
          Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
        rw [Approximation.Rational.Grid.Interior.interiorStep_scaled]
      _ = ((degreeBound + 1 : Nat) : Fraction.Rational) *
            Approximation.Rational.Grid.Interior.interiorStep a b degreeBound := by
        have successorCast : ((degreeBound + 2 : Nat) : Fraction.Rational) =
            ((degreeBound + 1 : Nat) : Fraction.Rational) + 1 := by
          calc
            ((degreeBound + 2 : Nat) : Fraction.Rational) =
                Fraction.Cast.fromInt ((degreeBound + 2 : Nat) : Int) :=
              Fraction.Cast.natCast_eq_fromInt _
            _ = Fraction.Cast.fromInt ((degreeBound + 1 : Nat) : Int) +
                Fraction.Cast.fromInt 1 :=
              (Fraction.Cast.add_fromInt ((degreeBound + 1 : Nat) : Int) 1).symm
            _ = ((degreeBound + 1 : Nat) : Fraction.Rational) + 1 :=
              congrArg (fun value : Fraction.Rational => value + 1)
                (Fraction.Cast.natCast_eq_fromInt (degreeBound + 1)).symm
        rw [successorCast]
        ring1

end Purelib.Approximation.Rational.Grid.Interior
