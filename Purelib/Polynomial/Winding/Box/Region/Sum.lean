module
public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

open Purelib.Data
open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Finite sums of clear-region winding

The original ordered list of clear regions determines an integer raw-winding
sum. Concatenation, nonnegative contributions and zero totals have direct
finite-list certificates retaining each original region occurrence.
-/

namespace Purelib.Polynomial.Winding.Box.Region.Sum

/-- Sum raw windings over the original finite clear-region list.

Mapping preserves the region order and reads the same polynomial winding from
each retained box before the original integer sum consumes the list. -/
@[expose] public def totalRaw
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (regions : List (Clearance.Box.Region.ClearRegion p ambient)) : Int :=
  (regions.map fun region => Winding.Box.Basic.quadrupledBoxWinding p region.box).sum

/-- The empty list of clear cells has total raw winding zero. -/
@[simp] public theorem totalRaw_nil
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} :
    totalRaw ([] : List (Clearance.Box.Region.ClearRegion p ambient)) = 0 := rfl

/-- Prepending a clear cell adds its raw winding to the tail total. -/
@[simp] public theorem totalRaw_cons
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (region : Clearance.Box.Region.ClearRegion p ambient) (regions : List (Clearance.Box.Region.ClearRegion p ambient))
      :
    totalRaw (region :: regions) =
      Winding.Box.Basic.quadrupledBoxWinding p region.box + totalRaw regions := rfl

/-- Concatenating two region lists adds their original winding totals.

The mapped list preserves the two original spines. The finite sum identity
uses direct integer zero and associativity certificates. -/
public theorem totalRaw_append
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (left right : List (Clearance.Box.Region.ClearRegion p ambient)) :
    totalRaw (left ++ right) = totalRaw left + totalRaw right := by
  unfold totalRaw
  rewrite [List.Map.map_append]
  exact List.Fold.sum_append Int.Arithmetic.zero_add Int.Arithmetic.add_assoc _ _

/-- Nonnegative winding contributions give a nonnegative region total.

Every original list occurrence must carry its own nonnegative winding bound.
Structural induction adds those scalar bounds in the same retained order. -/
public theorem totalRaw_nonnegative
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (regions : List (Clearance.Box.Region.ClearRegion p ambient))
    (nonnegative : ∀ region ∈ regions,
      0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box) :
    0 ≤ totalRaw regions := by
  induction regions with
  | nil => exact Int.Order.le_refl 0
  | cons head tail inductionHypothesis =>
      rw [totalRaw_cons]
      apply Int.Order.add_nonneg (nonnegative head (List.Mem.head tail))
      exact inductionHypothesis fun region member =>
        nonnegative region (List.Mem.tail head member)

/-- Every member of a nonnegative finite winding sum is zero when the total is zero.

The conclusion concerns the displayed member cell and requires nonnegativity of every contribution in the same list. -/
public theorem rawWinding_eq_zero_of_mem_totalRaw_eq_zero
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (regions : List (Clearance.Box.Region.ClearRegion p ambient))
    (nonnegative : ∀ region ∈ regions,
      0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (totalZero : totalRaw regions = 0)
    {region : Clearance.Box.Region.ClearRegion p ambient} (member : region ∈ regions) :
    Winding.Box.Basic.quadrupledBoxWinding p region.box = 0 := by
  induction regions with
  | nil => nomatch member
  | cons head tail inductionHypothesis =>
      have headNonnegative := nonnegative head (List.Mem.head tail)
      have tailMembers : ∀ value ∈ tail,
          0 ≤ Winding.Box.Basic.quadrupledBoxWinding p value.box := by
        intro value valueMember
        exact nonnegative value (List.Mem.tail head valueMember)
      have tailNonnegative := totalRaw_nonnegative tail tailMembers
      rw [totalRaw_cons] at totalZero
      have headLeTotal : Winding.Box.Basic.quadrupledBoxWinding p head.box ≤
          Winding.Box.Basic.quadrupledBoxWinding p head.box + totalRaw tail := by
        have shifted := Int.Order.add_le_add
          (Int.Order.le_refl (Winding.Box.Basic.quadrupledBoxWinding p head.box))
          tailNonnegative
        rewrite [Int.add_zero] at shifted
        exact shifted
      have headZero : Winding.Box.Basic.quadrupledBoxWinding p head.box = 0 :=
        Int.Order.le_antisymm (totalZero ▸ headLeTotal) headNonnegative
      have tailLeTotal : totalRaw tail ≤
          Winding.Box.Basic.quadrupledBoxWinding p head.box + totalRaw tail := by
        have shifted := Int.Order.add_le_add headNonnegative (Int.Order.le_refl (totalRaw tail))
        rewrite [Int.Arithmetic.zero_add] at shifted
        exact shifted
      have tailZero : totalRaw tail = 0 :=
        Int.Order.le_antisymm (totalZero ▸ tailLeTotal) tailNonnegative
      rcases List.Membership.mem_cons.mp member with rfl | tailMember
      · exact headZero
      · exact inductionHypothesis tailMembers tailZero tailMember
end Purelib.Polynomial.Winding.Box.Region.Sum
