module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Cast
import Purelib.Data.List.Nodup
import Purelib.Data.List.Range.Nodup
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Extensionality
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.RootBound
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Bool.Decide
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

/-!
# Finite Gaussian probes and normalized coefficient extensionality

The original finite natural-cast probe prefix retains its count and distinct
Gaussian values. Those exact probes identify represented zero from a supplied
evaluation equation and recover the original normalized coefficient lists.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Extensionality

/-- A bounded list of pairwise distinct Gaussian-rational probes.

The original natural range is mapped to its Gaussian natural casts.
This preserves the supplied count, increasing order and exact finite
probe values. -/
@[expose] public def gaussianProbePoints (count : Nat) : List Gaussian.Basic.Canonical :=
  List.map (fun value : Nat => (value : Gaussian.Basic.Canonical)) (List.range count)

/-- The finite Gaussian probe list has exactly the requested length.

The finite natural range has the supplied count. Mapping its entries
to the same Gaussian natural casts preserves that original length. -/
@[simp] public theorem gaussianProbePoints_length (count : Nat) :
    (Dense.Gaussian.Extensionality.gaussianProbePoints count).length = count := by
  exact (List.Map.length_map (fun value : Nat => (value : Gaussian.Basic.Canonical))
    (List.range count)).trans (List.Range.Basic.length_range count)

/-- The natural-number Gaussian probes are pairwise distinct.

Equality of two Gaussian natural casts identifies their real rational
casts and therefore their original natural values. The retained natural
range has no repeated entries. -/
public theorem gaussianProbePoints_nodup (count : Nat) :
    (Dense.Gaussian.Extensionality.gaussianProbePoints count).Nodup := open Purelib in open Purelib.Data.Rat in by
  unfold Dense.Gaussian.Extensionality.gaussianProbePoints
  apply Data.List.Nodup.nodup_map_of_injective
    (function := fun value : Nat => (value : Gaussian.Basic.Canonical))
  · intro left right equal
    have realEqual := congrArg (fun value : Gaussian.Basic.Canonical => value.re) equal
    simp only [Gaussian.Cast.natCast_re] at realEqual
    exact Fraction.Cast.Compatibility.natCast_injective_direct realEqual
  · exact Data.List.Range.Nodup.range_nodup count

/-- Equality on every Gaussian rational identifies normalized coefficient
lists.  The proof uses only the displayed probe prefix whose length is the
coefficient count of the difference.

The displayed pointwise evaluation equality makes every retained probe
a zero of the polynomial difference. Its finite coefficient-count-many
distinct probes force represented zero and the original normalized coefficient equality. -/
public theorem gaussian_normalized_eq_of_eval_eq
    {left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (leftNormalized : left.normalize = left)
    (rightNormalized : right.normalize = right)
    (equal : ∀ point : Gaussian.Basic.Canonical, left.eval point = right.eval point) :
    left = right := by
  have differenceZero : (left - right).isZero = true := by
    by_cases zero : (left - right).isZero = true
    · exact zero
    · have nonzero : (left - right).isZero = false :=
        Bool.Decide.bool_eq_false_of_not_eq_true _ zero
      have zeros : ∀ point ∈
          Dense.Gaussian.Extensionality.gaussianProbePoints (left - right).degreeCount,
          (left - right).eval point = 0 := by
        intro point member
        rw [Dense.Basic.DensePolynomial.eval_sub, equal point]
        exact Gaussian.Basic.sub_self _
      have tooMany :=
        Dense.RootBound.Extensionality.nodup_zeros_length_lt_degreeCount
          (left - right) nonzero
          (Dense.Gaussian.Extensionality.gaussianProbePoints (left - right).degreeCount)
          (Dense.Gaussian.Extensionality.gaussianProbePoints_nodup _) zeros
      rw [Dense.Gaussian.Extensionality.gaussianProbePoints_length] at tooMany
      exact (Nat.lt_irrefl _ tooMany).elim
  exact Dense.Extensionality.normalized_eq_of_sub_isZero
    leftNormalized rightNormalized differenceZero

/-- Adding the difference from a base polynomial recovers a normalized target polynomial.

At each supplied Gaussian point, the same scalar addition/subtraction
recovers the target evaluation. Finite normalized coefficient extensionality
then identifies the retained polynomial expressions. -/
public theorem add_sub_left_eq_of_normalized
    (base later : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (laterNormalized : later.normalize = later) :
    base + (later - base) = later := by
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq
  · exact Dense.Basic.DensePolynomial.normalize_add _ _
  · exact laterNormalized
  · intro point
    rw [Dense.Basic.DensePolynomial.eval_add,
      Dense.Basic.DensePolynomial.eval_sub]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1

end Purelib.Polynomial.Dense.Gaussian.Extensionality
