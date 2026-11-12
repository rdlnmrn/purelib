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
    (gaussianProbePoints count).length = count := by
  exact (List.Map.length_map (fun value : Nat => (value : Gaussian.Basic.Canonical))
    (List.range count)).trans (List.Range.Basic.length_range count)

/-- The natural-number Gaussian probes are pairwise distinct.

Equality of two Gaussian natural casts identifies their real rational
casts and therefore their original natural values. The retained natural
range has no repeated entries. -/
public theorem gaussianProbePoints_nodup (count : Nat) :
    (gaussianProbePoints count).Nodup := open Purelib in open Purelib.Data.Rat in by
  unfold gaussianProbePoints
  apply Data.List.Nodup.nodup_map_of_injective
    (function := fun value : Nat => (value : Gaussian.Basic.Canonical))
  · intro left right equal
    have realEqual := congrArg (fun value : Gaussian.Basic.Canonical => value.re) equal
    simp only [Gaussian.Cast.natCast_re] at realEqual
    exact Fraction.Cast.Compatibility.natCast_injective_direct realEqual
  · exact Data.List.Range.Nodup.range_nodup count

/-- Zero evaluation on the coefficient-sized finite probe grid certifies coefficient zero.

The retained finite root bound excludes a nonzero coefficient table with as
many distinct displayed zeros as its coefficient count. -/
public theorem isZero_of_grid_zero (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (zeros : ∀ point ∈ gaussianProbePoints polynomial.degreeCount, polynomial.eval point = 0) :
    polynomial.isZero = true := by
  by_cases zero : polynomial.isZero = true
  · exact zero
  · have nonzero : polynomial.isZero = false :=
      Bool.Decide.bool_eq_false_of_not_eq_true _ zero
    have tooMany := RootBound.Extensionality.nodup_zeros_length_lt_degreeCount polynomial nonzero
      (gaussianProbePoints polynomial.degreeCount) (gaussianProbePoints_nodup _) zeros
    rewrite [gaussianProbePoints_length] at tooMany
    exact False.elim (Nat.lt_irrefl _ tooMany)

/-- An all-input scalar zero law provides the finite coefficient-zero certificate. -/
public theorem isZero_of_eval_eq_zero (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (zero : ∀ point : Gaussian.Basic.Canonical, polynomial.eval point = 0) : polynomial.isZero = true :=
  isZero_of_grid_zero polynomial (fun point _ => zero point)

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
  have differenceZero : (left - right).isZero = true :=
    isZero_of_eval_eq_zero (left - right) (fun point => by
      rewrite [Basic.DensePolynomial.eval_sub, equal point]
      exact Gaussian.Basic.sub_self _)
  exact Extensionality.normalized_eq_of_sub_isZero
    leftNormalized rightNormalized differenceZero

/-- Adding the difference from a base polynomial recovers a normalized target polynomial.

At each supplied Gaussian point, the same scalar addition/subtraction
recovers the target evaluation. Finite normalized coefficient extensionality
then identifies the retained polynomial expressions. -/
public theorem add_sub_left_eq_of_normalized
    (base later : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (laterNormalized : later.normalize = later) :
    base + (later - base) = later := by
  apply gaussian_normalized_eq_of_eval_eq
  · exact Basic.DensePolynomial.normalize_add _ _
  · exact laterNormalized
  · intro point
    rw [Basic.DensePolynomial.eval_add,
      Basic.DensePolynomial.eval_sub]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1

/-- A finite probe bank on the strictly positive real Gaussian axis.

The retained indices are exactly the original range followed by successor
and natural Gaussian inclusion. Zero is absent from the actual probe data. -/
@[expose] public def positiveProbePoints (count : Nat) : List Gaussian.Basic.Canonical :=
  (List.range count).map (fun value => ((value + 1 : Nat) : Gaussian.Basic.Canonical))

/-- The positive Gaussian probe bank has exactly the requested finite length. -/
public theorem positiveProbePoints_length (count : Nat) :
    (positiveProbePoints count).length = count :=
  (List.Map.length_map _ _).trans (List.Range.Basic.length_range count)

/-- The actual positive Gaussian probe list has no repeated entries. -/
public theorem positiveProbePoints_nodup (count : Nat) :
    (positiveProbePoints count).Nodup := by
  apply List.Nodup.nodup_map_of_injective
    (function := fun value : Nat => ((value + 1 : Nat) : Gaussian.Basic.Canonical))
  · intro left right equal
    have realEqual := congrArg (fun value : Gaussian.Basic.Canonical => value.re) equal
    rewrite [Gaussian.Cast.natCast_re, Gaussian.Cast.natCast_re] at realEqual
    exact Nat.succ.inj (Fraction.Cast.Compatibility.natCast_injective_direct realEqual)
  · exact List.Range.Nodup.range_nodup count

/-- Every retained positive Gaussian probe is nonzero. -/
public theorem positiveProbePoints_nonzero (count : Nat)
    (point : Gaussian.Basic.Canonical) (member : point ∈ positiveProbePoints count) : point ≠ 0 := by
  obtain ⟨value, _, pointEq⟩ := List.Map.mem_map.mp member
  intro pointZero
  have realZero := congrArg (fun value : Gaussian.Basic.Canonical => value.re)
    (pointEq.trans pointZero)
  rewrite [Gaussian.Cast.natCast_re] at realZero
  have impossible : value + 1 = 0 := Fraction.Cast.Compatibility.natCast_injective_direct realZero
  exact Nat.succ_ne_zero value impossible

/-- Vanishing on the coefficient-sized positive grid certifies zero original coefficients. -/
public theorem isZero_of_positive_grid_zero (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (zeros : ∀ point ∈ positiveProbePoints polynomial.degreeCount, polynomial.eval point = 0) :
    polynomial.isZero = true := by
  by_cases zero : polynomial.isZero = true
  · exact zero
  · have nonzero := Bool.Decide.bool_eq_false_of_not_eq_true _ zero
    have tooMany := RootBound.Extensionality.nodup_zeros_length_lt_degreeCount polynomial nonzero
      (positiveProbePoints polynomial.degreeCount) (positiveProbePoints_nodup _) zeros
    rewrite [positiveProbePoints_length] at tooMany
    exact (Nat.lt_irrefl _ tooMany).elim

/-- Equality away from zero identifies the original normalized Gaussian coefficient tables.

Only the actual coefficient-sized positive probe bank is used in the proof.
No value at zero is inferred from an expression with a zero-input guard. -/
public theorem gaussian_normalized_eq_of_eval_eq_nonzero
    {left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (leftNormalized : left.normalize = left) (rightNormalized : right.normalize = right)
    (equal : ∀ point : Gaussian.Basic.Canonical, point ≠ 0 → left.eval point = right.eval point) :
    left = right := by
  have differenceZero := isZero_of_positive_grid_zero (left - right) (fun point member => by
    rewrite [Basic.DensePolynomial.eval_sub, equal point (positiveProbePoints_nonzero _ point member)]
    exact Gaussian.Basic.sub_self _)
  exact Extensionality.normalized_eq_of_sub_isZero leftNormalized rightNormalized differenceZero

end Purelib.Polynomial.Dense.Gaussian.Extensionality
