module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Bool.Decide
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Nodup
import Purelib.Data.List.Range.Nodup
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Extensionality
public import Purelib.Polynomial.Dense.RootBound

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# A finite rational evaluation grid

The original natural prefix, cast to constructive rationals, retains its
length and distinct entries. A grid as long as the difference's coefficient
count suffices to identify normalized coefficient lists by the finite root
bound; no carrier-wide root enumeration is constructed.
-/

namespace Purelib.Polynomial.Dense.Rational.Extensionality

open Purelib.Polynomial.Dense
open Purelib.Data.Rat
open Purelib.Data.Bool
open Purelib.Data.List

/-- The retained descending dense polynomial representation over constructive rationals. -/
public abbrev RationalPolynomial := RootBound.CoefficientPolynomial Fraction.Rational

/-- Cast the original natural prefix to the retained rational evaluation grid.

The finite range keeps its original ascending labels. Casting each label
retains its position and supplies exactly the requested number of points. -/
@[expose] public def rationalPoints (count : Nat) : List Fraction.Rational :=
  List.map (fun value : Nat => (value : Fraction.Rational)) (List.range count)

/-- The rational images of the natural prefix from zero to `count - 1` are pairwise distinct.

Injectivity of the retained natural cast transports the original range's
no-duplicate certificate to those same rational grid entries. -/
public theorem rationalPoints_nodup (count : Nat) :
    (rationalPoints count).Nodup := by
  change ((List.range count).map
    (fun value : Nat => (value : Fraction.Rational))).Nodup
  apply Data.List.Nodup.nodup_map_of_injective
  · intro left right equal
    exact Fraction.Cast.Compatibility.natCast_injective_direct equal
  · exact Range.Nodup.range_nodup count

/-- The bounded rational evaluation grid contains exactly the requested number of points. -/
@[simp] public theorem rationalPoints_length (count : Nat) :
    (rationalPoints count).length = count := by
  change ((List.range count).map
    (fun value : Nat => (value : Fraction.Rational))).length = count
  rw [Map.length_map, Range.Basic.length_range]

/-- Equality at every constructive rational point identifies normalized dense coefficient lists.

The original bounded rational prefix has exactly the coefficient count of the
difference. The finite root bound forces that difference to vanish, and the
retained normalization witnesses identify the two input coefficient lists. -/
public theorem rational_normalized_eq_of_eval_eq
    {left right : RationalPolynomial}
    (leftNormalized : left.normalize = left)
    (rightNormalized : right.normalize = right)
    (equal : ∀ point : Fraction.Rational, left.eval point = right.eval point) :
    left = right := by
  have differenceZero : (left - right).isZero = true := by
    by_cases zero : (left - right).isZero = true
    · exact zero
    · have nonzero : (left - right).isZero = false :=
        Decide.bool_eq_false_of_not_eq_true _ zero
      have zeros : ∀ point ∈ rationalPoints (left - right).degreeCount,
          (left - right).eval point = 0 := by
        intro point member
        rw [Basic.DensePolynomial.eval_sub, equal point]
        ring0
      have tooMany := RootBound.Extensionality.nodup_zeros_length_lt_degreeCount
        (left - right) nonzero
        (rationalPoints (left - right).degreeCount)
        (rationalPoints_nodup _) zeros
      rw [rationalPoints_length] at tooMany
      exact (Nat.lt_irrefl _ tooMany).elim
  exact Extensionality.normalized_eq_of_sub_isZero leftNormalized rightNormalized
    differenceZero

end Purelib.Polynomial.Dense.Rational.Extensionality
