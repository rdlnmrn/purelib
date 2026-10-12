module
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Multiplication

import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Mathlib.Data.Bool.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.List.Zip
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Addition
import Purelib.Data.Nat.Order

/-!
# Finite leading-term bookkeeping for dense polynomials

These predicates retain normalized finite coefficient counts and displayed
leading coefficients. Their closure laws transport those readbacks through
the original dense addition, multiplication, scaling and shift programs.
-/

namespace Purelib.Polynomial.Dense.Leading

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense
open Purelib.Data.List
open Purelib.Data.Nat

/-- The descending dense polynomial representation whose normalized leading term is certified here. -/
public abbrev CoefficientPolynomial (K : Type*) :=
  Basic.DensePolynomial K

open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- A normalized nonzero polynomial with a specified degree and leading coefficient.

The certificate retains ordinary equalities to the executable degree and coefficient readbacks. -/
public structure LeadingTerm (p : CoefficientPolynomial K) (degree : Nat)
    (coefficient : K) : Prop where
  /-- The polynomial already has its leading zeros removed. -/ normalized : p.normalize = p
  /-- The normalized coefficient list is nonempty. -/ nonzero : p.isZero = false
  /-- The executable natural degree equals the displayed degree. -/ degree_eq : p.natDegree = degree
  /-- The executable leading coefficient equals the displayed coefficient. -/ coefficient_eq : p.leadingCoeff =
    coefficient

/-- A normalized dense polynomial with at most `degree + 1` coefficient slots.

This finite count convention includes the zero polynomial without assigning it a separate degree value. -/
public structure DegreeAtMost (p : CoefficientPolynomial K) (degree : Nat) : Prop where
  /-- The polynomial already has its leading zeros removed. -/ normalized : p.normalize = p
  /-- The normalized coefficient count is at most one more than the displayed degree bound. -/ count_le : p.degreeCount
    ≤ degree + 1

/-- A normalized dense polynomial with at most `degree` coefficient slots.

For a nonzero polynomial this states strict degree inequality, while the empty zero representation is admitted at every
bound. -/
public structure DegreeBelow (p : CoefficientPolynomial K) (degree : Nat) : Prop where
  /-- The polynomial already has its leading zeros removed. -/ normalized : p.normalize = p
  /-- The normalized coefficient count is at most the displayed strict degree threshold. -/ count_le : p.degreeCount ≤
    degree

namespace LeadingTerm

/-- Transport a displayed leading-term certificate across three ordinary equalities.

The original polynomial, degree and coefficient equalities retain the same
certificate fields after constructor transport. -/
public theorem of_equal {p q : CoefficientPolynomial K} {degree otherDegree : Nat}
    {coefficient otherCoefficient : K}
    (polynomialEqual : p = q) (degreeEqual : degree = otherDegree)
    (coefficientEqual : coefficient = otherCoefficient)
    (leading : LeadingTerm q otherDegree otherCoefficient) :
    LeadingTerm p degree coefficient := by
  cases polynomialEqual
  cases degreeEqual
  cases coefficientEqual
  exact leading

/-- A normalized nonzero representative carries its executable leading term.

Repeated normalization preserves its original coefficient list. The degree,
nonempty zero-test and head-coefficient readbacks therefore agree. -/
public theorem normalizeSelf {p : CoefficientPolynomial K} (nonzero : p.isZero = false) :
    LeadingTerm p.normalize p.natDegree p.leadingCoeff where
  normalized := Basic.DensePolynomial.normalize_normalize p
  nonzero := by simpa only [Basic.DensePolynomial.isZero_normalize] using nonzero
  degree_eq := Basic.DensePolynomial.natDegree_normalize p
  coefficient_eq := by
    change p.normalize.normalize.coeffs.headD 0 =
      p.normalize.coeffs.headD 0
    rw [Basic.DensePolynomial.normalize_normalize]

/-- A normalized nonzero polynomial carries its displayed leading term. -/
public theorem ofNormalized {p : CoefficientPolynomial K} (nonzero : p.isZero = false)
    (normalized : p.normalize = p) :
    LeadingTerm p p.natDegree p.leadingCoeff where
  normalized := normalized
  nonzero := nonzero
  degree_eq := rfl
  coefficient_eq := rfl

/-- A displayed nonzero leading term fixes the coefficient count to its degree plus one. -/
public theorem count_eq {p : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) :
    p.degreeCount = degree + 1 := by
  rw [← leading.degree_eq]
  exact (Basic.DensePolynomial.natDegree_add_one_eq_degreeCount leading.nonzero).symm

/-- The coefficient in a displayed leading-term certificate is nonzero. -/
public theorem coefficient_ne_zero
    {p : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) : coefficient ≠ 0 := by
  rw [← leading.coefficient_eq]
  exact Basic.DensePolynomial.leadingCoeff_ne_zero leading.nonzero

/-- Forget the exact leading coefficient and retain its non-strict degree bound. -/
public theorem atMost {p : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) : DegreeAtMost p degree :=
  { normalized := leading.normalized
    count_le := leading.count_eq.le }

/-- Multiply displayed leading terms, adding degrees and multiplying coefficients.

The original dense product preserves nonzero normalized heads. Its retained
natural-degree and leading-coefficient certificates give the two scalar readbacks. -/
public theorem mul {p q : CoefficientPolynomial K} {pDegree qDegree : Nat}
    {pCoefficient qCoefficient : K}
    (left : LeadingTerm p pDegree pCoefficient)
    (right : LeadingTerm q qDegree qCoefficient) :
    LeadingTerm (p * q) (pDegree + qDegree)
      (pCoefficient * qCoefficient) where
  normalized := Basic.DensePolynomial.normalize_mul p q
  nonzero := Basic.DensePolynomial.isZero_mul_eq_false left.nonzero right.nonzero
  degree_eq := by
    rw [Basic.DensePolynomial.natDegree_mul left.nonzero right.nonzero,
      left.degree_eq, right.degree_eq]
  coefficient_eq := by
    rw [Basic.DensePolynomial.leadingCoeff_mul left.nonzero right.nonzero,
      left.coefficient_eq, right.coefficient_eq]

/-- A nonzero constant polynomial has degree zero and its constant as leading coefficient.

The same singleton normalization certificate fixes the zero test, natural
degree and head coefficient of the original constant display. -/
public theorem constant {a : K} (nonzero : a ≠ 0) :
    LeadingTerm (Basic.DensePolynomial.constant a) 0 a where
  normalized := Basic.DensePolynomial.normalize_constant_of_ne nonzero
  nonzero := by
    change (Basic.DensePolynomial.constant a).normalize.coeffs.isEmpty = false
    rewrite [Basic.DensePolynomial.normalize_constant_of_ne nonzero]
    exact Eq.refl _
  degree_eq := by
    change (Basic.DensePolynomial.constant a).normalize.coeffs.length - 1 = 0
    rewrite [Basic.DensePolynomial.normalize_constant_of_ne nonzero]
    exact Eq.refl _
  coefficient_eq := by
    change (Basic.DensePolynomial.constant a).normalize.coeffs.headD 0 = a
    rewrite [Basic.DensePolynomial.normalize_constant_of_ne nonzero]
    exact Eq.refl _

/-- Negation preserves degree and negates the displayed leading coefficient.

The original normalized negation has the same coefficient count and nonempty
zero test, with the scalar-negative retained leading coefficient. -/
public theorem neg {p : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) :
    LeadingTerm (-p) degree (-coefficient) where
  normalized := Basic.DensePolynomial.normalize_neg p
  nonzero := by simpa only [Basic.DensePolynomial.isZero_neg] using leading.nonzero
  degree_eq := by simpa only [Basic.DensePolynomial.natDegree_neg] using leading.degree_eq
  coefficient_eq := by
    rw [Basic.DensePolynomial.leadingCoeff_neg, leading.coefficient_eq]

/-- Scaling by a nonzero scalar preserves the displayed degree and scales its leading coefficient.

The original scaling map retains the normalized list length. Its nonempty
head gives the same degree and the displayed scalar product coefficient. -/
public theorem scale {p : CoefficientPolynomial K} {degree : Nat} {coefficient scalar : K}
    (scalarNonzero : scalar ≠ 0)
    (leading : LeadingTerm p degree coefficient) :
    LeadingTerm (Basic.DensePolynomial.scale scalar p)
      degree (scalar * coefficient) := by
  have coefficientsNonempty : p.normalize.coeffs.isEmpty = false :=
    leading.nonzero
  have scaledCoefficients := Basic.DensePolynomial.scale_coeffs_of_ne_zero scalarNonzero p
  refine
    { normalized := Basic.DensePolynomial.normalize_scale scalar p
      nonzero := ?_
      degree_eq := ?_
      coefficient_eq := ?_ }
  · rw [Basic.DensePolynomial.isZero, Basic.DensePolynomial.normalize_scale, scaledCoefficients]
    cases coefficients : p.normalize.coeffs with
    | nil =>
        rw [coefficients] at coefficientsNonempty
        exact Bool.noConfusion coefficientsNonempty
    | cons head tail => rfl
  · rw [Basic.DensePolynomial.natDegree, Basic.DensePolynomial.degreeCount, Basic.DensePolynomial.normalize_scale,
      scaledCoefficients,
      Map.length_map]
    have count := leading.count_eq
    change p.normalize.coeffs.length = degree + 1 at count
    rewrite [count]
    exact Subtraction.add_sub_cancel_right degree 1
  · rw [Basic.DensePolynomial.leadingCoeff, Basic.DensePolynomial.normalize_scale, scaledCoefficients]
    cases coefficients : p.normalize.coeffs with
    | nil =>
        rw [coefficients] at coefficientsNonempty
        exact Bool.noConfusion coefficientsNonempty
    | cons head tail =>
        simp only [List.map_cons, List.headD_cons]
        have coefficientIdentity := leading.coefficient_eq
        rw [Basic.DensePolynomial.leadingCoeff, coefficients, List.headD_cons] at coefficientIdentity
        rw [coefficientIdentity]

/-- Appending a power-of-variable shift adds its amount to the degree and preserves the leading coefficient.

The original shift appends the retained zero block to the normalized input.
Its nonzero head remains unchanged, and its length increases by that exact amount. -/
public theorem shift {p : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (amount : Nat) (leading : LeadingTerm p degree coefficient) :
    LeadingTerm (Basic.DensePolynomial.shift amount p)
      (degree + amount) coefficient := by
  have coefficientsIdentity :
      (Basic.DensePolynomial.shift amount p).coeffs =
        p.normalize.coeffs ++ List.replicate amount 0 := by
    have notZero : p.isZero ≠ true := fun zero =>
      Bool.noConfusion (leading.nonzero.symm.trans zero)
    rewrite [Basic.DensePolynomial.shift, if_neg notZero]
    exact Eq.refl _
  have normalized := Basic.DensePolynomial.normalize_shift amount p
  refine
    { normalized := normalized
      nonzero := ?_
      degree_eq := ?_
      coefficient_eq := ?_ }
  · change (Basic.DensePolynomial.shift amount p).normalize.coeffs.isEmpty = false
    rewrite [normalized, coefficientsIdentity]
    cases coefficients : p.normalize.coeffs with
    | nil =>
        have nonempty := leading.nonzero
        change p.normalize.coeffs.isEmpty = false at nonempty
        rewrite [coefficients] at nonempty
        exact Bool.noConfusion nonempty
    | cons head tail => exact Eq.refl _
  · change (Basic.DensePolynomial.shift amount p).normalize.coeffs.length - 1 = degree + amount
    rewrite [normalized, coefficientsIdentity, Append.length_append, Replicate.length_replicate]
    have count := leading.count_eq
    change p.normalize.coeffs.length = degree + 1 at count
    rewrite [count, Nat.succ_add]
    exact Subtraction.add_sub_cancel_right (degree + amount) 1
  · change (Basic.DensePolynomial.shift amount p).normalize.coeffs.headD 0 = coefficient
    rewrite [normalized, coefficientsIdentity]
    cases coefficients : p.normalize.coeffs with
    | nil =>
        have nonempty := leading.nonzero
        change p.normalize.coeffs.isEmpty = false at nonempty
        rewrite [coefficients] at nonempty
        exact Bool.noConfusion nonempty
    | cons head tail =>
        have coefficientIdentity := leading.coefficient_eq
        change p.normalize.coeffs.headD 0 = coefficient at coefficientIdentity
        rewrite [coefficients] at coefficientIdentity
        exact coefficientIdentity

/-- Subtracting a polynomial strictly below a displayed degree preserves the higher leading term.

The original subtraction shape retains the higher polynomial head and its
coefficient count. These readbacks determine the same degree and coefficient. -/
public theorem subBelow {p q : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (left : LeadingTerm p degree coefficient)
    (right : DegreeBelow q degree) :
    LeadingTerm (p - q) degree coefficient := by
  have shorter : q.degreeCount < p.degreeCount := by
    rw [left.count_eq]
    exact Nat.lt_succ_of_le right.count_le
  obtain ⟨out, hcoeffs, hout⟩ :=
    Basic.DensePolynomial.sub_coeffs_shape_of_degreeCount_lt left.nonzero left.normalized shorter
  have outputNonzero : (p - q).isZero = false := by
    rewrite [Basic.DensePolynomial.isZero, Basic.DensePolynomial.normalize_sub, hcoeffs]
    exact Eq.refl _
  refine
    { normalized := Basic.DensePolynomial.normalize_sub p q
      nonzero := outputNonzero
      degree_eq := ?_
      coefficient_eq := ?_ }
  · have outputCount := Basic.DensePolynomial.natDegree_add_one_eq_degreeCount outputNonzero
    have leftCount := left.count_eq
    have exactOutputCount : (p - q).degreeCount = p.degreeCount := by
      rw [Basic.DensePolynomial.degreeCount, Basic.DensePolynomial.normalize_sub, hcoeffs]
      exact hout
    exact Nat.succ.inj
      (outputCount.trans (exactOutputCount.trans leftCount))
  · change (p - q).normalize.coeffs.headD 0 = coefficient
    rw [Basic.DensePolynomial.normalize_sub, hcoeffs]
    simpa only [List.headD_cons] using left.coefficient_eq

end LeadingTerm

namespace DegreeAtMost

/-- Transport a finite degree bound across displayed polynomial and degree equalities.

Constructor transport retains the original normalized polynomial and its same
coefficient-count bound at the identified threshold. -/
public theorem of_equal {p q : CoefficientPolynomial K} {degree otherDegree : Nat}
    (polynomialEqual : p = q) (degreeEqual : degree = otherDegree)
    (bounded : DegreeAtMost q otherDegree) : DegreeAtMost p degree := by
  cases polynomialEqual
  cases degreeEqual
  exact bounded

/-- The empty zero polynomial satisfies every non-strict finite degree bound. -/
public theorem zero (degree : Nat) : DegreeAtMost (0 : CoefficientPolynomial K) degree where
  normalized := rfl
  count_le := Nat.zero_le _

/-- Enlarge a certified non-strict degree bound while preserving normalization. -/
public theorem mono {p : CoefficientPolynomial K} {smaller larger : Nat}
    (bounded : DegreeAtMost p smaller) (less : smaller ≤ larger) :
    DegreeAtMost p larger where
  normalized := bounded.normalized
  count_le := bounded.count_le.trans (Nat.succ_le_succ less)

/-- Multiply two normalized bounded-degree polynomials and add their degree bounds.

The zero branches retain the empty product. In the nonzero branches, scalar
addition and subtraction transport the original multiplication count bound. -/
public theorem mul {p q : CoefficientPolynomial K} {pDegree qDegree : Nat}
    (left : DegreeAtMost p pDegree)
    (right : DegreeAtMost q qDegree) :
    DegreeAtMost (p * q) (pDegree + qDegree) where
  normalized := Basic.DensePolynomial.normalize_mul p q
  count_le := by
    by_cases hp : p.isZero = true
    · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_left hp]
      exact Nat.zero_le _
    · by_cases hq : q.isZero = true
      · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_right hq]
        exact Nat.zero_le _
      · have sumBound := Nat.add_le_add left.count_le right.count_le
        have subtractBound := Nat.sub_le_sub_right sumBound 1
        rewrite [Nat.succ_add, Nat.add_succ] at subtractBound
        change p.degreeCount + q.degreeCount - 1 ≤ (pDegree + qDegree + 1) + 1 - 1 at subtractBound
        rewrite [Subtraction.add_sub_cancel_right] at subtractBound
        exact (Basic.DensePolynomial.degreeCount_mul_le p q).trans subtractBound

/-- Subtract two normalized polynomials sharing a non-strict degree bound.

The maximum of their retained coefficient counts bounds the original
subtraction count and therefore preserves the common threshold. -/
public theorem sub {p q : CoefficientPolynomial K} {degree : Nat}
    (left : DegreeAtMost p degree) (right : DegreeAtMost q degree) :
    DegreeAtMost (p - q) degree where
  normalized := Basic.DensePolynomial.normalize_sub p q
  count_le := by
    exact (Basic.DensePolynomial.degreeCount_sub_le_of_normalized left.normalized).trans
      (Order.max_le left.count_le right.count_le)

/-- A non-strict degree bound becomes a strict bound at its successor. -/
public theorem toBelowSucc {p : CoefficientPolynomial K} {degree : Nat}
    (bounded : DegreeAtMost p degree) : DegreeBelow p (degree + 1) where
  normalized := bounded.normalized
  count_le := bounded.count_le

end DegreeAtMost

namespace DegreeBelow

/-- Transport a strict degree bound across displayed polynomial and degree equalities.

Constructor transport retains the original normalized polynomial and its same
coefficient-count bound at the identified strict threshold. -/
public theorem of_equal {p q : CoefficientPolynomial K} {degree otherDegree : Nat}
    (polynomialEqual : p = q) (degreeEqual : degree = otherDegree)
    (bounded : DegreeBelow q otherDegree) : DegreeBelow p degree := by
  cases polynomialEqual
  cases degreeEqual
  exact bounded

/-- A smaller nonzero natural degree gives the displayed strict coefficient-count bound.

The original count is one more than that natural degree. Its retained strict
comparison therefore bounds the same normalized coefficient list. -/
public theorem ofNatDegreeLt {p : CoefficientPolynomial K} {degree : Nat}
    (nonzero : p.isZero = false) (normalized : p.normalize = p)
    (smaller : p.natDegree < degree) : DegreeBelow p degree where
  normalized := normalized
  count_le := by
    have count := Basic.DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
    omega

/-- The empty zero polynomial satisfies every strict finite degree threshold. -/
public theorem zero (degree : Nat) : DegreeBelow (0 : CoefficientPolynomial K) degree where
  normalized := rfl
  count_le := Nat.zero_le _

/-- Enlarge a certified strict degree threshold while preserving normalization. -/
public theorem mono {p : CoefficientPolynomial K} {smaller larger : Nat}
    (below : DegreeBelow p smaller) (less : smaller ≤ larger) :
    DegreeBelow p larger where
  normalized := below.normalized
  count_le := below.count_le.trans less

/-- Forget strictness of a finite degree bound at the same threshold. -/
public theorem toAtMost {p : CoefficientPolynomial K} {degree : Nat}
    (below : DegreeBelow p degree) : DegreeAtMost p degree where
  normalized := below.normalized
  count_le := below.count_le.trans (Nat.le_succ _)

/-- Negation preserves the strict coefficient-count bound and normalization. -/
public theorem neg {p : CoefficientPolynomial K} {degree : Nat}
    (below : DegreeBelow p degree) : DegreeBelow (-p) degree where
  normalized := Basic.DensePolynomial.normalize_neg p
  count_le := by simpa only [Basic.DensePolynomial.degreeCount_neg] using below.count_le

/-- A strict left degree bound and non-strict right bound yield a strict product bound at their sum.

The original product count is bounded by the sum of the retained input
counts minus one; scalar subtraction gives the displayed strict threshold. -/
public theorem mulAtMost {p q : CoefficientPolynomial K} {pDegree qDegree : Nat}
    (left : DegreeBelow p pDegree)
    (right : DegreeAtMost q qDegree) :
    DegreeBelow (p * q) (pDegree + qDegree) where
  normalized := Basic.DensePolynomial.normalize_mul p q
  count_le := by
    by_cases hp : p.isZero = true
    · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_left hp]
      exact Nat.zero_le _
    · by_cases hq : q.isZero = true
      · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_right hq]
        exact Nat.zero_le _
      · have sumBound := Nat.add_le_add left.count_le right.count_le
        have subtractBound := Nat.sub_le_sub_right sumBound 1
        rewrite [Nat.add_succ] at subtractBound
        change p.degreeCount + q.degreeCount - 1 ≤ (pDegree + qDegree) + 1 - 1 at subtractBound
        rewrite [Subtraction.add_sub_cancel_right] at subtractBound
        exact (Basic.DensePolynomial.degreeCount_mul_le p q).trans subtractBound

/-- A non-strict left degree bound and strict right bound yield a strict product bound at their sum.

The original product count is bounded by the sum of the retained input
counts minus one; scalar subtraction gives the displayed strict threshold. -/
public theorem atMostMul {p q : CoefficientPolynomial K} {pDegree qDegree : Nat}
    (left : DegreeAtMost p pDegree)
    (right : DegreeBelow q qDegree) :
    DegreeBelow (p * q) (pDegree + qDegree) where
  normalized := Basic.DensePolynomial.normalize_mul p q
  count_le := by
    by_cases hp : p.isZero = true
    · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_left hp]
      exact Nat.zero_le _
    · by_cases hq : q.isZero = true
      · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_right hq]
        exact Nat.zero_le _
      · have sumBound := Nat.add_le_add left.count_le right.count_le
        have subtractBound := Nat.sub_le_sub_right sumBound 1
        rewrite [Nat.succ_add] at subtractBound
        change p.degreeCount + q.degreeCount - 1 ≤ (pDegree + qDegree) + 1 - 1 at subtractBound
        rewrite [Subtraction.add_sub_cancel_right] at subtractBound
        exact (Basic.DensePolynomial.degreeCount_mul_le p q).trans subtractBound

/-- Subtract normalized polynomials sharing a strict finite degree threshold.

The maximum of their retained coefficient counts bounds the original
subtraction count and therefore preserves the common threshold. -/
public theorem sub {p q : CoefficientPolynomial K} {degree : Nat}
    (left : DegreeBelow p degree) (right : DegreeBelow q degree) :
    DegreeBelow (p - q) degree where
  normalized := Basic.DensePolynomial.normalize_sub p q
  count_le := by
    exact (Basic.DensePolynomial.degreeCount_sub_le_of_normalized left.normalized).trans
      (Order.max_le left.count_le right.count_le)

end DegreeBelow

namespace LeadingTerm

/-- Equal-degree leading terms add with their nonzero displayed coefficient sum.

The original padding counts both vanish, so the same retained tails are
zipped entry by entry. Their equal lengths fix the resulting coefficient count. -/
public theorem add {p q : CoefficientPolynomial K} {degree : Nat} {leftCoefficient rightCoefficient : K}
    (left : LeadingTerm p degree leftCoefficient)
    (right : LeadingTerm q degree rightCoefficient)
    (sumNonzero : leftCoefficient + rightCoefficient ≠ 0) :
    LeadingTerm (p + q) degree (leftCoefficient + rightCoefficient) := by
  obtain ⟨leftTail, leftCoefficients, leftLength⟩ :=
    Basic.DensePolynomial.normalized_coeffs_shape left.nonzero
  obtain ⟨rightTail, rightCoefficients, rightLength⟩ :=
    Basic.DensePolynomial.normalized_coeffs_shape right.nonzero
  rw [left.normalized, left.coefficient_eq] at leftCoefficients
  rw [right.normalized, right.coefficient_eq] at rightCoefficients
  have leftCount := left.count_eq
  have rightCount := right.count_eq
  have outputCoefficients :
      (p + q).coeffs =
        (leftCoefficient + rightCoefficient) ::
          List.zipWith (· + ·) leftTail rightTail := by
    change (Basic.DensePolynomial.add p q).coeffs = _
    simp only [Basic.DensePolynomial.add,
      leftCoefficients, rightCoefficients, List.length_cons]
    have sameMaximum : max (degree + 1) (degree + 1) = degree + 1 := by
      change (if degree + 1 ≤ degree + 1 then degree + 1 else degree + 1) = degree + 1
      rewrite [if_pos (Nat.le_refl _)]
      exact Eq.refl _
    rw [leftLength, rightLength, left.degree_eq, right.degree_eq,
      sameMaximum, Nat.sub_self]
    simp only [Basic.DensePolynomial.padLeft,
      List.replicate_zero, List.nil_append, List.zipWith_cons_cons]
    change ((leftCoefficient + rightCoefficient) ::
      List.zipWith (· + ·) leftTail rightTail).dropWhile (· = 0) = _
    exact DropWhile.cons_of_false (fun value : K => decide (value = 0))
      (leftCoefficient + rightCoefficient) (List.zipWith (· + ·) leftTail rightTail)
      (decide_eq_false sumNonzero)
  have outputNonzero : (p + q).isZero = false := by
    rw [Basic.DensePolynomial.isZero, Basic.DensePolynomial.normalize_add, outputCoefficients]
    rfl
  refine
    { normalized := Basic.DensePolynomial.normalize_add p q
      nonzero := outputNonzero
      degree_eq := ?_
      coefficient_eq := ?_ }
  · have outputCount := Basic.DensePolynomial.natDegree_add_one_eq_degreeCount outputNonzero
    have outputLength :
        (List.zipWith (· + ·) leftTail rightTail).length = degree := by
      have equalLengths : leftTail.length = rightTail.length :=
        leftLength.trans (left.degree_eq.trans (right.degree_eq.symm.trans rightLength.symm))
      exact (Zip.length_zipWith_of_length_eq (· + ·) leftTail rightTail equalLengths).trans
        (leftLength.trans left.degree_eq)
    rw [Basic.DensePolynomial.degreeCount, Basic.DensePolynomial.normalize_add, outputCoefficients,
      List.length_cons, outputLength] at outputCount
    exact Addition.add_right_cancel outputCount
  · rw [Basic.DensePolynomial.leadingCoeff, Basic.DensePolynomial.normalize_add, outputCoefficients]
    rfl

/-- Adding a polynomial below a displayed degree preserves the higher leading term.

Negating the same lower polynomial preserves its count bound. Subtraction
then retains the higher head, and double negation restores the original addition. -/
public theorem addBelow {p q : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (left : LeadingTerm p degree coefficient)
    (right : DegreeBelow q degree) :
    LeadingTerm (p + q) degree coefficient := by
  have result := left.subBelow (DegreeBelow.neg right)
  change LeadingTerm (p + - -q) degree coefficient at result
  rw [Basic.DensePolynomial.neg_neg,
    right.normalized] at result
  exact result

/-- Addition with the higher-degree term on the right preserves that term.

Commuting the original dense addition places that retained leading term first,
where the lower coefficient-count certificate preserves its head and degree. -/
public theorem belowAdd {p q : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (left : DegreeBelow p degree)
    (right : LeadingTerm q degree coefficient) :
    LeadingTerm (p + q) degree coefficient := by
  rw [Basic.DensePolynomial.add_comm_direct]
  exact right.addBelow left

/-- Subtracting a higher-degree right term exposes its negated leading term.

The same right input supplies its normalized negative head and degree. Adding
the lower left input retains those two readbacks. -/
public theorem belowSub {p q : CoefficientPolynomial K} {degree : Nat} {coefficient : K}
    (left : DegreeBelow p degree)
    (right : LeadingTerm q degree coefficient) :
    LeadingTerm (p - q) degree (-coefficient) := by
  change LeadingTerm (p + -q) degree (-coefficient)
  exact (right.neg).belowAdd left

/-- A zero difference identifies the degrees of normalized nonzero polynomials.

Either strict degree comparison would retain a nonzero leading term in that
same coefficient difference. Excluding both comparisons identifies the two degrees. -/
public theorem natDegree_eq_of_sub_isZero
    {p q : CoefficientPolynomial K} (pNonzero : p.isZero = false)
    (qNonzero : q.isZero = false) (pNormalized : p.normalize = p)
    (qNormalized : q.normalize = q) (differenceZero : (p - q).isZero = true) :
    p.natDegree = q.natDegree := by
  by_cases leftSmaller : p.natDegree < q.natDegree
  · have leftBelow := DegreeBelow.ofNatDegreeLt pNonzero pNormalized
      leftSmaller
    have rightLeading := LeadingTerm.ofNormalized qNonzero qNormalized
    have differenceNonzero := (rightLeading.belowSub leftBelow).nonzero
    rw [differenceZero] at differenceNonzero
    exact Bool.noConfusion differenceNonzero
  · by_cases rightSmaller : q.natDegree < p.natDegree
    · have rightBelow := DegreeBelow.ofNatDegreeLt qNonzero qNormalized
        rightSmaller
      have leftLeading := LeadingTerm.ofNormalized pNonzero pNormalized
      have differenceNonzero := (leftLeading.subBelow rightBelow).nonzero
      rw [differenceZero] at differenceNonzero
      exact Bool.noConfusion differenceNonzero
    · exact Nat.le_antisymm (Nat.le_of_not_gt rightSmaller)
        (Nat.le_of_not_gt leftSmaller)

end LeadingTerm

end Purelib.Polynomial.Dense.Leading
