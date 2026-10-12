module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.Multiplication
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Replicate
import Purelib.Data.List.Zip
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-!
# One retained leading-coefficient cancellation

The original coefficient ratio and degree difference construct a one-term
quotient and shifted scaled divisor. Their leading entries cancel in the same
padded subtraction, strictly reducing the retained normalized coefficient count
when both input polynomials are normalized and nonzero.
-/

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Algebra.Field
open Purelib.Algebra.Ring
open Purelib.Data.List
open Purelib.Data.Nat
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- The one-term quotient used to cancel the current leading coefficient.

The original leading coefficient ratio is retained at the displayed natural degree difference. A single original shift
places that same quotient coefficient in its required slot. -/
@[expose] public def leadQuotient (p q : DensePolynomial K) : DensePolynomial K :=
  let exponent := p.natDegree - q.natDegree
  shift exponent ⟨[p.leadingCoeff / q.leadingCoeff]⟩

/-- One exact long-division cancellation step.

The original divisor is scaled by the retained leading-coefficient ratio, then shifted by the same degree difference.
Subtraction consumes that completed original polynomial once. -/
@[expose] public def cancelLead (p q : DensePolynomial K) : DensePolynomial K :=
  p - shift (p.natDegree - q.natDegree)
    (scale (p.leadingCoeff / q.leadingCoeff) q)

/-- A leading-term cancellation produces an already normalized polynomial. -/
@[simp] public theorem normalize_cancelLead (p q : DensePolynomial K) :
    (cancelLead p q).normalize = cancelLead p q := by
  exact normalize_sub _ _

/-- Negating a nonzero divisor changes the one-term quotient sign but leaves
the long-division cancellation polynomial unchanged.

The original nonzero leading coefficient supplies the retained inverse cancellation law. The scaled negated divisor
therefore has the same coefficient output. -/
public theorem cancelLead_neg_right (p q : DensePolynomial K) (hq : q.isZero = false) :
    cancelLead p (-q) = cancelLead p q := by
  rw [cancelLead, cancelLead, natDegree_neg, leadingCoeff_neg,
    scale_div_neg_neg (leadingCoeff_ne_zero hq)]

/-- Simultaneously negating dividend and divisor negates the exact
long-division cancellation remainder.

The two original coefficient negations cancel in their ratio. The normalized dividend and shifted scaled divisor retain
the same subtraction coefficients with every sign reversed. -/
public theorem cancelLead_neg_both (p q : DensePolynomial K)
    (pNormalized : p.normalize = p) :
    cancelLead (-p) (-q) = -cancelLead p q := by
  have quotient : (-p.leadingCoeff) / (-q.leadingCoeff) =
      p.leadingCoeff / q.leadingCoeff := by
    rw [ExplicitField.div_eq_mul_inv,
      ExplicitField.inv_neg, Multiplication.neg_mul_neg,
      ← ExplicitField.div_eq_mul_inv]
  rw [cancelLead, cancelLead, natDegree_neg, natDegree_neg,
    leadingCoeff_neg, leadingCoeff_neg, quotient,
    scale_neg_right, shift_neg]
  exact neg_sub_neg_of_normalized p
    (shift (p.natDegree - q.natDegree)
      (scale (p.leadingCoeff / q.leadingCoeff) q))
    pNormalized (normalize_shift _ _)

/-- Evaluate the one-term quotient as its coefficient ratio times the degree-difference power.

The retained quotient coefficient is the original leading ratio. Its exact shift contributes the point raised to the
same original degree difference. -/
public theorem eval_leadQuotient (p q : DensePolynomial K) (x : K) :
    (leadQuotient p q).eval x =
      (p.leadingCoeff / q.leadingCoeff) * x ^ (p.natDegree - q.natDegree) := by
  rw [leadQuotient, eval_shift]
  change (constant (p.leadingCoeff / q.leadingCoeff)).eval x *
      x ^ (p.natDegree - q.natDegree) = _
  rewrite [eval_constant]
  exact Eq.refl _

/-- A cancellation step subtracts the divisor value times the one-term quotient value.

Scalar evaluation transports the retained shifted scale and subtraction. The original quotient value accounts for the
same divisor contribution. -/
public theorem eval_cancelLead (p q : DensePolynomial K) (x : K) :
    (cancelLead p q).eval x =
      p.eval x - q.eval x * (leadQuotient p q).eval x := by
  rw [cancelLead, eval_sub, eval_shift, eval_scale, eval_leadQuotient]
  let c := p.leadingCoeff / q.leadingCoeff
  let y := x ^ (p.natDegree - q.natDegree)
  change p.eval x - c * q.eval x * y =
    p.eval x - q.eval x * (c * y)
  ring1

/-- Leading cancellation strictly decreases the dividend coefficient count.

Both inputs are normalized and nonzero, and the divisor degree does not exceed the dividend degree; the head terms
cancel exactly. -/
public theorem cancelLead_degreeCount_lt {p q : DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false)
    (hpNormalized : p.normalize = p) (hqNormalized : q.normalize = q)
    (hdegree : q.natDegree ≤ p.natDegree) :
    (cancelLead p q).degreeCount < p.degreeCount := by
  obtain ⟨a, as, hpcoeffs, ha⟩ :
      ∃ a as, p.coeffs = a :: as ∧ a ≠ 0 := by
    cases hpcase : p.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpNormalized, hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        rw [hpNormalized] at hlead
        rewrite [hpcase] at hlead
        exact hlead
  obtain ⟨b, bs, hqcoeffs, hb⟩ :
      ∃ b bs, q.coeffs = b :: bs ∧ b ≠ 0 := by
    cases hqcase : q.coeffs with
    | nil =>
        have hq' : q.normalize.coeffs.isEmpty = false := hq
        rw [hqNormalized, hqcase] at hq'
        exact Bool.noConfusion hq'
    | cons b bs =>
        refine ⟨b, bs, rfl, ?_⟩
        have hlead := leadingCoeff_ne_zero hq
        change q.normalize.coeffs.headD 0 ≠ 0 at hlead
        rw [hqNormalized] at hlead
        rewrite [hqcase] at hlead
        exact hlead
  have hpCount : p.degreeCount = as.length + 1 := by
    change p.normalize.coeffs.length = as.length + 1
    rewrite [hpNormalized, hpcoeffs]
    exact Eq.refl _
  have hqCount : q.degreeCount = bs.length + 1 := by
    change q.normalize.coeffs.length = bs.length + 1
    rewrite [hqNormalized, hqcoeffs]
    exact Eq.refl _
  have hpDegree : p.natDegree = as.length := by
    change p.degreeCount - 1 = as.length
    rewrite [hpCount]
    exact Subtraction.add_sub_cancel_right as.length 1
  have hqDegree : q.natDegree = bs.length := by
    change q.degreeCount - 1 = bs.length
    rewrite [hqCount]
    exact Subtraction.add_sub_cancel_right bs.length 1
  have hlength : bs.length ≤ as.length := by
    rewrite [hqDegree, hpDegree] at hdegree
    exact hdegree
  have hleadP : p.leadingCoeff = a := by
    change p.normalize.coeffs.headD 0 = a
    rewrite [hpNormalized, hpcoeffs]
    exact Eq.refl _
  have hleadQ : q.leadingCoeff = b := by
    change q.normalize.coeffs.headD 0 = b
    rewrite [hqNormalized, hqcoeffs]
    exact Eq.refl _
  let c : K := a / b
  have hc : c ≠ 0 := div_ne_zero_direct ha hb
  have hcb : c * b = a := by
    dsimp [c]
    exact ExplicitField.div_mul_cancel a hb
  have hscaleCoeffs : (scale c q).coeffs =
      c * b :: bs.map (c * ·) := by
    rw [scale_coeffs_of_ne_zero hc, hqNormalized, hqcoeffs]
    rfl
  have hscaleZero : (scale c q).isZero = false := by
    unfold isZero
    rewrite [normalize_scale, hscaleCoeffs]
    exact Eq.refl _
  have hexponent : p.natDegree - q.natDegree = as.length - bs.length :=
    congrArg₂ (fun left right : Nat => left - right) hpDegree hqDegree
  let shifted := shift (p.natDegree - q.natDegree) (scale c q)
  have hshiftCoeffs : shifted.coeffs =
      c * b :: (bs.map (c * ·) ++ List.replicate (as.length - bs.length) 0) := by
    dsimp [shifted]
    rw [shift, if_neg (fun equal => Bool.noConfusion (hscaleZero.symm.trans equal)), normalize_scale,
      hscaleCoeffs, hexponent]
    rfl
  have hshiftLength : shifted.coeffs.length = p.coeffs.length := by
    rewrite [hshiftCoeffs, hpcoeffs, List.length_cons, Append.length_append,
      Map.length_map, Replicate.length_replicate]
    exact congrArg Nat.succ (Subtraction.add_sub_of_le hlength)
  have hshiftHead : shifted.coeffs.headD 0 = a := by
    rewrite [hshiftCoeffs]
    exact hcb
  have hshiftNormalized : shifted.normalize = shifted := by
    apply ext
    change shifted.coeffs.dropWhile (fun value => value = 0) = shifted.coeffs
    rewrite [hshiftCoeffs, hcb,
      DropWhile.cons_of_false (fun value : K => decide (value = 0)) a _
        (decide_eq_false ha)]
    exact Eq.refl _
  have hnegCoeffs : (-shifted).coeffs = shifted.coeffs.map (-·) := by
    rw [neg_coeffs, hshiftNormalized]
  rw [cancelLead, hleadP, hleadQ]
  change (p + -shifted).degreeCount < p.degreeCount
  rw [degreeCount, normalize_add, hpCount]
  change (add p (-shifted)).coeffs.length < as.length + 1
  simp only [add]
  have maximum : max p.coeffs.length p.coeffs.length = p.coeffs.length :=
    Nat.le_antisymm (Order.max_le (Nat.le_refl _) (Nat.le_refl _))
      (Order.le_max_left _ _)
  rw [hnegCoeffs, Map.length_map, hshiftLength, maximum, Nat.sub_self,
    hpcoeffs]
  simp only [padLeft, List.replicate_zero, List.nil_append]
  rw [hshiftCoeffs]
  simp only [List.map_cons, List.zipWith_cons_cons, hcb, add_neg_cancel]
  let out := List.zipWith (· + ·) as
    ((bs.map (c * ·) ++ List.replicate (as.length - bs.length) 0).map (-·))
  have houtLength : out.length = as.length := by
    have pairedLength : as.length =
        ((bs.map (c * ·) ++ List.replicate (as.length - bs.length) 0).map (-·)).length := by
      rewrite [Map.length_map, Append.length_append, Map.length_map,
        Replicate.length_replicate]
      exact (Subtraction.add_sub_of_le hlength).symm
    exact Zip.length_zipWith_of_length_eq (· + ·) _ _ pairedLength
  change ((0 :: out).dropWhile (· = 0)).length < (0 :: as).length
  have strict := DropWhile.length_lt_cons_of_true
    (fun value : K => decide (value = 0)) 0 out
      (decide_eq_true (Eq.refl (0 : K)))
  rewrite [List.length_cons, houtLength] at strict
  exact strict

end Purelib.Polynomial.Dense.Basic.DensePolynomial
