module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
import Purelib.Data.Bool.Decide
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Replicate
import Purelib.Data.List.Zip
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction

section
public section

/-!
# Finite dense polynomial multiplication

The original coefficient program scans the left polynomial from high degree
to low degree. Each Horner step shifts its retained accumulator and adds a
scaled right factor. Direct coefficient-shape certificates describe the same
padding, leading-zero normalization, degree and scalar evaluation.
-/

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Algebra.Field

open Purelib.Polynomial.Dense
open Purelib.Data.List
open Purelib.Data.Nat

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Bound the retained coefficient length after a finite multiplication Horner fold.

The accumulator begins within the supplied bound and the right factor's normalized count is at most one larger; each
scanned coefficient increases the bound by one. -/
private theorem coeffs_length_mulFold_le (q : Basic.DensePolynomial K) :
    ∀ (coefficients : List K) (acc : Basic.DensePolynomial K) (bound : Nat),
      q.degreeCount ≤ bound + 1 →
      acc.coeffs.length ≤ bound →
      (coefficients.foldl
        (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) acc).coeffs.length ≤
          bound + coefficients.length
  | [], acc, bound, _, hacc => by
      change acc.coeffs.length ≤ bound + 0
      rewrite [Nat.add_zero]
      exact hacc
  | a :: remaining, acc, bound, hq, hacc => by
      simp only [List.foldl_cons, List.length_cons]
      have hnext : (Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale a q).coeffs.length ≤ bound + 1 := by
        apply (Basic.DensePolynomial.coeffs_length_add_le _ _).trans
        apply Order.max_le
        · exact (Basic.DensePolynomial.coeffs_length_shift_le acc).trans (by
            have := Basic.DensePolynomial.degreeCount_le_coeffs_length acc
            omega)
        · exact (Basic.DensePolynomial.coeffs_length_scale_le a q).trans hq
      have hrecursive := Purelib.Polynomial.Dense.Basic.DensePolynomial.coeffs_length_mulFold_le q remaining
        (Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale a q) (bound + 1) (by omega) hnext
      omega

/-- Polynomial multiplication as a finite Horner fold over the left factor.

Each original coefficient shifts the retained accumulator once and adds its
scaled right factor. The fold scans the unchanged left coefficient list from
the original empty polynomial accumulator. -/
@[expose] def mulPolynomial (p q : Basic.DensePolynomial K) : Basic.DensePolynomial K :=
  p.coeffs.foldl (fun acc a => Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale a q) 0

/-- The multiplication instance uses the finite polynomial Horner fold. -/
instance : Mul (Basic.DensePolynomial K) := ⟨Basic.DensePolynomial.mulPolynomial⟩

omit [DecidableEq K] in
/-- Pairwise addition of a matching zero list on the left preserves the coefficient list. -/
theorem zipWith_replicate_zero_add (cs : List K) :
    List.zipWith (· + ·) (List.replicate cs.length 0) cs = cs := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.length_cons]
      rw [List.replicate_succ, List.zipWith_cons_cons, zero_add, ih]

/-- Adding represented zero on the left returns the normalized input polynomial.

The original maximum aligns the empty left input with the retained right
coefficient list. Pairwise addition of the matching zero list then feeds the
same leading-zero normalization as the original addition operation. -/
theorem zero_add_normalize (p : Basic.DensePolynomial K) :
    (0 : Basic.DensePolynomial K) + p = p.normalize := by
  apply Basic.DensePolynomial.ext
  change (Basic.DensePolynomial.add 0 p).coeffs = p.normalize.coeffs
  rw [show (0 : Basic.DensePolynomial K) = ⟨[]⟩ from rfl]
  have maximum : max 0 p.coeffs.length = p.coeffs.length := by
    change (if 0 ≤ p.coeffs.length then p.coeffs.length else 0) = p.coeffs.length
    rewrite [if_pos (Nat.zero_le _)]
    exact Eq.refl _
  change (List.zipWith (· + ·)
    (List.replicate (max 0 p.coeffs.length - 0) 0 ++ [])
    (List.replicate (max 0 p.coeffs.length - p.coeffs.length) 0 ++ p.coeffs)).dropWhile (· = 0) =
      p.coeffs.dropWhile (· = 0)
  rewrite [maximum, Nat.sub_zero, Nat.sub_self, Append.append_nil]
  change (List.zipWith (· + ·) (List.replicate p.coeffs.length 0) p.coeffs).dropWhile (· = 0) = _
  exact congrArg (fun coefficients : List K => coefficients.dropWhile (· = 0))
    (Basic.DensePolynomial.zipWith_replicate_zero_add p.coeffs)

omit [DecidableEq K] in
/-- Pairwise addition of a matching zero list on the right preserves the coefficient list. -/
private theorem zipWith_add_replicate_zero (cs : List K) :
    List.zipWith (· + ·) cs (List.replicate cs.length 0) = cs := by
  induction cs with
  | nil => rfl
  | cons a as inductionHypothesis =>
      simp only [List.length_cons, List.replicate_succ,
        List.zipWith_cons_cons, add_zero]
      rw [inductionHypothesis]

/-- Adding the represented zero on the right changes only normalization.

The original maximum aligns the empty right input with the retained left
coefficient list. Pairwise addition of the matching zero list then feeds the
same leading-zero normalization as the original addition operation. -/
theorem add_zero_normalize (p : Basic.DensePolynomial K) :
    p + (0 : Basic.DensePolynomial K) = p.normalize := by
  apply Basic.DensePolynomial.ext
  change (Basic.DensePolynomial.add p 0).coeffs = p.normalize.coeffs
  rw [show (0 : Basic.DensePolynomial K) = ⟨[]⟩ from rfl]
  have maximum : max p.coeffs.length 0 = p.coeffs.length := by
    change (if p.coeffs.length ≤ 0 then 0 else p.coeffs.length) = p.coeffs.length
    by_cases emptyLength : p.coeffs.length ≤ 0
    · rewrite [if_pos emptyLength]
      exact (Nat.le_antisymm emptyLength (Nat.zero_le _)).symm
    · rewrite [if_neg emptyLength]
      exact Eq.refl _
  change (List.zipWith (· + ·)
    (List.replicate (max p.coeffs.length 0 - p.coeffs.length) 0 ++ p.coeffs)
    (List.replicate (max p.coeffs.length 0 - 0) 0 ++ [])).dropWhile (· = 0) =
      p.coeffs.dropWhile (· = 0)
  rewrite [maximum, Nat.sub_self, Nat.sub_zero, Append.append_nil]
  change (List.zipWith (· + ·) p.coeffs (List.replicate p.coeffs.length 0)).dropWhile (· = 0) = _
  exact congrArg (fun coefficients : List K => coefficients.dropWhile (· = 0))
    (Basic.DensePolynomial.zipWith_add_replicate_zero p.coeffs)

/-- When the left input is strictly longer and has a nonzero leading
coefficient, finite left-padded addition preserves that leading coefficient
and length.

The exact length difference supplies the original left zero padding for the
shorter input. The first unmatched coefficient remains nonzero, while the
equal-length tails retain their pairwise sum and original coefficient count. -/
private theorem add_coeffs_of_left_longer
    {p q : Basic.DensePolynomial K} {a : K} {as : List K}
    (hp : p.coeffs = a :: as) (ha : a ≠ 0)
    (hlen : q.coeffs.length < p.coeffs.length) :
    ∃ bs, (p + q).coeffs = a :: bs ∧ bs.length = as.length := by
  have hle : q.coeffs.length ≤ p.coeffs.length := Nat.le_of_lt hlen
  have hmax : max p.coeffs.length q.coeffs.length = p.coeffs.length :=
    by
      change (if p.coeffs.length ≤ q.coeffs.length then q.coeffs.length else p.coeffs.length) = p.coeffs.length
      by_cases forward : p.coeffs.length ≤ q.coeffs.length
      · rewrite [if_pos forward]
        exact Nat.le_antisymm hle forward
      · rewrite [if_neg forward]
        exact Eq.refl _
  have hsubpos : 0 < p.coeffs.length - q.coeffs.length := by
    apply Nat.pos_of_ne_zero
    intro vanished
    have reconstruction := Subtraction.add_sub_of_le hle
    rewrite [vanished, Nat.add_zero] at reconstruction
    exact (Nat.ne_of_lt hlen) reconstruction
  cases hsub : p.coeffs.length - q.coeffs.length with
  | zero =>
      have impossible : 0 < 0 := hsub ▸ hsubpos
      exact (Nat.lt_irrefl 0 impossible).elim
  | succ d =>
      refine ⟨List.zipWith (· + ·) as
        (List.replicate d 0 ++ q.coeffs), ?_, ?_⟩
      · change (Basic.DensePolynomial.add p q).coeffs = _
        simp only [Basic.DensePolynomial.add]
        rw [hmax]
        simp only [Nat.sub_self, Basic.DensePolynomial.padLeft, List.replicate_zero, List.nil_append]
        rw [hsub, hp]
        simp only [List.replicate_succ, List.cons_append,
          List.zipWith_cons_cons, add_zero, Basic.DensePolynomial.normalize]
        rw [DropWhile.cons_of_false (fun value : K => decide (value = 0)) a
          (List.zipWith (· + ·) as (List.replicate d 0 ++ q.coeffs))
          (decide_eq_false ha)]
      · have hlength : p.coeffs.length = as.length + 1 := by
          exact congrArg List.length hp
        have rearranged : (d + q.coeffs.length) + 1 =
            (d + 1) + q.coeffs.length := by
          rw [Nat.add_assoc, Nat.add_comm q.coeffs.length 1,
            ← Nat.add_assoc]
        have equalSuccessors : (d + q.coeffs.length) + 1 =
            as.length + 1 := by
          calc
            (d + q.coeffs.length) + 1 =
                (d + 1) + q.coeffs.length := rearranged
            _ = (p.coeffs.length - q.coeffs.length) +
                q.coeffs.length := by rw [hsub]
            _ = p.coeffs.length :=
              (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le hle)
            _ = as.length + 1 := hlength
        have heq : as.length = d + q.coeffs.length :=
          (Nat.succ.inj equalSuccessors).symm
        apply Zip.length_zipWith_of_length_eq (· + ·)
        rewrite [Append.length_append, Replicate.length_replicate]
        exact heq

/-- A displayed coefficient list with nonzero head is already normalized.

The original leading-zero scan retains the whole list at its first nonzero
entry. Coefficient equality then identifies the original polynomial record. -/
private theorem normalize_eq_self_of_coeffs_cons
    {p : Basic.DensePolynomial K} {a : K} {as : List K}
    (hp : p.coeffs = a :: as) (ha : a ≠ 0) : p.normalize = p := by
  apply Basic.DensePolynomial.ext
  change p.coeffs.dropWhile (· = 0) = p.coeffs
  rewrite [hp]
  exact DropWhile.cons_of_false (fun value : K => decide (value = 0)) a as
    (decide_eq_false ha)

/-- A displayed coefficient list with nonzero head fails the polynomial zero test.

The original normalization retains that first entry, so the resulting list
is nonempty. The Boolean result is the existing list emptiness computation. -/
theorem isZero_false_of_coeffs_cons
    {p : Basic.DensePolynomial K} {a : K} {as : List K}
    (hp : p.coeffs = a :: as) (ha : a ≠ 0) : p.isZero = false := by
  change (p.coeffs.dropWhile (· = 0)).isEmpty = false
  rewrite [hp, DropWhile.cons_of_false (fun value : K => decide (value = 0)) a as
    (decide_eq_false ha)]
  exact Eq.refl _

/-- One multiplication Horner step preserves a displayed nonzero leading
coefficient and adds exactly one coefficient slot.

The shifted accumulator is strictly longer than the scaled right factor.
Their original padded addition preserves the retained nonzero head and adds
one coefficient slot without changing the tail construction. -/
private theorem mulStep_preserves_leading_shape
    (q : Basic.DensePolynomial K) {acc : Basic.DensePolynomial K} {a : K} {as : List K}
    (hcoeffs : acc.coeffs = a :: as) (ha : a ≠ 0)
    (hlength : q.normalize.coeffs.length ≤ acc.coeffs.length) (b : K) :
  ∃ out,
      (Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale b q).coeffs = a :: out ∧
        out.length = as.length + 1 := by
  have hzero : acc.isZero = false :=
    Basic.DensePolynomial.isZero_false_of_coeffs_cons hcoeffs ha
  have hnormalize : acc.normalize = acc :=
    Basic.DensePolynomial.normalize_eq_self_of_coeffs_cons hcoeffs ha
  have hshift : (Basic.DensePolynomial.shift 1 acc).coeffs = a :: (as ++ [0]) := by
    rw [Basic.DensePolynomial.shift, if_neg (fun impossible => Bool.noConfusion (hzero.symm.trans impossible)),
      hnormalize, hcoeffs]
    rfl
  have hscale : (Basic.DensePolynomial.scale b q).coeffs.length ≤ q.normalize.coeffs.length := by
    by_cases hb : b = 0
    · subst b
      rw [Basic.DensePolynomial.scale_zero_left]
      change [].length ≤ q.normalize.coeffs.length
      exact Nat.zero_le _
    · rewrite [Basic.DensePolynomial.scale_coeffs_of_ne_zero hb, Map.length_map]
      exact Nat.le_refl _
  have hlt : (Basic.DensePolynomial.scale b q).coeffs.length < (Basic.DensePolynomial.shift 1 acc).coeffs.length := by
    have haccLength : acc.coeffs.length = as.length + 1 := congrArg List.length hcoeffs
    have shiftLonger : acc.coeffs.length <
        (Basic.DensePolynomial.shift 1 acc).coeffs.length := by
      rw [haccLength, hshift]
      simp only [List.length_cons, Append.length_append]
      exact Nat.lt_succ_self _
    exact (hscale.trans hlength).trans_lt shiftLonger
  obtain ⟨out, hout, houtLength⟩ :=
    Basic.DensePolynomial.add_coeffs_of_left_longer hshift ha hlt
  refine ⟨out, hout, ?_⟩
  rewrite [houtLength, Append.length_append]
  exact Eq.refl _

/-- Repeated multiplication Horner steps retain the same displayed leading
coefficient while growing by exactly the number of scanned coefficients.

Each original Horner step retains the nonzero leading entry and adds one
slot. Recursion follows the supplied coefficient tail, so the accumulated
length increase is exactly the length of that original list. -/
private theorem foldl_mulStep_preserves_leading_shape
    (q : Basic.DensePolynomial K) :
    ∀ (coefficients : List K) (acc : Basic.DensePolynomial K)
      (a : K) (as : List K),
      acc.coeffs = a :: as → a ≠ 0 →
      q.normalize.coeffs.length ≤ acc.coeffs.length →
      ∃ out,
        (coefficients.foldl
          (fun value coefficient =>
            Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale coefficient q) acc).coeffs = a :: out ∧
          out.length = as.length + coefficients.length
  | [], _, _, as, hcoeffs, _, _ => ⟨as, hcoeffs, (Nat.add_zero _).symm⟩
  | coefficient :: remaining, acc, a, as, hcoeffs, ha, hlength => by
      obtain ⟨next, hnext, hnextLength⟩ :=
        Basic.DensePolynomial.mulStep_preserves_leading_shape q hcoeffs ha hlength coefficient
      have hnextBound : q.normalize.coeffs.length ≤
          (Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale coefficient q).coeffs.length := by
        rw [hnext, List.length_cons]
        have haccLength : acc.coeffs.length = as.length + 1 := congrArg List.length hcoeffs
        have accumulatorNext : acc.coeffs.length = next.length :=
          haccLength.trans hnextLength.symm
        have retainedBound : acc.coeffs.length ≤ next.length := by
          rewrite [← accumulatorNext]
          exact Nat.le_refl _
        exact hlength.trans (retainedBound.trans (Nat.le_add_right _ _))
      obtain ⟨out, hout, houtLength⟩ :=
        Purelib.Polynomial.Dense.Basic.DensePolynomial.foldl_mulStep_preserves_leading_shape q remaining
          (Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale coefficient q) a next hnext ha hnextBound
      refine ⟨out, ?_, ?_⟩
      · simpa only [List.foldl_cons] using hout
      · rw [houtLength, hnextLength]
        simp only [List.length_cons]
        calc
          (as.length + 1) + remaining.length =
              as.length + (1 + remaining.length) :=
            Nat.add_assoc _ _ _
          _ = as.length + (remaining.length + 1) :=
            congrArg (as.length + ·) (Nat.add_comm 1 remaining.length)

/-- Subtracting a strictly shorter normalized polynomial preserves the
displayed leading coefficient and the exact coefficient count of the left
polynomial.

Negation retains the shorter input coefficient count. Its padded addition
to the longer normalized input leaves the original leading coefficient
unchanged and retains the displayed count of the longer coefficient list. -/
theorem sub_coeffs_shape_of_degreeCount_lt
    {p q : Basic.DensePolynomial K} (hp : p.isZero = false)
    (hpNormalized : p.normalize = p)
    (hlength : q.degreeCount < p.degreeCount) :
    ∃ out,
      (p - q).coeffs = p.leadingCoeff :: out ∧
        out.length + 1 = p.degreeCount := by
  obtain ⟨a, as, hpcoeffs, ha⟩ :
      ∃ a as, p.coeffs = a :: as ∧ a ≠ 0 := by
    cases hpcase : p.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpNormalized, hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := Basic.DensePolynomial.leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        rw [hpNormalized, hpcase] at hlead
        simpa only [List.headD_cons] using hlead
  have hpLeading : p.leadingCoeff = a := by
    change p.normalize.coeffs.headD 0 = a
    rw [hpNormalized, hpcoeffs]
    rfl
  have hpCount : p.coeffs.length = p.degreeCount := by
    change p.coeffs.length = p.normalize.coeffs.length
    rw [hpNormalized]
  have hqCount : (-q).coeffs.length = q.degreeCount := by
    rw [Basic.DensePolynomial.neg_coeffs, Map.length_map]
    rfl
  have hshort : (-q).coeffs.length < p.coeffs.length := by
    rw [hqCount, hpCount]
    exact hlength
  obtain ⟨out, hout, houtLength⟩ :=
    Basic.DensePolynomial.add_coeffs_of_left_longer hpcoeffs ha hshort
  refine ⟨out, ?_, ?_⟩
  · change (p + -q).coeffs = _
    rw [hout, hpLeading]
  · rw [houtLength]
    have hpLength : p.coeffs.length = as.length + 1 := congrArg List.length hpcoeffs
    exact hpLength.symm.trans hpCount

/-- A finite Horner accumulator has a nonzero leading coefficient and is at
least as long as the normalized right factor. -/
private def HasLeadingAtLeast (q p : Basic.DensePolynomial K) : Prop :=
  ∃ a as, p.coeffs = a :: as ∧ a ≠ 0 ∧
    q.normalize.coeffs.length ≤ p.coeffs.length

/-- One multiplication Horner step retains a nonzero head and sufficient coefficient length.

The accumulator is at least as long as the normalized right factor, so its shifted leading term cannot be cancelled by
the scaled coefficient contribution. -/
private theorem mulStep_preserves_hasLeadingAtLeast (q : Basic.DensePolynomial K)
    {acc : Basic.DensePolynomial K} (hacc : Basic.DensePolynomial.HasLeadingAtLeast q acc) (b : K) :
    Basic.DensePolynomial.HasLeadingAtLeast q (Basic.DensePolynomial.shift 1 acc + Basic.DensePolynomial.scale b q) :=
      by
  rcases hacc with ⟨a, as, hcoeffs, ha, hlength⟩
  have hzero : acc.isZero = false :=
    Basic.DensePolynomial.isZero_false_of_coeffs_cons hcoeffs ha
  have hnormalize : acc.normalize = acc :=
    Basic.DensePolynomial.normalize_eq_self_of_coeffs_cons hcoeffs ha
  have hshift : (Basic.DensePolynomial.shift 1 acc).coeffs = a :: (as ++ [0]) := by
    rw [Basic.DensePolynomial.shift, if_neg (fun impossible => Bool.noConfusion (hzero.symm.trans impossible)),
      hnormalize, hcoeffs]
    rfl
  have hscale : (Basic.DensePolynomial.scale b q).coeffs.length ≤ q.normalize.coeffs.length := by
    by_cases hb : b = 0
    · subst b
      rw [Basic.DensePolynomial.scale_zero_left]
      change [].length ≤ q.normalize.coeffs.length
      exact Nat.zero_le _
    · rewrite [Basic.DensePolynomial.scale_coeffs_of_ne_zero hb, Map.length_map]
      exact Nat.le_refl _
  have hlt : (Basic.DensePolynomial.scale b q).coeffs.length < (Basic.DensePolynomial.shift 1 acc).coeffs.length := by
    have haccLength : acc.coeffs.length = as.length + 1 := congrArg List.length hcoeffs
    have shiftLonger : acc.coeffs.length <
        (Basic.DensePolynomial.shift 1 acc).coeffs.length := by
      rw [haccLength, hshift]
      simp only [List.length_cons, Append.length_append]
      exact Nat.lt_succ_self _
    exact (hscale.trans hlength).trans_lt shiftLonger
  obtain ⟨out, hout, houtLength⟩ :=
    Basic.DensePolynomial.add_coeffs_of_left_longer hshift ha hlt
  refine ⟨a, out, hout, ha, ?_⟩
  rw [hout]
  simp only [List.length_cons]
  rw [houtLength]
  have haccLength : acc.coeffs.length = as.length + 1 := congrArg List.length hcoeffs
  simp only [Append.length_append, List.length_cons, List.length_nil]
  rw [← haccLength]
  exact hlength.trans (Nat.le_add_right _ _)

/-- A finite multiplication Horner fold preserves a nonzero head and the lower length bound from the right factor. -/
private theorem foldl_mulStep_preserves_hasLeadingAtLeast
    (q : Basic.DensePolynomial K) (cs : List K) {acc : Basic.DensePolynomial K}
    (hacc : Basic.DensePolynomial.HasLeadingAtLeast q acc) :
    Basic.DensePolynomial.HasLeadingAtLeast q
      (cs.foldl (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) acc) := by
  induction cs generalizing acc with
  | nil => exact hacc
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact ih (Basic.DensePolynomial.mulStep_preserves_hasLeadingAtLeast q hacc a)

/-- Leading zero coefficients do not change a multiplication Horner fold starting at zero.

Each discarded leading zero contributes the original zero shift and zero
scale to the accumulator. The first retained coefficient and all subsequent
coefficients follow the unchanged multiplication recurrence. -/
private theorem foldl_mulStep_dropWhile_zero (q : Basic.DensePolynomial K)
    (cs : List K) :
    (cs.dropWhile (· = 0)).foldl
        (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 =
      cs.foldl (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · subst a
        rw [DropWhile.cons_of_true (fun value : K => decide (value = 0)) 0 as
          (decide_eq_true rfl)]
        simp only [List.foldl_cons]
        rw [show Basic.DensePolynomial.shift 1 (0 : Basic.DensePolynomial K) + Basic.DensePolynomial.scale 0 q = 0 by
          rw [Basic.DensePolynomial.scale_zero_left]
          change Basic.DensePolynomial.add (Basic.DensePolynomial.shift 1 0) 0 = 0
          rw [Basic.DensePolynomial.shift, if_pos (show (0 : Basic.DensePolynomial K).isZero = true by rfl)]
          rfl]
        exact ih
      · rewrite [DropWhile.cons_of_false (fun value : K => decide (value = 0)) a as
          (decide_eq_false ha)]
        exact Eq.refl _

/-- A left factor passing the zero test makes the dense product the empty zero representation. -/
theorem mul_eq_zero_of_isZero_left {p q : Basic.DensePolynomial K}
    (hp : p.isZero = true) : p * q = 0 := by
  rw [show p * q = Basic.DensePolynomial.mulPolynomial p q from rfl, Basic.DensePolynomial.mulPolynomial]
  rw [← Basic.DensePolynomial.foldl_mulStep_dropWhile_zero q p.coeffs]
  change p.normalize.coeffs.foldl
      (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 = 0
  rw [Basic.DensePolynomial.normalize_eq_zero_of_isZero hp]
  rfl

/-- A right factor passing the zero test makes the dense product the empty zero representation. -/
theorem mul_eq_zero_of_isZero_right {p q : Basic.DensePolynomial K}
    (hq : q.isZero = true) : p * q = 0 := by
  rw [show p * q = Basic.DensePolynomial.mulPolynomial p q from rfl, Basic.DensePolynomial.mulPolynomial]
  rw [← Basic.DensePolynomial.foldl_mulStep_dropWhile_zero q p.coeffs]
  change p.normalize.coeffs.foldl
      (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 = 0
  induction p.normalize.coeffs with
  | nil => rfl
  | cons a remaining inductionHypothesis =>
      rw [List.foldl_cons, Basic.DensePolynomial.scale_eq_zero_of_isZero a hq]
      rw [Basic.DensePolynomial.shift, if_pos (show (0 : Basic.DensePolynomial K).isZero = true by rfl)]
      change remaining.foldl
        (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 = 0
      exact inductionHypothesis

/-- The product degree count is at most the sum of input counts minus one.

The separate zero-factor branches retain the empty polynomial representation.
For nonzero factors, the original Horner coefficient bound retains the right
factor's predecessor count; reconstructing that positive count identifies the
same truncated total bound. -/
theorem degreeCount_mul_le (p q : Basic.DensePolynomial K) :
    (p * q).degreeCount ≤ p.degreeCount + q.degreeCount - 1 := by
  by_cases hp : p.isZero = true
  · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_left hp,
      Basic.DensePolynomial.degreeCount_eq_zero_of_isZero (p := (0 : Basic.DensePolynomial K)) rfl]
    exact Nat.zero_le _
  · by_cases hq : q.isZero = true
    · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_right hq,
        Basic.DensePolynomial.degreeCount_eq_zero_of_isZero (p := (0 : Basic.DensePolynomial K)) rfl]
      exact Nat.zero_le _
    · have hqFalse : q.isZero = false := Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true q.isZero hq
      have hqPositive := Basic.DensePolynomial.degreeCount_pos_of_isZero_false hqFalse
      have rightCount : q.degreeCount - 1 + 1 = q.degreeCount :=
        (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le hqPositive)
      have rightBound : q.degreeCount ≤ q.degreeCount - 1 + 1 := by
        rewrite [rightCount]
        exact Nat.le_refl _
      have hfold := Basic.DensePolynomial.coeffs_length_mulFold_le q p.normalize.coeffs 0
        (q.degreeCount - 1) rightBound
        (show (0 : Basic.DensePolynomial K).coeffs.length ≤ q.degreeCount - 1 by
          exact Nat.zero_le _)
      have hcoeffs : (p * q).coeffs.length ≤
          q.degreeCount - 1 + p.degreeCount := by
        have hproduct : p * q = p.normalize.coeffs.foldl
            (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 := by
          rw [show p * q = Basic.DensePolynomial.mulPolynomial p q from rfl, Basic.DensePolynomial.mulPolynomial]
          rw [← Basic.DensePolynomial.foldl_mulStep_dropWhile_zero q p.coeffs]
          rfl
        rw [hproduct]
        exact hfold
      have totalCount : (q.degreeCount - 1 + p.degreeCount) + 1 =
          p.degreeCount + q.degreeCount := by
        calc
          (q.degreeCount - 1 + p.degreeCount) + 1 =
              p.degreeCount + (q.degreeCount - 1 + 1) := by
            rw [Nat.add_comm (q.degreeCount - 1) p.degreeCount,
              Nat.add_assoc]
          _ = p.degreeCount + q.degreeCount :=
            congrArg (p.degreeCount + ·) rightCount
      have sameBound : q.degreeCount - 1 + p.degreeCount =
          p.degreeCount + q.degreeCount - 1 :=
        (Nat.succ_sub_one _).symm.trans
          (congrArg (fun count : Nat => count - 1) totalCount)
      rewrite [← sameBound]
      exact (Basic.DensePolynomial.degreeCount_le_coeffs_length (p * q)).trans hcoeffs

/-- Exact finite coefficient shape of a product of two nonzero dense
polynomials.  In particular, the displayed head is the product of the two
displayed leading coefficients and the tail has the sum of the input natural
degrees. -/
theorem mul_coeffs_shape {p q : Basic.DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    ∃ out,
      (p * q).coeffs = p.leadingCoeff * q.leadingCoeff :: out ∧
        out.length = p.natDegree + q.natDegree := by
  obtain ⟨pa, pas, hpcoeffs, hpa⟩ :
      ∃ pa pas, p.normalize.coeffs = pa :: pas ∧ pa ≠ 0 := by
    cases hpcase : p.normalize.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := Basic.DensePolynomial.leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hpcase, List.headD_cons] using hlead
  obtain ⟨qa, qas, hqcoeffs, hqa⟩ :
      ∃ qa qas, q.normalize.coeffs = qa :: qas ∧ qa ≠ 0 := by
    cases hqcase : q.normalize.coeffs with
    | nil =>
        have hq' : q.normalize.coeffs.isEmpty = false := hq
        rw [hqcase] at hq'
        exact Bool.noConfusion hq'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := Basic.DensePolynomial.leadingCoeff_ne_zero hq
        change q.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hqcase, List.headD_cons] using hlead
  have hpLeading : p.leadingCoeff = pa := by
    change p.normalize.coeffs.headD 0 = pa
    rw [hpcoeffs]
    rfl
  have hqLeading : q.leadingCoeff = qa := by
    change q.normalize.coeffs.headD 0 = qa
    rw [hqcoeffs]
    rfl
  have hpDegree : p.natDegree = pas.length := by
    change p.normalize.coeffs.length - 1 = pas.length
    rewrite [hpcoeffs]
    exact Nat.succ_sub_one _
  have hqDegree : q.natDegree = qas.length := by
    change q.normalize.coeffs.length - 1 = qas.length
    rewrite [hqcoeffs]
    exact Nat.succ_sub_one _
  let base := Basic.DensePolynomial.shift 1 (0 : Basic.DensePolynomial K) + Basic.DensePolynomial.scale pa q
  have hbase : base = Basic.DensePolynomial.scale pa q := by
    dsimp only [base]
    rw [Basic.DensePolynomial.shift, if_pos (show (0 : Basic.DensePolynomial K).isZero = true by rfl),
      Basic.DensePolynomial.zero_add_normalize, Basic.DensePolynomial.normalize_scale]
  have hbaseCoeffs : base.coeffs =
      pa * qa :: qas.map (pa * ·) := by
    rw [hbase, Basic.DensePolynomial.scale_coeffs_of_ne_zero hpa, hqcoeffs]
    rfl
  have hbaseBound : q.normalize.coeffs.length ≤ base.coeffs.length := by
    rewrite [hqcoeffs, hbaseCoeffs, List.length_cons, List.length_cons, Map.length_map]
    exact Nat.le_refl _
  obtain ⟨out, hout, houtLength⟩ :=
    Basic.DensePolynomial.foldl_mulStep_preserves_leading_shape q pas base (pa * qa)
      (qas.map (pa * ·)) hbaseCoeffs (Basic.DensePolynomial.mul_ne_zero_direct hpa hqa) hbaseBound
  have hmul : p * q =
      pas.foldl (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) base := by
    rw [show p * q = Basic.DensePolynomial.mulPolynomial p q from rfl, Basic.DensePolynomial.mulPolynomial]
    rw [← Basic.DensePolynomial.foldl_mulStep_dropWhile_zero q p.coeffs]
    change p.normalize.coeffs.foldl
        (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 = _
    rw [hpcoeffs]
    rfl
  refine ⟨out, ?_, ?_⟩
  · rw [hmul, hout, hpLeading, hqLeading]
  · rw [houtLength, Map.length_map, hpDegree, hqDegree]
    exact Nat.add_comm _ _

/-- Two represented nonzero dense polynomials have product degree equal to the sum of their degrees.

The exact product coefficient shape retains a nonzero head. Its original
leading-zero scan keeps the whole list, and subtracting that head from the
coefficient count gives the sum of the retained input tail lengths. -/
theorem natDegree_mul {p q : Basic.DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  obtain ⟨out, hcoeffs, hout⟩ := Basic.DensePolynomial.mul_coeffs_shape hp hq
  have hleading : p.leadingCoeff * q.leadingCoeff ≠ 0 :=
    Basic.DensePolynomial.mul_ne_zero_direct (Basic.DensePolynomial.leadingCoeff_ne_zero hp)
      (Basic.DensePolynomial.leadingCoeff_ne_zero hq)
  have hnormalized : (p * q).normalize.coeffs =
      p.leadingCoeff * q.leadingCoeff :: out := by
    change (p * q).coeffs.dropWhile (· = 0) = _
    rw [hcoeffs, DropWhile.cons_of_false (fun value : K => decide (value = 0))
      (p.leadingCoeff * q.leadingCoeff) out (decide_eq_false hleading)]
  change (p * q).normalize.coeffs.length - 1 = _
  rw [hnormalized]
  rewrite [List.length_cons, Nat.succ_sub_one]
  exact hout

/-- For represented nonzero factors, the product leading coefficient is the product of their leading coefficients.

The product's exact coefficient shape begins with the product of the two
retained nonzero heads. Original leading-zero normalization preserves that
entry, so its head readback is the displayed scalar product. -/
theorem leadingCoeff_mul {p q : Basic.DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  obtain ⟨out, hcoeffs, _⟩ := Basic.DensePolynomial.mul_coeffs_shape hp hq
  have hleading : p.leadingCoeff * q.leadingCoeff ≠ 0 :=
    Basic.DensePolynomial.mul_ne_zero_direct (Basic.DensePolynomial.leadingCoeff_ne_zero hp)
      (Basic.DensePolynomial.leadingCoeff_ne_zero hq)
  change (p * q).normalize.coeffs.headD 0 = _
  change ((p * q).coeffs.dropWhile (· = 0)).headD 0 = _
  rw [hcoeffs, DropWhile.cons_of_false (fun value : K => decide (value = 0))
      (p.leadingCoeff * q.leadingCoeff) out (decide_eq_false hleading)]
  rfl

/-- Dense Horner multiplication returns an already normalized polynomial.

A zero-factor branch returns the original empty representation. Otherwise
the exact product coefficient shape has a nonzero head, so the existing
leading-zero scan retains that entire multiplication result. -/
theorem normalize_mul (p q : Basic.DensePolynomial K) :
    (p * q).normalize = p * q := by
  by_cases hp : p.isZero = true
  · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_left hp]
    rfl
  · have hpFalse : p.isZero = false := Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true p.isZero hp
    by_cases hq : q.isZero = true
    · rw [Basic.DensePolynomial.mul_eq_zero_of_isZero_right hq]
      rfl
    · have hqFalse : q.isZero = false := Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true q.isZero hq
      obtain ⟨out, hcoeffs, _⟩ := Basic.DensePolynomial.mul_coeffs_shape hpFalse hqFalse
      have hleading : p.leadingCoeff * q.leadingCoeff ≠ 0 :=
        Basic.DensePolynomial.mul_ne_zero_direct (Basic.DensePolynomial.leadingCoeff_ne_zero hpFalse)
          (Basic.DensePolynomial.leadingCoeff_ne_zero hqFalse)
      apply Basic.DensePolynomial.ext
      change (p * q).coeffs.dropWhile (· = 0) = (p * q).coeffs
      rw [hcoeffs, DropWhile.cons_of_false (fun value : K => decide (value = 0))
      (p.leadingCoeff * q.leadingCoeff) out (decide_eq_false hleading)]

/-- The finite dense Horner product of two nonzero polynomials is nonzero.
This proof tracks its leading coefficient directly and does not pass through
Mathlib's sparse-polynomial finite-support representation.

The original multiplication fold retains a nonzero leading entry from its
first nonzero coefficient onward. The existing normalization scan therefore
keeps a nonempty list, whose original emptiness test is false. -/
theorem isZero_mul_eq_false {p q : Basic.DensePolynomial K}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).isZero = false := by
  obtain ⟨pa, pas, hpcoeffs, hpa⟩ :
      ∃ pa pas, p.normalize.coeffs = pa :: pas ∧ pa ≠ 0 := by
    cases hpcase : p.normalize.coeffs with
    | nil =>
        have hp' : p.normalize.coeffs.isEmpty = false := hp
        rw [hpcase] at hp'
        exact Bool.noConfusion hp'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := Basic.DensePolynomial.leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hpcase, List.headD_cons] using hlead
  obtain ⟨qa, qas, hqcoeffs, hqa⟩ :
      ∃ qa qas, q.normalize.coeffs = qa :: qas ∧ qa ≠ 0 := by
    cases hqcase : q.normalize.coeffs with
    | nil =>
        have hq' : q.normalize.coeffs.isEmpty = false := hq
        rw [hqcase] at hq'
        exact Bool.noConfusion hq'
    | cons a as =>
        refine ⟨a, as, rfl, ?_⟩
        have hlead := Basic.DensePolynomial.leadingCoeff_ne_zero hq
        change q.normalize.coeffs.headD 0 ≠ 0 at hlead
        simpa only [hqcase, List.headD_cons] using hlead
  have hbase : Basic.DensePolynomial.HasLeadingAtLeast q
      (Basic.DensePolynomial.shift 1 (0 : Basic.DensePolynomial K) + Basic.DensePolynomial.scale pa q) := by
    rw [show Basic.DensePolynomial.shift 1 (0 : Basic.DensePolynomial K) + Basic.DensePolynomial.scale pa q =
      Basic.DensePolynomial.scale pa q by
      rw [Basic.DensePolynomial.shift, if_pos (show (0 : Basic.DensePolynomial K).isZero = true by rfl),
        Basic.DensePolynomial.zero_add_normalize, Basic.DensePolynomial.normalize_scale]]
    refine ⟨pa * qa, qas.map (pa * ·), ?_, Basic.DensePolynomial.mul_ne_zero_direct hpa hqa, ?_⟩
    · rw [Basic.DensePolynomial.scale_coeffs_of_ne_zero hpa, hqcoeffs]
      rfl
    · rewrite [Basic.DensePolynomial.scale_coeffs_of_ne_zero hpa, Map.length_map]
      exact Nat.le_refl _
  have hfold := Basic.DensePolynomial.foldl_mulStep_preserves_hasLeadingAtLeast q pas hbase
  rcases hfold with ⟨a, as, hcoeffs, ha, _⟩
  have hmul : p * q =
      pas.foldl (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q)
        (Basic.DensePolynomial.shift 1 0 + Basic.DensePolynomial.scale pa q) := by
    rw [show p * q = Basic.DensePolynomial.mulPolynomial p q from rfl, Basic.DensePolynomial.mulPolynomial]
    rw [← Basic.DensePolynomial.foldl_mulStep_dropWhile_zero q p.coeffs]
    change p.normalize.coeffs.foldl
        (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) 0 = _
    rw [hpcoeffs]
    rfl
  rw [hmul]
  exact Basic.DensePolynomial.isZero_false_of_coeffs_cons hcoeffs ha

/-- Evaluating a polynomial multiplication fold yields its scalar Horner recurrence.

Each coefficient contribution is multiplied by the fixed right factor's value, and the initial scalar state is the
accumulator polynomial's value. -/
private theorem eval_foldl_mulPolynomial (x : K) (q : Basic.DensePolynomial K)
    (cs : List K) (acc : Basic.DensePolynomial K) :
    (cs.foldl (fun value a => Basic.DensePolynomial.shift 1 value + Basic.DensePolynomial.scale a q) acc).eval x =
      cs.foldl (fun value a => value * x + a * q.eval x) (acc.eval x) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, Basic.DensePolynomial.eval_add, Basic.DensePolynomial.eval_shift, Basic.DensePolynomial.eval_scale]
      rewrite [pow_one]
      exact Eq.refl _

omit [DecidableEq K] in
/-- Scaling each Horner contribution and the initial accumulator scales the final value. -/
private theorem foldl_scaled_horner (x c : K) (cs : List K) (acc : K) :
    cs.foldl (fun value a => value * x + a * c) (acc * c) =
      cs.foldl (fun value a => value * x + a) acc * c := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [show acc * c * x + a * c = (acc * x + a) * c by ring1, ih]

/-- Evaluation of dense multiplication is multiplication of the two values. -/
@[simp] theorem eval_mul (p q : Basic.DensePolynomial K) (x : K) :
    (p * q).eval x = p.eval x * q.eval x := by
  rw [show p * q = Basic.DensePolynomial.mulPolynomial p q from rfl, Basic.DensePolynomial.mulPolynomial,
    Basic.DensePolynomial.eval_foldl_mulPolynomial]
  rw [Basic.DensePolynomial.eval_zero]
  simpa only [zero_mul, Basic.DensePolynomial.eval, Basic.DensePolynomial.evalCoeffs] using
    Basic.DensePolynomial.foldl_scaled_horner x (q.eval x) p.coeffs 0
end Purelib.Polynomial.Dense.Basic.DensePolynomial

end
