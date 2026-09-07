import FTA.DensePolynomialBridge
import FTA.DenseSquarefree

/-!
# Signed Euclidean chains and finite endpoint variation

This is the executable core of Section 3.  We use doubled variations, so all
values are integers and endpoint zeros require no half-integer representation.
-/

namespace FTA.Sturm

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial

/-- Decidable sign in `{-1,0,1}`. -/
def ratSign (x : ℚ) : ℤ :=
  if x < 0 then -1 else if x = 0 then 0 else 1

@[simp] theorem ratSign_zero : ratSign 0 = 0 := by simp [ratSign]

theorem ratSign_of_pos {x : ℚ} (hx : 0 < x) : ratSign x = 1 := by
  simp [ratSign, hx.ne', not_lt.mpr hx.le]

theorem ratSign_of_neg {x : ℚ} (hx : x < 0) : ratSign x = -1 := by
  simp [ratSign, hx]

theorem ratSign_eq_zero_iff {x : ℚ} : ratSign x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_cases hx : x < 0
    · rw [ratSign_of_neg hx] at h
      norm_num at h
    · by_cases hx0 : x = 0
      · exact hx0
      · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx0)
        rw [ratSign_of_pos hxpos] at h
        norm_num at h
  · rintro rfl
    exact ratSign_zero

theorem ratSign_neg (x : ℚ) : ratSign (-x) = -ratSign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hnegpos : 0 < -x := neg_pos.mpr hx
    rw [ratSign_of_pos hnegpos, ratSign_of_neg hx]
    norm_num
  · subst x
    simp
  · have hnegneg : -x < 0 := by linarith
    rw [ratSign_of_neg hnegneg, ratSign_of_pos hx]

theorem ratSign_mul (x y : ℚ) : ratSign (x * y) = ratSign x * ratSign y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [ratSign_of_pos (mul_pos_of_neg_of_neg hx hy),
      ratSign_of_neg hx, ratSign_of_neg hy]
    norm_num
  · simp
  · rw [ratSign_of_neg (mul_neg_of_neg_of_pos hx hy),
      ratSign_of_neg hx, ratSign_of_pos hy]
    norm_num
  · simp
  · simp
  · simp
  · rw [ratSign_of_neg (mul_neg_of_pos_of_neg hx hy),
      ratSign_of_pos hx, ratSign_of_neg hy]
    norm_num
  · simp
  · rw [ratSign_of_pos (mul_pos hx hy), ratSign_of_pos hx,
      ratSign_of_pos hy]
    norm_num

theorem ratSign_eq_of_mul_pos {x y : ℚ} (hxy : 0 < x * y) :
    ratSign x = ratSign y := by
  rcases mul_pos_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [ratSign_of_pos hx, ratSign_of_pos hy]
  · rw [ratSign_of_neg hx, ratSign_of_neg hy]

/-- One doubled variation contribution. -/
def signJump (x y : ℚ) : ℕ := (ratSign x - ratSign y).natAbs

theorem signJump_comm (x y : ℚ) : signJump x y = signJump y x := by
  dsimp [signJump]
  rw [show ratSign y - ratSign x = -(ratSign x - ratSign y) by ring, Int.natAbs_neg]

theorem signJump_neg_neg (x y : ℚ) : signJump (-x) (-y) = signJump x y := by
  simp only [signJump, ratSign_neg]
  rw [show -ratSign x - -ratSign y = -(ratSign x - ratSign y) by ring, Int.natAbs_neg]

theorem signJump_self (x : ℚ) : signJump x x = 0 := by
  simp [signJump]

theorem signJump_zero_neg_of_ne {x : ℚ} (hx : x ≠ 0) :
    signJump x 0 + signJump 0 (-x) = 2 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [signJump, signJump, ratSign_of_neg hxneg, ratSign_zero,
      ratSign_neg, ratSign_of_neg hxneg]
    norm_num
  · rw [signJump, signJump, ratSign_of_pos hxpos, ratSign_zero,
      ratSign_neg, ratSign_of_pos hxpos]
    norm_num

theorem signJump_zero_of_ne {x : ℚ} (hx : x ≠ 0) : signJump 0 x = 1 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [signJump, ratSign_zero, ratSign_of_neg hxneg]
    norm_num
  · rw [signJump, ratSign_zero, ratSign_of_pos hxpos]
    norm_num

/-- The complete adjacent-sign table used in Cauchy--Sturm inversion.  Unless
both entries vanish, passing from `x` through `y` to `-x` contributes exactly
two doubled half-jumps. -/
theorem signJump_add_signJump_neg {x y : ℚ}
    (hnotBoth : x ≠ 0 ∨ y ≠ 0) :
    signJump x y + signJump y (-x) = 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [signJump, ratSign_of_neg, ratSign_of_pos]

/-- If the two outer values have opposite strict signs, the two adjacent
doubled jumps through any middle value sum to two. -/
theorem signJump_add_signJump_of_outer_mul_neg {x y z : ℚ}
    (hxz : x * z < 0) : signJump x y + signJump y z = 2 := by
  rcases mul_neg_iff.mp hxz with ⟨hx, hz⟩ | ⟨hx, hz⟩ <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [signJump, ratSign_of_neg, ratSign_of_pos]

theorem signJump_eq_two_of_mul_neg {x y : ℚ} (hxy : x * y < 0) :
    signJump x y = 2 := by
  rcases mul_neg_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    simp [signJump, ratSign_of_neg, ratSign_of_pos, hx, hy]

theorem signJump_eq_zero_of_mul_pos {x y : ℚ} (hxy : 0 < x * y) :
    signJump x y = 0 := by
  rcases mul_pos_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
    simp [signJump, ratSign_of_neg, ratSign_of_pos, hx, hy]

theorem signJump_add_signJump_mul_of_mul_neg {a b x y : ℚ}
    (hab : a * b < 0) (hnotBoth : x ≠ 0 ∨ y ≠ 0) :
    signJump x y + signJump (a * x) (b * y) = 2 := by
  rcases (mul_neg_iff.mp hab) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [signJump, ratSign_mul, ratSign_of_neg, ratSign_of_pos]

/-- The three initial jumps in the equal-degree inversion case depend only on
the sign of the leading-coefficient ratio, not on the endpoint values. -/
theorem equalDegree_initial_sign_sum {p q r c k : ℚ}
    (hc : c ≠ 0) (hck : c * k = -1) (hrelation : p = c * q - r)
    (hpq : p ≠ 0 ∨ q ≠ 0) (hqr : q ≠ 0 ∨ r ≠ 0) :
    signJump p q + signJump q r + signJump p (k * r) =
      if 0 < c then 2 else 4 := by
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hkpos : 0 < k := by nlinarith
    rcases lt_trichotomy p 0 with hp | rfl | hp <;>
      rcases lt_trichotomy q 0 with hq | rfl | hq <;>
      rcases lt_trichotomy r 0 with hr | rfl | hr
    all_goals try { norm_num at hpq }
    all_goals try { norm_num at hqr }
    all_goals try { exfalso; nlinarith }
    all_goals
      simp only [signJump, ratSign_mul, ratSign_zero]
      repeat' first
        | rw [ratSign_of_neg (by assumption)]
        | rw [ratSign_of_pos (by assumption)]
      rw [if_neg (not_lt_of_ge hcneg.le)]
      norm_num
  · have hkneg : k < 0 := by nlinarith
    rcases lt_trichotomy p 0 with hp | rfl | hp <;>
      rcases lt_trichotomy q 0 with hq | rfl | hq <;>
      rcases lt_trichotomy r 0 with hr | rfl | hr
    all_goals try { norm_num at hpq }
    all_goals try { norm_num at hqr }
    all_goals try { exfalso; nlinarith }
    all_goals
      simp only [signJump, ratSign_mul, ratSign_zero]
      repeat' first
        | rw [ratSign_of_neg (by assumption)]
        | rw [ratSign_of_pos (by assumption)]
      rw [if_pos hcpos]
      norm_num

/-- Twice the sign variation of a finite rational list, equation (7). -/
def variation2 : List ℚ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => signJump x y + variation2 (y :: xs)

@[simp] theorem variation2_nil : variation2 [] = 0 := rfl
@[simp] theorem variation2_singleton (x : ℚ) : variation2 [x] = 0 := rfl

theorem signJump_congr {x x' y y' : ℚ}
    (hx : ratSign x = ratSign x') (hy : ratSign y = ratSign y') :
    signJump x y = signJump x' y' := by
  simp only [signJump, hx, hy]

/-- Doubled variation depends only on the finite list of decidable signs. -/
theorem variation2_congr_of_forall₂_sign :
    ∀ {xs ys : List ℚ},
      List.Forall₂ (fun x y => ratSign x = ratSign y) xs ys →
        variation2 xs = variation2 ys
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | x :: x' :: xs, y :: y' :: ys,
      List.Forall₂.cons hxy (List.Forall₂.cons hxy' htail) => by
      rw [variation2, variation2,
        signJump_congr hxy hxy',
        variation2_congr_of_forall₂_sign (List.Forall₂.cons hxy' htail)]

/-- If every sign except one interior entry agrees, and the two jumps adjacent
to that entry have the same total, then the complete finite variation agrees. -/
theorem variation2_eq_of_middle_change :
    ∀ {prefixA prefixB suffixA suffixB : List ℚ}
      {leftA leftB middleA middleB rightA rightB : ℚ},
      List.Forall₂ (fun x y => ratSign x = ratSign y) prefixA prefixB →
      List.Forall₂ (fun x y => ratSign x = ratSign y) suffixA suffixB →
      ratSign leftA = ratSign leftB →
      ratSign rightA = ratSign rightB →
      signJump leftA middleA + signJump middleA rightA =
        signJump leftB middleB + signJump middleB rightB →
      variation2 (prefixA ++ leftA :: middleA :: rightA :: suffixA) =
        variation2 (prefixB ++ leftB :: middleB :: rightB :: suffixB)
  | [], [], suffixA, suffixB, leftA, leftB, middleA, middleB, rightA, rightB,
      .nil, hsuffix, hleft, hright, hlocal => by
        have htail := variation2_congr_of_forall₂_sign
          (List.Forall₂.cons hright hsuffix)
        simp only [List.nil_append, variation2]
        omega
  | headA :: prefixA, headB :: prefixB, suffixA, suffixB,
      leftA, leftB, middleA, middleB,
      rightA, rightB, List.Forall₂.cons hhead hprefix, hsuffix, hleft,
      hright, hlocal => by
        cases hprefix with
        | nil =>
            have hrecursive := variation2_eq_of_middle_change
              (prefixA := []) (prefixB := []) List.Forall₂.nil
              hsuffix hleft hright hlocal
            have hrecursive' :
                variation2 (leftA :: middleA :: rightA :: suffixA) =
                  variation2 (leftB :: middleB :: rightB :: suffixB) := by
              simpa only [List.nil_append] using hrecursive
            change signJump headA leftA +
                variation2 (leftA :: middleA :: rightA :: suffixA) =
              signJump headB leftB +
                variation2 (leftB :: middleB :: rightB :: suffixB)
            rw [signJump_congr hhead hleft, hrecursive']
        | @cons nextA nextB tailA tailB hnext htail =>
            have hrecursive := variation2_eq_of_middle_change
              (prefixA := nextA :: tailA) (prefixB := nextB :: tailB)
              (List.Forall₂.cons hnext htail) hsuffix hleft hright hlocal
            change signJump headA nextA +
                variation2
                  (nextA :: tailA ++ leftA :: middleA :: rightA :: suffixA) =
              signJump headB nextB +
                variation2
                  (nextB :: tailB ++ leftB :: middleB :: rightB :: suffixB)
            rw [signJump_congr hhead hnext, hrecursive]

/-- Last value of the nonempty list represented by a head and a tail. -/
def terminalValue (x : ℚ) : List ℚ → ℚ
  | [] => x
  | y :: values => terminalValue y values

/-- One doubled sign jump differs from its signed endpoint difference by an
even integer. -/
theorem signJump_sub_signDifference_even (x y : ℚ) :
    Even (((signJump x y : ℕ) : ℤ) - (ratSign x - ratSign y)) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [signJump, ratSign_of_neg, ratSign_of_pos]
  all_goals decide

/-- Every interior signed endpoint difference cancels: the doubled variation
minus its first-to-last signed difference is even. -/
theorem variation2_sub_signDifference_even : ∀ (x : ℚ) (values : List ℚ),
    Even (((variation2 (x :: values) : ℕ) : ℤ) -
      (ratSign x - ratSign (terminalValue x values)))
  | x, [] => by
      refine ⟨0, ?_⟩
      simp [terminalValue]
  | x, y :: values => by
      rcases signJump_sub_signDifference_even x y with ⟨a, ha⟩
      rcases variation2_sub_signDifference_even y values with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simp only [variation2, terminalValue, Nat.cast_add]
      calc
        ((signJump x y : ℕ) : ℤ) + ((variation2 (y :: values) : ℕ) : ℤ) -
            (ratSign x - ratSign (terminalValue y values)) =
            (((signJump x y : ℕ) : ℤ) - (ratSign x - ratSign y)) +
              (((variation2 (y :: values) : ℕ) : ℤ) -
                (ratSign y - ratSign (terminalValue y values))) := by ring
        _ = (a + a) + (b + b) := by rw [ha, hb]
        _ = (a + b) + (a + b) := by ring

theorem ratSign_sub_even_of_ne_zero {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Even (ratSign x - ratSign y) := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos <;>
    rcases lt_or_gt_of_ne hy with hyneg | hypos <;>
    simp_all [ratSign_of_neg, ratSign_of_pos, Even]
  · exact ⟨0, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- Against a nonzero terminal sign, the signed endpoint difference has the
same parity as the explicit zero flag of its first endpoint. -/
theorem ratSign_sub_terminal_sub_zeroFlag_even
    {x y : ℚ} (hy : y ≠ 0) :
    Even ((ratSign x - ratSign y) - (if x = 0 then 1 else 0)) := by
  by_cases hx : x = 0
  · subst x
    rcases lt_or_gt_of_ne hy with hyneg | hypos
    · exact ⟨0, by simp [ratSign_of_neg hyneg]⟩
    · exact ⟨-1, by simp [ratSign_of_pos hypos]⟩
  · simpa [hx] using ratSign_sub_even_of_ne_zero hx hy

/-- A finite sign list with nonzero first and last values has even doubled
variation, including when any interior value is exactly zero. -/
theorem variation2_even_of_first_terminal_ne_zero
    {x : ℚ} {values : List ℚ} (hx : x ≠ 0)
    (hlast : terminalValue x values ≠ 0) : Even (variation2 (x :: values)) := by
  have variationEven := variation2_sub_signDifference_even x values
  have endpointsEven := ratSign_sub_even_of_ne_zero hx hlast
  have totalEven := variationEven.add endpointsEven
  have castEven : Even ((variation2 (x :: values) : ℕ) : ℤ) := by
    simpa only [sub_add_cancel] using totalEven
  exact (Int.even_coe_nat _).mp castEven

theorem variation2_map_neg : ∀ values : List ℚ,
    variation2 (values.map (-·)) = variation2 values
  | [] => rfl
  | [_] => rfl
  | x :: y :: values => by
      simp only [List.map_cons, variation2, signJump_neg_neg]
      exact congrArg (signJump x y + ·) (variation2_map_neg (y :: values))

/-- Alternating scalar multiplication of a rational sign list. -/
def alternatingMul (a b : ℚ) : List ℚ → List ℚ
  | [] => []
  | x :: values => a * x :: alternatingMul b a values

/-- No two adjacent entries of a finite sign list vanish together. -/
def NoAdjacentZero : List ℚ → Prop
  | [] => True
  | [_] => True
  | x :: y :: values => (x ≠ 0 ∨ y ≠ 0) ∧ NoAdjacentZero (y :: values)

theorem variation2_add_alternatingMul {a b : ℚ} (hab : a * b < 0) :
    ∀ values : List ℚ, NoAdjacentZero values →
      variation2 values + variation2 (alternatingMul a b values) =
        2 * (values.length - 1)
  | [], _ => rfl
  | [_], _ => by simp [alternatingMul]
  | x :: y :: values, hvalues => by
      have hlocal := signJump_add_signJump_mul_of_mul_neg hab hvalues.1
      have htail := variation2_add_alternatingMul (a := b) (b := a)
        (by simpa [mul_comm] using hab) (y :: values) hvalues.2
      simp only [alternatingMul, variation2, List.length_cons] at htail ⊢
      omega

abbrev RatPolynomial := DensePolynomial ℚ

/-- Two dense rational polynomials have no common exact rational zero.  This
pointwise consequence of coprimality is the condition consumed by finite sign
tables at rational endpoints. -/
def NoCommonRationalZero (p q : RatPolynomial) : Prop :=
  ∀ x, ¬(p.eval x = 0 ∧ q.eval x = 0)

/-- Fuel-bounded signed remainder chain. -/
def signedRemainderChainAux : ℕ → RatPolynomial → RatPolynomial → List RatPolynomial
  | 0, p, q => [p, q]
  | fuel + 1, p, q =>
      if q.isZero then [p]
      else
        let dm := divMod p q
        if dm.remainder.isZero then [p, q]
        else p :: signedRemainderChainAux fuel q (-dm.remainder)

/-- The same signed Euclidean chain with termination checked directly from
strict normalized-degree descent. -/
def signedRemainderChainWF (p q : RatPolynomial) : List RatPolynomial :=
  if _hq : q.isZero then [p]
  else
    let dm := divMod p q
    if _hr : dm.remainder.isZero then [p, q]
    else p :: signedRemainderChainWF q (-dm.remainder)
termination_by q.degreeCount
decreasing_by
  have hqFalse : q.isZero = false := by simpa using _hq
  have hrFalse : (divMod p q).remainder.isZero = false := by simpa using _hr
  rcases divMod_remainder_small p q hqFalse with hzero | hdegree
  · exact (_hr hzero).elim
  · have hrCount := natDegree_add_one_eq_degreeCount hrFalse
    have hqCount := natDegree_add_one_eq_degreeCount hqFalse
    rw [degreeCount_neg]
    omega

/-- Definition 3.1's finite signed Euclidean chain.  Termination is certified
directly by strict normalized-degree descent. -/
def signedRemainderChain (p q : RatPolynomial) : List RatPolynomial :=
  signedRemainderChainWF p q

/-- Negating both inputs negates every member of the finite signed remainder
chain.  The proof follows the executable recursion and its checked degree
descent, rather than appealing to an abstract Euclidean sequence. -/
theorem signedRemainderChainWF_neg (p q : RatPolynomial) :
    signedRemainderChainWF (-p) (-q) =
      (signedRemainderChainWF p q).map (-·) := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rw [signedRemainderChainWF, signedRemainderChainWF]
      simp only [isZero_neg]
      split
      · simp
      · rename_i hq
        have hqFalse : q.isZero = false := by simpa using hq
        rw [divMod_remainder_neg_both p q hqFalse]
        simp only [isZero_neg]
        split
        · simp
        · rename_i hr
          simp only [List.map_cons, DensePolynomial.neg_neg]
          congr 1
          have hrFalse : (divMod p q).remainder.isZero = false := by
            simpa using hr
          have hcount : (-((divMod p q).remainder)).degreeCount < n := by
            rw [degreeCount_neg, ← hn]
            exact divMod_remainder_degreeCount_lt p q hqFalse
          simpa using ih _ hcount q (-((divMod p q).remainder)) rfl

theorem signedRemainderChain_neg (p q : RatPolynomial) :
    signedRemainderChain (-p) (-q) =
      (signedRemainderChain p q).map (-·) :=
  signedRemainderChainWF_neg p q

/-- Alternating rescaling of a finite signed chain. -/
def alternatingScale (a b : ℚ) : List RatPolynomial → List RatPolynomial
  | [] => []
  | p :: chain => scale a p :: alternatingScale b a chain

/-- Scaling the two initial polynomials by nonzero rationals scales every even
and odd chain member by the corresponding alternating scalar. -/
theorem signedRemainderChainWF_scale (p q : RatPolynomial) {a b : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    signedRemainderChainWF (scale a p) (scale b q) =
      alternatingScale a b (signedRemainderChainWF p q) := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q a b with
  | h n ih =>
      rw [signedRemainderChainWF, signedRemainderChainWF]
      rw [isZero_scale_of_ne_zero hb]
      split
      · simp [alternatingScale]
      · rename_i hq
        have hqFalse : q.isZero = false := by simpa using hq
        dsimp only
        rw [divMod_remainder_scale p q ha hb hqFalse,
          isZero_scale_of_ne_zero ha]
        split
        · simp [alternatingScale]
        · rename_i hr
          simp only [alternatingScale]
          congr 1
          rw [← scale_neg]
          have hrFalse : (divMod p q).remainder.isZero = false := by
            simpa using hr
          have hcount : (-((divMod p q).remainder)).degreeCount < n := by
            rw [degreeCount_neg, ← hn]
            exact divMod_remainder_degreeCount_lt p q hqFalse
          exact ih _ hcount q (-((divMod p q).remainder)) hb ha rfl

theorem signedRemainderChain_scale (p q : RatPolynomial) {a b : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    signedRemainderChain (scale a p) (scale b q) =
      alternatingScale a b (signedRemainderChain p q) :=
  signedRemainderChainWF_scale p q ha hb

/-- The structurally terminating chain has the sharp degree-count length
bound: at most one list entry per divisor degree slot, plus the initial term. -/
theorem signedRemainderChainWF_length_le (p q : RatPolynomial) :
    (signedRemainderChainWF p q).length ≤ q.degreeCount + 1 := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rw [signedRemainderChainWF]
      split
      · simp
      · rename_i hq
        dsimp only
        split
        · have hqFalse : q.isZero = false := by simpa using hq
          have hqPos := degreeCount_pos_of_isZero_false hqFalse
          simp only [List.length_cons, List.length_nil]
          omega
        · rename_i hr
          simp only [List.length_cons]
          have hqFalse : q.isZero = false := by simpa using hq
          have hrFalse : (divMod p q).remainder.isZero = false := by simpa using hr
          rcases divMod_remainder_small p q hqFalse with hzero | hdegree
          · exact (hr hzero).elim
          · have hrCount := natDegree_add_one_eq_degreeCount hrFalse
            have hqCount := natDegree_add_one_eq_degreeCount hqFalse
            have hcount : (-((divMod p q).remainder)).degreeCount < n := by
              rw [degreeCount_neg, ← hn]
              omega
            have hrec := ih _ hcount q (-((divMod p q).remainder)) rfl
            omega

/-- The finite signed chain has an explicit coefficient-computable length
bound, independently of coefficient values. -/
theorem signedRemainderChainAux_length_le (fuel : ℕ) (p q : RatPolynomial) :
    (signedRemainderChainAux fuel p q).length ≤ fuel + 2 := by
  induction fuel generalizing p q with
  | zero => simp [signedRemainderChainAux]
  | succ fuel ih =>
      rw [signedRemainderChainAux]
      split
      · simp
      · dsimp only
        split
        · simp
        · simp only [List.length_cons]
          have := ih q (-((divMod p q).remainder))
          omega

theorem signedRemainderChain_length_le (p q : RatPolynomial) :
    (signedRemainderChain p q).length ≤ q.degreeCount + 1 := by
  exact signedRemainderChainWF_length_le p q

theorem first_mem_signedRemainderChain (p q : RatPolynomial) :
    p ∈ signedRemainderChain p q := by
  rw [signedRemainderChain, signedRemainderChainWF]
  split
  · simp
  · dsimp only
    split <;> simp

theorem signedRemainderChain_eq_cons (p q : RatPolynomial) :
    ∃ tail, signedRemainderChain p q = p :: tail := by
  rw [signedRemainderChain, signedRemainderChainWF]
  split
  · exact ⟨[], rfl⟩
  · dsimp only
    split
    · exact ⟨[q], rfl⟩
    · exact ⟨signedRemainderChainWF q (-((divMod p q).remainder)), rfl⟩

/-- Starting from two represented nonzero inputs, every member emitted by the
structurally recursive signed chain is represented nonzero. -/
theorem signedRemainderChainWF_all_nonzero {p q : RatPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (signedRemainderChainWF p q).Forall (fun r => r.isZero = false) := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rw [signedRemainderChainWF]
      split
      · rename_i hqZero
        simp [hq] at hqZero
      · rename_i hqNonzero
        dsimp only
        split
        · simp [hp, hq]
        · rename_i hrNonzero
          simp only [List.forall_cons, hp, true_and]
          have hrFalse : (divMod p q).remainder.isZero = false := by
            simpa using hrNonzero
          have hnextFalse : (-((divMod p q).remainder)).isZero = false := by
            simpa using hrFalse
          have hcount : (-((divMod p q).remainder)).degreeCount < n := by
            rw [degreeCount_neg, ← hn]
            exact divMod_remainder_degreeCount_lt p q hq
          exact ih _ hcount hq hnextFalse rfl

theorem signedRemainderChain_all_nonzero {p q : RatPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (signedRemainderChain p q).Forall (fun r => r.isZero = false) :=
  signedRemainderChainWF_all_nonzero hp hq

/-- Every nonzero signed remainder has strictly smaller specification degree
than the preceding divisor.  This is the degree-descent assertion in (8). -/
theorem signedRemainder_degree_lt (p q : RatPolynomial) (hq : q.isZero = false) :
    (divMod p q).remainder.isZero = true ∨
      (-((divMod p q).remainder)).toPolynomial.degree < q.toPolynomial.degree := by
  rcases divMod_remainder_small p q hq with hzero | hdegree
  · exact Or.inl hzero
  · by_cases hr : (divMod p q).remainder.isZero = true
    · exact Or.inl hr
    · right
      have hrFalse : (divMod p q).remainder.isZero = false := by simpa using hr
      have hrP := toPolynomial_ne_zero_of_isZero_false hrFalse
      have hqP := toPolynomial_ne_zero_of_isZero_false hq
      rw [toPolynomial_neg, Polynomial.degree_neg,
        Polynomial.degree_eq_natDegree hrP, Polynomial.degree_eq_natDegree hqP,
        natDegree_toPolynomial hrFalse, natDegree_toPolynomial hq]
      exact_mod_cast hdegree

/-- Equation (8) for one executable signed-remainder step, stated through
exact Horner evaluation. -/
theorem signedStep_eval_identity (p q : RatPolynomial) (x : ℚ) :
    p.eval x = q.eval x * (divMod p q).quotient.eval x -
      (-((divMod p q).remainder)).eval x := by
  have h := divMod_eval_equation p q x
  rw [eval_neg]
  linarith

/-- The exact local zero-event rule behind Theorem 3.2(c).  At a zero of the
middle chain member, the signed recurrence makes its two neighbors nonzero
and opposite, so their two doubled half-jumps sum to two. -/
theorem signedStep_zero_event (p q : RatPolynomial) (x : ℚ)
    (hq : q.eval x = 0) (hp : p.eval x ≠ 0) :
    signJump (p.eval x) (q.eval x) +
      signJump (q.eval x) ((-((divMod p q).remainder)).eval x) = 2 := by
  have hstep := signedStep_eval_identity p q x
  have hnext : (-((divMod p q).remainder)).eval x = -p.eval x := by
    rw [hq, zero_mul] at hstep
    linarith
  rw [hq, hnext]
  exact signJump_zero_neg_of_ne hp

/-- Coprimality is preserved by one signed Euclidean step. -/
theorem noCommonRationalZero_signedStep {p q : RatPolynomial}
    (hcoprime : NoCommonRationalZero p q) :
    NoCommonRationalZero q (-((divMod p q).remainder)) := by
  intro x
  rintro ⟨hq, hnext⟩
  have hstep := signedStep_eval_identity p q x
  have hp : p.eval x = 0 := by rw [hq, hnext, zero_mul, zero_sub] at hstep; exact hstep
  exact hcoprime x ⟨hp, hq⟩

theorem noCommonRationalZero_of_isCoprime {p q : RatPolynomial}
    (hcoprime : IsCoprime p.toPolynomial q.toPolynomial) :
    NoCommonRationalZero p q := by
  rcases hcoprime with ⟨U, V, hbezout⟩
  intro x
  rintro ⟨hp, hq⟩
  have heval := congrArg (Polynomial.eval x) hbezout
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_toPolynomial, eval_toPolynomial, hp, hq] at heval
  norm_num at heval

/-- The terminal member of a coprime signed remainder chain never vanishes at
a rational evaluation point.  In the terminal division case, a zero of the
last divisor would also be a zero of its predecessor; otherwise the statement
descends with the Euclidean degree. -/
theorem terminalValue_signedRemainderChain_eval_ne_zero
    {p q : RatPolynomial} (hq : q.isZero = false)
    (hcoprime : NoCommonRationalZero p q) (x : ℚ) {tail : List RatPolynomial}
    (hchain : signedRemainderChain p q = p :: tail) :
    terminalValue (p.eval x) (tail.map fun r => r.eval x) ≠ 0 := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q tail with
  | h n ih =>
      rw [signedRemainderChain, signedRemainderChainWF] at hchain
      split at hchain
      · rename_i hqZero
        have hqTrue : q.isZero = true := by simpa using hqZero
        simp [hq] at hqTrue
      · rename_i hqNonzero
        dsimp only at hchain
        split at hchain
        · rename_i hremZero
          have hremTrue : (divMod p q).remainder.isZero = true := by
            simpa using hremZero
          have htail : tail = [q] := by
            simpa using (congrArg List.tail hchain).symm
          subst tail
          simp only [List.map_cons, List.map_nil, terminalValue]
          intro hqx
          have hstep := signedStep_eval_identity p q x
          have hremEval : (divMod p q).remainder.eval x = 0 :=
            eval_eq_zero_of_isZero hremTrue x
          rw [hqx, eval_neg, hremEval] at hstep
          norm_num at hstep
          exact hcoprime x ⟨hstep, hqx⟩
        · rename_i hremNonzero
          let next := -((divMod p q).remainder)
          have hnextFalse : next.isZero = false := by
            simpa [next] using hremNonzero
          have hnextCoprime : NoCommonRationalZero q next := by
            simpa [next] using noCommonRationalZero_signedStep hcoprime
          have hcount : next.degreeCount < n := by
            dsimp only [next]
            rw [degreeCount_neg, ← hn]
            exact divMod_remainder_degreeCount_lt p q hq
          have htail : tail = signedRemainderChain q next := by
            simpa [signedRemainderChain, next] using
              (congrArg List.tail hchain).symm
          obtain ⟨recursiveTail, hrecursive⟩ :=
            signedRemainderChain_eq_cons q next
          rw [htail, hrecursive]
          simp only [List.map_cons, terminalValue]
          exact ih next.degreeCount hcount hnextFalse hnextCoprime hrecursive rfl

theorem noAdjacentZero_signedRemainderChain {p q : RatPolynomial}
    (hcoprime : NoCommonRationalZero p q) (x : ℚ) :
    NoAdjacentZero ((signedRemainderChain p q).map fun r => r.eval x) := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rw [signedRemainderChain, signedRemainderChainWF]
      split
      · simp [NoAdjacentZero]
      · rename_i hq
        dsimp only
        have hqFalse : q.isZero = false := by simpa using hq
        have hpair : p.eval x ≠ 0 ∨ q.eval x ≠ 0 := by
          by_cases hp : p.eval x = 0
          · right
            intro hqx
            exact hcoprime x ⟨hp, hqx⟩
          · exact Or.inl hp
        split
        · simpa [NoAdjacentZero] using hpair
        · rename_i hr
          let next := -((divMod p q).remainder)
          have hnext : NoCommonRationalZero q next :=
            noCommonRationalZero_signedStep hcoprime
          have hcount : next.degreeCount < n := by
            dsimp only [next]
            rw [degreeCount_neg, ← hn]
            exact divMod_remainder_degreeCount_lt p q hqFalse
          have hrec := ih next.degreeCount hcount (p := q) (q := next) hnext rfl
          rw [signedRemainderChain] at hrec
          have ⟨tail, htail⟩ := signedRemainderChain_eq_cons q next
          rw [signedRemainderChain] at htail
          rw [show -((divMod p q).remainder) = next by rfl, htail]
          rw [htail] at hrec
          simpa [NoAdjacentZero, hpair] using hrec

/-- Evaluation signs of a finite chain at a rational endpoint. -/
def endpointVariation2 (chain : List RatPolynomial) (x : ℚ) : ℕ :=
  variation2 (chain.map fun p => p.eval x)

/-- Coprimality makes the terminal chain value nonzero, so a nonzero first
value forces the doubled endpoint variation to be even. -/
theorem endpointVariation2_signedRemainderChain_even
    {p q : RatPolynomial} (hq : q.isZero = false)
    (hcoprime : NoCommonRationalZero p q) {x : ℚ} (hp : p.eval x ≠ 0) :
    Even (endpointVariation2 (signedRemainderChain p q) x) := by
  obtain ⟨tail, hchain⟩ := signedRemainderChain_eq_cons p q
  have hterminal := terminalValue_signedRemainderChain_eval_ne_zero
    hq hcoprime x hchain
  rw [endpointVariation2, hchain]
  simp only [List.map_cons]
  exact variation2_even_of_first_terminal_ne_zero hp hterminal

theorem map_eval_alternatingScale (chain : List RatPolynomial)
    (a b x : ℚ) :
    (alternatingScale a b chain).map (fun p => p.eval x) =
      alternatingMul a b (chain.map fun p => p.eval x) := by
  induction chain generalizing a b with
  | nil => rfl
  | cons p chain ih =>
      simp [alternatingScale, alternatingMul, ih]

theorem endpointVariation2_add_alternatingScale
    (chain : List RatPolynomial) {a b : ℚ} (x : ℚ)
    (hab : a * b < 0)
    (hchain : NoAdjacentZero (chain.map fun p => p.eval x)) :
    endpointVariation2 chain x +
        endpointVariation2 (alternatingScale a b chain) x =
      2 * (chain.length - 1) := by
  rw [endpointVariation2, endpointVariation2,
    map_eval_alternatingScale chain a b x]
  simpa only [List.length_map] using
    variation2_add_alternatingMul hab _ hchain

/-- Removing the first member of a nonterminal signed chain exposes exactly
one adjacent sign jump. -/
theorem endpointVariation2_signedRemainderChain_step {p q : RatPolynomial}
    (hq : q.isZero = false) (x : ℚ) :
    endpointVariation2 (signedRemainderChain p q) x =
      signJump (p.eval x) (q.eval x) +
        endpointVariation2
          (signedRemainderChain q (-((divMod p q).remainder))) x := by
  rw [signedRemainderChain, signedRemainderChainWF]
  split
  · rename_i hqZero
    simp [hq] at hqZero
  · dsimp only
    split
    · rename_i hr
      have hrTrue : (divMod p q).remainder.isZero = true := by simpa using hr
      rw [signedRemainderChain, signedRemainderChainWF]
      simp [hrTrue, endpointVariation2, variation2]
    · rename_i hr
      have ⟨tail, htail⟩ := signedRemainderChain_eq_cons
        q (-((divMod p q).remainder))
      rw [signedRemainderChain] at htail
      rw [htail, signedRemainderChain, htail]
      simp [endpointVariation2, variation2]

theorem endpointVariation2_signedRemainderChain_neg (p q : RatPolynomial) (x : ℚ) :
    endpointVariation2 (signedRemainderChain (-p) (-q)) x =
      endpointVariation2 (signedRemainderChain p q) x := by
  rw [signedRemainderChain_neg]
  let chain := signedRemainderChain p q
  have hmap : (chain.map (-·)).map (fun r => r.eval x) =
      (chain.map fun r => r.eval x).map (-·) := by
    induction chain with
    | nil => rfl
    | cons r rs ih => simp [ih]
  unfold endpointVariation2
  rw [hmap]
  exact variation2_map_neg _

/-- Negating the second member of a coprime signed chain changes endpoint
variation by a constant independent of the endpoint.  This is the telescoping
form of the paper's nine-pair sign table. -/
theorem endpointVariation2_neg_second_sum_eq {p q : RatPolynomial}
    (hcoprime : NoCommonRationalZero p q) (a b : ℚ) :
    endpointVariation2 (signedRemainderChain p q) a +
        endpointVariation2 (signedRemainderChain p (-q)) a =
      endpointVariation2 (signedRemainderChain p q) b +
        endpointVariation2 (signedRemainderChain p (-q)) b := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      by_cases hq : q.isZero = true
      · have hneg : (-q).isZero = true := by simpa using hq
        simp [signedRemainderChain, signedRemainderChainWF, hq, hneg,
          endpointVariation2]
      · have hqFalse : q.isZero = false := by simpa using hq
        have hnegFalse : (-q).isZero = false := by simpa using hqFalse
        let r := (divMod p q).remainder
        have hnext : NoCommonRationalZero q (-r) :=
          noCommonRationalZero_signedStep hcoprime
        have hcount : (-r).degreeCount < n := by
          dsimp only [r]
          rw [degreeCount_neg, ← hn]
          exact divMod_remainder_degreeCount_lt p q hqFalse
        have hind := ih (-r).degreeCount hcount (p := q) (q := -r) hnext rfl
        have hnotBothA : q.eval a ≠ 0 ∨ p.eval a ≠ 0 := by
          by_cases hqa : q.eval a = 0
          · right
            intro hpa
            exact hcoprime a ⟨hpa, hqa⟩
          · exact Or.inl hqa
        have hnotBothB : q.eval b ≠ 0 ∨ p.eval b ≠ 0 := by
          by_cases hqb : q.eval b = 0
          · right
            intro hpb
            exact hcoprime b ⟨hpb, hqb⟩
          · exact Or.inl hqb
        have hsignA := signJump_add_signJump_neg hnotBothA
        have hsignB := signJump_add_signJump_neg hnotBothB
        rw [signJump_comm (q.eval a) (p.eval a)] at hsignA
        rw [signJump_comm (q.eval b) (p.eval b)] at hsignB
        rw [endpointVariation2_signedRemainderChain_step hqFalse a,
          endpointVariation2_signedRemainderChain_step hnegFalse a,
          endpointVariation2_signedRemainderChain_step hqFalse b,
          endpointVariation2_signedRemainderChain_step hnegFalse b,
          divMod_remainder_neg_right p q hqFalse]
        simp only [eval_neg]
        rw [show (divMod p q).remainder = r by rfl]
        rw [endpointVariation2_signedRemainderChain_neg q r a,
          endpointVariation2_signedRemainderChain_neg q r b]
        have hrnorm : r.normalize = r := by
          exact divMod_remainder_normalize p q
        rw [DensePolynomial.neg_neg, hrnorm] at hind
        omega

/-- Strict-degree Cauchy--Sturm inversion for one already coprime dense pair.
The lower-degree reverse division stops immediately, reducing inversion to the
endpoint-independent negated-second variation theorem above. -/
theorem signedRemainderChain_inversionResidual_strictDegree
    {p q : RatPolynomial} (hp : p.isZero = false)
    (hdegree : q.natDegree < p.natDegree)
    (hcoprime : NoCommonRationalZero p q) (a b : ℚ) :
    (endpointVariation2 (signedRemainderChain p q) a : ℤ) +
          endpointVariation2 (signedRemainderChain q p) a -
        signJump (p.eval a) (q.eval a) =
      (endpointVariation2 (signedRemainderChain p q) b : ℤ) +
          endpointVariation2 (signedRemainderChain q p) b -
        signJump (p.eval b) (q.eval b) := by
  have hdivision := divMod_of_natDegree_lt hdegree
  have hsum := endpointVariation2_neg_second_sum_eq hcoprime a b
  rw [endpointVariation2_signedRemainderChain_step hp a,
    endpointVariation2_signedRemainderChain_step hp b,
    hdivision.2, neg_normalize,
    signJump_comm (q.eval a) (p.eval a),
    signJump_comm (q.eval b) (p.eval b)]
  push_cast
  omega

/-- Equal-degree inversion for one coprime dense pair.  The two Euclidean
chains share a tail up to alternating nonzero rational scales; every paired
tail jump therefore contributes the same endpoint-independent constant. -/
theorem signedRemainderChain_inversionResidual_equalDegree
    {p q : RatPolynomial} (hp : p.isZero = false) (hq : q.isZero = false)
    (hdegree : p.natDegree = q.natDegree)
    (hcoprime : IsCoprime p.toPolynomial q.toPolynomial) (a b : ℚ) :
    (endpointVariation2 (signedRemainderChain p q) a : ℤ) +
          endpointVariation2 (signedRemainderChain q p) a -
        signJump (p.eval a) (q.eval a) =
      (endpointVariation2 (signedRemainderChain p q) b : ℤ) +
          endpointVariation2 (signedRemainderChain q p) b -
        signJump (p.eval b) (q.eval b) := by
  by_cases hdegreeZero : p.natDegree = 0
  · have hqDegreeZero : q.natDegree = 0 := by omega
    have hpRemainder : (divMod p q).remainder.isZero = true := by
      rcases divMod_remainder_small p q hq with hzero | hlt
      · exact hzero
      · omega
    have hqRemainder : (divMod q p).remainder.isZero = true := by
      rcases divMod_remainder_small q p hp with hzero | hlt
      · exact hzero
      · omega
    have hpChain : signedRemainderChain p q = [p, q] := by
      rw [signedRemainderChain, signedRemainderChainWF]
      simp [hq, hpRemainder]
    have hqChain : signedRemainderChain q p = [q, p] := by
      rw [signedRemainderChain, signedRemainderChainWF]
      simp [hp, hqRemainder]
    have hpa := eval_eq_of_natDegree_zero hp hdegreeZero a b
    have hqa := eval_eq_of_natDegree_zero hq hqDegreeZero a b
    rw [hpChain, hqChain]
    simp [endpointVariation2, variation2, hpa, hqa, signJump_comm]
  · let r := -((divMod p q).remainder)
    let c := p.leadingCoeff / q.leadingCoeff
    let k := -(q.leadingCoeff / p.leadingCoeff)
    have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero hp) (leadingCoeff_ne_zero hq)
    have hk : k ≠ 0 := neg_ne_zero.mpr
      (div_ne_zero (leadingCoeff_ne_zero hq) (leadingCoeff_ne_zero hp))
    have hck : c * k = -1 := by
      dsimp only [c, k]
      field_simp [leadingCoeff_ne_zero hp, leadingCoeff_ne_zero hq]
    have hkc : k * c < 0 := by rw [mul_comm, hck]; norm_num
    have hr : r.isZero = false := by
      by_contra hrFalse
      have hrTrue : r.isZero = true := by simpa using hrFalse
      have hremTrue : (divMod p q).remainder.isZero = true := by
        simpa [r] using hrTrue
      have hremPoly := (toPolynomial_eq_zero_iff_isZero
        (divMod p q).remainder).2 hremTrue
      have hdvd : q.toPolynomial ∣ p.toPolynomial := by
        refine ⟨(divMod p q).quotient.toPolynomial, ?_⟩
        rw [divMod_toPolynomial_equation p q, hremPoly, add_zero]
      have hunit := hcoprime.symm.isUnit_of_dvd hdvd
      have hunitDegree := Polynomial.natDegree_eq_zero_of_isUnit hunit
      rw [natDegree_toPolynomial hq] at hunitDegree
      omega
    let t := -((divMod q r).remainder)
    have hnoCommon : NoCommonRationalZero p q :=
      noCommonRationalZero_of_isCoprime hcoprime
    have hnoCommonQR : NoCommonRationalZero q r :=
      noCommonRationalZero_signedStep hnoCommon
    have hnoCommonRT : NoCommonRationalZero r t :=
      noCommonRationalZero_signedStep hnoCommonQR
    have hs : -((divMod q p).remainder) = scale k r := by
      exact signedRemainder_swap_of_natDegree_eq hp hq hdegree
    have htailRemainder : (divMod p (scale k r)).remainder =
        scale c (divMod q r).remainder := by
      exact divMod_remainder_equalDegree_tail hp hq hdegree hr
    have htailSigned : -((divMod p (scale k r)).remainder) = scale c t := by
      rw [htailRemainder, ← scale_neg]
    have hscaleR : (scale k r).isZero = false := scale_isZero_false hk hr
    have hscaledChain :
        signedRemainderChain (scale k r) (scale c t) =
          alternatingScale k c (signedRemainderChain r t) :=
      signedRemainderChain_scale r t hk hc
    have hrelation (x : ℚ) : p.eval x = c * q.eval x - r.eval x := by
      dsimp only [r, c]
      rw [divMod_remainder_eq_cancelLead_of_natDegree_eq hp hq hdegree,
        eval_neg, eval_cancelLead, eval_leadQuotient, hdegree]
      simp
      ring
    have hendpoint (x : ℚ) :
        (endpointVariation2 (signedRemainderChain p q) x : ℤ) +
              endpointVariation2 (signedRemainderChain q p) x -
            signJump (p.eval x) (q.eval x) =
          ((if 0 < c then 2 else 4 : ℕ) : ℤ) +
            ((2 * ((signedRemainderChain r t).length - 1) : ℕ) : ℤ) := by
      have hfirst := equalDegree_initial_sign_sum hc hck (hrelation x)
        (by
          by_cases hpx : p.eval x = 0
          · right
            intro hqx
            exact hnoCommon x ⟨hpx, hqx⟩
          · exact Or.inl hpx)
        (by
          by_cases hqx : q.eval x = 0
          · right
            intro hrx
            exact hnoCommonQR x ⟨hqx, hrx⟩
          · exact Or.inl hqx)
      have htail := endpointVariation2_add_alternatingScale
        (signedRemainderChain r t) x hkc
        (noAdjacentZero_signedRemainderChain hnoCommonRT x)
      have hfirstInt :
          (signJump (p.eval x) (q.eval x) : ℤ) +
                signJump (q.eval x) (r.eval x) +
              signJump (p.eval x) (k * r.eval x) =
            ((if 0 < c then 2 else 4 : ℕ) : ℤ) := by
        exact_mod_cast hfirst
      have htailInt :
          (endpointVariation2 (signedRemainderChain r t) x : ℤ) +
              endpointVariation2
                (alternatingScale k c (signedRemainderChain r t)) x =
            ((2 * ((signedRemainderChain r t).length - 1) : ℕ) : ℤ) := by
        exact_mod_cast htail
      rw [endpointVariation2_signedRemainderChain_step hq x,
        endpointVariation2_signedRemainderChain_step hp x,
        show -((divMod p q).remainder) = r by rfl,
        hs,
        endpointVariation2_signedRemainderChain_step hr x,
        endpointVariation2_signedRemainderChain_step hscaleR x,
        show -((divMod q r).remainder) = t by rfl,
        htailSigned, hscaledChain]
      simp only [eval_scale]
      rw [signJump_comm (q.eval x) (p.eval x)]
      push_cast at hfirstInt htailInt ⊢
      omega
    rw [hendpoint a, hendpoint b]

/-- Numerator after the finite Euclidean program divides out the common gcd. -/
def reducedNumerator (R S : RatPolynomial) : RatPolynomial :=
  FTA.DenseGCD.symmetricLeftFactor R S

/-- Denominator after the finite Euclidean program divides out the common gcd. -/
def reducedDenominator (R S : RatPolynomial) : RatPolynomial :=
  FTA.DenseGCD.symmetricRightFactor R S

@[simp] theorem reducedDenominator_derivative_eq_squarefreePart
    (p : RatPolynomial) :
    reducedDenominator (FTA.DenseDerivative.derivative p) p =
      FTA.DenseSquarefree.squarefreePart p :=
  rfl

theorem reducedNumerator_swap (R S : RatPolynomial) :
    reducedNumerator S R = reducedDenominator R S :=
  FTA.DenseGCD.symmetricLeftFactor_swap R S

theorem reducedDenominator_swap (R S : RatPolynomial) :
    reducedDenominator S R = reducedNumerator R S :=
  FTA.DenseGCD.symmetricRightFactor_swap R S

/-- Definition 3.1's signed chain starts only after common-gcd reduction. -/
def cauchyChain (R S : RatPolynomial) : List RatPolynomial :=
  signedRemainderChain (reducedDenominator R S) (reducedNumerator R S)

theorem reducedNumerator_isZero_false {R S : RatPolynomial}
    (hR : R.isZero = false) : (reducedNumerator R S).isZero = false :=
  FTA.DenseGCD.symmetricLeftFactor_isZero_false hR

theorem reducedDenominator_isZero_false {R S : RatPolynomial}
    (hS : S.isZero = false) : (reducedDenominator R S).isZero = false :=
  FTA.DenseGCD.symmetricRightFactor_isZero_false hS

theorem reducedPair_isCoprime {R S : RatPolynomial}
    (hR : R.isZero = false) (_hS : S.isZero = false) :
    IsCoprime (reducedDenominator R S).toPolynomial
      (reducedNumerator R S).toPolynomial := by
  exact (FTA.DenseGCD.symmetricFactors_isCoprime R S (Or.inl hR)).symm

/-- At an endpoint where the original denominator is nonzero, the variation
of the gcd-reduced Cauchy chain is even. -/
theorem endpointVariation2_cauchyChain_even
    {R S : RatPolynomial} (hR : R.isZero = false) (hS : S.isZero = false)
    {x : ℚ} (hSx : S.eval x ≠ 0) :
    Even (endpointVariation2 (cauchyChain R S) x) := by
  have hfirst : (reducedDenominator R S).eval x ≠ 0 := by
    exact FTA.DenseGCD.symmetricRightFactor_eval_ne_zero hSx
  have hcoprime : NoCommonRationalZero (reducedDenominator R S)
      (reducedNumerator R S) :=
    noCommonRationalZero_of_isCoprime (reducedPair_isCoprime hR hS)
  exact endpointVariation2_signedRemainderChain_even
    (reducedNumerator_isZero_false hR) hcoprime hfirst

theorem reducedNatDegree_lt {R S : RatPolynomial}
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hdegree : R.natDegree < S.natDegree) :
    (reducedNumerator R S).natDegree <
      (reducedDenominator R S).natDegree :=
  FTA.DenseGCD.symmetricFactor_natDegree_lt hR hS hdegree

/-- Definition 3.1 in doubled form. -/
def cauchyIndex2 (R S : RatPolynomial) (a b : ℚ) : ℤ :=
  if R.isZero || S.isZero then 0
  else (endpointVariation2 (cauchyChain R S) a : ℤ) -
    endpointVariation2 (cauchyChain R S) b

/-- Doubled endpoint variation of the gcd-reduced two-entry sign list. -/
def pairEndpointVariation2 (R S : RatPolynomial) (x : ℚ) : ℕ :=
  signJump ((reducedDenominator R S).eval x) ((reducedNumerator R S).eval x)

/-- The right-hand side of Theorem 3.2(b), in doubled integer form. -/
def pairVariationDifference2 (R S : RatPolynomial) (a b : ℚ) : ℤ :=
  (pairEndpointVariation2 R S a : ℤ) - pairEndpointVariation2 R S b

theorem pairEndpointVariation2_swap (R S : RatPolynomial) (x : ℚ) :
    pairEndpointVariation2 S R x = pairEndpointVariation2 R S x := by
  dsimp only [pairEndpointVariation2]
  rw [reducedDenominator_swap R S, reducedNumerator_swap R S]
  exact signJump_comm _ _

theorem pairVariationDifference2_swap (R S : RatPolynomial) (a b : ℚ) :
    pairVariationDifference2 S R a b = pairVariationDifference2 R S a b := by
  rw [pairVariationDifference2, pairVariationDifference2,
    pairEndpointVariation2_swap R S a, pairEndpointVariation2_swap R S b]

/-- Endpoint residual for the inversion formula.  The universal theorem below
shows that this finite integer is endpoint-independent for every pair of
nonzero input polynomials. -/
def inversionResidual2 (R S : RatPolynomial) (x : ℚ) : ℤ :=
  (endpointVariation2 (cauchyChain R S) x : ℤ) +
    endpointVariation2 (cauchyChain S R) x -
      pairEndpointVariation2 R S x

/-- Fully decidable finite certificate for one instance of Theorem 3.2(b). -/
def inversionCheck (R S : RatPolynomial) (a b : ℚ) : Bool :=
  decide (inversionResidual2 R S a = inversionResidual2 R S b)

/-- Soundness of the finite inversion certificate against the executable
Cauchy--Sturm indices. -/
theorem cauchyIndex2_inversion_of_residual (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hres : inversionResidual2 R S a = inversionResidual2 R S b) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b := by
  have hRS : ¬(R.isZero || S.isZero) := by simp [hR, hS]
  have hSR : ¬(S.isZero || R.isZero) := by simp [hR, hS]
  simp only [cauchyIndex2, if_neg hRS, if_neg hSR]
  dsimp [inversionResidual2, pairVariationDifference2, pairEndpointVariation2] at hres ⊢
  omega

/-- Universal inversion in the strict reduced-degree case.  This is the case
used by squarefree derivative Sturm chains and requires no endpoint-specific
Boolean certificate. -/
theorem cauchyIndex2_inversion_of_reducedDegree_lt
    (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hdegree : (reducedNumerator R S).natDegree <
      (reducedDenominator R S).natDegree) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b := by
  apply cauchyIndex2_inversion_of_residual R S a b hR hS
  have hcoprime : NoCommonRationalZero (reducedDenominator R S)
      (reducedNumerator R S) :=
    noCommonRationalZero_of_isCoprime (reducedPair_isCoprime hR hS)
  have hraw := signedRemainderChain_inversionResidual_strictDegree
    (reducedDenominator_isZero_false hS) hdegree hcoprime a b
  dsimp only [inversionResidual2, cauchyChain, pairEndpointVariation2]
  rw [reducedDenominator_swap R S, reducedNumerator_swap R S]
  exact hraw

/-- Universal inversion in the equal reduced-degree case.  The two signed
Euclidean chains share an alternatingly rescaled tail after their first
division steps. -/
theorem cauchyIndex2_inversion_of_reducedDegree_eq
    (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hdegree : (reducedDenominator R S).natDegree =
      (reducedNumerator R S).natDegree) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b := by
  apply cauchyIndex2_inversion_of_residual R S a b hR hS
  have hraw := signedRemainderChain_inversionResidual_equalDegree
    (reducedDenominator_isZero_false hS)
    (reducedNumerator_isZero_false hR) hdegree
    (reducedPair_isCoprime hR hS) a b
  dsimp only [inversionResidual2, cauchyChain, pairEndpointVariation2]
  rw [reducedDenominator_swap R S, reducedNumerator_swap R S]
  exact hraw

theorem cauchyIndex2_inversion_of_degree_lt
    (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hdegree : R.natDegree < S.natDegree) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b :=
  cauchyIndex2_inversion_of_reducedDegree_lt R S a b hR hS
    (reducedNatDegree_lt hR hS hdegree)

theorem cauchyIndex2_inversion_of_degree_gt
    (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hdegree : S.natDegree < R.natDegree) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b := by
  have hreverse := cauchyIndex2_inversion_of_degree_lt S R a b hS hR hdegree
  rw [pairVariationDifference2_swap R S] at hreverse
  omega

theorem cauchyIndex2_inversion_of_natDegree_ne
    (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hdegree : R.natDegree ≠ S.natDegree) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b := by
  rcases lt_or_gt_of_ne hdegree with hlt | hgt
  · exact cauchyIndex2_inversion_of_degree_lt R S a b hR hS hlt
  · exact cauchyIndex2_inversion_of_degree_gt R S a b hR hS hgt

/-- Theorem 3.2(b): universal Cauchy--Sturm inversion for arbitrary nonzero
rational polynomials.  Gcd reduction supplies a coprime pair; comparison of
its two degrees selects one strict orientation or the equal-degree tail
argument. -/
theorem cauchyIndex2_inversion (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b := by
  rcases lt_trichotomy (reducedNumerator R S).natDegree
      (reducedDenominator R S).natDegree with hlt | heq | hgt
  · exact cauchyIndex2_inversion_of_reducedDegree_lt R S a b hR hS hlt
  · exact cauchyIndex2_inversion_of_reducedDegree_eq R S a b hR hS heq.symm
  · have hreverse := cauchyIndex2_inversion_of_reducedDegree_lt
      S R a b hS hR (by
        rw [reducedNumerator_swap R S, reducedDenominator_swap R S]
        exact hgt)
    rw [pairVariationDifference2_swap R S] at hreverse
    omega

theorem cauchyIndex2_inversion_of_check (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hcheck : inversionCheck R S a b = true) :
    cauchyIndex2 R S a b + cauchyIndex2 S R a b =
      pairVariationDifference2 R S a b := by
  apply cauchyIndex2_inversion_of_residual R S a b hR hS
  simpa [inversionCheck] using hcheck

/-- Exact executable sanity check for the inversion certificate on `1/T`
over `[-1,1]`. -/
theorem inversionCheck_linear_example :
    inversionCheck ⟨[1]⟩ ⟨[1, 0]⟩ (-1) 1 = true := by
  native_decide

/-- Regression witness: omitting the paper's gcd reduction makes inversion
fail when an endpoint is a shared zero. -/
private def unreducedInversionResidual2 (R S : RatPolynomial) (x : ℚ) : ℤ :=
  (endpointVariation2 (signedRemainderChain S R) x : ℤ) +
    endpointVariation2 (signedRemainderChain R S) x -
      signJump (S.eval x) (R.eval x)

private def unreducedInversionCheck (R S : RatPolynomial) (a b : ℚ) : Bool :=
  decide (unreducedInversionResidual2 R S a = unreducedInversionResidual2 R S b)

theorem unreducedInversionCheck_shared_factor_regression :
    unreducedInversionCheck ⟨[1, 0]⟩ ⟨[1, 0, 0]⟩ 0 1 = false := by
  native_decide

/-- Gcd reduction repairs the shared-factor endpoint case. -/
theorem inversionCheck_shared_factor_endpoint_example :
    inversionCheck ⟨[1, 0]⟩ ⟨[1, 0, 0]⟩ 0 1 = true := by
  native_decide

/-- The subdivision identity in Theorem 3.2(a). -/
theorem cauchyIndex2_add (R S : RatPolynomial) (a b c : ℚ) :
    cauchyIndex2 R S a b + cauchyIndex2 R S b c = cauchyIndex2 R S a c := by
  by_cases h : R.isZero || S.isZero
  · simp [cauchyIndex2, h]
  · simp only [cauchyIndex2, if_neg h]
    omega

/-- The reversal identity in Theorem 3.2(a). -/
theorem cauchyIndex2_reverse (R S : RatPolynomial) (a b : ℚ) :
    cauchyIndex2 R S b a = -cauchyIndex2 R S a b := by
  by_cases h : R.isZero || S.isZero
  · simp [cauchyIndex2, h]
  · simp only [cauchyIndex2, if_neg h]
    omega

@[simp] theorem cauchyIndex2_refl (R S : RatPolynomial) (a : ℚ) :
    cauchyIndex2 R S a a = 0 := by
  by_cases h : R.isZero || S.isZero
  · simp [cauchyIndex2, h]
  · simp [cauchyIndex2, h]

/-! ## Squarefree derivative chains -/

/-- The finite squarefree certificate supplies the initial coprimality
condition for the derivative Sturm chain. -/
theorem noCommonRationalZero_derivative {p : RatPolynomial}
    (certificate : FTA.DenseSquarefree.SquarefreeCertificate p) :
    NoCommonRationalZero p (FTA.DenseDerivative.derivative p) := by
  intro x
  rintro ⟨hp, hderivative⟩
  have hidentity := certificate.identity x
  rw [hp, hderivative] at hidentity
  norm_num at hidentity

/-- At an exact rational zero of a squarefree polynomial, its executable
derivative is provably nonzero. -/
theorem derivative_eval_ne_zero_of_squarefree_root {p : RatPolynomial}
    (certificate : FTA.DenseSquarefree.SquarefreeCertificate p) {x : ℚ}
    (hroot : p.eval x = 0) :
    (FTA.DenseDerivative.derivative p).eval x ≠ 0 := by
  intro hderivative
  exact noCommonRationalZero_derivative certificate x ⟨hroot, hderivative⟩

/-- Consequently an exact first-member endpoint event contributes one unit to
the doubled adjacent sign jump.  This is the endpoint half-event convention
used by the finite Sturm calculation. -/
theorem firstMemberEndpointJump {p : RatPolynomial}
    (certificate : FTA.DenseSquarefree.SquarefreeCertificate p) {x : ℚ}
    (hroot : p.eval x = 0) :
    signJump (p.eval x) ((FTA.DenseDerivative.derivative p).eval x) = 1 := by
  rw [hroot]
  exact signJump_zero_of_ne
    (derivative_eval_ne_zero_of_squarefree_root certificate hroot)

/-- The doubled signed-variation root-count program for the squarefree
derivative chain.  Endpoint events remain explicit; clear endpoints give an
even result whose half is the usual Sturm count. -/
def sturmRootCount2 (p : RatPolynomial) (a b : ℚ) : ℤ :=
  cauchyIndex2 (FTA.DenseDerivative.derivative p) p a b

/-- Clear endpoints give an even doubled Sturm count.  This is the parity
half of Theorem 3.2(d)'s `0/1` event labeling and does not assume that any
interior chain member is nonzero at an endpoint. -/
theorem sturmRootCount2_even {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0)
    {a b : ℚ} (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    Even (sturmRootCount2 p a b) := by
  have hderivative := FTA.DenseDerivative.derivative_isZero_false hp hdegree
  have haEven := endpointVariation2_cauchyChain_even hderivative hp ha
  have hbEven := endpointVariation2_cauchyChain_even hderivative hp hb
  have hcondition : ¬((FTA.DenseDerivative.derivative p).isZero || p.isZero) := by
    simp [hderivative, hp]
  rw [sturmRootCount2, cauchyIndex2, if_neg hcondition]
  apply Int.even_sub.mpr
  exact iff_of_true ((Int.even_coe_nat _).mpr haEven)
    ((Int.even_coe_nat _).mpr hbEven)

/-- The inversion law is unconditional for every nonconstant derivative
chain: the executable derivative is nonzero and has strictly smaller degree. -/
theorem sturmRootCount2_inversion {p : RatPolynomial}
    (hp : p.isZero = false) (hdegree : p.natDegree ≠ 0) (a b : ℚ) :
    sturmRootCount2 p a b +
        cauchyIndex2 p (FTA.DenseDerivative.derivative p) a b =
      pairVariationDifference2 (FTA.DenseDerivative.derivative p) p a b := by
  exact cauchyIndex2_inversion_of_degree_lt
    (FTA.DenseDerivative.derivative p) p a b
    (FTA.DenseDerivative.derivative_isZero_false hp hdegree) hp
    (FTA.DenseDerivative.derivative_natDegree_lt hp hdegree)

theorem sturmRootCount2_add (p : RatPolynomial) (a b c : ℚ) :
    sturmRootCount2 p a b + sturmRootCount2 p b c =
      sturmRootCount2 p a c :=
  cauchyIndex2_add _ _ _ _ _

theorem sturmRootCount2_reverse (p : RatPolynomial) (a b : ℚ) :
    sturmRootCount2 p b a = -sturmRootCount2 p a b :=
  cauchyIndex2_reverse _ _ _ _

@[simp] theorem sturmRootCount2_refl (p : RatPolynomial) (a : ℚ) :
    sturmRootCount2 p a a = 0 :=
  cauchyIndex2_refl _ _ _

end FTA.Sturm
