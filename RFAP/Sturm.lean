import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.Squarefree
import Mathlib.Data.List.Basic

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`RFAP.ComputablePolynomial`; no sparse polynomial or root set is involved.
-/

namespace RFAP.Sturm

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ComputablePolynomial.DensePolynomial

/-- Decidable sign in `{-1, 0, 1}`. -/
def sign (x : Coordinate) : Int :=
  if x < 0 then -1 else if x = 0 then 0 else 1

@[simp] theorem sign_zero : sign 0 = 0 := by simp [sign]

theorem sign_of_pos {x : Coordinate} (hx : 0 < x) : sign x = 1 := by
  simp [sign, hx.ne', not_lt.mpr hx.le]

theorem sign_of_neg {x : Coordinate} (hx : x < 0) : sign x = -1 := by
  simp [sign, hx]

theorem sign_eq_zero_iff {x : Coordinate} : sign x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [sign_of_neg hx] at h
      exact ((by decide : (-1 : Int) ≠ 0) h).elim
    · exact hx
    · rw [sign_of_pos hx] at h
      exact ((by decide : (1 : Int) ≠ 0) h).elim
  · rintro rfl
    exact sign_zero

theorem sign_eq_neg_one_iff {x : Coordinate} : sign x = -1 ↔ x < 0 := by
  constructor
  · intro equal
    rcases lt_trichotomy x 0 with negative | rfl | positive
    · exact negative
    · rw [sign_zero] at equal
      exact ((by decide : (0 : Int) ≠ -1) equal).elim
    · rw [sign_of_pos positive] at equal
      exact ((by decide : (1 : Int) ≠ -1) equal).elim
  · exact sign_of_neg

theorem sign_eq_one_iff {x : Coordinate} : sign x = 1 ↔ 0 < x := by
  constructor
  · intro equal
    rcases lt_trichotomy x 0 with negative | rfl | positive
    · rw [sign_of_neg negative] at equal
      exact ((by decide : (-1 : Int) ≠ 1) equal).elim
    · rw [sign_zero] at equal
      exact ((by decide : (0 : Int) ≠ 1) equal).elim
    · exact positive
  · exact sign_of_pos

theorem sign_neg (x : Coordinate) : sign (-x) = -sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [sign_of_pos (neg_pos.mpr hx), sign_of_neg hx]
    decide
  · subst x
    simp only [neg_zero, sign_zero]
  · rw [sign_of_neg (neg_neg_of_pos hx), sign_of_pos hx]

theorem sign_mul (x y : Coordinate) : sign (x * y) = sign x * sign y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [sign_of_pos
        (RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct hx hy),
      sign_of_neg hx, sign_of_neg hy]
    decide
  · simp only [mul_zero, sign_zero]
  · rw [sign_of_neg
        (RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct hx hy),
      sign_of_neg hx, sign_of_pos hy]
    decide
  · simp only [zero_mul, sign_zero]
  · simp only [zero_mul, sign_zero]
  · simp only [zero_mul, sign_zero]
  · rw [sign_of_neg
        (RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct hx hy),
      sign_of_pos hx, sign_of_neg hy]
    decide
  · simp only [mul_zero, sign_zero]
  · rw [sign_of_pos (RFAP.ConstructiveFraction.mul_pos_direct hx hy),
      sign_of_pos hx, sign_of_pos hy]
    decide

theorem sign_eq_of_mul_pos {x y : Coordinate} (hxy : 0 < x * y) :
    sign x = sign y := by
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy y 0 with yNegative | rfl | yPositive
  · rw [sign_of_neg xNegative, sign_of_neg yNegative]
  · rw [mul_zero] at hxy
    exact (lt_irrefl 0 hxy).elim
  · have productNegative :=
      RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        xNegative yPositive
    exact (lt_asymm hxy productNegative).elim
  · rw [zero_mul] at hxy
    exact (lt_irrefl 0 hxy).elim
  · rw [zero_mul] at hxy
  · rw [zero_mul] at hxy
    exact (lt_irrefl 0 hxy).elim
  · have productNegative :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        xPositive yNegative
    exact (lt_asymm hxy productNegative).elim
  · rw [mul_zero] at hxy
    exact (lt_irrefl 0 hxy).elim
  · rw [sign_of_pos xPositive, sign_of_pos yPositive]

/-- One doubled adjacent sign variation. -/
def signJump (x y : Coordinate) : Nat := (sign x - sign y).natAbs

@[simp] theorem signJump_self (x : Coordinate) : signJump x x = 0 := by
  simp [signJump]

theorem signJump_comm (x y : Coordinate) : signJump x y = signJump y x := by
  dsimp only [signJump]
  rw [show sign y - sign x = -(sign x - sign y) by ring1, Int.natAbs_neg]

theorem signJump_neg_neg (x y : Coordinate) :
    signJump (-x) (-y) = signJump x y := by
  simp only [signJump, sign_neg]
  rw [show -sign x - -sign y = -(sign x - sign y) by ring1,
    Int.natAbs_neg]

theorem signJump_zero_neg_of_ne {x : Coordinate} (hx : x ≠ 0) :
    signJump x 0 + signJump 0 (-x) = 2 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [signJump, signJump, sign_of_neg hx, sign_zero, sign_neg,
      sign_of_neg hx]
    decide
  · rw [signJump, signJump, sign_of_pos hx, sign_zero, sign_neg,
      sign_of_pos hx]
    decide

theorem signJump_zero_of_ne {x : Coordinate} (hx : x ≠ 0) :
    signJump 0 x = 1 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [signJump, sign_zero, sign_of_neg hx]
    decide
  · rw [signJump, sign_zero, sign_of_pos hx]
    decide

/-- Unless both values vanish, passing from `x` through `y` to `-x`
contributes exactly two doubled half-jumps. -/
theorem signJump_add_signJump_neg {x y : Coordinate}
    (notBoth : x ≠ 0 ∨ y ≠ 0) :
    signJump x y + signJump y (-x) = 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [signJump, sign_of_neg, sign_of_pos]

theorem signJump_add_signJump_of_outer_mul_neg {x y z : Coordinate}
    (hxz : x * z < 0) : signJump x y + signJump y z = 2 := by
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy z 0 with zNegative | rfl | zPositive
  · have productPositive :=
      RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
        xNegative zNegative
    exact (lt_asymm hxz productPositive).elim
  · rw [mul_zero] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rcases lt_trichotomy y 0 with yNegative | rfl | yPositive
    · simp [signJump, sign_of_neg xNegative,
        sign_of_neg yNegative, sign_of_pos zPositive]
    · simp [signJump, sign_of_neg xNegative, sign_of_pos zPositive]
    · simp [signJump, sign_of_neg xNegative,
        sign_of_pos yPositive, sign_of_pos zPositive]
  · rw [zero_mul] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rw [zero_mul] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rw [zero_mul] at hxz
    exact (lt_irrefl 0 hxz).elim
  · rcases lt_trichotomy y 0 with yNegative | rfl | yPositive
    · simp [signJump, sign_of_pos xPositive,
        sign_of_neg yNegative, sign_of_neg zNegative]
    · simp [signJump, sign_of_pos xPositive, sign_of_neg zNegative]
    · simp [signJump, sign_of_pos xPositive,
        sign_of_pos yPositive, sign_of_neg zNegative]
  · rw [mul_zero] at hxz
    exact (lt_irrefl 0 hxz).elim
  · have productPositive :=
      RFAP.ConstructiveFraction.mul_pos_direct xPositive zPositive
    exact (lt_asymm hxz productPositive).elim

theorem signJump_eq_two_of_mul_neg {x y : Coordinate} (hxy : x * y < 0) :
    signJump x y = 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  · have positive :=
      RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct hx hy
    exact (lt_asymm hxy positive).elim
  · simp at hxy
  · simp [signJump, sign_of_neg hx, sign_of_pos hy]
  · simp at hxy
  · simp at hxy
  · simp at hxy
  · simp [signJump, sign_of_pos hx, sign_of_neg hy]
  · simp at hxy
  · have positive := RFAP.ConstructiveFraction.mul_pos_direct hx hy
    exact (lt_asymm hxy positive).elim

theorem signJump_eq_zero_of_mul_pos {x y : Coordinate} (hxy : 0 < x * y) :
    signJump x y = 0 := by
  unfold signJump
  rw [sign_eq_of_mul_pos hxy]
  simp only [sub_self, Int.natAbs_zero]

theorem signJump_add_signJump_mul_of_mul_neg {a b x y : Coordinate}
    (hab : a * b < 0) (notBoth : x ≠ 0 ∨ y ≠ 0) :
    signJump x y + signJump (a * x) (b * y) = 2 := by
  have oppositeSigns :
      (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0) := by
    rcases lt_trichotomy a 0 with aNegative | rfl | aPositive
    · rcases lt_trichotomy b 0 with bNegative | rfl | bPositive
      · have productPositive :=
          RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
            aNegative bNegative
        exact (lt_asymm hab productPositive).elim
      · rw [mul_zero] at hab
        exact (lt_irrefl 0 hab).elim
      · exact Or.inl ⟨aNegative, bPositive⟩
    · rw [zero_mul] at hab
      exact (lt_irrefl 0 hab).elim
    · rcases lt_trichotomy b 0 with bNegative | rfl | bPositive
      · exact Or.inr ⟨aPositive, bNegative⟩
      · rw [mul_zero] at hab
        exact (lt_irrefl 0 hab).elim
      · have productPositive :=
          RFAP.ConstructiveFraction.mul_pos_direct aPositive bPositive
        exact (lt_asymm hab productPositive).elim
  rcases oppositeSigns with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all only [signJump, sign_mul, sign_of_neg, sign_of_pos, sign_zero]
  all_goals first | decide | contradiction

/-- Twice the variation of a finite sign list. -/
def variation2 : List Coordinate → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: values => signJump x y + variation2 (y :: values)

@[simp] theorem variation2_nil : variation2 [] = 0 := rfl
@[simp] theorem variation2_singleton (x : Coordinate) : variation2 [x] = 0 := rfl

theorem signJump_congr {x x' y y' : Coordinate}
    (hx : sign x = sign x') (hy : sign y = sign y') :
    signJump x y = signJump x' y' := by
  simp only [signJump, hx, hy]

/-- Doubled variation depends only on the finite list of decidable signs. -/
theorem variation2_congr_of_forall₂_sign :
    ∀ {xs ys : List Coordinate},
      List.Forall₂ (fun x y => sign x = sign y) xs ys →
        variation2 xs = variation2 ys
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | x :: x' :: xs, y :: y' :: ys,
      List.Forall₂.cons hxy (List.Forall₂.cons hxy' tail) => by
      rw [variation2, variation2, signJump_congr hxy hxy',
        variation2_congr_of_forall₂_sign (List.Forall₂.cons hxy' tail)]

/-- If all signs except one interior entry agree, and the two jumps adjacent
to that entry have the same total, then the full finite variation agrees. -/
theorem variation2_eq_of_middle_change
    {prefixA prefixB suffixA suffixB : List Coordinate}
    {leftA leftB middleA middleB rightA rightB : Coordinate}
    (prefixSigns :
      List.Forall₂ (fun x y => sign x = sign y) prefixA prefixB)
    (suffixSigns :
      List.Forall₂ (fun x y => sign x = sign y) suffixA suffixB)
    (leftSign : sign leftA = sign leftB)
    (rightSign : sign rightA = sign rightB)
    (localEquality :
      signJump leftA middleA + signJump middleA rightA =
        signJump leftB middleB + signJump middleB rightB) :
    variation2 (prefixA ++ leftA :: middleA :: rightA :: suffixA) =
      variation2 (prefixB ++ leftB :: middleB :: rightB :: suffixB) := by
  induction prefixSigns with
  | nil =>
      have tailSigns := variation2_congr_of_forall₂_sign
        (List.Forall₂.cons rightSign suffixSigns)
      simp only [List.nil_append, variation2]
      have combined := congrArg₂ (· + ·) localEquality tailSigns
      simpa only [Nat.add_assoc] using combined
  | @cons headA headB prefixA prefixB headSign prefixSigns inductionHypothesis =>
      cases prefixSigns with
      | nil =>
          have recursive' :
              variation2 (leftA :: middleA :: rightA :: suffixA) =
                variation2 (leftB :: middleB :: rightB :: suffixB) := by
            simpa only [List.nil_append] using inductionHypothesis
          change signJump headA leftA +
              variation2 (leftA :: middleA :: rightA :: suffixA) =
            signJump headB leftB +
              variation2 (leftB :: middleB :: rightB :: suffixB)
          rw [signJump_congr headSign leftSign, recursive']
      | @cons nextA nextB tailA tailB nextSign tailSigns =>
          change signJump headA nextA +
              variation2
                (nextA :: tailA ++ leftA :: middleA :: rightA :: suffixA) =
            signJump headB nextB +
              variation2
                (nextB :: tailB ++ leftB :: middleB :: rightB :: suffixB)
          rw [signJump_congr headSign nextSign, inductionHypothesis]

/-- Negating every entry preserves finite doubled variation. -/
theorem variation2_map_neg : ∀ values : List Coordinate,
    variation2 (values.map (-·)) = variation2 values
  | [] => rfl
  | [_] => rfl
  | x :: y :: values => by
      simp only [List.map_cons, variation2, signJump_neg_neg]
      exact congrArg (signJump x y + ·) (variation2_map_neg (y :: values))

/-- Alternating scalar multiplication of a finite sign list. -/
def alternatingMul (a b : Coordinate) : List Coordinate → List Coordinate
  | [] => []
  | x :: values => a * x :: alternatingMul b a values

/-- No two adjacent entries of a finite sign list vanish together. -/
def NoAdjacentZero : List Coordinate → Prop
  | [] => True
  | [_] => True
  | x :: y :: values => (x ≠ 0 ∨ y ≠ 0) ∧ NoAdjacentZero (y :: values)

theorem variation2_add_alternatingMul {a b : Coordinate} (hab : a * b < 0) :
    ∀ values : List Coordinate, NoAdjacentZero values →
      variation2 values + variation2 (alternatingMul a b values) =
        2 * (values.length - 1)
  | [], _ => rfl
  | [_], _ => by simp [alternatingMul]
  | x :: y :: values, valid => by
      have hlocal := signJump_add_signJump_mul_of_mul_neg hab valid.1
      have tail := variation2_add_alternatingMul (a := b) (b := a)
        (by simpa [mul_comm] using hab) (y :: values) valid.2
      simp only [alternatingMul, variation2, List.length_cons] at tail ⊢
      omega

/-- The final value of the nonempty list represented by a head and tail. -/
def terminalValue (x : Coordinate) : List Coordinate → Coordinate
  | [] => x
  | y :: values => terminalValue y values

/-- One doubled jump differs from its signed endpoint difference by an even
integer. -/
theorem signJump_sub_signDifference_even (x y : Coordinate) :
    Even (((signJump x y : Nat) : Int) - (sign x - sign y)) := by
  let difference := sign x - sign y
  by_cases negative : difference < 0
  · refine ⟨-difference, ?_⟩
    change ((difference.natAbs : Nat) : Int) - difference =
      -difference + -difference
    rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt negative)]
    ring1
  · refine ⟨0, ?_⟩
    change ((difference.natAbs : Nat) : Int) - difference = 0 + 0
    rw [Int.ofNat_natAbs_of_nonneg (Int.le_of_not_gt negative)]
    ring1

/-- Interior signed endpoint differences cancel in a finite variation. -/
theorem variation2_sub_signDifference_even :
    ∀ (x : Coordinate) (values : List Coordinate),
      Even (((variation2 (x :: values) : Nat) : Int) -
        (sign x - sign (terminalValue x values)))
  | x, [] => by
      refine ⟨0, ?_⟩
      simp [terminalValue]
  | x, y :: values => by
      rcases signJump_sub_signDifference_even x y with ⟨a, ha⟩
      rcases variation2_sub_signDifference_even y values with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simp only [variation2, terminalValue, Nat.cast_add]
      calc
        ((signJump x y : Nat) : Int) +
              ((variation2 (y :: values) : Nat) : Int) -
            (sign x - sign (terminalValue y values)) =
            (((signJump x y : Nat) : Int) - (sign x - sign y)) +
              (((variation2 (y :: values) : Nat) : Int) -
                (sign y - sign (terminalValue y values))) := by ring1
        _ = (a + a) + (b + b) := by rw [ha, hb]
        _ = (a + b) + (a + b) := by ring1

theorem sign_sub_even_of_ne_zero {x y : Coordinate}
    (hx : x ≠ 0) (hy : y ≠ 0) : Even (sign x - sign y) := by
  rcases lt_or_gt_of_ne hx with xNegative | xPositive
  · rcases lt_or_gt_of_ne hy with yNegative | yPositive
    · refine ⟨0, ?_⟩
      rw [sign_of_neg xNegative, sign_of_neg yNegative]
      decide
    · refine ⟨-1, ?_⟩
      rw [sign_of_neg xNegative, sign_of_pos yPositive]
      decide
  · rcases lt_or_gt_of_ne hy with yNegative | yPositive
    · refine ⟨1, ?_⟩
      rw [sign_of_pos xPositive, sign_of_neg yNegative]
      decide
    · refine ⟨0, ?_⟩
      rw [sign_of_pos xPositive, sign_of_pos yPositive]
      decide

/-- Against a nonzero terminal sign, the signed endpoint difference has the
same parity as the explicit zero flag of its first endpoint. -/
theorem sign_sub_terminal_sub_zeroFlag_even
    {x y : Coordinate} (hy : y ≠ 0) :
    Even ((sign x - sign y) - (if x = 0 then 1 else 0)) := by
  by_cases hx : x = 0
  · subst x
    rcases lt_or_gt_of_ne hy with hy | hy
    · exact ⟨0, by simp [sign_of_neg hy]⟩
    · exact ⟨-1, by simp [sign_of_pos hy]⟩
  · simpa [hx] using sign_sub_even_of_ne_zero hx hy

/-- Two dense coordinate polynomials never vanish simultaneously. -/
def NoCommonZero (p q : Polynomial) : Prop :=
  ∀ x : Coordinate, p.eval x ≠ 0 ∨ q.eval x ≠ 0

/-- Fuel-bounded signed Euclidean chain.  The public calculation supplies the
second polynomial's coefficient count as fuel; every nonterminal remainder
has strictly smaller count. -/
def signedRemainderChainFuel : Nat → Polynomial → Polynomial → List Polynomial
  := Nat.rec
    (fun p _ => [p])
    (fun _ recursive p q =>
      if q.isZero then [p]
      else
        let dm := divMod p q
        if dm.remainder.isZero then [p, q]
        else p :: recursive q (-dm.remainder))

@[simp] theorem signedRemainderChainFuel_zero (p q : Polynomial) :
    signedRemainderChainFuel 0 p q = [p] := rfl

theorem signedRemainderChainFuel_succ
    (fuel : Nat) (p q : Polynomial) :
    signedRemainderChainFuel (fuel + 1) p q =
      if q.isZero then [p]
      else
        let dm := divMod p q
        if dm.remainder.isZero then [p, q]
        else p :: signedRemainderChainFuel fuel q (-dm.remainder) := rfl

/-- Once the fuel already covers the represented degree, one further step of
fuel leaves the calculated chain unchanged. -/
theorem signedRemainderChainFuel_succ_of_degreeCount_le :
    ∀ (fuel : Nat) (p q : Polynomial), q.degreeCount ≤ fuel →
      signedRemainderChainFuel (fuel + 1) p q =
        signedRemainderChainFuel fuel p q := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q enough
      have degreeZero : q.degreeCount = 0 := Nat.eq_zero_of_le_zero enough
      have qZero := isZero_true_of_degreeCount_eq_zero degreeZero
      change (if q.isZero then [p]
          else
            let dm := divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel 0 q (-dm.remainder)) = [p]
      rw [qZero]
      simp only [↓reduceIte]
  | succ fuel inductionHypothesis =>
      intro p q enough
      change (if q.isZero then [p]
          else
            let dm := divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel (fuel + 1) q (-dm.remainder)) =
        if q.isZero then [p]
          else
            let dm := divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel fuel q (-dm.remainder)
      cases qZero : q.isZero
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases remainderZero : (divMod p q).remainder.isZero
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply congrArg (List.cons p)
          apply inductionHypothesis q (-((divMod p q).remainder))
          have remainderDegree := divMod_remainder_degreeCount_lt p q qZero
          rw [degreeCount_neg]
          exact Nat.lt_succ_iff.mp
            (lt_of_lt_of_le remainderDegree enough)
        · rfl
      · simp only [↓reduceIte]

/-- Adding any finite surplus to sufficient fuel cannot change the calculated
signed chain. -/
theorem signedRemainderChainFuel_add_of_degreeCount_le
    (extra fuel : Nat) (p q : Polynomial) (enough : q.degreeCount ≤ fuel) :
    signedRemainderChainFuel (fuel + extra) p q =
      signedRemainderChainFuel fuel p q := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      calc
        signedRemainderChainFuel (fuel + extra + 1) p q =
            signedRemainderChainFuel (fuel + extra) p q :=
          signedRemainderChainFuel_succ_of_degreeCount_le
            (fuel + extra) p q
              (enough.trans (Nat.le_add_right fuel extra))
        _ = signedRemainderChainFuel fuel p q := inductionHypothesis

/-- Extra fuel cannot change a signed chain once the fuel reaches the second
polynomial's coefficient count. -/
theorem signedRemainderChainFuel_stable
    (fuel : Nat) (p q : Polynomial) (enough : q.degreeCount ≤ fuel) :
    signedRemainderChainFuel fuel p q =
      signedRemainderChainFuel q.degreeCount p q := by
  have fuelEquation : q.degreeCount + (fuel - q.degreeCount) = fuel :=
    Nat.add_sub_of_le enough
  rw [← fuelEquation]
  exact signedRemainderChainFuel_add_of_degreeCount_le
    (fuel - q.degreeCount) q.degreeCount p q le_rfl

/-- Signed Euclidean chain with its finite fuel chosen from the represented
second-polynomial degree. -/
def signedRemainderChainWF (p q : Polynomial) : List Polynomial :=
  signedRemainderChainFuel q.degreeCount p q

/-- One executable unfolding of the fuelled signed Euclidean chain. -/
theorem signedRemainderChainWF_eq (p q : Polynomial) :
    signedRemainderChainWF p q =
      if q.isZero then [p]
      else
        let dm := divMod p q
        if dm.remainder.isZero then [p, q]
        else p :: signedRemainderChainWF q (-dm.remainder) := by
  change signedRemainderChainFuel q.degreeCount p q =
    if q.isZero then [p]
    else
      let dm := divMod p q
      if dm.remainder.isZero then [p, q]
      else p :: signedRemainderChainFuel (-dm.remainder).degreeCount q
        (-dm.remainder)
  cases qZero : q.isZero
  · have degreePositive := degreeCount_pos_of_isZero_false qZero
    obtain ⟨qDegree, degreeEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero degreePositive.ne'
    rw [degreeEq, signedRemainderChainFuel_succ, qZero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases remainderZero : (divMod p q).remainder.isZero
    · have remainderDegree := divMod_remainder_degreeCount_lt p q qZero
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply congrArg (List.cons p)
      exact signedRemainderChainFuel_stable qDegree q
          (-((divMod p q).remainder)) (by
            rw [degreeCount_neg]
            omega)
    · rfl
  · have degreeZero := degreeCount_eq_zero_of_isZero qZero
    rw [degreeZero, signedRemainderChainFuel_zero]
    simp only [↓reduceIte]

def signedRemainderChain (p q : Polynomial) : List Polynomial :=
  signedRemainderChainWF p q

theorem signedRemainderChainFuel_length_le
    (fuel : Nat) (p q : Polynomial) :
    (signedRemainderChainFuel fuel p q).length ≤ fuel + 1 := by
  induction fuel generalizing p q with
  | zero =>
      change [p].length ≤ 1
      exact le_rfl
  | succ fuel inductionHypothesis =>
      change (if q.isZero then [p]
          else
            let dm := divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel fuel q (-dm.remainder)).length ≤
        (fuel + 1) + 1
      split
      · simp only [List.length_cons, List.length_nil]
        omega
      · change (if (divMod p q).remainder.isZero then [p, q]
            else p :: signedRemainderChainFuel fuel q
              (-((divMod p q).remainder))).length ≤
          fuel + 1 + 1
        split
        · simp only [List.length_cons, List.length_nil]
          omega
        · simp only [List.length_cons]
          have recursive := inductionHypothesis q (-((divMod p q).remainder))
          omega

theorem signedRemainderChainWF_length_le (p q : Polynomial) :
    (signedRemainderChainWF p q).length ≤ q.degreeCount + 1 :=
  signedRemainderChainFuel_length_le q.degreeCount p q

theorem signedRemainderChain_length_le (p q : Polynomial) :
    (signedRemainderChain p q).length ≤ q.degreeCount + 1 :=
  signedRemainderChainWF_length_le p q

theorem signedRemainderChain_eq_cons (p q : Polynomial) :
    ∃ tail, signedRemainderChain p q = p :: tail := by
  change ∃ tail, signedRemainderChainWF p q = p :: tail
  cases qZero : q.isZero
  · cases remainderZero : (divMod p q).remainder.isZero
    · refine ⟨signedRemainderChainWF q (-((divMod p q).remainder)), ?_⟩
      have unfolded := signedRemainderChainWF_eq p q
      simpa only [qZero, remainderZero, Bool.false_eq_true, ↓reduceIte]
        using unfolded
    · refine ⟨[q], ?_⟩
      have unfolded := signedRemainderChainWF_eq p q
      simpa only [qZero, remainderZero, Bool.false_eq_true, ↓reduceIte]
        using unfolded
  · refine ⟨[], ?_⟩
    have unfolded := signedRemainderChainWF_eq p q
    simpa only [qZero, ↓reduceIte] using unfolded

/-- With a represented nonzero second member, the signed chain exposes its
first Euclidean step uniformly, including the terminal zero-remainder case. -/
theorem signedRemainderChain_step_of_second_nonzero
    (p q : Polynomial) (qNonzero : q.isZero = false) :
    signedRemainderChain p q =
      p :: signedRemainderChain q (-((divMod p q).remainder)) := by
  rw [signedRemainderChain, signedRemainderChainWF_eq]
  split
  · rename_i qZero
    have : q.isZero = true := by simpa using qZero
    simp [qNonzero] at this
  · dsimp only
    split
    · rename_i remainderZero
      have nextZero : (-((divMod p q).remainder)).isZero = true := by
        simpa only [isZero_neg] using remainderZero
      rw [signedRemainderChain, signedRemainderChainWF_eq]
      simp only [nextZero, ↓reduceIte]
    · rfl

/-- A nonzero constant-degree second member ends the finite signed chain
after the displayed pair. -/
theorem signedRemainderChain_eq_pair_of_second_degreeCount_one
    {p q : Polynomial} (qNonzero : q.isZero = false)
    (qCount : q.degreeCount = 1) :
    signedRemainderChain p q = [p, q] := by
  rw [signedRemainderChain, signedRemainderChainWF_eq]
  split
  · rename_i qZero
    have : q.isZero = true := by simpa using qZero
    simp [qNonzero] at this
  · dsimp only
    split
    · rfl
    · rename_i remainderNonzero
      have remainderCount := divMod_remainder_degreeCount_lt p q qNonzero
      rw [qCount] at remainderCount
      have countZero : (divMod p q).remainder.degreeCount = 0 :=
        Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ remainderCount)
      have remainderZero := isZero_true_of_degreeCount_eq_zero countZero
      exact (remainderNonzero (by simpa using remainderZero)).elim

/-- If the first member has smaller degree, its normalization is exactly the
first remainder and the executable signed chain takes that recursive step. -/
theorem signedRemainderChain_eq_cons_of_degree_lt
    {p q : Polynomial} (pNonzero : p.isZero = false)
    (qNonzero : q.isZero = false) (degree : p.natDegree < q.natDegree) :
    signedRemainderChain p q =
      p :: signedRemainderChain q (-p.normalize) := by
  have division := divMod_of_natDegree_lt (p := p) (q := q) degree
  have normalizedNonzero : p.normalize.isZero = false := by simpa using pNonzero
  rw [signedRemainderChain, signedRemainderChainWF_eq]
  split
  · rename_i qZero
    have : q.isZero = true := by simpa using qZero
    simp [qNonzero] at this
  · dsimp only
    rw [division.2]
    split
    · rename_i remainderZero
      have : p.normalize.isZero = true := by simpa using remainderZero
      simp [normalizedNonzero] at this
    · rfl

/-- Every emitted member is represented nonzero when the first two are. -/
theorem signedRemainderChainWF_all_nonzero {p q : Polynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (signedRemainderChainWF p q).Forall (fun r => r.isZero = false) := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rw [signedRemainderChainWF_eq]
      split
      · rename_i hqZero
        have : q.isZero = true := by simpa using hqZero
        simp [hq] at this
      · dsimp only
        split
        · simp [hp, hq]
        · rename_i hr
          simp only [List.forall_cons, hp, true_and]
          have hnext : (-((divMod p q).remainder)).isZero = false := by
            simpa using hr
          have hcount : (-((divMod p q).remainder)).degreeCount < n := by
            rw [degreeCount_neg, ← hn]
            exact divMod_remainder_degreeCount_lt p q hq
          exact ih _ hcount hq hnext rfl

theorem signedRemainderChain_all_nonzero {p q : Polynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (signedRemainderChain p q).Forall (fun r => r.isZero = false) :=
  signedRemainderChainWF_all_nonzero hp hq

/-- Exact Horner identity for one signed remainder step. -/
theorem signedStep_eval_identity (p q : Polynomial) (x : Coordinate) :
    p.eval x = q.eval x * (divMod p q).quotient.eval x -
      (-((divMod p q).remainder)).eval x := by
  have h := divMod_eval_equation p q x
  rw [eval_neg]
  calc
    p.eval x = (divMod p q).remainder.eval x +
        q.eval x * (divMod p q).quotient.eval x := h.symm
    _ = q.eval x * (divMod p q).quotient.eval x -
        -((divMod p q).remainder.eval x) := by ring1

/-- No-common-zero data descends through one signed Euclidean step. -/
theorem noCommonZero_signedStep {p q : Polynomial}
    (coprime : NoCommonZero p q) :
    NoCommonZero q (-((divMod p q).remainder)) := by
  intro x
  by_cases hq : q.eval x = 0
  · right
    intro hnext
    have hstep := signedStep_eval_identity p q x
    have hp : p.eval x = 0 := by
      rw [hq, hnext, zero_mul, zero_sub] at hstep
      exact hstep
    rcases coprime x with hpNe | hqNe
    · exact hpNe hp
    · exact hqNe hq
  · exact Or.inl hq

/-- The terminal chain value of a coprime pair never vanishes. -/
theorem terminalValue_signedRemainderChain_eval_ne_zero
    {p q : Polynomial} (hq : q.isZero = false)
    (coprime : NoCommonZero p q) (x : Coordinate) {tail : List Polynomial}
    (hchain : signedRemainderChain p q = p :: tail) :
    terminalValue (p.eval x) (tail.map fun r => r.eval x) ≠ 0 := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q tail with
  | h n ih =>
      rw [signedRemainderChain, signedRemainderChainWF_eq] at hchain
      split at hchain
      · rename_i hqZero
        have : q.isZero = true := by simpa using hqZero
        simp [hq] at this
      · dsimp only at hchain
        split at hchain
        · rename_i hrem
          have hremTrue : (divMod p q).remainder.isZero = true := by
            simpa using hrem
          have htail : tail = [q] := by
            simpa using (congrArg List.tail hchain).symm
          subst tail
          simp only [List.map_cons, List.map_nil, terminalValue]
          intro hqx
          have hstep := signedStep_eval_identity p q x
          have hremEval := eval_eq_zero_of_isZero hremTrue x
          rw [hqx, eval_neg, hremEval, neg_zero, zero_mul, sub_zero] at hstep
          rcases coprime x with hpNe | hqNe
          · exact hpNe hstep
          · exact hqNe hqx
        · rename_i hremNonzero
          let next := -((divMod p q).remainder)
          have hremFalse : (divMod p q).remainder.isZero = false := by
            simpa using hremNonzero
          have hnextFalse : next.isZero = false := by
            simpa [next] using hremFalse
          have hnextCoprime : NoCommonZero q next := by
            simpa [next] using noCommonZero_signedStep coprime
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

theorem noAdjacentZero_signedRemainderChain {p q : Polynomial}
    (coprime : NoCommonZero p q) (x : Coordinate) :
    NoAdjacentZero ((signedRemainderChain p q).map fun r => r.eval x) := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rw [signedRemainderChain, signedRemainderChainWF_eq]
      split
      · simp [NoAdjacentZero]
      · rename_i hq
        dsimp only
        have hqFalse : q.isZero = false := by simpa using hq
        have pair : p.eval x ≠ 0 ∨ q.eval x ≠ 0 := coprime x
        split
        · simpa [NoAdjacentZero] using pair
        · let next := -((divMod p q).remainder)
          have nextCoprime : NoCommonZero q next := by
            simpa [next] using noCommonZero_signedStep coprime
          have count : next.degreeCount < n := by
            dsimp only [next]
            rw [degreeCount_neg, ← hn]
            exact divMod_remainder_degreeCount_lt p q hqFalse
          have recursive := ih next.degreeCount count
            (p := q) (q := next) nextCoprime rfl
          rw [signedRemainderChain] at recursive
          obtain ⟨tail, chain⟩ := signedRemainderChain_eq_cons q next
          rw [signedRemainderChain] at chain
          rw [show -((divMod p q).remainder) = next by rfl, chain]
          rw [chain] at recursive
          simpa [NoAdjacentZero, pair] using recursive

/-- Evaluation variation of a finite chain at one endpoint. -/
def endpointVariation2 (chain : List Polynomial) (x : Coordinate) : Nat :=
  variation2 (chain.map fun p => p.eval x)

/-- The endpoint variation of an exposed signed step is its first jump plus
the endpoint variation of the recursively emitted tail. -/
theorem endpointVariation2_signedRemainderChain_step
    (p q : Polynomial) (qNonzero : q.isZero = false) (x : Coordinate) :
    endpointVariation2 (signedRemainderChain p q) x =
      signJump (p.eval x) (q.eval x) +
        endpointVariation2
          (signedRemainderChain q (-((divMod p q).remainder))) x := by
  rw [endpointVariation2,
    signedRemainderChain_step_of_second_nonzero p q qNonzero]
  obtain ⟨tail, chain⟩ :=
    signedRemainderChain_eq_cons q (-((divMod p q).remainder))
  rw [chain]
  rfl

/-- Normalizing both displayed inputs preserves every endpoint variation of
the structurally computed signed remainder chain. -/
theorem endpointVariation2_signedRemainderChain_normalize
    (p q : Polynomial) (x : Coordinate) :
    endpointVariation2 (signedRemainderChain p.normalize q.normalize) x =
      endpointVariation2 (signedRemainderChain p q) x := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      by_cases qZero : q.isZero = true
      · have normalizedZero : q.normalize.isZero = true := by
          simpa using qZero
        simp [endpointVariation2, signedRemainderChain,
          signedRemainderChainWF_eq, qZero, normalizedZero]
      · have qNonzero : q.isZero = false := by simpa using qZero
        have normalizedNonzero : q.normalize.isZero = false := by
          simpa using qNonzero
        rw [endpointVariation2_signedRemainderChain_step
            p.normalize q.normalize normalizedNonzero x,
          endpointVariation2_signedRemainderChain_step
            p q qNonzero x]
        rw [eval_normalize, eval_normalize]
        have remainderEqual :
            (divMod p.normalize q.normalize).remainder =
              (divMod p q).remainder := by
          rw [divMod, divMod, degreeCount_normalize,
            normalize_normalize, normalize_normalize]
        rw [remainderEqual]
        let next := -((divMod p q).remainder)
        have nextNormalized : next.normalize = next := by
          exact normalize_neg _
        have nextCount : next.degreeCount < degree := by
          dsimp only [next]
          rw [degreeCount_neg, ← degreeEquation]
          exact divMod_remainder_degreeCount_lt p q qNonzero
        have recursive := inductionHypothesis next.degreeCount nextCount
          (p := q) (q := next) rfl
        rw [nextNormalized] at recursive
        rw [recursive]

/-- Simultaneous negation of both inputs preserves the endpoint variation
of the finite signed remainder chain. -/
theorem endpointVariation2_signedRemainderChain_neg
    (p q : Polynomial) (x : Coordinate) :
    endpointVariation2 (signedRemainderChain (-p) (-q)) x =
      endpointVariation2 (signedRemainderChain p q) x := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      by_cases qZero : q.isZero = true
      · have negZero : (-q).isZero = true := by simpa using qZero
        simp [endpointVariation2, signedRemainderChain,
          signedRemainderChainWF_eq, qZero, negZero]
      · have qNonzero : q.isZero = false := by simpa using qZero
        have negNonzero : (-q).isZero = false := by simpa using qNonzero
        rw [endpointVariation2_signedRemainderChain_step
            (-p) (-q) negNonzero x,
          endpointVariation2_signedRemainderChain_step
            p q qNonzero x]
        simp only [eval_neg, signJump_neg_neg,
          divMod_remainder_neg_both_direct]
        let next := -((divMod p q).remainder)
        have nextCount : next.degreeCount < degree := by
          dsimp only [next]
          rw [degreeCount_neg, ← degreeEquation]
          exact divMod_remainder_degreeCount_lt p q qNonzero
        rw [inductionHypothesis next.degreeCount nextCount
          (p := q) (q := next) rfl]

/-- Negating the second member of a coprime signed chain changes endpoint
variation by a constant independent of the displayed endpoint. -/
theorem endpointVariation2_neg_second_sum_eq
    {p q : Polynomial} {a b : Coordinate}
    (pairAtA : p.eval a ≠ 0 ∨ q.eval a ≠ 0)
    (pairAtB : p.eval b ≠ 0 ∨ q.eval b ≠ 0) :
    endpointVariation2 (signedRemainderChain p q) a +
        endpointVariation2 (signedRemainderChain p (-q)) a =
      endpointVariation2 (signedRemainderChain p q) b +
        endpointVariation2 (signedRemainderChain p (-q)) b := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      by_cases qZero : q.isZero = true
      · have negZero : (-q).isZero = true := by simpa using qZero
        simp [signedRemainderChain, signedRemainderChainWF_eq,
          endpointVariation2, qZero, negZero]
      · have qNonzero : q.isZero = false := by simpa using qZero
        have negNonzero : (-q).isZero = false := by simpa using qNonzero
        let remainder := (divMod p q).remainder
        have nextPair (x : Coordinate)
            (pair : p.eval x ≠ 0 ∨ q.eval x ≠ 0) :
            q.eval x ≠ 0 ∨ (-remainder).eval x ≠ 0 := by
          by_cases qZeroAtX : q.eval x = 0
          · right
            intro remainderZeroAtX
            have step := signedStep_eval_identity p q x
            have pZeroAtX : p.eval x = 0 := by
              rw [qZeroAtX] at step
              change p.eval x = 0 * (divMod p q).quotient.eval x -
                (-remainder).eval x at step
              rw [zero_mul, remainderZeroAtX, sub_zero] at step
              exact step
            rcases pair with pNonzeroAtX | qNonzeroAtX
            · exact pNonzeroAtX pZeroAtX
            · exact qNonzeroAtX qZeroAtX
          · exact Or.inl qZeroAtX
        have nextAtA := nextPair a pairAtA
        have nextAtB := nextPair b pairAtB
        have nextCount : (-remainder).degreeCount < degree := by
          rw [degreeCount_neg, ← degreeEquation]
          exact divMod_remainder_degreeCount_lt p q qNonzero
        have recursive := inductionHypothesis (-remainder).degreeCount
          nextCount (p := q) (q := -remainder)
          nextAtA nextAtB rfl
        have atA := signJump_add_signJump_neg pairAtA.symm
        have atB := signJump_add_signJump_neg pairAtB.symm
        rw [signJump_comm (q.eval a) (p.eval a)] at atA
        rw [signJump_comm (q.eval b) (p.eval b)] at atB
        rw [endpointVariation2_signedRemainderChain_step
              p q qNonzero a,
            endpointVariation2_signedRemainderChain_step
              p (-q) negNonzero a,
            endpointVariation2_signedRemainderChain_step
              p q qNonzero b,
            endpointVariation2_signedRemainderChain_step
              p (-q) negNonzero b,
            divMod_remainder_neg_right p q qNonzero]
        simp only [eval_neg]
        rw [show (divMod p q).remainder = remainder by rfl]
        rw [endpointVariation2_signedRemainderChain_neg q remainder a,
          endpointVariation2_signedRemainderChain_neg q remainder b]
        have remainderNormalized : remainder.normalize = remainder := by
          exact divMod_remainder_normalize p q
        rw [RFAP.ComputablePolynomial.DensePolynomial.neg_neg,
          remainderNormalized] at recursive
        calc
          signJump (p.eval a) (q.eval a) +
                endpointVariation2
                  (signedRemainderChain q (-remainder)) a +
              (signJump (p.eval a) (-q.eval a) +
                endpointVariation2
                  (signedRemainderChain q remainder) a) =
              (signJump (p.eval a) (q.eval a) +
                signJump (p.eval a) (-q.eval a)) +
                (endpointVariation2
                    (signedRemainderChain q (-remainder)) a +
                  endpointVariation2
                    (signedRemainderChain q remainder) a) := by ring1
          _ = 2 +
                (endpointVariation2
                    (signedRemainderChain q (-remainder)) b +
                  endpointVariation2
                    (signedRemainderChain q remainder) b) := by
              rw [atA, recursive]
          _ = (signJump (p.eval b) (q.eval b) +
                signJump (p.eval b) (-q.eval b)) +
                (endpointVariation2
                    (signedRemainderChain q (-remainder)) b +
                  endpointVariation2
                    (signedRemainderChain q remainder) b) := by
              rw [atB]
          _ = signJump (p.eval b) (q.eval b) +
                endpointVariation2
                  (signedRemainderChain q (-remainder)) b +
              (signJump (p.eval b) (-q.eval b) +
                endpointVariation2
                  (signedRemainderChain q remainder) b) := by ring1

/-- For a coprime pair, endpoint variation has the parity of the flag saying
that the first displayed coordinate vanishes. -/
theorem endpointVariation2_sub_firstZeroFlag_even
    {p q : Polynomial} (hq : q.isZero = false)
    (coprime : NoCommonZero p q) (x : Coordinate) :
    Even (((endpointVariation2 (signedRemainderChain p q) x : Nat) : Int) -
      (if p.eval x = 0 then 1 else 0)) := by
  obtain ⟨tail, chain⟩ := signedRemainderChain_eq_cons p q
  have terminal := terminalValue_signedRemainderChain_eval_ne_zero
    hq coprime x chain
  have variation := variation2_sub_signDifference_even
    (p.eval x) (tail.map fun r => r.eval x)
  have endpoint := sign_sub_terminal_sub_zeroFlag_even
    (x := p.eval x) terminal
  rcases variation.add endpoint with ⟨k, hk⟩
  rw [endpointVariation2, chain]
  simp only [List.map_cons]
  refine ⟨k, ?_⟩
  calc
    ((variation2 (p.eval x :: tail.map fun r => r.eval x) : Nat) : Int) -
          (if p.eval x = 0 then 1 else 0) =
        (((variation2 (p.eval x :: tail.map fun r => r.eval x) : Nat) : Int) -
          (sign (p.eval x) -
            sign (terminalValue (p.eval x) (tail.map fun r => r.eval x)))) +
        ((sign (p.eval x) -
            sign (terminalValue (p.eval x) (tail.map fun r => r.eval x))) -
          (if p.eval x = 0 then 1 else 0)) := by ring1
    _ = k + k := hk

/-- Doubled Cauchy index of a displayed coprime coordinate pair. -/
def cauchyIndex2 (p q : Polynomial) (a b : Coordinate) : Int :=
  (endpointVariation2 (signedRemainderChain q p) a : Int) -
    endpointVariation2 (signedRemainderChain q p) b

theorem cauchyIndex2_normalize (p q : Polynomial) (a b : Coordinate) :
    cauchyIndex2 p.normalize q.normalize a b = cauchyIndex2 p q a b := by
  unfold cauchyIndex2
  rw [endpointVariation2_signedRemainderChain_normalize,
    endpointVariation2_signedRemainderChain_normalize]

/-- Conjugating a pointwise coordinate pair negates its complete finite
Cauchy index. -/
theorem cauchyIndex2_neg_denominator
    {p q : Polynomial} {a b : Coordinate}
    (pairAtA : p.eval a ≠ 0 ∨ q.eval a ≠ 0)
    (pairAtB : p.eval b ≠ 0 ∨ q.eval b ≠ 0) :
    cauchyIndex2 p (-q) a b = -cauchyIndex2 p q a b := by
  rw [← cauchyIndex2_normalize p (-q) a b,
    ← cauchyIndex2_normalize p q a b]
  rw [normalize_neg, ← neg_normalize q]
  let P := p.normalize
  let Q := q.normalize
  have pNormalized : P.normalize = P := normalize_normalize p
  have normalizedAtA : Q.eval a ≠ 0 ∨ P.eval a ≠ 0 := by
    simpa only [P, Q, eval_normalize] using pairAtA.symm
  have normalizedAtB : Q.eval b ≠ 0 ∨ P.eval b ≠ 0 := by
    simpa only [P, Q, eval_normalize] using pairAtB.symm
  have variationSum := endpointVariation2_neg_second_sum_eq
    normalizedAtA normalizedAtB
  have negAtA := endpointVariation2_signedRemainderChain_neg Q (-P) a
  have negAtB := endpointVariation2_signedRemainderChain_neg Q (-P) b
  rw [RFAP.ComputablePolynomial.DensePolynomial.neg_neg,
    pNormalized] at negAtA negAtB
  change cauchyIndex2 P (-Q) a b = -cauchyIndex2 P Q a b
  unfold cauchyIndex2
  rw [negAtA, negAtB]
  have variationSumInt :=
    congrArg (fun value : Nat => (value : Int)) variationSum
  simp only [Nat.cast_add] at variationSumInt
  calc
    (endpointVariation2 (signedRemainderChain Q (-P)) a : Int) -
          endpointVariation2 (signedRemainderChain Q (-P)) b =
        ((endpointVariation2 (signedRemainderChain Q P) a : Int) +
            endpointVariation2 (signedRemainderChain Q (-P)) a) -
          ((endpointVariation2 (signedRemainderChain Q P) a : Int) +
            endpointVariation2 (signedRemainderChain Q (-P)) b) := by ring1
    _ = ((endpointVariation2 (signedRemainderChain Q P) b : Int) +
            endpointVariation2 (signedRemainderChain Q (-P)) b) -
          ((endpointVariation2 (signedRemainderChain Q P) a : Int) +
            endpointVariation2 (signedRemainderChain Q (-P)) b) := by
        rw [variationSumInt]
    _ = -((endpointVariation2 (signedRemainderChain Q P) a : Int) -
          endpointVariation2 (signedRemainderChain Q P) b) := by ring1

/-- A coprime displayed pair has Cauchy-index parity equal to the difference
of its denominator-coordinate endpoint-zero flags. -/
theorem cauchyIndex2_sub_secondZeroFlags_even
    {p q : Polynomial} (coprime : NoCommonZero p q) (a b : Coordinate) :
    Even (cauchyIndex2 p q a b -
      ((if q.eval a = 0 then 1 else 0) -
        (if q.eval b = 0 then 1 else 0))) := by
  by_cases pZero : p.isZero = true
  · have pa := eval_eq_zero_of_isZero pZero a
    have pb := eval_eq_zero_of_isZero pZero b
    have qa : q.eval a ≠ 0 := (coprime a).resolve_left (by simpa using pa)
    have qb : q.eval b ≠ 0 := (coprime b).resolve_left (by simpa using pb)
    refine ⟨0, ?_⟩
    simp [cauchyIndex2, endpointVariation2, signedRemainderChain,
      signedRemainderChainWF_eq, pZero, qa, qb]
  · have pNonzero : p.isZero = false := by simpa using pZero
    have reverseCoprime : NoCommonZero q p := fun x => (coprime x).symm
    have atA := endpointVariation2_sub_firstZeroFlag_even
      pNonzero reverseCoprime a
    have atB := endpointVariation2_sub_firstZeroFlag_even
      pNonzero reverseCoprime b
    rcases atA with ⟨leftHalf, leftIdentity⟩
    rcases atB with ⟨rightHalf, rightIdentity⟩
    refine ⟨leftHalf - rightHalf, ?_⟩
    simp only [cauchyIndex2]
    calc
      (endpointVariation2 (signedRemainderChain q p) a : Int) -
            endpointVariation2 (signedRemainderChain q p) b -
          ((if q.eval a = 0 then 1 else 0) -
            (if q.eval b = 0 then 1 else 0)) =
          ((endpointVariation2 (signedRemainderChain q p) a : Int) -
              (if q.eval a = 0 then 1 else 0)) -
            ((endpointVariation2 (signedRemainderChain q p) b : Int) -
              (if q.eval b = 0 then 1 else 0)) := by ring1
      _ = (leftHalf + leftHalf) - (rightHalf + rightHalf) := by
        rw [leftIdentity, rightIdentity]
      _ = (leftHalf - rightHalf) + (leftHalf - rightHalf) := by ring1

theorem cauchyIndex2_add (p q : Polynomial) (a b c : Coordinate) :
    cauchyIndex2 p q a c = cauchyIndex2 p q a b + cauchyIndex2 p q b c := by
  simp only [cauchyIndex2]
  ring1

theorem cauchyIndex2_reverse (p q : Polynomial) (a b : Coordinate) :
    cauchyIndex2 p q b a = -cauchyIndex2 p q a b := by
  simp only [cauchyIndex2]
  ring1

end RFAP.Sturm
