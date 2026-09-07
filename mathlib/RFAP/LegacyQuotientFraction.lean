import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring.Basic
import mathlib.RFAP.ExplicitField

/-!
# Legacy quotient-valued constructive fractions

A rational coordinate is represented as a quotient of explicit integer
numerator/positive-integer-denominator records.  This module is retained only
as a migration bridge.  Active quotient-free code belongs in the independent
`CanonicalFraction*` modules and must not import this file.

All operations, equality tests, and order tests compute from finite input
data.  The implementation deliberately avoids global enumeration,
`Classical.choice`, and `noncomputable` definitions, but its equality proofs
still use `Quot.sound`.
-/

namespace RFAP.ConstructiveFraction

structure Fraction where
  num : Int
  den : Int
  den_pos : 0 < den

def Equivalent (a b : Fraction) : Prop :=
  a.num * b.den = b.num * a.den

instance (a b : Fraction) : Decidable (Equivalent a b) :=
  inferInstanceAs (Decidable (a.num * b.den = b.num * a.den))

private theorem equivalent_refl (a : Fraction) : Equivalent a a := rfl

private theorem equivalent_symm {a b : Fraction} :
    Equivalent a b → Equivalent b a := Eq.symm

private theorem equivalent_trans {a b c : Fraction}
    (hab : Equivalent a b) (hbc : Equivalent b c) : Equivalent a c := by
  have hmul : (a.num * c.den - c.num * a.den) * b.den = 0 := by
    rw [sub_mul]
    calc
      a.num * c.den * b.den - c.num * a.den * b.den =
          c.den * (a.num * b.den) - a.den * (c.num * b.den) := by ring1
      _ = c.den * (b.num * a.den) - a.den * (b.num * c.den) := by
        rw [hab, ← hbc]
      _ = 0 := by ring1
  have hden : b.den ≠ 0 := Int.ne_of_gt b.den_pos
  have hdiff : a.num * c.den - c.num * a.den = 0 :=
    (Int.mul_eq_zero.mp hmul).resolve_right hden
  exact Int.sub_eq_zero.mp hdiff

instance fractionSetoid : Setoid Fraction where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

def Rational := Quotient fractionSetoid

def ofFraction (f : Fraction) : Rational := Quotient.mk' f

def zeroFraction : Fraction := ⟨0, 1, by decide⟩
def oneFraction : Fraction := ⟨1, 1, by decide⟩

def addFraction (a b : Fraction) : Fraction :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den,
    Int.mul_pos a.den_pos b.den_pos⟩

def negFraction (a : Fraction) : Fraction :=
  ⟨-a.num, a.den, a.den_pos⟩

def mulFraction (a b : Fraction) : Fraction :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

private theorem int_mul_self_pos {n : Int} (hn : n ≠ 0) : 0 < n * n := by
  cases n with
  | ofNat n =>
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
          exact Int.mul_pos (Int.ofNat_succ_pos n) (Int.ofNat_succ_pos n)
  | negSucc n => exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)

/-- `a.den / a.num`, represented with the always-positive denominator
`a.num²`; zero is mapped to zero. -/
def invFraction (a : Fraction) : Fraction :=
  if h : a.num = 0 then zeroFraction else
    ⟨a.den * a.num, a.num * a.num, int_mul_self_pos h⟩

private theorem addFraction_respects {a a' b b' : Fraction}
    (ha : Equivalent a a') (hb : Equivalent b b') :
    Equivalent (addFraction a b) (addFraction a' b') := by
  dsimp [Equivalent, addFraction] at ha hb ⊢
  calc
    (a.num * b.den + b.num * a.den) * (a'.den * b'.den) =
        (a.num * a'.den) * (b.den * b'.den) +
          (b.num * b'.den) * (a.den * a'.den) := by ring1
    _ = (a'.num * b'.den + b'.num * a'.den) * (a.den * b.den) := by
      rw [ha, hb]
      ring1

private theorem negFraction_respects {a b : Fraction}
    (h : Equivalent a b) : Equivalent (negFraction a) (negFraction b) := by
  dsimp [Equivalent, negFraction] at h ⊢
  rw [Int.neg_mul, Int.neg_mul, h]

private theorem mulFraction_respects {a a' b b' : Fraction}
    (ha : Equivalent a a') (hb : Equivalent b b') :
    Equivalent (mulFraction a b) (mulFraction a' b') := by
  dsimp [Equivalent, mulFraction] at ha hb ⊢
  calc
    a.num * b.num * (a'.den * b'.den) =
        (a.num * a'.den) * (b.num * b'.den) := by ring1
    _ = (a'.num * a.den) * (b'.num * b.den) := by rw [ha, hb]
    _ = a'.num * b'.num * (a.den * b.den) := by ring1

private theorem numerator_zero_iff_of_equivalent {a b : Fraction}
    (h : Equivalent a b) : a.num = 0 ↔ b.num = 0 := by
  constructor
  · intro ha
    rw [Equivalent, ha, Int.zero_mul] at h
    have hproduct : b.num * a.den = 0 := h.symm
    exact (Int.mul_eq_zero.mp hproduct).resolve_right (Int.ne_of_gt a.den_pos)
  · intro hb
    rw [Equivalent, hb, Int.zero_mul] at h
    exact (Int.mul_eq_zero.mp h).resolve_right (Int.ne_of_gt b.den_pos)

private theorem invFraction_respects {a b : Fraction}
    (h : Equivalent a b) : Equivalent (invFraction a) (invFraction b) := by
  have hzero := numerator_zero_iff_of_equivalent h
  by_cases ha : a.num = 0
  · have hb := hzero.mp ha
    simp [invFraction, ha, hb, Equivalent, zeroFraction]
  · have hb : b.num ≠ 0 := fun hb => ha (hzero.mpr hb)
    rw [invFraction, dif_neg ha, invFraction, dif_neg hb]
    dsimp [Equivalent]
    dsimp [Equivalent] at h
    calc
      a.den * a.num * (b.num * b.num) =
          b.num * a.num * (a.den * b.num) := by ring1
      _ = b.num * a.num * (b.den * a.num) := by
        rw [show a.den * b.num = b.den * a.num by
          calc
            a.den * b.num = b.num * a.den := Int.mul_comm _ _
            _ = a.num * b.den := h.symm
            _ = b.den * a.num := Int.mul_comm _ _]
      _ = b.den * b.num * (a.num * a.num) := by ring1

def add : Rational → Rational → Rational :=
  Quotient.map₂ addFraction
    (fun _ _ ha _ _ hb => addFraction_respects ha hb)

def neg : Rational → Rational :=
  Quotient.map negFraction (fun _ _ h => negFraction_respects h)

def mul : Rational → Rational → Rational :=
  Quotient.map₂ mulFraction
    (fun _ _ ha _ _ hb => mulFraction_respects ha hb)

def inv : Rational → Rational :=
  Quotient.map invFraction (fun _ _ h => invFraction_respects h)

instance : Zero Rational := ⟨ofFraction zeroFraction⟩
instance : One Rational := ⟨ofFraction oneFraction⟩
instance : Add Rational := ⟨add⟩
instance : Neg Rational := ⟨neg⟩
instance : Mul Rational := ⟨mul⟩
instance : Inv Rational := ⟨inv⟩

theorem add_comm (a b : Rational) : a + b = b + a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change Quotient.mk' (addFraction x y) = Quotient.mk' (addFraction y x)
  exact Quotient.sound (show Equivalent (addFraction x y) (addFraction y x) by
    dsimp [Equivalent, addFraction]
    ring1)

theorem add_assoc (a b c : Rational) : a + b + c = a + (b + c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (show
      Equivalent (addFraction (addFraction x y) z)
        (addFraction x (addFraction y z)) by
    dsimp [Equivalent, addFraction]
    ring1)

theorem zero_add (a : Rational) : 0 + a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (show Equivalent (addFraction zeroFraction x) x by
    dsimp [Equivalent, addFraction, zeroFraction]
    ring1)

theorem neg_add_cancel (a : Rational) : -a + a = 0 := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (show
      Equivalent (addFraction (negFraction x) x) zeroFraction by
    dsimp [Equivalent, addFraction, negFraction, zeroFraction]
    ring1)

theorem mul_assoc (a b c : Rational) : a * b * c = a * (b * c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (show
      Equivalent (mulFraction (mulFraction x y) z)
        (mulFraction x (mulFraction y z)) by
    dsimp [Equivalent, mulFraction]
    ring1)

theorem mul_comm (a b : Rational) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (show Equivalent (mulFraction x y) (mulFraction y x) by
    dsimp [Equivalent, mulFraction]
    ring1)

theorem one_mul (a : Rational) : 1 * a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (show Equivalent (mulFraction oneFraction x) x by
    dsimp [Equivalent, mulFraction, oneFraction]
    ring1)

theorem left_distrib (a b c : Rational) : a * (b + c) = a * b + a * c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro x y z
  exact Quotient.sound (show
      Equivalent (mulFraction x (addFraction y z))
        (addFraction (mulFraction x y) (mulFraction x z)) by
    dsimp [Equivalent, mulFraction, addFraction]
    ring1)

theorem mul_inv_cancel (a : Rational) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  refine Quotient.inductionOn a ?_ ha
  intro x hx
  by_cases hnum : x.num = 0
  · have hzero : (Quotient.mk' x : Rational) = ofFraction zeroFraction :=
      Quotient.sound (show Equivalent x zeroFraction by
      dsimp [Equivalent, zeroFraction]
      simp [hnum])
    exact (hx hzero).elim
  · exact Quotient.sound (show
        Equivalent (mulFraction x (invFraction x)) oneFraction by
      rw [invFraction, dif_neg hnum]
      dsimp [Equivalent, mulFraction, oneFraction]
      ring1)

theorem inv_zero : (0 : Rational)⁻¹ = 0 := by
  exact Quotient.sound (show Equivalent (invFraction zeroFraction) zeroFraction by
    simp [invFraction, zeroFraction, Equivalent])

theorem zero_ne_one : (0 : Rational) ≠ 1 := by
  intro h
  have hexact : Equivalent zeroFraction oneFraction := Quotient.exact h
  change (0 : Int) = 1 at hexact
  have hn : (0 : Nat) = 1 := Int.ofNat.inj hexact
  exact Nat.noConfusion hn

instance instField : Field Rational :=
  Field.ofMinimalAxioms Rational
    add_assoc
    zero_add
    neg_add_cancel
    mul_assoc
    mul_comm
    one_mul
    mul_inv_cancel
    inv_zero
    left_distrib
    ⟨0, 1, zero_ne_one⟩

/-- Reassociate four factors and exchange only the two middle factors. -/
theorem mul_pair_swap (a b c d : Rational) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  ring1

/-- Natural-number casts have their expected explicit denominator-one representative. -/
theorem natCast_eq_fraction (n : Nat) : (n : Rational) =
    ofFraction ⟨Int.ofNat n, 1, by decide⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.cast_succ, ih]
      apply Quotient.sound
      change Equivalent
        (addFraction ⟨Int.ofNat n, 1, by decide⟩ oneFraction)
        ⟨Int.ofNat n.succ, 1, by decide⟩
      dsimp [Equivalent, addFraction, oneFraction]
      simp only [Int.mul_one]

/-- Integer casts have their expected explicit denominator-one representative. -/
theorem intCast_eq_fraction (z : Int) : (z : Rational) =
    ofFraction ⟨z, 1, by decide⟩ := by
  cases z with
  | ofNat n =>
      change (((n : Nat) : Int) : Rational) =
        ofFraction ⟨Int.ofNat n, 1, by decide⟩
      rw [Int.cast_natCast, natCast_eq_fraction]
  | negSucc n =>
      rw [Int.cast_negSucc, natCast_eq_fraction]
      apply Quotient.sound
      change Equivalent
        (negFraction ⟨Int.ofNat (n + 1), 1, by decide⟩)
        ⟨Int.negSucc n, 1, by decide⟩
      rfl

private theorem equivalent_congr {a a' b b' : Fraction}
    (ha : Equivalent a a') (hb : Equivalent b b') :
    Equivalent a b ↔ Equivalent a' b' := by
  constructor
  · intro hab
    exact equivalent_trans (equivalent_symm ha) (equivalent_trans hab hb)
  · intro hab
    exact equivalent_trans ha (equivalent_trans hab (equivalent_symm hb))

def equal (a b : Rational) : Bool :=
  Quotient.liftOn₂ a b (fun x y => decide (Equivalent x y)) (by
    intro x x' y y' hx hy
    apply decide_eq_decide.mpr
    exact equivalent_congr hx hy)

theorem equal_eq_true_iff (a b : Rational) : equal a b = true ↔ a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change decide (Equivalent x y) = true ↔ Quotient.mk' x = Quotient.mk' y
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact @Quotient.sound Fraction fractionSetoid x y h
  · intro h
    exact @Quotient.exact Fraction fractionSetoid x y h

def rationalDecEq (a b : Rational) : Decidable (a = b) :=
  if h : equal a b = true then
    isTrue ((equal_eq_true_iff a b).mp h)
  else
    isFalse (fun equality => h ((equal_eq_true_iff a b).mpr equality))

instance instDecidableEq : DecidableEq Rational := rationalDecEq

def LessEqFraction (a b : Fraction) : Prop :=
  a.num * b.den ≤ b.num * a.den

instance (a b : Fraction) : Decidable (LessEqFraction a b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))

/-- Cancel a strictly positive integer factor on the right of a weak inequality. -/
theorem int_le_of_mul_le_mul_right {a b c : Int}
    (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hba : b < a := Int.not_le.mp hab
    have hstrict : b * c < a * c := Int.mul_lt_mul_of_pos_right hba hc
    exact ((Int.not_lt_of_ge h) hstrict).elim

private theorem lessEqFraction_imp {a a' b b' : Fraction}
    (ha : Equivalent a a') (hb : Equivalent b b') :
    LessEqFraction a b → LessEqFraction a' b' := by
  intro h
  have hpositive : 0 < a.den * b.den := Int.mul_pos a.den_pos b.den_pos
  apply int_le_of_mul_le_mul_right hpositive
  have hscale : 0 ≤ a'.den * b'.den :=
    Int.le_of_lt (Int.mul_pos a'.den_pos b'.den_pos)
  have hmul := Int.mul_le_mul_of_nonneg_right h hscale
  dsimp [LessEqFraction] at h hmul ⊢
  dsimp [Equivalent] at ha hb
  calc
    a'.num * b'.den * (a.den * b.den) =
        (a'.num * a.den) * (b'.den * b.den) := by ring1
    _ = (a.num * a'.den) * (b.den * b'.den) := by rw [← ha]; ring1
    _ = (a.num * b.den) * (a'.den * b'.den) := by ring1
    _ ≤ (b.num * a.den) * (a'.den * b'.den) := hmul
    _ = (b.num * b'.den) * (a.den * a'.den) := by ring1
    _ = (b'.num * b.den) * (a'.den * a.den) := by rw [hb]; ring1
    _ = b'.num * a'.den * (a.den * b.den) := by ring1

private theorem lessEqFraction_congr {a a' b b' : Fraction}
    (ha : Equivalent a a') (hb : Equivalent b b') :
    LessEqFraction a b ↔ LessEqFraction a' b' :=
  ⟨lessEqFraction_imp ha hb,
    lessEqFraction_imp (equivalent_symm ha) (equivalent_symm hb)⟩

def le (a b : Rational) : Prop :=
  Quotient.liftOn₂ a b LessEqFraction (fun _ _ _ _ ha hb =>
    propext (lessEqFraction_congr ha hb))

instance instLE : LE Rational := ⟨le⟩
instance instLT : LT Rational := ⟨fun a b => a ≤ b ∧ ¬b ≤ a⟩

theorem le_refl (a : Rational) : a ≤ a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Int.le_refl _

theorem le_trans (a b c : Rational) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  refine Quotient.inductionOn₃ a b c ?_ hab hbc
  intro x y z hxy hyz
  change LessEqFraction x z
  change LessEqFraction x y at hxy
  change LessEqFraction y z at hyz
  apply int_le_of_mul_le_mul_right y.den_pos
  dsimp [LessEqFraction] at hxy hyz ⊢
  have hz : 0 ≤ z.den := Int.le_of_lt z.den_pos
  have hx : 0 ≤ x.den := Int.le_of_lt x.den_pos
  have hxy' := Int.mul_le_mul_of_nonneg_right hxy hz
  have hyz' := Int.mul_le_mul_of_nonneg_right hyz hx
  calc
    x.num * z.den * y.den = (x.num * y.den) * z.den := by ring1
    _ ≤ (y.num * x.den) * z.den := hxy'
    _ = (y.num * z.den) * x.den := by ring1
    _ ≤ (z.num * y.den) * x.den := hyz'
    _ = z.num * x.den * y.den := by ring1

theorem le_antisymm (a b : Rational) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  refine Quotient.inductionOn₂ a b ?_ hab hba
  intro x y hxy hyx
  apply Quotient.sound
  exact Int.le_antisymm hxy hyx

instance instPartialOrder : PartialOrder Rational where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

theorem le_total (a b : Rational) : a ≤ b ∨ b ≤ a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Int.le_total (x.num * y.den) (y.num * x.den)

def lessEqual (a b : Rational) : Bool :=
  Quotient.liftOn₂ a b (fun x y => decide (LessEqFraction x y)) (by
    intro x x' y y' hx hy
    apply decide_eq_decide.mpr
    exact lessEqFraction_congr hx hy)

theorem lessEqual_eq_true_iff (a b : Rational) :
    lessEqual a b = true ↔ a ≤ b := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change decide (LessEqFraction x y) = true ↔ LessEqFraction x y
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

def rationalDecLE (a b : Rational) : Decidable (a ≤ b) :=
  if h : lessEqual a b = true then
    isTrue ((lessEqual_eq_true_iff a b).mp h)
  else
    isFalse (fun equality => h ((lessEqual_eq_true_iff a b).mpr equality))

instance instDecidableLE : DecidableLE Rational := rationalDecLE

def rationalDecLT (a b : Rational) : Decidable (a < b) :=
  show Decidable (a ≤ b ∧ ¬b ≤ a) from
    instDecidableAnd

instance instDecidableLT : DecidableLT Rational := rationalDecLT
instance instMin : Min Rational := minOfLe
instance instMax : Max Rational := maxOfLe
instance instOrd : Ord Rational := ⟨fun a b => compareOfLessAndEq a b⟩

instance instLinearOrder : LinearOrder Rational where
  le_total := le_total
  toDecidableLE := instDecidableLE
  toDecidableEq := instDecidableEq
  toDecidableLT := instDecidableLT
  compare_eq_compareOfLessAndEq := by intros; rfl

private theorem add_le_add_left_rational (a b : Rational) (hab : a ≤ b)
    (c : Rational) : a + c ≤ b + c := by
  refine Quotient.inductionOn₃ a b c ?_ hab
  intro x y z hxy
  change LessEqFraction (addFraction x z) (addFraction y z)
  change LessEqFraction x y at hxy
  have hz : 0 ≤ z.den * z.den :=
    Int.le_of_lt (int_mul_self_pos (Int.ne_of_gt z.den_pos))
  have hscaled := Int.mul_le_mul_of_nonneg_right hxy hz
  dsimp [LessEqFraction, addFraction] at hxy ⊢
  calc
    (x.num * z.den + z.num * x.den) * (y.den * z.den) =
        z.num * x.den * y.den * z.den +
          (x.num * y.den) * (z.den * z.den) := by ring1
    _ ≤ z.num * x.den * y.den * z.den +
          (y.num * x.den) * (z.den * z.den) :=
      Int.add_le_add_left hscaled _
    _ = (y.num * z.den + z.num * y.den) * (x.den * z.den) := by ring1

private theorem le_of_add_le_add_left_rational
    (a b c : Rational) (h : a + b ≤ a + c) : b ≤ c := by
  refine Quotient.inductionOn₃ a b c ?_ h
  intro x y z hsum
  change LessEqFraction y z
  change LessEqFraction (addFraction x y) (addFraction x z) at hsum
  have hrewritten :
      x.num * x.den * y.den * z.den +
          (y.num * z.den) * (x.den * x.den) ≤
        x.num * x.den * y.den * z.den +
          (z.num * y.den) * (x.den * x.den) := by
    calc
      x.num * x.den * y.den * z.den +
          (y.num * z.den) * (x.den * x.den) =
          (x.num * y.den + y.num * x.den) * (x.den * z.den) := by ring1
      _ ≤ (x.num * z.den + z.num * x.den) * (x.den * y.den) := hsum
      _ = x.num * x.den * y.den * z.den +
          (z.num * y.den) * (x.den * x.den) := by ring1
  have hcancelled :
      (y.num * z.den) * (x.den * x.den) ≤
        (z.num * y.den) * (x.den * x.den) :=
    Int.le_of_add_le_add_left hrewritten
  exact int_le_of_mul_le_mul_right
    (int_mul_self_pos (Int.ne_of_gt x.den_pos)) hcancelled

instance instIsOrderedAddMonoid : IsOrderedAddMonoid Rational where
  add_le_add_left := add_le_add_left_rational

instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Rational where
  le_of_add_le_add_left := le_of_add_le_add_left_rational

/-- Explicit weak right addition. -/
theorem add_le_add_right_direct {a b : Rational} (lessEqual : a ≤ b)
    (c : Rational) : a + c ≤ b + c :=
  add_le_add_left_rational a b lessEqual c

/-- Explicit weak addition in both arguments. -/
theorem add_le_add_direct {a b c d : Rational}
    (left : a ≤ b) (right : c ≤ d) : a + c ≤ b + d := by
  calc
    a + c ≤ b + c := add_le_add_right_direct left c
    _ = c + b := by ring1
    _ ≤ d + b := add_le_add_right_direct right b
    _ = b + d := by ring1

/-- Recover a weak comparison from the failure of the reverse strict
comparison using the concrete decidable order. -/
theorem le_of_not_gt_direct {a b : Rational} (notGreater : ¬ b < a) :
    a ≤ b := by
  rcases le_total a b with lessEqual | reverse
  · exact lessEqual
  · by_cases direct : a ≤ b
    · exact direct
    · exact (notGreater ⟨reverse, direct⟩).elim

/-- Recover a strict comparison from the failure of the reverse weak
comparison using the concrete decidable order. -/
theorem lt_of_not_ge_direct {a b : Rational} (notGreaterEqual : ¬ b ≤ a) :
    a < b := by
  have lessEqual : a ≤ b := by
    rcases le_total a b with direct | reverse
    · exact direct
    · exact (notGreaterEqual reverse).elim
  exact ⟨lessEqual, notGreaterEqual⟩

/-- Forget the strict half of the concrete rational comparison without
routing through the generic ordered-type projection, whose bundled instance
can retain a choice-bearing implementation detail. -/
theorem le_of_lt_direct {a b : Rational} (less : a < b) : a ≤ b := by
  change a ≤ b ∧ ¬ b ≤ a at less
  exact less.1

/-- Explicit weak translation by a common subtraction. -/
theorem sub_le_sub_right_direct {a b : Rational} (lessEqual : a ≤ b)
    (c : Rational) : a - c ≤ b - c := by
  calc
    a - c = a + -c := by ring1
    _ ≤ b + -c := add_le_add_right_direct lessEqual (-c)
    _ = b - c := by ring1

/-- Explicit cancellation of the same right summand. -/
theorem le_of_add_le_add_right_direct {a b c : Rational}
    (lessEqual : a + c ≤ b + c) : a ≤ b := by
  apply le_of_add_le_add_left_rational c a b
  calc
    c + a = a + c := add_comm _ _
    _ ≤ b + c := lessEqual
    _ = c + b := add_comm _ _

/-- A weak comparison gives a nonnegative explicit difference. -/
theorem sub_nonneg_direct {a b : Rational} (lessEqual : a ≤ b) :
    0 ≤ b - a := by
  have shifted := add_le_add_right_direct lessEqual (-a)
  calc
    0 = a + -a := by ring1
    _ ≤ b + -a := shifted
    _ = b - a := by ring1

/-- Recover a weak comparison from a nonnegative explicit difference. -/
theorem le_of_sub_nonneg_direct {a b : Rational} (nonnegative : 0 ≤ b - a) :
    a ≤ b := by
  have shifted := add_le_add_right_direct nonnegative a
  calc
    a = 0 + a := by ring1
    _ ≤ (b - a) + a := shifted
    _ = b := by ring1

/-- A strict inequality gives a positive difference by direct ordered-additive
reasoning.  The generic ordered-field `sub_pos` route selects a choice-bearing
inheritance path for this concrete type. -/
theorem sub_pos_direct {a b : Rational} (less : a < b) : 0 < b - a := by
  have nonnegative : 0 ≤ b - a := by
    rw [sub_eq_add_neg]
    calc
      0 = a + -a := by ring1
      _ ≤ b + -a := add_le_add_left_rational a b less.1 (-a)
  refine ⟨nonnegative, ?_⟩
  intro reverse
  apply less.2
  calc
    b = (b - a) + a := by ring1
    _ ≤ 0 + a := add_le_add_left_rational (b - a) 0 reverse a
    _ = a := by ring1

/-- A strict inequality gives the corresponding negative difference without
using the generic ordered-field inheritance route. -/
theorem sub_neg_direct {a b : Rational} (less : a < b) : a - b < 0 := by
  have positive : 0 < b - a := sub_pos_direct less
  calc
    a - b = -(b - a) := by ring1
    _ < 0 := neg_neg_of_pos positive

/-- Strict right addition using the concrete order and its direct cancellation
law. -/
theorem add_lt_add_right_direct {a b : Rational} (less : a < b)
    (c : Rational) : a + c < b + c := by
  refine ⟨add_le_add_left_rational a b less.1 c, ?_⟩
  intro reverse
  apply less.2
  apply le_of_add_le_add_left_rational c b a
  calc
    c + b = b + c := add_comm _ _
    _ ≤ a + c := reverse
    _ = c + a := add_comm _ _

/-- Explicit strict translation by a common subtraction. -/
theorem sub_lt_sub_right_direct {a b : Rational} (less : a < b)
    (c : Rational) : a - c < b - c := by
  calc
    a - c = a + -c := by ring1
    _ < b + -c := add_lt_add_right_direct less (-c)
    _ = b - c := by ring1

/-- Recover a strict comparison from a negative explicit difference using
only direct ordered-additive cancellation. -/
theorem lt_of_sub_neg_direct {a b : Rational} (negative : a - b < 0) :
    a < b := by
  have shifted := add_lt_add_right_direct negative b
  calc
    a = (a - b) + b := by ring1
    _ < 0 + b := shifted
    _ = b := by ring1

/-- Strict left addition obtained from the direct right-addition theorem. -/
theorem add_lt_add_left_direct {a b : Rational} (less : a < b)
    (c : Rational) : c + a < c + b := by
  rw [add_comm c a, add_comm c b]
  exact add_lt_add_right_direct less c

/-- Strict negation reverses order by direct ordered-additive cancellation.
The generic ordered-ring inheritance route for this concrete quotient type
introduces `Classical.choice`. -/
theorem neg_lt_neg_direct {a b : Rational} (less : a < b) : -b < -a := by
  have shifted := add_lt_add_right_direct less (-b)
  have belowZero : a - b < 0 := by
    calc
      a - b = a + -b := sub_eq_add_neg _ _
      _ < b + -b := shifted
      _ = 0 := by ring1
  have shiftedAgain := add_lt_add_right_direct belowZero (-a)
  calc
    -b = (a - b) + -a := by ring1
    _ < 0 + -a := shiftedAgain
    _ = -a := by ring1

/-- Strict subtraction from a common left term, obtained by explicit
negation reversal and addition. -/
theorem sub_lt_sub_left_direct {a b : Rational} (less : a < b)
    (c : Rational) : c - b < c - a := by
  calc
    c - b = c + -b := by ring1
    _ < c + -a := add_lt_add_left_direct (neg_lt_neg_direct less) c
    _ = c - a := by ring1

/-- Weak negation reversal from a finite equality/strict-order split. -/
theorem neg_le_neg_direct {a b : Rational} (lessEqual : a ≤ b) : -b ≤ -a := by
  by_cases equal : a = b
  · rw [equal]
  · exact (neg_lt_neg_direct
      ⟨lessEqual, fun reverse => equal (le_antisymm a b lessEqual reverse)⟩).le

/-- Strict addition in both arguments through the explicit one-sided laws. -/
theorem add_lt_add_direct {a b c d : Rational}
    (left : a < b) (right : c < d) : a + c < b + d :=
  (add_lt_add_right_direct left c).trans
    (add_lt_add_left_direct right b)

/-- Recover a strict comparison from a positive explicit difference. -/
theorem lt_of_sub_pos_direct {a b : Rational} (positive : 0 < b - a) : a < b := by
  have shifted := add_lt_add_right_direct positive a
  calc
    a = 0 + a := (zero_add a).symm
    _ < (b - a) + a := shifted
    _ = b := by ring1

instance instZeroLEOneClass : ZeroLEOneClass Rational where
  zero_le_one := by decide

private theorem quotient_lt_iff_fraction_lt (a b : Fraction) :
    (ofFraction a : Rational) < ofFraction b ↔
      a.num * b.den < b.num * a.den := by
  change (LessEqFraction a b ∧ ¬ LessEqFraction b a) ↔ _
  constructor
  · intro h
    exact lt_of_le_not_ge h.1 h.2
  · intro h
    exact ⟨Int.le_of_lt h, Int.not_le_of_gt h⟩

/-- Strict positivity of a natural cast, proved from its displayed
denominator-one representative.  This bypasses the generic characteristic
zero instance route. -/
theorem natCast_pos_direct {n : Nat} (hn : 0 < n) :
    (0 : Rational) < (n : Rational) := by
  change ((0 : Nat) : Rational) < (n : Rational)
  rw [natCast_eq_fraction 0, natCast_eq_fraction n,
    quotient_lt_iff_fraction_lt]
  simpa only [Int.zero_mul, Int.mul_one] using
    (show Int.ofNat 0 < Int.ofNat n from Int.ofNat_lt.mpr hn)

/-- Strict order of natural casts by direct representative comparison. -/
theorem natCast_lt_direct {m n : Nat} (hmn : m < n) :
    (m : Rational) < (n : Rational) := by
  rw [natCast_eq_fraction m, natCast_eq_fraction n,
    quotient_lt_iff_fraction_lt]
  simpa only [Int.mul_one] using
    (show Int.ofNat m < Int.ofNat n from Int.ofNat_lt.mpr hmn)

/-- Weak order of natural casts by a finite equality/strict-order split. -/
theorem natCast_le_direct {m n : Nat} (hmn : m ≤ n) :
    (m : Rational) ≤ (n : Rational) := by
  by_cases equal : m = n
  · subst n
    exact le_rfl
  · exact (natCast_lt_direct (lt_of_le_of_ne hmn equal)).le

/-- Equality of natural casts reflects equality without using a generic
infinite-carrier or characteristic-zero argument. -/
theorem natCast_injective_direct {m n : Nat}
    (equal : (m : Rational) = (n : Rational)) : m = n := by
  rw [natCast_eq_fraction m, natCast_eq_fraction n] at equal
  have representatives : Equivalent
      ⟨Int.ofNat m, 1, by decide⟩ ⟨Int.ofNat n, 1, by decide⟩ :=
    Quotient.exact equal
  change Int.ofNat m * 1 = Int.ofNat n * 1 at representatives
  simp only [Int.mul_one] at representatives
  exact Int.ofNat.inj representatives

/-- Strict order of natural casts is reflected without using a global
characteristic-zero instance. -/
theorem natCast_lt_iff_direct {m n : Nat} :
    (m : Rational) < (n : Rational) ↔ m < n := by
  constructor
  · intro castLess
    apply Nat.lt_of_not_ge
    intro reverse
    exact (not_lt_of_ge (natCast_le_direct reverse)) castLess
  · exact natCast_lt_direct

/-- Weak order of natural casts is reflected by a finite strict/equality
split. -/
theorem natCast_le_iff_direct {m n : Nat} :
    (m : Rational) ≤ (n : Rational) ↔ m ≤ n := by
  constructor
  · intro castOrder
    by_cases order : m ≤ n
    · exact order
    · have reverse : n < m := Nat.lt_of_not_ge order
      exact ((not_lt_of_ge castOrder) (natCast_lt_direct reverse)).elim
  · exact natCast_le_direct

/-- Equality of integer casts reflects equality by direct comparison of
their denominator-one representatives. -/
theorem intCast_injective_direct {m n : Int}
    (equal : (m : Rational) = (n : Rational)) : m = n := by
  rw [intCast_eq_fraction m, intCast_eq_fraction n] at equal
  have representatives : Equivalent
      ⟨m, 1, by decide⟩ ⟨n, 1, by decide⟩ := Quotient.exact equal
  change m * 1 = n * 1 at representatives
  simpa only [Int.mul_one] using representatives

private theorem mul_lt_mul_of_pos_left_rational
    {a : Rational} (ha : 0 < a) {b c : Rational} (hbc : b < c) :
    a * b < a * c := by
  refine Quotient.inductionOn₃ a b c ?_ ha hbc
  intro x y z hx hyz
  change (ofFraction zeroFraction : Rational) < ofFraction x at hx
  change (ofFraction y : Rational) < ofFraction z at hyz
  change (ofFraction (mulFraction x y) : Rational) <
    ofFraction (mulFraction x z)
  rw [quotient_lt_iff_fraction_lt] at hx hyz ⊢
  dsimp [zeroFraction, mulFraction] at hx hyz ⊢
  have hxnum : 0 < x.num := by
    simpa only [Int.zero_mul, Int.mul_one] using hx
  have hscaled := Int.mul_lt_mul_of_pos_left hyz
    (Int.mul_pos hxnum x.den_pos)
  calc
    x.num * y.num * (x.den * z.den) =
        (x.num * x.den) * (y.num * z.den) := by ring1
    _ < (x.num * x.den) * (z.num * y.den) := hscaled
    _ = x.num * z.num * (x.den * y.den) := by ring1

private theorem mul_lt_mul_of_pos_right_rational
    {c : Rational} (hc : 0 < c) {a b : Rational} (hab : a < b) :
    a * c < b * c := by
  rw [mul_comm a c, mul_comm b c]
  exact mul_lt_mul_of_pos_left_rational hc hab

theorem mul_lt_mul_of_pos_left_direct {a b c : Rational}
    (ha : 0 < a) (less : b < c) : a * b < a * c :=
  mul_lt_mul_of_pos_left_rational ha less

theorem mul_lt_mul_of_pos_right_direct {a b c : Rational}
    (less : a < b) (hc : 0 < c) : a * c < b * c :=
  mul_lt_mul_of_pos_right_rational hc less

/-- Strict positivity of a product through the concrete quotient order. -/
theorem mul_pos_direct {a b : Rational} (ha : 0 < a) (hb : 0 < b) :
    0 < a * b := by
  calc
    0 = a * 0 := by ring1
    _ < a * b := mul_lt_mul_of_pos_left_rational ha hb

theorem mul_pos_of_neg_of_neg_direct {a b : Rational}
    (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have negativeAPositive := sub_pos_direct ha
  have negativeBPositive := sub_pos_direct hb
  rw [show (0 : Rational) - a = -a by ring1] at negativeAPositive
  rw [show (0 : Rational) - b = -b by ring1] at negativeBPositive
  calc
    0 < (-a) * (-b) := mul_pos_direct negativeAPositive negativeBPositive
    _ = a * b := by ring1

theorem mul_neg_of_neg_of_pos_direct {a b : Rational}
    (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have negativeAPositive := sub_pos_direct ha
  rw [show (0 : Rational) - a = -a by ring1] at negativeAPositive
  have positive : 0 < (-a) * b := mul_pos_direct negativeAPositive hb
  have negated : 0 < -(a * b) := by
    calc
      0 < (-a) * b := positive
      _ = -(a * b) := by ring1
  exact neg_pos.mp negated

theorem mul_neg_of_pos_of_neg_direct {a b : Rational}
    (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  rw [mul_comm]
  exact mul_neg_of_neg_of_pos_direct hb ha

/-- Reflect strict positivity through an explicitly nonnegative left factor.
This direct three-sign proof avoids the generic reflected-order instance,
whose bundled construction carries `Classical.choice` in its axiom closure. -/
theorem pos_of_mul_pos_right_direct {a b : Rational}
    (productPositive : 0 < a * b) (aNonnegative : 0 ≤ a) : 0 < b := by
  rcases lt_trichotomy b 0 with bNegative | rfl | bPositive
  · rcases lt_trichotomy a 0 with aNegative | rfl | aPositive
    · exact (not_lt_of_ge aNonnegative aNegative).elim
    · rw [zero_mul] at productPositive
      exact (lt_irrefl 0 productPositive).elim
    · have productNegative :=
        mul_neg_of_pos_of_neg_direct aPositive bNegative
      exact (lt_asymm productPositive productNegative).elim
  · rw [mul_zero] at productPositive
    exact (lt_irrefl 0 productPositive).elim
  · exact bPositive

instance instPosMulStrictMono : PosMulStrictMono Rational where
  mul_lt_mul_of_pos_left := fun {a} ha {b c} hbc =>
    mul_lt_mul_of_pos_left_rational (a := a) ha (b := b) (c := c) hbc

instance instMulPosStrictMono : MulPosStrictMono Rational where
  mul_lt_mul_of_pos_right := fun {c} hc {a b} hab =>
    mul_lt_mul_of_pos_right_rational (c := c) hc (a := a) (b := b) hab

instance instIsStrictOrderedRing : IsStrictOrderedRing Rational where

/-- A square is nonnegative by direct inspection of a representative.  This avoids the
generic weak-monotonicity instance whose construction uses a proposition split. -/
theorem sq_nonneg_direct (a : Rational) : 0 ≤ a ^ 2 := by
  rw [pow_two]
  refine Quotient.inductionOn a ?_
  intro x
  change LessEqFraction zeroFraction (mulFraction x x)
  dsimp [LessEqFraction, zeroFraction, mulFraction]
  have hn : 0 ≤ x.num * x.num := by
    cases x.num with
    | ofNat n =>
        exact Int.mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg n)
    | negSucc n =>
        have hnonpositive : Int.negSucc n ≤ 0 :=
          Int.le_of_lt (Int.negSucc_lt_zero n)
        exact Int.mul_nonneg_of_nonpos_of_nonpos hnonpositive hnonpositive
  simpa only [Int.zero_mul, Int.mul_one] using hn

/-- A square vanishes exactly when its finite numerator vanishes. -/
theorem sq_eq_zero_direct (a : Rational) : a ^ 2 = 0 ↔ a = 0 := by
  constructor
  · rw [pow_two]
    refine Quotient.inductionOn a ?_
    intro x h
    have hexact : Equivalent (mulFraction x x) zeroFraction :=
      Quotient.exact h
    have hproduct : x.num * x.num = 0 := by
      simpa only [Equivalent, mulFraction, zeroFraction, Int.mul_one,
        Int.zero_mul] using hexact
    have hnum : x.num = 0 :=
      match Int.mul_eq_zero.mp hproduct with
      | Or.inl hzero => hzero
      | Or.inr hzero => hzero
    apply Quotient.sound
    change x.num * 1 = 0 * x.den
    simpa only [Int.mul_one, Int.zero_mul] using hnum
  · intro h
    rw [h]
    change (0 : Rational) * 0 = 0
    ring1

/-- Right multiplication cancels a nonzero divisor from an explicit quotient. -/
theorem div_mul_cancel_of_ne (a c : Rational) (hc : c ≠ 0) :
    (a / c) * c = a := by
  change (a * c⁻¹) * c = a
  calc
    (a * c⁻¹) * c = a * (c⁻¹ * c) := mul_assoc _ _ _
    _ = a * (c * c⁻¹) := congrArg (fun value => a * value) (mul_comm _ _)
    _ = a * 1 := by rw [mul_inv_cancel c hc]
    _ = 1 * a := mul_comm _ _
    _ = a := one_mul _

/-- Direct weak monotonicity, avoiding the generic instance constructor that splits an
inequality through `Classical.propDecidable`. -/
theorem mul_le_mul_of_nonneg_right_direct {a b c : Rational}
    (hab : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  by_cases hc0 : c = 0
  · rw [hc0, mul_zero, mul_zero]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    by_cases habEq : a = b
    · rw [habEq]
    · have hablt : a < b :=
        ⟨hab, fun hba => habEq (le_antisymm a b hab hba)⟩
      exact (mul_lt_mul_of_pos_right hablt hcpos).le

theorem mul_le_mul_of_nonneg_left_direct {a b c : Rational}
    (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_le_mul_of_nonneg_right_direct hab hc

/-- A direct finite ordered-ring proof that comparison of squares against a
nonnegative bound controls the upper sign.  This avoids importing the broad
absolute-value hierarchy for one elementary rational fact. -/
theorem le_of_sq_le_sq_direct {a bound : Rational} (boundNonnegative : 0 ≤ bound)
    (squares : a ^ 2 ≤ bound ^ 2) : a ≤ bound := by
  by_cases direct : a ≤ bound
  · exact direct
  · have boundLt : bound < a := lt_of_not_ge direct
    have aPositive : 0 < a := lt_of_le_of_lt boundNonnegative boundLt
    have first : bound * bound ≤ bound * a :=
      mul_le_mul_of_nonneg_left_direct boundLt.le boundNonnegative
    have second : bound * a < a * a :=
      mul_lt_mul_of_pos_right_rational aPositive boundLt
    have squareLt : bound ^ 2 < a ^ 2 := by
      simpa only [pow_two] using first.trans_lt second
    exact ((not_lt_of_ge squares) squareLt).elim

/-- The matching lower-sign consequence of a finite square comparison. -/
theorem neg_le_of_sq_le_sq_direct {a bound : Rational}
    (boundNonnegative : 0 ≤ bound) (squares : a ^ 2 ≤ bound ^ 2) :
    -bound ≤ a := by
  have negSquares : (-a) ^ 2 ≤ bound ^ 2 := by
    have identity : (-a) ^ 2 = a ^ 2 := by ring1
    rw [identity]
    exact squares
  have upper : -a ≤ bound :=
    le_of_sq_le_sq_direct boundNonnegative negSquares
  calc
    -bound ≤ -(-a) := neg_le_neg upper
    _ = a := by ring1

theorem mul_nonneg_direct {a b : Rational} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a * b := by
  have h := mul_le_mul_of_nonneg_right_direct ha hb
  rwa [zero_mul] at h

/-- Nonnegativity of a finite power through the explicit quotient order.
This avoids the generic ordered-monoid instance route. -/
theorem pow_nonneg_direct {a : Rational} (ha : 0 ≤ a) :
    ∀ exponent : Nat, 0 ≤ a ^ exponent
  | 0 => by
      change (0 : Rational) ≤ 1
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact mul_nonneg_direct (pow_nonneg_direct ha exponent) ha

theorem pow_pos_direct {a : Rational} (ha : 0 < a) :
    ∀ exponent : Nat, 0 < a ^ exponent
  | 0 => by
      change (0 : Rational) < 1
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact mul_pos_direct (pow_pos_direct ha exponent) ha

theorem mul_le_mul_direct {a b c d : Rational}
    (hab : a ≤ b) (hcd : c ≤ d) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_right_direct hab hc).trans
    (mul_le_mul_of_nonneg_left_direct hcd hb)

/-- Monotonicity of finite natural powers through explicit quotient
multiplication. -/
theorem pow_le_pow_direct {a b : Rational} (ha : 0 ≤ a) (less : a ≤ b) :
    ∀ exponent : Nat, a ^ exponent ≤ b ^ exponent
  | 0 => le_rfl
  | exponent + 1 => by
      rw [pow_succ, pow_succ]
      exact mul_le_mul_direct
        (pow_le_pow_direct ha less exponent) less ha
        (pow_nonneg_direct (ha.trans less) exponent)

/-- Direct cancellation of a strictly positive right factor. -/
theorem le_of_mul_le_mul_right_direct {a b c : Rational}
    (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hba : b ≤ a := (le_total b a).resolve_right hab
    have hstrict : b * c < a * c :=
      mul_lt_mul_of_pos_right ⟨hba, hab⟩ hc
    exact ((not_lt_of_ge h) hstrict).elim

/-- Direct strict cancellation of a positive right factor. -/
theorem lt_of_mul_lt_mul_right_direct {a b c : Rational}
    (h : a * c < b * c) (hc : 0 < c) : a < b := by
  by_cases less : a < b
  · exact less
  · have reverse : b ≤ a := le_of_not_gt less
    have scaled := mul_le_mul_of_nonneg_right_direct reverse hc.le
    exact ((not_lt_of_ge scaled) h).elim

/-- Direct strict cancellation of a common additive right term. -/
theorem lt_of_add_lt_add_right_direct {a b c : Rational}
    (h : a + c < b + c) : a < b := by
  calc
    a = (a + c) + -c := by ring1
    _ < (b + c) + -c := add_lt_add_right_direct h (-c)
    _ = b := by ring1

/-- Constructive positive-denominator division comparison. -/
theorem div_le_iff_pos {a b c : Rational} (hc : 0 < c) :
    a / c ≤ b ↔ a ≤ b * c := by
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right_direct h hc.le
    rwa [div_mul_cancel_of_ne a c (ne_of_gt hc)] at hmul
  · intro h
    apply le_of_mul_le_mul_right_direct _ hc
    rwa [div_mul_cancel_of_ne a c (ne_of_gt hc)]

/-- Constructive positive-denominator comparison into a quotient. -/
theorem le_div_iff_pos {a b c : Rational} (hc : 0 < c) :
    a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right_direct h hc.le
    rwa [div_mul_cancel_of_ne b c (ne_of_gt hc)] at hmul
  · intro h
    apply le_of_mul_le_mul_right_direct _ hc
    rwa [div_mul_cancel_of_ne b c (ne_of_gt hc)]

/-- Constructive strict positive-denominator division comparison. -/
theorem div_lt_iff_pos {a b c : Rational} (hc : 0 < c) :
    a / c < b ↔ a < b * c := by
  constructor
  · intro less
    have scaled := mul_lt_mul_of_pos_right_direct less hc
    rwa [div_mul_cancel_of_ne a c hc.ne'] at scaled
  · intro less
    apply lt_of_mul_lt_mul_right_direct (c := c) _ hc
    rwa [div_mul_cancel_of_ne a c hc.ne']

/-- Constructive strict comparison into a positive-denominator quotient. -/
theorem lt_div_iff_pos {a b c : Rational} (hc : 0 < c) :
    a < b / c ↔ a * c < b := by
  constructor
  · intro less
    have scaled := mul_lt_mul_of_pos_right_direct less hc
    rwa [div_mul_cancel_of_ne b c hc.ne'] at scaled
  · intro less
    apply lt_of_mul_lt_mul_right_direct (c := c) _ hc
    rwa [div_mul_cancel_of_ne b c hc.ne']

private theorem floorFraction_respects {a b : Fraction}
    (h : Equivalent a b) : a.num / a.den = b.num / b.den := by
  apply Int.le_antisymm
  · apply (Int.le_ediv_iff_mul_le b.den_pos).mpr
    apply int_le_of_mul_le_mul_right a.den_pos
    have hq := Int.ediv_mul_le a.num (Int.ne_of_gt a.den_pos)
    have hscaled :=
      Int.mul_le_mul_of_nonneg_right hq (Int.le_of_lt b.den_pos)
    calc
      (a.num / a.den * b.den) * a.den =
          (a.num / a.den * a.den) * b.den := by ring1
      _ ≤ a.num * b.den := hscaled
      _ = b.num * a.den := h
  · apply (Int.le_ediv_iff_mul_le a.den_pos).mpr
    apply int_le_of_mul_le_mul_right b.den_pos
    have hq := Int.ediv_mul_le b.num (Int.ne_of_gt b.den_pos)
    have hscaled :=
      Int.mul_le_mul_of_nonneg_right hq (Int.le_of_lt a.den_pos)
    calc
      (b.num / b.den * a.den) * b.den =
          (b.num / b.den * b.den) * a.den := by ring1
      _ ≤ b.num * a.den := hscaled
      _ = a.num * b.den := h.symm

/-- The integer floor, computed by Euclidean division on any representative. -/
def floor (a : Rational) : Int :=
  Quotient.liftOn a (fun x => x.num / x.den)
    (fun _ _ h => floorFraction_respects h)

/-- An integer lies below a fraction exactly when it lies below its floor. -/
theorem intCast_le_iff_floor (z : Int) (a : Rational) :
    (z : Rational) ≤ a ↔ z ≤ floor a := by
  refine Quotient.inductionOn a ?_
  intro x
  rw [intCast_eq_fraction]
  change z * x.den ≤ x.num * 1 ↔ z ≤ x.num / x.den
  rw [Int.mul_one]
  exact (Int.le_ediv_iff_mul_le x.den_pos).symm

/-- The integer ceiling, defined constructively from the floor. -/
def ceil (a : Rational) : Int := -floor (-a)

/-- The ceiling is the least integer lying above a fraction. -/
theorem ceil_le_intCast_iff (a : Rational) (z : Int) :
    ceil a ≤ z ↔ a ≤ (z : Rational) := by
  rw [ceil]
  constructor
  · intro h
    have hneg : (-z : Int) ≤ floor (-a) := by
      simpa only [Int.neg_neg] using Int.neg_le_neg_iff.mpr h
    have hcast := (intCast_le_iff_floor (-z) (-a)).mpr hneg
    rw [Int.cast_neg] at hcast
    exact neg_le_neg_iff.mp hcast
  · intro h
    have hneg : ((-z : Int) : Rational) ≤ -a := by
      rw [Int.cast_neg]
      exact neg_le_neg_iff.mpr h
    have hfloor := (intCast_le_iff_floor (-z) (-a)).mp hneg
    simpa only [Int.neg_neg] using Int.neg_le_neg_iff.mpr hfloor

/-- Integer-cast order reflection by direct denominator-one comparison. -/
theorem intCast_le_intCast_iff_direct (m n : Int) :
    (m : Rational) ≤ (n : Rational) ↔ m ≤ n := by
  rw [intCast_eq_fraction, intCast_eq_fraction]
  change m * 1 ≤ n * 1 ↔ m ≤ n
  simp only [Int.mul_one]

/-- Every constructive fraction lies below its computed integer ceiling. -/
theorem le_intCast_ceil (a : Rational) : a ≤ (ceil a : Rational) :=
  (ceil_le_intCast_iff a (ceil a)).mp le_rfl

/-- Natural ceiling of a nonnegative constructive fraction.  Negative inputs
are sent to zero; callers use the nonnegative bound below. -/
def ceilNat (a : Rational) : Nat := (ceil a).toNat

theorem le_natCast_ceilNat_of_nonneg {a : Rational} (nonnegative : 0 ≤ a) :
    a ≤ (ceilNat a : Nat) := by
  have castNonnegative : (0 : Rational) ≤ (ceil a : Rational) :=
    nonnegative.trans (le_intCast_ceil a)
  have ceilingNonnegative : (0 : Int) ≤ ceil a :=
    (intCast_le_intCast_iff_direct 0 (ceil a)).mp (by
      simpa only [Int.cast_zero] using castNonnegative)
  have ceilingCast : ((ceil a).toNat : Int) = ceil a :=
    Int.toNat_of_nonneg ceilingNonnegative
  calc
    a ≤ (ceil a : Rational) := le_intCast_ceil a
    _ = (((ceil a).toNat : Int) : Rational) :=
      (congrArg (fun z : Int => (z : Rational)) ceilingCast).symm
    _ = (((ceil a).toNat : Nat) : Rational) := by
      rw [Int.cast_natCast]
    _ = (ceilNat a : Nat) := rfl

theorem mul_zero_direct (a : Rational) : a * 0 = 0 := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (show Equivalent
      (mulFraction x zeroFraction) zeroFraction by
    dsimp [Equivalent, mulFraction, zeroFraction]
    ring1)

theorem zero_mul_direct (a : Rational) : 0 * a = 0 := by
  rw [mul_comm, mul_zero_direct]

theorem div_zero_direct (a : Rational) : a / 0 = 0 := by
  change a * (0 : Rational)⁻¹ = 0
  rw [inv_zero, mul_zero_direct]

theorem zero_div_direct (a : Rational) : 0 / a = 0 := by
  change 0 * a⁻¹ = 0
  exact zero_mul_direct _

theorem mul_one_direct (a : Rational) : a * 1 = a := by
  rw [mul_comm]
  exact one_mul a

theorem inv_mul_cancel (a : Rational) (ha : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel a ha

/-- The inverse of a positive constructive fraction is positive.  This direct
proof avoids the generic ordered-field lemma, whose instance route introduces
`Classical.choice`. -/
theorem inv_pos_direct {a : Rational} (ha : 0 < a) : 0 < a⁻¹ := by
  have inverseNonzero : a⁻¹ ≠ 0 := by
    intro inverseZero
    have product := mul_inv_cancel a ha.ne'
    rw [inverseZero, mul_zero_direct] at product
    exact zero_ne_one product
  rcases lt_or_gt_of_ne inverseNonzero with inverseNegative | inversePositive
  · have productNegative := mul_lt_mul_of_pos_left inverseNegative ha
    rw [mul_inv_cancel a ha.ne', mul_zero_direct] at productNegative
    exact ((by decide : ¬ ((1 : Rational) < 0)) productNegative).elim
  · exact inversePositive

/-- Direct order reversal for positive inverses, avoiding the generic
conditionally-complete ordered-field route. -/
theorem inv_le_inv_of_pos_direct {a b : Rational}
    (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := ha.trans_le hab
  apply le_of_mul_le_mul_right_direct (c := a) ?_ ha
  calc
    b⁻¹ * a ≤ b⁻¹ * b :=
      mul_le_mul_of_nonneg_left_direct hab (inv_pos_direct hb).le
    _ = 1 := inv_mul_cancel b hb.ne'
    _ = a⁻¹ * a := (inv_mul_cancel a ha.ne').symm

/-- Positive division proved from the explicit inverse and strict
multiplication monotonicity. -/
theorem div_pos_direct {a b : Rational} (ha : 0 < a) (hb : 0 < b) :
    0 < a / b := by
  change 0 < a * b⁻¹
  have inversePositive := inv_pos_direct hb
  have productPositive := mul_lt_mul_of_pos_right ha inversePositive
  have zeroProduct : (0 : Rational) * b⁻¹ = 0 := by
    rw [mul_comm, mul_zero_direct]
  rwa [zeroProduct] at productPositive

/-- Weak nonnegativity of explicit fraction division.  The generic ordered
field theorem reaches a choice-bearing compatibility instance for this
quotient type, so the two zero cases are handled directly. -/
theorem div_nonneg_direct {a b : Rational} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a / b := by
  by_cases aZero : a = 0
  · rw [aZero, zero_div_direct]
  · by_cases bZero : b = 0
    · rw [bZero, div_zero_direct]
    · exact (div_pos_direct
        (lt_of_le_of_ne ha (Ne.symm aZero))
        (lt_of_le_of_ne hb (Ne.symm bZero))).le

/-- A nonnegative numerator decreases when its positive denominator grows. -/
theorem div_le_div_of_nonneg_left_direct {a b c : Rational}
    (numeratorNonnegative : 0 ≤ a) (denominatorPositive : 0 < b)
    (denominatorOrder : b ≤ c) : a / c ≤ a / b := by
  change a * c⁻¹ ≤ a * b⁻¹
  exact mul_le_mul_of_nonneg_left_direct
    (inv_le_inv_of_pos_direct denominatorPositive denominatorOrder)
    numeratorNonnegative

theorem mul_right_cancel_of_ne {a b c : Rational} (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have hinverse := congrArg (fun value => value * c⁻¹) h
  simpa only [mul_assoc, mul_inv_cancel c hc, mul_one_direct] using hinverse

theorem mul_ne_zero_direct {a b : Rational} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro hproduct
  apply ha
  apply mul_right_cancel_of_ne hb
  calc
    a * b = 0 := hproduct
    _ = 0 * b := by rw [mul_comm, mul_zero_direct]

theorem inv_ne_zero_direct {a : Rational} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hinverse
  have hproduct := mul_inv_cancel a ha
  rw [hinverse, mul_zero_direct] at hproduct
  exact zero_ne_one hproduct

/-- Inversion distributes over a product, proved by explicit cancellation in
the two nonzero cases and by computation in the zero cases. -/
theorem inv_mul_direct (a b : Rational) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  by_cases aZero : a = 0
  · subst a
    rw [zero_mul_direct, inv_zero, zero_mul_direct]
  · by_cases bZero : b = 0
    · subst b
      rw [mul_zero_direct, inv_zero, mul_zero_direct]
    · have productNonzero := mul_ne_zero_direct aZero bZero
      apply mul_right_cancel_of_ne productNonzero
      calc
        (a * b)⁻¹ * (a * b) = 1 := inv_mul_cancel _ productNonzero
        _ = (a⁻¹ * a) * (b⁻¹ * b) := by
          rw [inv_mul_cancel a aZero, inv_mul_cancel b bZero]
          exact (mul_one_direct 1).symm
        _ = (a⁻¹ * b⁻¹) * (a * b) := mul_pair_swap _ _ _ _

/-- Inversion commutes with a displayed finite natural power.  This direct
recursion avoids routing the proof through a generic field hierarchy. -/
theorem inv_pow_direct (a : Rational) : ∀ exponent : Nat,
    (a ^ exponent)⁻¹ = a⁻¹ ^ exponent
  | 0 => by
      change (1 : Rational)⁻¹ = 1
      decide
  | exponent + 1 => by
      rw [pow_succ, inv_mul_direct, inv_pow_direct a exponent, pow_succ]

/-- Multiplication of two displayed quotients without using a generic field
normalization theorem. -/
theorem div_mul_div_direct (a b c d : Rational) :
    (a / b) * (c / d) = (a * c) / (b * d) := by
  change (a * b⁻¹) * (c * d⁻¹) = (a * c) * (b * d)⁻¹
  rw [inv_mul_direct]
  exact mul_pair_swap _ _ _ _

/-- Subtract two displayed quotients over explicit nonzero denominators. -/
theorem div_sub_div_direct (a b c d : Rational) (bNonzero : b ≠ 0)
    (dNonzero : d ≠ 0) :
    a / b - c / d = (a * d - c * b) / (b * d) := by
  change a * b⁻¹ - c * d⁻¹ = (a * d - c * b) * (b * d)⁻¹
  rw [inv_mul_direct]
  have bCancel : b * b⁻¹ = 1 := mul_inv_cancel b bNonzero
  have dCancel : d * d⁻¹ = 1 := mul_inv_cancel d dNonzero
  have firstReorder :
      (a * d) * (b⁻¹ * d⁻¹) = (a * b⁻¹) * (d * d⁻¹) :=
    mul_pair_swap a d b⁻¹ d⁻¹
  have secondReorder :
      (c * b) * (b⁻¹ * d⁻¹) = (c * d⁻¹) * (b * b⁻¹) := by
    calc
      (c * b) * (b⁻¹ * d⁻¹) = (c * b) * (d⁻¹ * b⁻¹) := by
        rw [mul_comm b⁻¹ d⁻¹]
      _ = (c * d⁻¹) * (b * b⁻¹) := mul_pair_swap c b d⁻¹ b⁻¹
  symm
  calc
    (a * d - c * b) * (b⁻¹ * d⁻¹) =
        (a * d) * (b⁻¹ * d⁻¹) - (c * b) * (b⁻¹ * d⁻¹) :=
      sub_mul _ _ _
    _ = (a * b⁻¹) * (d * d⁻¹) - (c * d⁻¹) * (b * b⁻¹) := by
      rw [firstReorder, secondReorder]
    _ = a * b⁻¹ - c * d⁻¹ := by
      rw [bCancel, dCancel,
        RFAP.ConstructiveFraction.mul_one_direct,
        RFAP.ConstructiveFraction.mul_one_direct]

/-- Cancel the same nonzero factor from numerator and denominator. -/
theorem mul_div_mul_left_direct (factor numerator denominator : Rational)
    (factorNonzero : factor ≠ 0) :
    (factor * numerator) / (factor * denominator) = numerator / denominator := by
  change (factor * numerator) * (factor * denominator)⁻¹ =
    numerator * denominator⁻¹
  rw [inv_mul_direct]
  calc
    (factor * numerator) * (factor⁻¹ * denominator⁻¹) =
        (factor * factor⁻¹) * (numerator * denominator⁻¹) :=
      mul_pair_swap _ _ _ _
    _ = 1 * (numerator * denominator⁻¹) := by
      rw [mul_inv_cancel factor factorNonzero]
    _ = numerator * denominator⁻¹ := one_mul _

theorem inv_neg_direct (a : Rational) : inv (-a) = -inv a := by
  by_cases ha : a = 0
  · subst a
    have hnegZero : -(0 : Rational) = 0 := by ring1
    rw [hnegZero]
    change (0 : Rational)⁻¹ = -((0 : Rational)⁻¹)
    rw [inv_zero, hnegZero]
  · have hneg : -a ≠ 0 := neg_ne_zero.mpr ha
    apply mul_right_cancel_of_ne hneg
    calc
      inv (-a) * (-a) = 1 := inv_mul_cancel (-a) hneg
      _ = inv a * a := (inv_mul_cancel a ha).symm
      _ = (-inv a) * (-a) := by
        let inverse := inv a
        change inverse * a = (-inverse) * (-a)
        ring1

/-- Direct operation path used by the finite dense-polynomial algorithms. -/
instance instExplicitField : RFAP.ExplicitField Rational where
  toCommRing := Field.toCommRing
  toInv := inferInstance
  toDiv := ⟨fun a b => a * b⁻¹⟩
  div_eq_mul_inv := by intros; rfl
  mul_inv_cancel := mul_inv_cancel
  mul_ne_zero := mul_ne_zero_direct
  inv_ne_zero := inv_ne_zero_direct
  inv_neg := by
    intro a
    change inv (-a) = -inv a
    exact inv_neg_direct a

theorem div_eq_mul_inv_direct (a b : Rational) : a / b = a * b⁻¹ := rfl

/-! ## Canonical finite representatives -/

/-- A gcd-reduced numerator and strictly positive natural denominator.  This
is finite data, not a selected representative obtained from the quotient. -/
structure ReducedFraction where
  num : Int
  den : Nat
  den_pos : 0 < den
  reduced : num.natAbs.Coprime den

namespace ReducedFraction

/-- Direct absolute-value accounting for exact integer division.  The library
lemma with the analogous statement passes through a choice-bearing generic
normalization route, so the finite factorization is proved here explicitly. -/
theorem natAbs_ediv_of_dvd_direct {num : Int} {divisor : Nat}
    (positive : 0 < divisor) (dvd : divisor ∣ num.natAbs) :
    (num / (divisor : Int)).natAbs = num.natAbs / divisor := by
  have integerDvd : (divisor : Int) ∣ num := by
    rw [← Int.dvd_natAbs, Int.ofNat_dvd]
    exact dvd
  rcases integerDvd with ⟨factor, factorization⟩
  have divisorCastNonzero : (divisor : Int) ≠ 0 := by
    intro zero
    have divisorZero : divisor = 0 := Int.ofNat.inj zero
    exact (Nat.ne_of_gt positive) divisorZero
  rw [factorization, Int.mul_ediv_cancel_left factor divisorCastNonzero,
    Int.natAbs_mul, Int.natAbs_natCast,
    Nat.mul_div_cancel_left _ positive]

/-- Positivity survives the explicit `Int.toNat` computation without using
the generic order bridge that imports choice into its proof closure. -/
theorem toNat_pos_direct {value : Int} (positive : 0 < value) :
    0 < value.toNat := by
  cases value with
  | ofNat value =>
      change 0 < value
      change Int.ofNat 0 < Int.ofNat value at positive
      exact Int.ofNat_lt.mp positive
  | negSucc value => exact (Int.not_lt_of_ge (by omega) positive).elim

/-- Executable gcd normalization of a displayed positive-denominator
fraction. -/
def normalize (fraction : Fraction) : ReducedFraction := by
  let denominator := fraction.den.toNat
  have denominatorPositive : 0 < denominator :=
    toNat_pos_direct fraction.den_pos
  let divisor := fraction.num.natAbs.gcd denominator
  have divisorPositive : 0 < divisor :=
    Nat.gcd_pos_of_pos_right _ denominatorPositive
  have divisorNumerator : divisor ∣ fraction.num.natAbs :=
    Nat.gcd_dvd_left _ _
  refine
    ⟨fraction.num / (divisor : Int), denominator / divisor,
      Nat.div_gcd_pos_of_pos_right fraction.num.natAbs denominatorPositive,
      ?_⟩
  rw [natAbs_ediv_of_dvd_direct divisorPositive divisorNumerator]
  exact Nat.coprime_div_gcd_div_gcd divisorPositive

/-- Re-embed reduced data as an ordinary positive-denominator record. -/
def toFraction (fraction : ReducedFraction) : Fraction :=
  ⟨fraction.num, (fraction.den : Int), Int.natCast_pos.mpr fraction.den_pos⟩

@[ext] theorem ext {left right : ReducedFraction}
    (numerator : left.num = right.num)
    (denominator : left.den = right.den) : left = right := by
  cases left
  cases right
  simp_all

/-- Coprime positive-denominator records with the same cross-product are
definitionally the same finite record. -/
theorem eq_of_cross {left right : ReducedFraction}
    (cross : left.num * (right.den : Int) =
      right.num * (left.den : Int)) : left = right := by
  have absoluteCross : left.num.natAbs * right.den =
      right.num.natAbs * left.den := by
    have absolute := congrArg Int.natAbs cross
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using absolute
  have leftDvdRight : left.num.natAbs ∣ right.num.natAbs :=
    left.reduced.dvd_of_dvd_mul_right
      ⟨right.den, absoluteCross.symm⟩
  have rightDvdLeft : right.num.natAbs ∣ left.num.natAbs :=
    right.reduced.dvd_of_dvd_mul_right
      ⟨left.den, absoluteCross⟩
  have absoluteEqual : left.num.natAbs = right.num.natAbs :=
    Nat.dvd_antisymm leftDvdRight rightDvdLeft
  have denominatorEqual : left.den = right.den := by
    by_cases numeratorZero : left.num.natAbs = 0
    · have leftOne : left.den = 1 :=
        left.reduced.symm.eq_one_of_dvd (by
          rw [numeratorZero]
          exact Nat.dvd_zero left.den)
      have rightZero : right.num.natAbs = 0 :=
        absoluteEqual.symm.trans numeratorZero
      have rightOne : right.den = 1 :=
        right.reduced.symm.eq_one_of_dvd (by
          rw [rightZero]
          exact Nat.dvd_zero right.den)
      exact leftOne.trans rightOne.symm
    · apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero numeratorZero)
      simpa only [absoluteEqual] using absoluteCross.symm
  have numeratorEqual : left.num = right.num := by
    have denominatorCastNonzero : (left.den : Int) ≠ 0 := by
      intro zero
      have denominatorZero : left.den = 0 := Int.ofNat.inj zero
      exact (Nat.ne_of_gt left.den_pos) denominatorZero
    apply Int.eq_of_mul_eq_mul_right denominatorCastNonzero
    simpa only [denominatorEqual] using cross
  exact ReducedFraction.ext numeratorEqual denominatorEqual

/-- Gcd normalization preserves the represented fraction by an explicit
common-factor calculation. -/
theorem normalize_equivalent (fraction : Fraction) :
    Equivalent (normalize fraction).toFraction fraction := by
  let denominator := fraction.den.toNat
  have denominatorCast : (denominator : Int) = fraction.den := by
    simp only [denominator, Int.toNat_of_nonneg fraction.den_pos.le]
  let divisor := fraction.num.natAbs.gcd denominator
  have divisorNumeratorNat : divisor ∣ fraction.num.natAbs :=
    Nat.gcd_dvd_left _ _
  have divisorNumerator : (divisor : Int) ∣ fraction.num := by
    rw [← Int.dvd_natAbs, Int.ofNat_dvd]
    exact divisorNumeratorNat
  have divisorDenominator : divisor ∣ denominator :=
    Nat.gcd_dvd_right _ _
  have numeratorFactor :
      fraction.num / (divisor : Int) * (divisor : Int) = fraction.num :=
    Int.ediv_mul_cancel divisorNumerator
  have denominatorFactorNat : denominator / divisor * divisor = denominator :=
    Nat.div_mul_cancel divisorDenominator
  have denominatorFactor :
      ((denominator / divisor : Nat) : Int) * (divisor : Int) =
        fraction.den := by
    rw [← Int.natCast_mul, denominatorFactorNat, denominatorCast]
  change
    fraction.num / (divisor : Int) * fraction.den =
      fraction.num * ((denominator / divisor : Nat) : Int)
  calc
    fraction.num / (divisor : Int) * fraction.den =
        fraction.num / (divisor : Int) *
          (((denominator / divisor : Nat) : Int) * (divisor : Int)) := by
      rw [denominatorFactor]
    _ = (fraction.num / (divisor : Int) * (divisor : Int)) *
        ((denominator / divisor : Nat) : Int) := by ring1
    _ = fraction.num * ((denominator / divisor : Nat) : Int) := by
      rw [numeratorFactor]

theorem normalize_respects {left right : Fraction}
    (equivalent : Equivalent left right) :
    normalize left = normalize right := by
  apply eq_of_cross
  have first : Equivalent (normalize left).toFraction right :=
    equivalent_trans (normalize_equivalent left) equivalent
  exact equivalent_trans first (normalize_equivalent right).symm

end ReducedFraction

/-- The computable canonical representative of a constructive rational.
Unlike `Quot.out`, this descends an explicit gcd normalization through the
quotient and therefore performs no representative selection. -/
def representative : Rational → ReducedFraction :=
  Quotient.lift ReducedFraction.normalize
    (fun _ _ equivalent => ReducedFraction.normalize_respects equivalent)

/-- The canonical finite representative denotes the original quotient. -/
theorem representative_spec (value : Rational) :
    ofFraction (representative value).toFraction = value := by
  refine Quotient.inductionOn value ?_
  intro fraction
  apply Quotient.sound
  exact ReducedFraction.normalize_equivalent fraction

/-- Re-embedding already reduced finite data and computing its representative
returns that same data. -/
theorem representative_of_reduced (reduced : ReducedFraction) :
    representative (ofFraction reduced.toFraction) = reduced := by
  apply ReducedFraction.eq_of_cross
  have equality := representative_spec (ofFraction reduced.toFraction)
  have equivalent : Equivalent
      (representative (ofFraction reduced.toFraction)).toFraction
      reduced.toFraction := Quotient.exact equality
  simpa only [Equivalent, ReducedFraction.toFraction] using equivalent

/-- Rebuild a rational from its computable gcd-reduced representative.  This
is propositionally the same rational, but subsequent executable arithmetic
starts from the reduced finite record instead of an arbitrarily swollen
quotient representative. -/
def canonical (value : Rational) : Rational :=
  ofFraction (representative value).toFraction

theorem canonical_eq (value : Rational) : canonical value = value :=
  representative_spec value

/-- Multiplying an explicit positive-denominator record by its displayed
denominator recovers its numerator. -/
theorem ofFraction_mul_den (fraction : Fraction) :
    ofFraction fraction * (fraction.den : Rational) =
      (fraction.num : Rational) := by
  rw [intCast_eq_fraction, intCast_eq_fraction]
  change Quotient.mk' (mulFraction fraction
      ⟨fraction.den, 1, by decide⟩) =
    Quotient.mk' ⟨fraction.num, 1, by decide⟩
  exact Quotient.sound (show Equivalent
      (mulFraction fraction ⟨fraction.den, 1, by decide⟩)
      ⟨fraction.num, 1, by decide⟩ by
    dsimp only [Equivalent, mulFraction]
    ring1)

/-- Multiplication by the positive denominator of the computable canonical
representative recovers its displayed integer numerator.  This is the
finite denominator-clearance identity used by bounded rational-root
searches; it does not select a representative from the quotient. -/
theorem representative_mul_den (value : Rational) :
    value * ((representative value).den : Rational) =
      ((representative value).num : Rational) := by
  let reduced := representative value
  calc
    value * (reduced.den : Rational) =
        ofFraction reduced.toFraction * (reduced.den : Rational) := by
      rw [representative_spec value]
    _ = (reduced.num : Rational) := by
      simpa only [reduced, ReducedFraction.toFraction,
        Int.cast_natCast] using ofFraction_mul_den reduced.toFraction

/-! ## A finite nonsquare certificate -/

/-- Divisibility of a displayed natural square by three forces divisibility
of its base.  Inspecting the three possible remainders keeps this argument
finite and avoids importing a general prime-factorization theory. -/
private theorem three_dvd_of_three_dvd_square {value : Nat}
    (divides : 3 ∣ value * value) : 3 ∣ value := by
  rw [Nat.dvd_iff_mod_eq_zero] at divides ⊢
  have remainderLt : value % 3 < 3 := Nat.mod_lt value (by decide)
  have squareRemainder :
      value * value % 3 = (value % 3) * (value % 3) % 3 := by
    rw [Nat.mul_mod]
  rw [squareRemainder] at divides
  have cases : value % 3 = 0 ∨ value % 3 = 1 ∨ value % 3 = 2 := by
    omega
  rcases cases with zero | one | two <;> simp_all

/-- No constructive rational has square three.  The computable canonical
representative turns a putative equality into
`num² = 3 * den²`; the remainder-three calculation makes both components
divisible by three, contradicting the stored gcd certificate. -/
theorem square_ne_three (value : Rational) : value ^ 2 ≠ 3 := by
  intro square
  let reduced := representative value
  have rebuilt : ofFraction reduced.toFraction = value :=
    representative_spec value
  have reducedSquare : ofFraction reduced.toFraction ^ 2 = (3 : Rational) := by
    rw [rebuilt]
    exact square
  rw [pow_two] at reducedSquare
  change ofFraction reduced.toFraction * ofFraction reduced.toFraction =
    ((3 : Nat) : Rational) at reducedSquare
  rw [natCast_eq_fraction 3] at reducedSquare
  have cross : Equivalent
      (mulFraction reduced.toFraction reduced.toFraction)
      ⟨3, 1, by decide⟩ := Quotient.exact reducedSquare
  have integerSquare :
      reduced.num * reduced.num =
        (3 : Int) * ((reduced.den : Int) * (reduced.den : Int)) := by
    simpa only [Equivalent, mulFraction, ReducedFraction.toFraction,
      Int.mul_one] using cross
  have absoluteSquare := congrArg Int.natAbs integerSquare
  have naturalSquare :
      reduced.num.natAbs * reduced.num.natAbs =
        3 * (reduced.den * reduced.den) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast,
      show Int.natAbs 3 = 3 from rfl] using absoluteSquare
  have threeDvdNumerator : 3 ∣ reduced.num.natAbs :=
    three_dvd_of_three_dvd_square ⟨reduced.den * reduced.den,
      naturalSquare⟩
  rcases threeDvdNumerator with ⟨numeratorFactor, numeratorEquation⟩
  have denominatorSquare :
      reduced.den * reduced.den = 3 * (numeratorFactor * numeratorFactor) := by
    have scaled :
        3 * (3 * (numeratorFactor * numeratorFactor)) =
          3 * (reduced.den * reduced.den) := by
      calc
        3 * (3 * (numeratorFactor * numeratorFactor)) =
            (3 * numeratorFactor) * (3 * numeratorFactor) := by ring1
        _ = 3 * (reduced.den * reduced.den) := by
          rw [← numeratorEquation]
          exact naturalSquare
    exact (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) scaled).symm
  have threeDvdDenominator : 3 ∣ reduced.den :=
    three_dvd_of_three_dvd_square
      ⟨numeratorFactor * numeratorFactor, denominatorSquare⟩
  have threeCoprimeDenominator : Nat.Coprime 3 reduced.den :=
    reduced.reduced.coprime_dvd_left
      ⟨numeratorFactor, numeratorEquation⟩
  have absurd : 3 = 1 :=
    threeCoprimeDenominator.eq_one_of_dvd threeDvdDenominator
  omega

end RFAP.ConstructiveFraction
