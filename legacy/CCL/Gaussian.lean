import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gaussian rationals

Exact coordinate model for the paper's `ℚ(i)`.  No real or complex completion
is involved.  The operations are deliberately transparent so all identities
reduce to rational polynomial arithmetic.
-/

namespace CCL

/-- A Gaussian rational `x + y i`, represented by its two rational coordinates. -/
@[ext]
structure GaussianRat where
  re : ℚ
  im : ℚ
deriving DecidableEq, Repr

namespace GaussianRat

instance : Zero GaussianRat := ⟨⟨0, 0⟩⟩
instance : One GaussianRat := ⟨⟨1, 0⟩⟩
instance : Add GaussianRat := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Sub GaussianRat := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Neg GaussianRat := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Mul GaussianRat :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem zero_re : (0 : GaussianRat).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussianRat).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussianRat).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussianRat).im = 0 := rfl
@[simp] theorem add_re (z w : GaussianRat) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : GaussianRat) : (z + w).im = z.im + w.im := rfl
@[simp] theorem sub_re (z w : GaussianRat) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : GaussianRat) : (z - w).im = z.im - w.im := rfl
@[simp] theorem neg_re (z : GaussianRat) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : GaussianRat) : (-z).im = -z.im := rfl
@[simp] theorem mul_re (z w : GaussianRat) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : GaussianRat) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl

theorem add_assoc (x y z : GaussianRat) : x + y + z = x + (y + z) := by
  ext <;> simp only [add_re, add_im] <;> ring

theorem add_comm (x y : GaussianRat) : x + y = y + x := by
  ext <;> simp only [add_re, add_im] <;> ring

/-- The transparent coordinate subtraction agrees with additive subtraction
from the field structure.  This bridge lets generic ring identities be used
without hiding the executable coordinate representation. -/
theorem sub_eq_add_neg (z w : GaussianRat) : z - w = z + -w := by
  ext <;> simp only [sub_re, sub_im, add_re, add_im, neg_re, neg_im] <;> ring

@[simp] theorem zero_add (z : GaussianRat) : 0 + z = z := by ext <;> simp
@[simp] theorem add_zero (z : GaussianRat) : z + 0 = z := by ext <;> simp
@[simp] theorem zero_sub (z : GaussianRat) : 0 - z = -z := by ext <;> simp
@[simp] theorem sub_zero (z : GaussianRat) : z - 0 = z := by ext <;> simp
@[simp] theorem sub_self (z : GaussianRat) : z - z = 0 := by ext <;> simp
@[simp] theorem one_mul (z : GaussianRat) : 1 * z = z := by ext <;> simp
@[simp] theorem mul_one (z : GaussianRat) : z * 1 = z := by ext <;> simp
@[simp] theorem zero_mul (z : GaussianRat) : 0 * z = 0 := by ext <;> simp
@[simp] theorem mul_zero (z : GaussianRat) : z * 0 = 0 := by ext <;> simp

theorem mul_comm (z w : GaussianRat) : z * w = w * z := by
  ext <;> simp only [mul_re, mul_im] <;> ring

theorem mul_assoc (x y z : GaussianRat) : x * y * z = x * (y * z) := by
  ext <;> simp only [mul_re, mul_im] <;> ring

theorem left_distrib (x y z : GaussianRat) : x * (y + z) = x * y + x * z := by
  ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring

theorem right_distrib (x y z : GaussianRat) : (x + y) * z = x * z + y * z := by
  ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring

/-- Gaussian conjugation. -/
def conj (z : GaussianRat) : GaussianRat := ⟨z.re, -z.im⟩

/-- The paper's rational Gaussian norm `N(x + yi) = x² + y²`. -/
def normSq (z : GaussianRat) : ℚ := z.re ^ 2 + z.im ^ 2

@[simp] theorem normSq_zero : normSq 0 = 0 := by norm_num [normSq]
@[simp] theorem normSq_one : normSq 1 = 1 := by norm_num [normSq]
@[simp] theorem normSq_neg (z : GaussianRat) : normSq (-z) = normSq z := by
  simp only [normSq, neg_re, neg_im]
  ring

theorem normSq_nonneg (z : GaussianRat) : 0 ≤ normSq z := by
  dsimp [normSq]
  positivity

theorem normSq_eq_zero {z : GaussianRat} : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [normSq] at h
    have hre2 : z.re ^ 2 = 0 := by nlinarith [sq_nonneg z.im]
    have him2 : z.im ^ 2 = 0 := by nlinarith [sq_nonneg z.re]
    have hre : z.re = 0 := sq_eq_zero_iff.mp hre2
    have him : z.im = 0 := sq_eq_zero_iff.mp him2
    ext <;> simp [hre, him]
  · rintro rfl
    exact normSq_zero

theorem normSq_pos {z : GaussianRat} (hz : z ≠ 0) : 0 < normSq z := by
  have hn := normSq_nonneg z
  have hne : normSq z ≠ 0 := fun h => hz (normSq_eq_zero.mp h)
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- The elementary multiplicativity identity used throughout the paper. -/
theorem normSq_mul (z w : GaussianRat) : normSq (z * w) = normSq z * normSq w := by
  simp only [normSq, mul_re, mul_im]
  ring

/-- The finite two-term estimate used by the polynomial and homotopy bounds. -/
theorem normSq_add_le_two (z w : GaussianRat) :
    normSq (z + w) ≤ 2 * (normSq z + normSq w) := by
  simp only [normSq, add_re, add_im]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]

theorem normSq_sub_le_two (z w : GaussianRat) :
    normSq (z - w) ≤ 2 * (normSq z + normSq w) := by
  simp only [normSq, sub_re, sub_im]
  nlinarith [sq_nonneg (z.re + w.re), sq_nonneg (z.im + w.im)]

/-- The reverse finite-sum estimate from Appendix B of the FTA paper. -/
theorem half_normSq_sub_le_normSq_sub (z w : GaussianRat) :
    normSq z / 2 - normSq w ≤ normSq (z - w) := by
  have h := normSq_add_le_two (z - w) w
  have hz : z - w + w = z := by
    ext <;> simp
  rw [hz] at h
  linarith

/-- `γ = 1 + i`. -/
def gamma : GaussianRat := ⟨1, 1⟩

@[simp] theorem normSq_gamma : normSq gamma = 2 := by norm_num [normSq, gamma]

/-- Transparent natural powers, avoiding any appeal to completed complex numbers. -/
def natPow (z : GaussianRat) : ℕ → GaussianRat
  | 0 => 1
  | n + 1 => natPow z n * z

@[simp] theorem natPow_zero (z : GaussianRat) : natPow z 0 = 1 := rfl
@[simp] theorem natPow_succ (z : GaussianRat) (n : ℕ) :
    natPow z (n + 1) = natPow z n * z := rfl

theorem normSq_natPow (z : GaussianRat) (n : ℕ) :
    normSq (natPow z n) = normSq z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [natPow, normSq_mul, ih, pow_succ]

/-- The paper's identity `N(γ^k z) = 2^k N(z)`. -/
theorem normSq_gamma_pow_mul (k : ℕ) (z : GaussianRat) :
    normSq (natPow gamma k * z) = (2 : ℚ) ^ k * normSq z := by
  rw [normSq_mul, normSq_natPow, normSq_gamma]

/-- Exact reciprocal on nonzero Gaussian rationals (and `0` at `0`). -/
def inv (z : GaussianRat) : GaussianRat :=
  ⟨z.re / normSq z, -z.im / normSq z⟩

instance : Inv GaussianRat := ⟨inv⟩

@[simp] theorem inv_eq (z : GaussianRat) : z⁻¹ = inv z := rfl

@[simp] theorem inv_zero : inv 0 = 0 := by
  ext <;> norm_num [inv, normSq]

theorem mul_inv (z : GaussianRat) (hz : z ≠ 0) : z * inv z = 1 := by
  have hn : normSq z ≠ 0 := fun h => hz (normSq_eq_zero.mp h)
  apply GaussianRat.ext
  · simp only [mul_re, inv, one_re]
    field_simp [normSq, hn]
    simp only [normSq]
    ring
  · simp only [mul_im, inv, one_im]
    field_simp [normSq, hn]
    ring

theorem inv_mul (z : GaussianRat) (hz : z ≠ 0) : inv z * z = 1 := by
  rw [mul_comm]
  exact mul_inv z hz

/-- The transparent coordinate operations form a computable field.  This lets
the FTA development use `Polynomial GaussianRat` and its finite Euclidean
algorithms without replacing the coordinate model by an opaque quotient. -/
instance instField : Field GaussianRat :=
  Field.ofMinimalAxioms GaussianRat
    add_assoc
    zero_add
    (fun z => by ext <;> simp)
    mul_assoc
    mul_comm
    one_mul
    (fun z hz => by simpa only [inv_eq] using mul_inv z hz)
    (by simpa only [inv_eq] using inv_zero)
    left_distrib
    ⟨0, 1, by
      intro h
      have hre := congrArg GaussianRat.re h
      norm_num at hre⟩

@[simp] theorem natCast_re (n : ℕ) : ((n : GaussianRat).re) = (n : ℚ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.cast_succ, add_re, ih, one_re]
      norm_num

@[simp] theorem natCast_im (n : ℕ) : ((n : GaussianRat).im) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Nat.cast_succ] using ih

/-- The transparent Gaussian-rational field has characteristic zero. -/
instance instCharZero : CharZero GaussianRat where
  cast_injective := by
    intro m n h
    simpa using congrArg GaussianRat.re h

theorem normSq_pow (z : GaussianRat) (n : ℕ) :
    normSq (z ^ n) = normSq z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, normSq_mul, ih, pow_succ]

theorem mul_right_cancel_of_ne {x y z : GaussianRat} (hz : z ≠ 0)
    (h : x * z = y * z) : x = y := by
  have hi := congrArg (fun w => w * inv z) h
  simpa only [mul_assoc, mul_inv z hz, mul_one] using hi

theorem normSq_inv (z : GaussianRat) (hz : z ≠ 0) :
    normSq (inv z) = 1 / normSq z := by
  have hn : normSq z ≠ 0 := fun h => hz (normSq_eq_zero.mp h)
  have h := congrArg normSq (mul_inv z hz)
  rw [normSq_mul, normSq_one] at h
  field_simp [hn]
  nlinarith

theorem normSq_div (z w : GaussianRat) (hw : w ≠ 0) :
    normSq (z / w) = normSq z / normSq w := by
  rw [div_eq_mul_inv, normSq_mul, inv_eq, normSq_inv w hw]
  ring

end GaussianRat

end CCL
