import CCL.Encoding.Normalization
import CCL.Geometry.Projective
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-dimensional baseline algorithms

Executable, structurally verified versions of Section 4.  Both encoders recurse
on the exact natural measure displayed in the paper; Lean checks the strict
decrease at the recursive call.
-/

namespace CCL

namespace BaselineAlgorithms

/-- Nonnegative Euclidean remainder, converted to a natural number. -/
def remNat (p : ℤ) (q : ℕ) : ℕ := (p % (q : ℤ)).toNat

theorem remNat_lt (p : ℤ) {q : ℕ} (hq : 0 < q) : remNat p q < q := by
  have hqInt : (0 : ℤ) < q := by exact_mod_cast hq
  have hr₀ := Int.emod_nonneg p (Int.ne_of_gt hqInt)
  have hr₁ := Int.emod_lt_of_pos p hqInt
  rw [remNat, Int.toNat_lt (by omega)]
  exact_mod_cast hr₁

theorem remNat_pos (p : ℤ) {q : ℕ} (hq : 0 < q)
    (hr : p % (q : ℤ) ≠ 0) : 0 < remNat p q := by
  have hqInt : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hr₀ := Int.emod_nonneg p hqInt
  rw [remNat, ← Int.pos_iff_toNat_pos]
  omega

/-- The standard rational continued-fraction encoder (Algorithm 4.1). -/
def cfEncode (p : ℤ) (q : ℕ) (hq : 0 < q) : List ℤ :=
  let a := p / (q : ℤ)
  let r := p % (q : ℤ)
  if hr : r = 0 then [a]
  else a :: cfEncode (q : ℤ) (remNat p q) (remNat_pos p hq hr)
termination_by q
decreasing_by exact remNat_lt p hq

/-- Finite decoder semantics for a list of standard partial quotients. -/
def cfDecode : List ℤ → Proj ℚ
  | [] => Proj.omega
  | a :: digits => Mat2.act (Mat2.cf (a : ℚ) 1) (cfDecode digits)

@[simp] theorem cfDecode_singleton (a : ℤ) :
    cfDecode [a] = ⟨(a : ℚ), 1⟩ := by
  ext <;> simp [cfDecode, Mat2.act, Mat2.cf, Proj.omega]

/-- Proposition 4.1: the executable encoder reconstructs its rational input. -/
theorem cfEncode_reconstruct (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (cfDecode (cfEncode p q hq)).Equivalent ⟨(p : ℚ), (q : ℚ)⟩ := by
  induction q using Nat.strong_induction_on generalizing p with
  | h q ih =>
      rw [cfEncode]
      split_ifs with hr
      · rw [cfDecode_singleton]
        dsimp [Proj.Equivalent]
        have hdiv := Int.ediv_mul_cancel_of_emod_eq_zero hr
        have hdivQ : ((p / (q : ℤ) : ℤ) : ℚ) * (q : ℚ) = (p : ℚ) := by
          exact_mod_cast hdiv
        simpa using hdivQ
      · let r := remNat p q
        have hrPos : 0 < r := remNat_pos p hq hr
        have hrLt : r < q := remNat_lt p hq
        have htail := ih r hrLt (q : ℤ) hrPos
        have hact := Mat2.act_respects_equivalent
          (Mat2.cf ((p / (q : ℤ) : ℤ) : ℚ) 1) htail
        have hremNonneg : 0 ≤ p % (q : ℤ) :=
          Int.emod_nonneg p (by exact_mod_cast (Nat.ne_of_gt hq))
        have hrCast : (r : ℤ) = p % (q : ℤ) := by
          simp [r, remNat, Int.toNat_of_nonneg hremNonneg]
        have hstep :
            (Mat2.act (Mat2.cf ((p / (q : ℤ) : ℤ) : ℚ) 1)
              (⟨(q : ℚ), (r : ℚ)⟩ : Proj ℚ)).Equivalent
              ⟨(p : ℚ), (q : ℚ)⟩ := by
          dsimp [Proj.Equivalent, Mat2.act, Mat2.cf]
          have hdecomp := Int.ediv_mul_add_emod p (q : ℤ)
          norm_num
          left
          exact_mod_cast (show p / (q : ℤ) * (q : ℤ) + (r : ℤ) = p by
            rw [hrCast]
            exact hdecomp)
        exact hact.trans_of_mid_q_domain hstep (by
          dsimp [Mat2.act, Mat2.cf]
          positivity)

/-- Certified scale consolidation for the real continued logarithm. -/
structure CLScale (p q : ℕ) where
  exponent : ℕ
  lower : 2 ^ exponent * q ≤ p
  upper : p < 2 ^ (exponent + 1) * q

/-- Bounded construction of the unique scale putting `p/q` in `[1,2)`. -/
def clScale (p q : ℕ) (hq : 0 < q) (hpq : q ≤ p) : CLScale p q := by
  by_cases hhigh : 2 * q ≤ p
  · let r := BinaryNormalization.high p q hq hhigh
    exact ⟨r.exponent, r.lower, r.upper⟩
  · exact ⟨0, by simpa using hpq, by simpa using Nat.lt_of_not_ge hhigh⟩

/-- The real continued-logarithm encoder from Proposition 4.2. -/
def clEncode (p q : ℕ) (hq : 0 < q) (hpq : q ≤ p) : List Bool :=
  if hpqEq : p = q then []
  else
    let scale := clScale p q hq hpq
    let n := 2 ^ scale.exponent * q
    if hterminal : n = p then List.replicate scale.exponent true
    else
      List.replicate scale.exponent true ++ false ::
        clEncode n (p - n)
          (by
            have hnle : n ≤ p := scale.lower
            have hnlt : n < p := lt_of_le_of_ne hnle hterminal
            exact Nat.sub_pos_of_lt hnlt)
          (by
            have hnle : n ≤ p := scale.lower
            have hnlt : n < p := lt_of_le_of_ne hnle hterminal
            have hupper : p < 2 * n := by
              dsimp only [n]
              have hupper₀ := scale.upper
              rw [pow_succ] at hupper₀
              nlinarith
            omega)
termination_by p
decreasing_by
  have hnle : n ≤ p := scale.lower
  exact lt_of_le_of_ne hnle hterminal

/-- Decoder branches for the real continued-logarithm bitstream. -/
def clDecode : List Bool → Proj ℚ
  | [] => ⟨1, 1⟩
  | true :: bits => Mat2.act (Mat2.scale (2 : ℚ)) (clDecode bits)
  | false :: bits => Mat2.act (Mat2.cf (1 : ℚ) 1) (clDecode bits)

@[simp] theorem clDecode_nil : clDecode [] = ⟨1, 1⟩ := rfl

theorem clDecode_replicate_true (k : ℕ) :
    clDecode (List.replicate k true) = ⟨(2 : ℚ) ^ k, 1⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, clDecode, ih, Mat2.act, Mat2.scale]
      ext <;> simp [pow_succ, mul_comm]

theorem clDecode_replicate_true_append (k : ℕ) (bits : List Bool) :
    clDecode (List.replicate k true ++ bits) =
      Mat2.act (Mat2.scale ((2 : ℚ) ^ k)) (clDecode bits) := by
  induction k with
  | zero =>
      ext <;> simp [Mat2.act, Mat2.scale]
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, clDecode, ih]
      apply Proj.ext
      · simp [Mat2.act, Mat2.scale, pow_succ]
        ring
      · simp [Mat2.act, Mat2.scale]

/-- Proposition 4.2: the executable continued-logarithm word reconstructs `p/q`. -/
theorem clEncode_reconstruct (p q : ℕ) (hq : 0 < q) (hpq : q ≤ p) :
    (clDecode (clEncode p q hq hpq)).Equivalent ⟨(p : ℚ), (q : ℚ)⟩ := by
  induction p using Nat.strong_induction_on generalizing q with
  | h p ih =>
      rw [clEncode]
      split_ifs with hpqEq
      · subst p
        dsimp [clDecode, Proj.Equivalent]
        ring
      · let scale := clScale p q hq hpq
        let n := 2 ^ scale.exponent * q
        change
          (clDecode
            (if hterminal : n = p then List.replicate scale.exponent true
            else List.replicate scale.exponent true ++ false ::
              clEncode n (p - n) _ _)).Equivalent
            ⟨(p : ℚ), (q : ℚ)⟩
        split_ifs with hterminal
        · rw [clDecode_replicate_true]
          dsimp [Proj.Equivalent]
          norm_num
          exact_mod_cast hterminal
        · have hnle : n ≤ p := scale.lower
          have hnlt : n < p := lt_of_le_of_ne hnle hterminal
          have hq' : 0 < p - n := Nat.sub_pos_of_lt hnlt
          have hupper₀ := scale.upper
          have hupper : p < 2 * n := by
            dsimp only [n]
            rw [pow_succ] at hupper₀
            nlinarith
          have hpq' : p - n ≤ n := by omega
          have htail := ih n hnlt (p - n) hq' hpq'
          have hfalse := Mat2.act_respects_equivalent (Mat2.cf (1 : ℚ) 1) htail
          have hscaled := Mat2.act_respects_equivalent
            (Mat2.scale ((2 : ℚ) ^ scale.exponent)) hfalse
          rw [clDecode_replicate_true_append]
          have hstep :
              (Mat2.act (Mat2.scale ((2 : ℚ) ^ scale.exponent))
                (Mat2.act (Mat2.cf (1 : ℚ) 1)
                  (⟨(n : ℚ), ((p - n : ℕ) : ℚ)⟩ : Proj ℚ))).Equivalent
                ⟨(p : ℚ), (q : ℚ)⟩ := by
            dsimp [Proj.Equivalent, Mat2.act, Mat2.scale, Mat2.cf]
            norm_num
            rw [Nat.cast_sub hnle]
            dsimp only [n]
            rw [Nat.cast_mul, Nat.cast_pow]
            ring
          apply hscaled.trans_of_mid_q_domain hstep
          dsimp [Mat2.act, Mat2.scale, Mat2.cf]
          norm_num
          exact_mod_cast (Nat.ne_of_gt (show 0 < n by positivity))

end BaselineAlgorithms

end CCL
