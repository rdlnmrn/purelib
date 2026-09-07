import CCL.Encoding.CCF.Contraction

/-!
# Executable coordinate-floor CCF encoder

Algorithm 5.1 is grouped into macros of at most three clauses.  A third
nonterminal clause invokes the finite contraction certificate and makes the
only recursive call, whose uncancelled Gaussian denominator norm is strictly
smaller.  The returned data also contains the exact decoder product and its
projective reconstruction proof.
-/

namespace CCL

open GaussianRat
open Integral

namespace CCFEncoder

/-- The coordinate-floor digit of an uncancelled fraction. -/
def digit (f : Frac) : GI := CoordinateFloor.floor f.value

/-- The square residual `z - ⌊z⌋`. -/
def residual (f : Frac) : GaussianRat := f.value - toRat (digit f)

/-- Its uncancelled Gaussian-integer numerator. -/
def remainder (f : Frac) : GI := f.num - digit f * f.den

theorem residual_sq (f : Frac) : CoordinateFloor.Sq (residual f) := by
  simpa [residual, digit, CoordinateFloor.fract] using
    CoordinateFloor.fract_sq f.value

theorem remainder_toRat (f : Frac) :
    toRat (remainder f) = residual f * toRat f.den := by
  rw [remainder, toRat_sub, toRat_mul]
  simp only [residual, digit]
  rw [← f.value_mul_den]
  ext <;> simp only [sub_re, sub_im, mul_re, mul_im] <;> ring

theorem residual_ne_zero {f : Frac} (hr : remainder f ≠ 0) : residual f ≠ 0 := by
  intro h
  have := remainder_toRat f
  rw [h, zero_mul] at this
  exact hr (toRat_eq_zero.mp this)

/-- One nonterminal CCF transition, without cancellation. -/
def next (f : Frac) (hr : remainder f ≠ 0) : Frac :=
  ⟨gammaInt * f.den, remainder f, hr⟩

@[simp] theorem next_num (f : Frac) (hr : remainder f ≠ 0) :
    (next f hr).num = gammaInt * f.den := rfl

@[simp] theorem next_den (f : Frac) (hr : remainder f ≠ 0) :
    (next f hr).den = remainder f := rfl

/-- Exact semantic transition `z⁺ = γ/(z-⌊z⌋)`. -/
theorem next_value (f : Frac) (hr : remainder f ≠ 0) :
    (next f hr).value = gamma * inv (residual f) := by
  apply mul_right_cancel_of_ne (show toRat (remainder f) ≠ 0 by simpa using hr)
  calc
    (next f hr).value * toRat (remainder f) =
        toRat (gammaInt * f.den) := (next f hr).value_mul_den
    _ = gamma * toRat f.den := by simp
    _ = (gamma * inv (residual f)) * toRat (remainder f) := by
      rw [remainder_toRat, GaussianRat.mul_assoc,
        ← GaussianRat.mul_assoc (inv (residual f)),
        inv_mul _ (residual_ne_zero hr), one_mul]

/-- Successive residuals are exactly iterates of the square return map. -/
theorem residual_next (f : Frac) (hr : remainder f ≠ 0) :
    residual (next f hr) = CoordinateFloor.step (residual f) := by
  rw [residual, digit, next_value]
  rfl

/-- Exact norm relation for the next uncancelled denominator. -/
theorem next_den_norm (f : Frac) (hr : remainder f ≠ 0) :
    (normNat (next f hr).den : ℚ) =
      normSq (residual f) * normNat f.den := by
  rw [next_den, ← normSq_toRat, remainder_toRat, normSq_mul, normSq_toRat]

/-- Three nonterminal clauses strictly decrease the original uncancelled
denominator norm. -/
theorem three_den_descent (f : Frac) (h₀ : remainder f ≠ 0)
    (h₁ : remainder (next f h₀) ≠ 0)
    (h₂ : remainder (next (next f h₀) h₁) ≠ 0) :
    normNat (next (next (next f h₀) h₁) h₂).den < normNat f.den := by
  let f₁ := next f h₀
  let f₂ := next f₁ h₁
  let f₃ := next f₂ h₂
  let u := residual f
  have hu : u ≠ 0 := residual_ne_zero h₀
  have hvEq : residual f₁ = CoordinateFloor.step u := by
    dsimp [f₁, u]
    exact residual_next f h₀
  have hv : CoordinateFloor.step u ≠ 0 := by
    rw [← hvEq]
    exact residual_ne_zero h₁
  have hwEq : residual f₂ = CoordinateFloor.step (CoordinateFloor.step u) := by
    rw [residual_next f₁ h₁, hvEq]
  have hcontract := CCFContraction.three_step_contraction u hu (residual_sq f) hv
  have hnorm₁ := next_den_norm f h₀
  have hnorm₂ := next_den_norm f₁ h₁
  have hnorm₃ := next_den_norm f₂ h₂
  have hnorm : (normNat f₃.den : ℚ) =
      normSq (u * CoordinateFloor.step u *
        CoordinateFloor.step (CoordinateFloor.step u)) * normNat f.den := by
    calc
      (normNat f₃.den : ℚ) = normSq (residual f₂) * normNat f₂.den := hnorm₃
      _ = normSq (residual f₂) *
          (normSq (residual f₁) * normNat f₁.den) := by rw [hnorm₂]
      _ = normSq (residual f₂) *
          (normSq (residual f₁) * (normSq u * normNat f.den)) := by rw [hnorm₁]
      _ = normSq (u * residual f₁ * residual f₂) * normNat f.den := by
        rw [normSq_mul, normSq_mul]
        ring
      _ = normSq (u * CoordinateFloor.step u *
          CoordinateFloor.step (CoordinateFloor.step u)) * normNat f.den := by
        rw [hvEq, hwEq]
  have hdenPos : (0 : ℚ) < normNat f.den := by
    exact_mod_cast normNat_pos f.den_ne
  have hlt : (normNat f₃.den : ℚ) < normNat f.den := by
    rw [hnorm]
    nlinarith [normSq_nonneg
      (u * CoordinateFloor.step u * CoordinateFloor.step (CoordinateFloor.step u))]
  exact_mod_cast hlt

/-- The integral decoder matrix `A(t,γ)` for one emitted CCF digit. -/
def digitMatrix (t : GI) : Mat2 GI := Mat2.cf t gammaInt

theorem map_digitMatrix (t : GI) :
    mapMat (digitMatrix t) = Mat2.cf (toRat t) gamma := by
  ext <;> simp [mapMat, digitMatrix, Mat2.cf]

/-- A finite digit list, its decoder product in emission order, and exact
projective reconstruction of the input fraction. -/
structure Encoding (f : Frac) where
  digits : List GI
  matrix : Mat2 GI
  reconstruct :
    (Mat2.act matrix (Proj.omega : Proj GI)).Equivalent ⟨f.num, f.den⟩

private def terminal (f : Frac) (h : remainder f = 0) : Encoding f := by
  have hnum : f.num = digit f * f.den := by
    apply sub_eq_zero.mp
    simpa [remainder] using h
  refine ⟨[digit f], digitMatrix (digit f), ?_⟩
  rw [hnum]
  dsimp [digitMatrix, Proj.Equivalent, Mat2.act, Mat2.cf, Proj.omega]
  ring

private theorem digit_step_reconstruct (f : Frac) (h : remainder f ≠ 0) :
    (Mat2.act (digitMatrix (digit f))
      ⟨(next f h).num, (next f h).den⟩).Equivalent ⟨f.num, f.den⟩ := by
  dsimp [digitMatrix, Proj.Equivalent, Mat2.act, Mat2.cf, next, remainder]
  ring

private theorem digit_step_den_ne (f : Frac) (h : remainder f ≠ 0) :
    (Mat2.act (digitMatrix (digit f))
      ⟨(next f h).num, (next f h).den⟩).q ≠ 0 := by
  dsimp [digitMatrix, Mat2.act, Mat2.cf, next]
  simpa using mul_ne_zero (show gammaInt ≠ 0 by decide) f.den_ne

/-- Prepend one nonterminal digit and its inverse-branch matrix. -/
private def prepend (f : Frac) (h : remainder f ≠ 0)
    (tail : Encoding (next f h)) : Encoding f :=
  let matrix := Mat2.mul (digitMatrix (digit f)) tail.matrix
  ⟨digit f :: tail.digits, matrix, by
    dsimp only [matrix]
    rw [Mat2.act_mul]
    have hact := Mat2.act_respects_equivalent (digitMatrix (digit f)) tail.reconstruct
    exact hact.trans_of_mid_q_domain (digit_step_reconstruct f h)
      (digit_step_den_ne f h)⟩

/-- Algorithm 5.1 as a well-founded three-clause macro-recursion. -/
def encodeResult (f : Frac) : Encoding f :=
  if h₀ : remainder f = 0 then terminal f h₀
  else
    let f₁ := next f h₀
    if h₁ : remainder f₁ = 0 then prepend f h₀ (terminal f₁ h₁)
    else
      let f₂ := next f₁ h₁
      if h₂ : remainder f₂ = 0 then
        prepend f h₀ (prepend f₁ h₁ (terminal f₂ h₂))
      else
        let f₃ := next f₂ h₂
        prepend f h₀ (prepend f₁ h₁ (prepend f₂ h₂ (encodeResult f₃)))
termination_by normNat f.den
decreasing_by exact three_den_descent f h₀ h₁ h₂

/-- The finite coordinate-floor digit list. -/
def encode (f : Frac) : List GI := (encodeResult f).digits

/-- Theorem 5.3, integral form. -/
theorem encode_reconstruct_pair (f : Frac) :
    (Mat2.act (encodeResult f).matrix (Proj.omega : Proj GI)).Equivalent
      ⟨f.num, f.den⟩ :=
  (encodeResult f).reconstruct

/-- Theorem 5.3 in Gaussian-rational affine coordinates. -/
theorem encode_reconstruct (f : Frac) :
    (Mat2.act (mapMat (encodeResult f).matrix)
      (Proj.omega : Proj GaussianRat)).Equivalent (Proj.affine f.value) := by
  have h := mapProj_equivalent (encodeResult f).reconstruct
  rw [mapProj_act, mapProj_omega] at h
  dsimp [Proj.Equivalent, mapProj, Proj.affine] at h ⊢
  rw [mul_one]
  apply mul_right_cancel_of_ne f.den_toRat_ne
  calc
    (Mat2.act (mapMat (encodeResult f).matrix)
        (Proj.omega : Proj GaussianRat)).p * toRat f.den =
        toRat f.num *
          (Mat2.act (mapMat (encodeResult f).matrix)
            (Proj.omega : Proj GaussianRat)).q := h
    _ = (f.value * toRat f.den) *
          (Mat2.act (mapMat (encodeResult f).matrix)
            (Proj.omega : Proj GaussianRat)).q := by rw [f.value_mul_den]
    _ = (f.value *
          (Mat2.act (mapMat (encodeResult f).matrix)
            (Proj.omega : Proj GaussianRat)).q) * toRat f.den := by
      rw [GaussianRat.mul_assoc, GaussianRat.mul_comm (toRat f.den),
        ← GaussianRat.mul_assoc]

end CCFEncoder

end CCL
