import CCL.Integral

/-!
# Coordinate-floor complex continued fractions

This module begins the formalization of Section 5.  It defines the exact
coordinate floor and square fractional-part map, then proves the digit-cone
lemma that reduces the later three-step contraction argument to a finite
integer table.
-/

namespace CCL

open GaussianRat
open Integral

namespace CoordinateFloor

/-- Coordinatewise Gaussian-integer floor. -/
def floor (z : GaussianRat) : GI := ⟨⌊z.re⌋, ⌊z.im⌋⟩

@[simp] theorem floor_re (z : GaussianRat) : (floor z).re = ⌊z.re⌋ := rfl
@[simp] theorem floor_im (z : GaussianRat) : (floor z).im = ⌊z.im⌋ := rfl

/-- The half-open coordinate unit square. -/
def Sq (z : GaussianRat) : Prop :=
  0 ≤ z.re ∧ z.re < 1 ∧ 0 ≤ z.im ∧ z.im < 1

/-- Coordinatewise fractional part. -/
def fract (z : GaussianRat) : GaussianRat := z - toRat (floor z)

/-- Every coordinatewise fractional part lies in the half-open unit square. -/
theorem fract_sq (z : GaussianRat) : Sq (fract z) := by
  constructor
  · dsimp [fract, Sq, floor, toRat]
    exact sub_nonneg.mpr (Int.floor_le z.re)
  constructor
  · dsimp [fract, floor, toRat]
    change z.re - (⌊z.re⌋ : ℚ) < 1
    have := Int.lt_floor_add_one z.re
    linarith
  constructor
  · dsimp [fract, floor, toRat]
    exact sub_nonneg.mpr (Int.floor_le z.im)
  · dsimp [fract, floor, toRat]
    change z.im - (⌊z.im⌋ : ℚ) < 1
    have := Int.lt_floor_add_one z.im
    linarith

/-- The square return map `F(u) = γ/u - ⌊γ/u⌋`. -/
def step (u : GaussianRat) : GaussianRat := fract (gamma * inv u)

theorem step_sq (u : GaussianRat) : Sq (step u) := fract_sq _

theorem normSq_lt_two_of_sq {z : GaussianRat} (hz : Sq z) : normSq z < 2 := by
  rcases hz with ⟨hx₀, hx₁, hy₀, hy₁⟩
  dsimp [normSq]
  have hx : z.re ^ 2 < 1 := by nlinarith
  have hy : z.im ^ 2 < 1 := by nlinarith
  linarith

/-- Decomposition into the coordinate-floor digit and square remainder. -/
theorem floor_add_step (u : GaussianRat) :
    toRat (floor (gamma * inv u)) + step u = gamma * inv u := by
  ext <;> simp only [step, fract, add_re, add_im, sub_re, sub_im] <;> ring

private theorem quotient_coordinates (u : GaussianRat) (hu : u ≠ 0) :
    (gamma * inv u).re = (u.re + u.im) / normSq u ∧
      (gamma * inv u).im = (u.re - u.im) / normSq u := by
  have hn : normSq u ≠ 0 := fun h => hu (normSq_eq_zero.mp h)
  constructor <;> simp only [mul_re, mul_im, gamma, inv] <;>
    field_simp [hn] <;> ring

private theorem quotient_real_gt_one (u : GaussianRat) (hu : u ≠ 0)
    (hsq : Sq u) : 1 < (gamma * inv u).re := by
  rcases hsq with ⟨hx₀, hx₁, hy₀, hy₁⟩
  have hn : 0 < normSq u := normSq_pos hu
  have hxprod : 0 ≤ u.re * (1 - u.re) :=
    mul_nonneg hx₀ (by linarith)
  have hyprod : 0 ≤ u.im * (1 - u.im) :=
    mul_nonneg hy₀ (by linarith)
  have hprod : 0 < u.re * (1 - u.re) + u.im * (1 - u.im) := by
    by_cases hx : u.re = 0
    · have hy : u.im ≠ 0 := by
        intro hy
        apply hu
        apply GaussianRat.ext <;> simp [hx, hy]
      have hypos : 0 < u.im := lt_of_le_of_ne hy₀ (Ne.symm hy)
      have : 0 < u.im * (1 - u.im) :=
        mul_pos hypos (by linarith)
      nlinarith
    · have hxpos : 0 < u.re := lt_of_le_of_ne hx₀ (Ne.symm hx)
      have : 0 < u.re * (1 - u.re) :=
        mul_pos hxpos (by linarith)
      nlinarith
  have hnum : normSq u < u.re + u.im := by
    dsimp [normSq]
    nlinarith
  rw [(quotient_coordinates u hu).1]
  exact (lt_div_iff₀ hn).2 (by simpa using hnum)

private theorem quotient_abs_im_le_real (u : GaussianRat) (hu : u ≠ 0)
    (hsq : Sq u) :
    -(gamma * inv u).re ≤ (gamma * inv u).im ∧
      (gamma * inv u).im ≤ (gamma * inv u).re := by
  rcases hsq with ⟨hx, _, hy, _⟩
  have hn : 0 < normSq u := normSq_pos hu
  rcases quotient_coordinates u hu with ⟨hre, him⟩
  rw [hre, him]
  constructor
  · rw [← neg_div]
    exact (div_le_div_iff_of_pos_right hn).2 (by linarith)
  · exact (div_le_div_iff_of_pos_right hn).2 (by linarith)

/-- Lemma 5.1: every nonzero square input produces a digit in the displayed
integer cone. -/
theorem digit_cone (u : GaussianRat) (hu : u ≠ 0) (hsq : Sq u) :
    let t := floor (gamma * inv u)
    1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re := by
  let z := gamma * inv u
  let t := floor z
  change 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re
  have hzreal : 1 < z.re := quotient_real_gt_one u hu hsq
  have hzabs := quotient_abs_im_le_real u hu hsq
  have ha : (1 : ℤ) ≤ t.re := by
    apply (Int.le_floor).2
    exact hzreal.le
  have hba : t.im ≤ t.re := by
    exact Int.floor_mono hzabs.2
  have hbUpper : z.im < (t.im : ℚ) + 1 := by
    dsimp [t, floor]
    exact Int.lt_floor_add_one z.im
  have haUpper : z.re < (t.re : ℚ) + 1 := by
    dsimp [t, floor]
    exact Int.lt_floor_add_one z.re
  have hcast : ((-t.im - 1 : ℤ) : ℚ) < ((t.re + 1 : ℤ) : ℚ) := by
    push_cast
    linarith
  have hInt : -t.im - 1 < t.re + 1 := by exact_mod_cast hcast
  exact ⟨ha, by omega, hba⟩

end CoordinateFloor

end CCL
