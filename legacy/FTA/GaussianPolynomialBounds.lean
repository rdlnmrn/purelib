import FTA.GaussianDerivative
import FTA.BoxGeometry

/-!
# Executable dense Gaussian-polynomial bounds

Mathlib's sparse polynomial representation is a useful specification but is
not executable.  This module propagates squared-norm value and Lipschitz
bounds directly through the dense Gaussian-rational Horner program.  The scan
is finite coefficient arithmetic and is used by the local extraction
algorithm.
-/

namespace FTA.GaussianPolynomialBounds

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.GaussianDerivative

/-- Squared-norm value and displacement coefficients propagated by one
Gaussian-rational Horner scan. -/
structure HornerNormBounds where
  value : ℚ
  slope : ℚ
deriving DecidableEq, Repr

/-- One Horner step.  The factors of two are the exact finite estimate
`N(u+v) ≤ 2(N(u)+N(v))`. -/
def HornerNormBounds.step (radiusSq : ℚ)
    (bounds : HornerNormBounds) (coefficient : QI) : HornerNormBounds where
  value := 2 * (bounds.value * radiusSq + normSq coefficient)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)

/-- Executable value and displacement bounds on a rational box. -/
def denseHornerNormBounds (p : GaussianPolynomial)
    (B : CCL.RatBox) : HornerNormBounds :=
  p.coeffs.foldl (HornerNormBounds.step (boxNormBound B)) ⟨0, 0⟩

def denseEvalNormBound (p : GaussianPolynomial) (B : CCL.RatBox) : ℚ :=
  (denseHornerNormBounds p B).value

/-- The raw executable squared-norm Lipschitz coefficient. -/
def denseEvalNormLipschitzBound
    (p : GaussianPolynomial) (B : CCL.RatBox) : ℚ :=
  (denseHornerNormBounds p B).slope

/-- Positive version used when a denominator or strictly positive search
scale is required. -/
def denseLipschitzBound (p : GaussianPolynomial) (B : CCL.RatBox) : ℚ :=
  max 1 (denseEvalNormLipschitzBound p B)

private theorem evalNormBoundsCoeffs_spec
    (coeffs : List QI) {radiusSq : ℚ} {x y : QI}
    (hradius : 0 ≤ radiusSq)
    (hx : normSq x ≤ radiusSq) (hy : normSq y ≤ radiusSq)
    (accX accY : QI) (bounds : HornerNormBounds)
    (hvalue : 0 ≤ bounds.value) (hslope : 0 ≤ bounds.slope)
    (haccX : normSq accX ≤ bounds.value)
    (haccY : normSq accY ≤ bounds.value)
    (hdiff : normSq (accX - accY) ≤
      bounds.slope * normSq (x - y)) :
    let finalX := coeffs.foldl
      (fun acc coefficient => acc * x + coefficient) accX
    let finalY := coeffs.foldl
      (fun acc coefficient => acc * y + coefficient) accY
    let finalBounds := coeffs.foldl
      (HornerNormBounds.step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      normSq finalX ≤ finalBounds.value ∧
      normSq finalY ≤ finalBounds.value ∧
      normSq (finalX - finalY) ≤
        finalBounds.slope * normSq (x - y) := by
  induction coeffs generalizing accX accY bounds with
  | nil => exact ⟨hvalue, hslope, haccX, haccY, hdiff⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp [HornerNormBounds.step]
        exact mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg hvalue hradius) (normSq_nonneg _))
      · dsimp [HornerNormBounds.step]
        exact mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg hslope hradius) hvalue)
      · dsimp [HornerNormBounds.step]
        have hmul : normSq accX * normSq x ≤
            bounds.value * radiusSq :=
          mul_le_mul haccX hx (normSq_nonneg x) hvalue
        calc
          normSq (accX * x + coefficient) ≤
              2 * (normSq (accX * x) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accX * normSq x + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) := by
            gcongr
      · dsimp [HornerNormBounds.step]
        have hmul : normSq accY * normSq y ≤
            bounds.value * radiusSq :=
          mul_le_mul haccY hy (normSq_nonneg y) hvalue
        calc
          normSq (accY * y + coefficient) ≤
              2 * (normSq (accY * y) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accY * normSq y + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) := by
            gcongr
      · dsimp [HornerNormBounds.step]
        have hidentity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by
          ext <;> simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
            <;> ring
        rw [hidentity]
        have hfirst : normSq (accX - accY) * normSq x ≤
            (bounds.slope * normSq (x - y)) * radiusSq :=
          mul_le_mul hdiff hx (normSq_nonneg x)
            (mul_nonneg hslope (normSq_nonneg (x - y)))
        have hsecond : normSq accY * normSq (x - y) ≤
            bounds.value * normSq (x - y) :=
          mul_le_mul_of_nonneg_right haccY (normSq_nonneg (x - y))
        calc
          normSq ((accX - accY) * x + accY * (x - y)) ≤
              2 * (normSq ((accX - accY) * x) +
                normSq (accY * (x - y))) := normSq_add_le_two _ _
          _ = 2 * (normSq (accX - accY) * normSq x +
                normSq accY * normSq (x - y)) := by
            rw [normSq_mul, normSq_mul]
          _ ≤ 2 * ((bounds.slope * normSq (x - y)) * radiusSq +
                bounds.value * normSq (x - y)) := by
            gcongr
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                normSq (x - y) := by ring

/-- Both raw Horner coefficients are nonnegative. -/
theorem denseHornerNormBounds_nonneg
    (p : GaussianPolynomial) (B : CCL.RatBox) :
    0 ≤ denseEvalNormBound p B ∧
      0 ≤ denseEvalNormLipschitzBound p B := by
  have hspec := evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := boxNormBound B) (x := 0) (y := 0)
    (boxNormBound_nonneg B)
    (by simpa using boxNormBound_nonneg B)
    (by simpa using boxNormBound_nonneg B)
    0 0 ⟨0, 0⟩ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hspec.1, hspec.2.1⟩

/-- Dense evaluation is bounded directly by the value coefficient. -/
theorem normSq_dense_eval_le_denseEvalNormBound
    (p : GaussianPolynomial) {B : CCL.RatBox} {z : QI}
    (hz : B.Contains z) :
    normSq (p.eval z) ≤ denseEvalNormBound p B := by
  have hspec := evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := boxNormBound B) (x := z) (y := z)
    (boxNormBound_nonneg B) (normSq_le_boxNormBound hz)
    (normSq_le_boxNormBound hz)
    0 0 ⟨0, 0⟩ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa [DensePolynomial.eval, evalCoeffs, denseEvalNormBound,
    denseHornerNormBounds] using hspec.2.2.1

/-- Evaluation bound enlarged to at least one for positive rational Bezout
margins. -/
def denseEvalNormMajorant
    (p : GaussianPolynomial) (B : CCL.RatBox) : ℚ :=
  max 1 (denseEvalNormBound p B)

theorem one_le_denseEvalNormMajorant
    (p : GaussianPolynomial) (B : CCL.RatBox) :
    1 ≤ denseEvalNormMajorant p B := le_max_left _ _

theorem normSq_dense_eval_le_denseEvalNormMajorant
    (p : GaussianPolynomial) {B : CCL.RatBox} {z : QI}
    (hz : B.Contains z) :
    normSq (p.eval z) ≤ denseEvalNormMajorant p B :=
  (normSq_dense_eval_le_denseEvalNormBound p hz).trans
    (le_max_right _ _)

/-- The raw dense Horner slope bounds squared-norm evaluation displacement. -/
theorem normSq_dense_eval_sub_eval_le
    (p : GaussianPolynomial) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (p.eval z + -(p.eval w)) ≤
      denseEvalNormLipschitzBound p B * normSq (z + -w) := by
  have hspec := evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := boxNormBound B) (x := z) (y := w)
    (boxNormBound_nonneg B) (normSq_le_boxNormBound hz)
    (normSq_le_boxNormBound hw)
    0 0 ⟨0, 0⟩ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa [DensePolynomial.eval, evalCoeffs, denseEvalNormLipschitzBound,
    denseHornerNormBounds, GaussianRat.sub_eq_add_neg] using hspec.2.2.2.2

theorem denseLipschitzBound_pos
    (p : GaussianPolynomial) (B : CCL.RatBox) :
    0 < denseLipschitzBound p B :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Positive executable specialization of the displacement theorem. -/
theorem normSq_dense_eval_sub_eval_le_denseLipschitzBound
    (p : GaussianPolynomial) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (p.eval z + -(p.eval w)) ≤
      denseLipschitzBound p B * normSq (z + -w) := by
  exact (normSq_dense_eval_sub_eval_le p hz hw).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (normSq_nonneg (z + -w)))

/-! ## Executable quadratic Taylor bounds -/

/-- Value, first-displacement, and quadratic-remainder coefficients propagated
by the finite Gaussian Horner scan. -/
structure HornerTaylorNormBounds where
  value : ℚ
  slope : ℚ
  remainder : ℚ
deriving DecidableEq, Repr

/-- One Taylor-bound Horner step. -/
def HornerTaylorNormBounds.step (radiusSq : ℚ)
    (bounds : HornerTaylorNormBounds) (coefficient : QI) :
    HornerTaylorNormBounds where
  value := 2 * (bounds.value * radiusSq + normSq coefficient)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)
  remainder := 2 * (bounds.slope + radiusSq * bounds.remainder)

/-- Executable three-component Taylor scan. -/
def denseHornerTaylorNormBounds
    (p : GaussianPolynomial) (B : CCL.RatBox) : HornerTaylorNormBounds :=
  p.coeffs.foldl (HornerTaylorNormBounds.step (boxNormBound B))
    ⟨0, 0, 0⟩

/-- Raw quadratic-remainder coefficient from the scan. -/
def denseEvalTaylorRemainderBound
    (p : GaussianPolynomial) (B : CCL.RatBox) : ℚ :=
  (denseHornerTaylorNormBounds p B).remainder

/-- Strictly positive executable quadratic Taylor coefficient. -/
def denseTaylorRemainderBound
    (p : GaussianPolynomial) (B : CCL.RatBox) : ℚ :=
  max 1 (denseEvalTaylorRemainderBound p B)

/-- Evaluation form of the automatic-differentiation Horner step. -/
def evalDerivativeStep (x : QI) (state : QI × QI) (coefficient : QI) :
    QI × QI :=
  (state.1 * x + coefficient, state.2 * x + state.1)

def evalDerivativeCoeffs (x : QI) (coeffs : List QI) : QI × QI :=
  coeffs.foldl (evalDerivativeStep x) (0, 0)

private theorem eval_derivativeFold
    (x : QI) (coeffs : List QI)
    (state : GaussianPolynomial × GaussianPolynomial) :
    ((coeffs.foldl derivativeStep state).1.eval x,
        (coeffs.foldl derivativeStep state).2.eval x) =
      coeffs.foldl (evalDerivativeStep x)
        (state.1.eval x, state.2.eval x) := by
  induction coeffs generalizing state with
  | nil => rfl
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      simp [derivativeStep, evalDerivativeStep]

theorem evalDerivativeCoeffs_derivative
    (p : GaussianPolynomial) (x : QI) :
    (evalDerivativeCoeffs x p.coeffs).2 = (derivative p).eval x := by
  have h := eval_derivativeFold x p.coeffs (0, 0)
  dsimp only [evalDerivativeCoeffs, derivative, derivativeState] at h ⊢
  simpa using congrArg Prod.snd h.symm

private theorem evalTaylorNormBoundsCoeffs_spec
    (coeffs : List QI) {radiusSq : ℚ} {x y : QI}
    (hradius : 0 ≤ radiusSq)
    (hx : normSq x ≤ radiusSq) (hy : normSq y ≤ radiusSq)
    (accX accY derivativeY : QI) (bounds : HornerTaylorNormBounds)
    (hvalue : 0 ≤ bounds.value) (hslope : 0 ≤ bounds.slope)
    (hremainder : 0 ≤ bounds.remainder)
    (haccX : normSq accX ≤ bounds.value)
    (haccY : normSq accY ≤ bounds.value)
    (hdiff : normSq (accX - accY) ≤
      bounds.slope * normSq (x - y))
    (htaylor : normSq
        (accX - accY - derivativeY * (x - y)) ≤
      bounds.remainder * normSq (x - y) ^ 2) :
    let finalX := coeffs.foldl
      (fun acc coefficient => acc * x + coefficient) accX
    let finalY := coeffs.foldl
      (fun acc coefficient => acc * y + coefficient) accY
    let finalDerivativeY := coeffs.foldl
      (evalDerivativeStep y) (accY, derivativeY) |>.2
    let finalBounds := coeffs.foldl
      (HornerTaylorNormBounds.step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      0 ≤ finalBounds.remainder ∧
      normSq finalX ≤ finalBounds.value ∧
      normSq finalY ≤ finalBounds.value ∧
      normSq (finalX - finalY) ≤
        finalBounds.slope * normSq (x - y) ∧
      normSq (finalX - finalY - finalDerivativeY * (x - y)) ≤
        finalBounds.remainder * normSq (x - y) ^ 2 := by
  induction coeffs generalizing accX accY derivativeY bounds with
  | nil =>
      exact ⟨hvalue, hslope, hremainder, haccX, haccY, hdiff, htaylor⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp [HornerTaylorNormBounds.step]
        exact mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg hvalue hradius) (normSq_nonneg _))
      · dsimp [HornerTaylorNormBounds.step]
        exact mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg hslope hradius) hvalue)
      · dsimp [HornerTaylorNormBounds.step]
        exact mul_nonneg (by norm_num)
          (add_nonneg hslope (mul_nonneg hradius hremainder))
      · dsimp [HornerTaylorNormBounds.step]
        have hmul : normSq accX * normSq x ≤
            bounds.value * radiusSq :=
          mul_le_mul haccX hx (normSq_nonneg x) hvalue
        calc
          normSq (accX * x + coefficient) ≤
              2 * (normSq (accX * x) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accX * normSq x + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) := by
            gcongr
      · dsimp [HornerTaylorNormBounds.step]
        have hmul : normSq accY * normSq y ≤
            bounds.value * radiusSq :=
          mul_le_mul haccY hy (normSq_nonneg y) hvalue
        calc
          normSq (accY * y + coefficient) ≤
              2 * (normSq (accY * y) + normSq coefficient) :=
            normSq_add_le_two _ _
          _ = 2 * (normSq accY * normSq y + normSq coefficient) := by
            rw [normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + normSq coefficient) := by
            gcongr
      · dsimp [HornerTaylorNormBounds.step]
        have hidentity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by
          ext <;> simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
            <;> ring
        rw [hidentity]
        have hfirst : normSq (accX - accY) * normSq x ≤
            (bounds.slope * normSq (x - y)) * radiusSq :=
          mul_le_mul hdiff hx (normSq_nonneg x)
            (mul_nonneg hslope (normSq_nonneg (x - y)))
        have hsecond : normSq accY * normSq (x - y) ≤
            bounds.value * normSq (x - y) :=
          mul_le_mul_of_nonneg_right haccY (normSq_nonneg (x - y))
        calc
          normSq ((accX - accY) * x + accY * (x - y)) ≤
              2 * (normSq ((accX - accY) * x) +
                normSq (accY * (x - y))) := normSq_add_le_two _ _
          _ = 2 * (normSq (accX - accY) * normSq x +
                normSq accY * normSq (x - y)) := by
            rw [normSq_mul, normSq_mul]
          _ ≤ 2 * ((bounds.slope * normSq (x - y)) * radiusSq +
                bounds.value * normSq (x - y)) := by
            gcongr
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                normSq (x - y) := by ring
      · dsimp [HornerTaylorNormBounds.step, evalDerivativeStep]
        have hidentity :
            (accX * x + coefficient) - (accY * y + coefficient) -
                (derivativeY * y + accY) * (x - y) =
              (accX - accY) * (x - y) +
                (accX - accY - derivativeY * (x - y)) * y := by
          ext <;> simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im]
            <;> ring
        rw [hidentity]
        have hfirst :
            normSq (accX - accY) * normSq (x - y) ≤
              bounds.slope * normSq (x - y) ^ 2 := by
          calc
            normSq (accX - accY) * normSq (x - y) ≤
                (bounds.slope * normSq (x - y)) * normSq (x - y) :=
              mul_le_mul_of_nonneg_right hdiff (normSq_nonneg (x - y))
            _ = bounds.slope * normSq (x - y) ^ 2 := by ring
        have hsecond :
            normSq (accX - accY - derivativeY * (x - y)) * normSq y ≤
              (bounds.remainder * normSq (x - y) ^ 2) * radiusSq := by
          exact mul_le_mul htaylor hy (normSq_nonneg y)
            (mul_nonneg hremainder (sq_nonneg _))
        calc
          normSq ((accX - accY) * (x - y) +
              (accX - accY - derivativeY * (x - y)) * y) ≤
            2 * (normSq ((accX - accY) * (x - y)) +
              normSq ((accX - accY - derivativeY * (x - y)) * y)) :=
                normSq_add_le_two _ _
          _ = 2 * (normSq (accX - accY) * normSq (x - y) +
              normSq (accX - accY - derivativeY * (x - y)) *
                normSq y) := by rw [normSq_mul, normSq_mul]
          _ ≤ 2 * (bounds.slope * normSq (x - y) ^ 2 +
              (bounds.remainder * normSq (x - y) ^ 2) * radiusSq) := by
                gcongr
          _ = 2 * (bounds.slope + radiusSq * bounds.remainder) *
              normSq (x - y) ^ 2 := by ring

/-- All three raw Taylor scan coefficients are nonnegative. -/
theorem denseHornerTaylorNormBounds_nonneg
    (p : GaussianPolynomial) (B : CCL.RatBox) :
    0 ≤ (denseHornerTaylorNormBounds p B).value ∧
      0 ≤ (denseHornerTaylorNormBounds p B).slope ∧
      0 ≤ denseEvalTaylorRemainderBound p B := by
  have hspec := evalTaylorNormBoundsCoeffs_spec p.coeffs
    (radiusSq := boxNormBound B) (x := 0) (y := 0)
    (boxNormBound_nonneg B)
    (by simpa using boxNormBound_nonneg B)
    (by simpa using boxNormBound_nonneg B)
    0 0 0 ⟨0, 0, 0⟩ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- Exact executable quadratic Taylor bound. -/
theorem normSq_dense_taylor_remainder_le
    (p : GaussianPolynomial) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (p.eval z + -(p.eval w) +
        -((derivative p).eval w * (z + -w))) ≤
      denseEvalTaylorRemainderBound p B * normSq (z + -w) ^ 2 := by
  have hspec := evalTaylorNormBoundsCoeffs_spec p.coeffs
    (radiusSq := boxNormBound B) (x := z) (y := w)
    (boxNormBound_nonneg B) (normSq_le_boxNormBound hz)
    (normSq_le_boxNormBound hw)
    0 0 0 ⟨0, 0, 0⟩ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hderivative := evalDerivativeCoeffs_derivative p w
  have hderivative' :
      (p.coeffs.foldl (evalDerivativeStep w) (0, 0)).2 =
        (derivative p).eval w := by
    simpa only [evalDerivativeCoeffs] using hderivative
  rw [hderivative'] at hspec
  simpa [DensePolynomial.eval, evalCoeffs, denseEvalTaylorRemainderBound,
    denseHornerTaylorNormBounds,
    GaussianRat.sub_eq_add_neg] using hspec.2.2.2.2.2.2

theorem denseTaylorRemainderBound_pos
    (p : GaussianPolynomial) (B : CCL.RatBox) :
    0 < denseTaylorRemainderBound p B :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Positive executable specialization of the Taylor bound. -/
theorem normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
    (p : GaussianPolynomial) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (p.eval z + -(p.eval w) +
        -((derivative p).eval w * (z + -w))) ≤
      denseTaylorRemainderBound p B * normSq (z + -w) ^ 2 := by
  exact (normSq_dense_taylor_remainder_le p hz hw).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (sq_nonneg (normSq (z + -w))))

/-! ## Native computation regression -/

/-- The scan is an actual finite computation, illustrated on `Z²-2` over
the unit symmetric square. -/
theorem denseHornerNormBounds_quadratic_example :
    denseHornerNormBounds
      ⟨[(1 : QI), 0, -2]⟩ (CCL.RatBox.symmetric 1 (by norm_num)) =
        ⟨40, 32⟩ := by
  native_decide

/-- The Taylor scan is likewise executable; the quadratic remainder
coefficient for `Z²-2` is eight on the same square. -/
theorem denseHornerTaylorNormBounds_quadratic_example :
    denseHornerTaylorNormBounds
      ⟨[(1 : QI), 0, -2]⟩ (CCL.RatBox.symmetric 1 (by norm_num)) =
        ⟨40, 32, 8⟩ := by
  native_decide

end FTA.GaussianPolynomialBounds
