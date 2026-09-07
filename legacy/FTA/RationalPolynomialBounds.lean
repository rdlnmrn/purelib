import FTA.DenseSquarefree
import Mathlib.Tactic.Positivity

/-!
# Finite rational polynomial bounds

This module supplies coefficient-computable bounds for rational polynomial
evaluation on a bounded interval.  All statements are finite inequalities on
coefficients and rational powers; no completion, limit, or named real root is
used.  The Sturm event partition uses these bounds to certify that a chain
member keeps its sign throughout a sufficiently small rational cell.
-/

namespace FTA.RationalPolynomialBounds

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.DenseDerivative

abbrev RatPolynomial := DensePolynomial ℚ

/-- Value and displacement coefficients propagated by one finite Horner
scan. -/
structure HornerBounds where
  value : ℚ
  slope : ℚ
deriving DecidableEq, Repr

def HornerBounds.step (B : ℚ) (bounds : HornerBounds) (coefficient : ℚ) :
    HornerBounds where
  value := bounds.value * B + |coefficient|
  slope := bounds.slope * B + bounds.value

/-- Executable value and Lipschitz bounds for a dense polynomial on
`[-B,B]`. -/
def denseHornerBounds (p : RatPolynomial) (B : ℚ) : HornerBounds :=
  p.coeffs.foldl (HornerBounds.step B) ⟨0, 0⟩

def denseEvalAbsBound (p : RatPolynomial) (B : ℚ) : ℚ :=
  (denseHornerBounds p B).value

def denseEvalLipschitzBound (p : RatPolynomial) (B : ℚ) : ℚ :=
  (denseHornerBounds p B).slope

private theorem evalBoundsCoeffs_spec (coeffs : List ℚ) {B x y : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (accX accY : ℚ) (bounds : HornerBounds)
    (hvalue : 0 ≤ bounds.value) (hslope : 0 ≤ bounds.slope)
    (haccX : |accX| ≤ bounds.value) (haccY : |accY| ≤ bounds.value)
    (hdiff : |accX - accY| ≤ bounds.slope * |x - y|) :
    let finalX := coeffs.foldl (fun acc coefficient => acc * x + coefficient) accX
    let finalY := coeffs.foldl (fun acc coefficient => acc * y + coefficient) accY
    let finalBounds := coeffs.foldl (HornerBounds.step B) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      |finalX| ≤ finalBounds.value ∧ |finalY| ≤ finalBounds.value ∧
      |finalX - finalY| ≤ finalBounds.slope * |x - y| := by
  induction coeffs generalizing accX accY bounds with
  | nil => exact ⟨hvalue, hslope, haccX, haccY, hdiff⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp [HornerBounds.step]
        positivity
      · dsimp [HornerBounds.step]
        positivity
      · dsimp [HornerBounds.step]
        calc
          |accX * x + coefficient| ≤ |accX * x| + |coefficient| :=
            abs_add_le _ _
          _ = |accX| * |x| + |coefficient| := by rw [abs_mul]
          _ ≤ bounds.value * B + |coefficient| := by gcongr
      · dsimp [HornerBounds.step]
        calc
          |accY * y + coefficient| ≤ |accY * y| + |coefficient| :=
            abs_add_le _ _
          _ = |accY| * |y| + |coefficient| := by rw [abs_mul]
          _ ≤ bounds.value * B + |coefficient| := by gcongr
      · dsimp [HornerBounds.step]
        have hidentity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by ring
        rw [hidentity]
        calc
          |(accX - accY) * x + accY * (x - y)| ≤
              |(accX - accY) * x| + |accY * (x - y)| := abs_add_le _ _
          _ = |accX - accY| * |x| + |accY| * |x - y| := by
            rw [abs_mul, abs_mul]
          _ ≤ (bounds.slope * B + bounds.value) * |x - y| := by
            calc
              |accX - accY| * |x| + |accY| * |x - y| ≤
                  (bounds.slope * |x - y|) * B +
                    bounds.value * |x - y| := by gcongr
              _ = (bounds.slope * B + bounds.value) * |x - y| := by ring

theorem denseHornerBounds_nonneg (p : RatPolynomial) {B : ℚ} (hB : 0 ≤ B) :
    0 ≤ denseEvalAbsBound p B ∧ 0 ≤ denseEvalLipschitzBound p B := by
  have hspec := evalBoundsCoeffs_spec p.coeffs hB
    (x := 0) (y := 0) (by positivity) (by positivity)
    0 0 ⟨0, 0⟩ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hspec.1, hspec.2.1⟩

private theorem hornerBoundsFold_mono (coeffs : List ℚ) {B C : ℚ}
    (hB : 0 ≤ B) (hBC : B ≤ C)
    (boundsB boundsC : HornerBounds)
    (hvalueB : 0 ≤ boundsB.value) (hslopeB : 0 ≤ boundsB.slope)
    (hvalueC : 0 ≤ boundsC.value) (hslopeC : 0 ≤ boundsC.slope)
    (hvalue : boundsB.value ≤ boundsC.value)
    (hslope : boundsB.slope ≤ boundsC.slope) :
    let finalB := coeffs.foldl (HornerBounds.step B) boundsB
    let finalC := coeffs.foldl (HornerBounds.step C) boundsC
    0 ≤ finalB.value ∧ 0 ≤ finalB.slope ∧
      0 ≤ finalC.value ∧ 0 ≤ finalC.slope ∧
      finalB.value ≤ finalC.value ∧ finalB.slope ≤ finalC.slope := by
  have hC : 0 ≤ C := hB.trans hBC
  induction coeffs generalizing boundsB boundsC with
  | nil => exact ⟨hvalueB, hslopeB, hvalueC, hslopeC, hvalue, hslope⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp [HornerBounds.step]
        positivity
      · dsimp [HornerBounds.step]
        positivity
      · dsimp [HornerBounds.step]
        positivity
      · dsimp [HornerBounds.step]
        positivity
      · dsimp [HornerBounds.step]
        have hmul : boundsB.value * B ≤ boundsC.value * C := by
          calc
            boundsB.value * B ≤ boundsC.value * B :=
              mul_le_mul_of_nonneg_right hvalue hB
            _ ≤ boundsC.value * C :=
              mul_le_mul_of_nonneg_left hBC hvalueC
        linarith
      · dsimp [HornerBounds.step]
        have hmul : boundsB.slope * B ≤ boundsC.slope * C := by
          calc
            boundsB.slope * B ≤ boundsC.slope * B :=
              mul_le_mul_of_nonneg_right hslope hB
            _ ≤ boundsC.slope * C :=
              mul_le_mul_of_nonneg_left hBC hslopeC
        linarith

/-- The executable Horner value and slope bounds are monotone in the
nonnegative ambient radius. -/
theorem denseHornerBounds_mono (p : RatPolynomial) {B C : ℚ}
    (hB : 0 ≤ B) (hBC : B ≤ C) :
    denseEvalAbsBound p B ≤ denseEvalAbsBound p C ∧
      denseEvalLipschitzBound p B ≤ denseEvalLipschitzBound p C := by
  have hspec := hornerBoundsFold_mono p.coeffs hB hBC
    ⟨0, 0⟩ ⟨0, 0⟩ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩

theorem abs_dense_eval_le_denseEvalAbsBound (p : RatPolynomial) {B x : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |p.eval x| ≤ denseEvalAbsBound p B := by
  have hspec := evalBoundsCoeffs_spec p.coeffs hB hx hx
    0 0 ⟨0, 0⟩ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa [DensePolynomial.eval, evalCoeffs, denseEvalAbsBound,
    denseHornerBounds] using hspec.2.2.1

theorem abs_dense_eval_sub_eval_le_dense (p : RatPolynomial) {B x y : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |p.eval x - p.eval y| ≤ denseEvalLipschitzBound p B * |x - y| := by
  have hspec := evalBoundsCoeffs_spec p.coeffs hB hx hy
    0 0 ⟨0, 0⟩ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa [DensePolynomial.eval, evalCoeffs, denseEvalLipschitzBound,
    denseHornerBounds] using hspec.2.2.2.2

/-- Coefficient sum bounding absolute evaluation on `|x| ≤ B`. -/
def evalAbsBound (p : Polynomial ℚ) (B : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * B ^ i

theorem evalAbsBound_nonneg (p : Polynomial ℚ) {B : ℚ} (hB : 0 ≤ B) :
    0 ≤ evalAbsBound p B := by
  apply Finset.sum_nonneg
  intro i hi
  positivity

/-- The finite coefficient sum bounds evaluation at every rational point in
the displayed symmetric interval. -/
theorem abs_eval_le_evalAbsBound (p : Polynomial ℚ) {B x : ℚ}
    (_hB : 0 ≤ B) (hx : |x| ≤ B) :
    |p.eval x| ≤ evalAbsBound p B := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    |∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i| ≤
        ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i * x ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * B ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      gcongr
    _ = evalAbsBound p B := rfl

/-- Coefficient sum bounding the evaluation difference per unit displacement
on `[-B,B]`. -/
def evalLipschitzBound (p : Polynomial ℚ) (B : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    |p.coeff i| * (i : ℚ) * B ^ (i - 1)

theorem evalLipschitzBound_nonneg (p : Polynomial ℚ) {B : ℚ}
    (hB : 0 ≤ B) : 0 ≤ evalLipschitzBound p B := by
  apply Finset.sum_nonneg
  intro i hi
  positivity

/-- Direct coefficient proof of the rational Lipschitz estimate. -/
theorem abs_eval_sub_eval_le (p : Polynomial ℚ) {B x y : ℚ}
    (_hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |p.eval x - p.eval y| ≤ evalLipschitzBound p B * |x - y| := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range,
    ← Finset.sum_sub_distrib, evalLipschitzBound, Finset.sum_mul]
  calc
    |∑ i ∈ Finset.range (p.natDegree + 1),
        (p.coeff i * x ^ i - p.coeff i * y ^ i)| ≤
        ∑ i ∈ Finset.range (p.natDegree + 1),
          |p.coeff i * x ^ i - p.coeff i * y ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
        (|p.coeff i| * (i : ℚ) * B ^ (i - 1)) * |x - y| := by
      apply Finset.sum_le_sum
      intro i hi
      have hmaxNonneg : 0 ≤ max |x| |y| :=
        (abs_nonneg x).trans (le_max_left _ _)
      have hmax : max |x| |y| ≤ B := max_le hx hy
      have hpow : max |x| |y| ^ (i - 1) ≤ B ^ (i - 1) :=
        pow_le_pow_left₀ hmaxNonneg hmax _
      rw [← mul_sub, abs_mul]
      calc
        |p.coeff i| * |x ^ i - y ^ i| ≤
            |p.coeff i| *
              (|x - y| * (i : ℚ) * max |x| |y| ^ (i - 1)) :=
          mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le x y i)
            (abs_nonneg _)
        _ ≤ |p.coeff i| *
              (|x - y| * (i : ℚ) * B ^ (i - 1)) := by
          gcongr
        _ = (|p.coeff i| * (i : ℚ) * B ^ (i - 1)) * |x - y| := by
          ring

/-- Dense-polynomial form consumed by the executable Sturm modules. -/
theorem abs_dense_eval_sub_eval_le (p : RatPolynomial) {B x y : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |p.eval x - p.eval y| ≤ evalLipschitzBound p.toPolynomial B * |x - y| := by
  rw [← eval_toPolynomial, ← eval_toPolynomial]
  exact abs_eval_sub_eval_le p.toPolynomial hB hx hy

theorem abs_dense_eval_le_evalAbsBound (p : RatPolynomial) {B x : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |p.eval x| ≤ evalAbsBound p.toPolynomial B := by
  rw [← eval_toPolynomial]
  exact abs_eval_le_evalAbsBound p.toPolynomial hB hx

/-! ## Exact rational Taylor remainder -/

/-- The finite geometric sum representing the first divided difference of
`X^n`.  It is defined at equal arguments as well, so no division or limit is
hidden in the Taylor estimate. -/
def powerDividedDifferenceRat (n : ℕ) (z w : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)

theorem mul_powerDividedDifferenceRat (n : ℕ) (z w : ℚ) :
    (z - w) * powerDividedDifferenceRat n z w = z ^ n - w ^ n := by
  simpa only [powerDividedDifferenceRat] using
    (Commute.all z w).mul_geom_sum₂ n

theorem powerDividedDifferenceRat_self (n : ℕ) (w : ℚ) :
    powerDividedDifferenceRat n w w = (n : ℚ) * w ^ (n - 1) := by
  rw [powerDividedDifferenceRat]
  calc
    ∑ i ∈ Finset.range n, w ^ i * w ^ (n - 1 - i) =
        ∑ _i ∈ Finset.range n, w ^ (n - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add]
      congr 1
      have hin : i < n := Finset.mem_range.mp hi
      omega
    _ = (n : ℚ) * w ^ (n - 1) := by simp [nsmul_eq_mul]

/-- First divided difference of a rational polynomial, as a finite
coefficient sum. -/
def dividedDifferenceRat (p : Polynomial ℚ) (z w : ℚ) : ℚ :=
  p.sum fun n a => a * powerDividedDifferenceRat n z w

@[simp] theorem dividedDifferenceRat_add (p q : Polynomial ℚ) (z w : ℚ) :
    dividedDifferenceRat (p + q) z w =
      dividedDifferenceRat p z w + dividedDifferenceRat q z w := by
  rw [dividedDifferenceRat, Polynomial.sum_add_index]
  · rfl
  · intro n
    simp
  · intro n a b
    rw [add_mul]

@[simp] theorem dividedDifferenceRat_monomial (n : ℕ) (a z w : ℚ) :
    dividedDifferenceRat (Polynomial.monomial n a) z w =
      a * powerDividedDifferenceRat n z w := by
  simp [dividedDifferenceRat]

theorem eval_sub_eq_mul_dividedDifferenceRat (p : Polynomial ℚ) (z w : ℚ) :
    p.eval z - p.eval w = (z - w) * dividedDifferenceRat p z w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval_add, Polynomial.eval_add, dividedDifferenceRat_add]
      calc
        p.eval z + q.eval z - (p.eval w + q.eval w) =
            (p.eval z - p.eval w) + (q.eval z - q.eval w) := by ring
        _ = (z - w) * dividedDifferenceRat p z w +
            (z - w) * dividedDifferenceRat q z w := by rw [hp, hq]
        _ = (z - w) *
            (dividedDifferenceRat p z w + dividedDifferenceRat q z w) := by ring
  | monomial n a =>
      rw [Polynomial.eval_monomial, Polynomial.eval_monomial,
        dividedDifferenceRat_monomial]
      have hpower := mul_powerDividedDifferenceRat n z w
      calc
        a * z ^ n - a * w ^ n = a * (z ^ n - w ^ n) := by ring
        _ = a * ((z - w) * powerDividedDifferenceRat n z w) := by rw [hpower]
        _ = (z - w) * (a * powerDividedDifferenceRat n z w) := by ring

theorem dividedDifferenceRat_self (p : Polynomial ℚ) (w : ℚ) :
    dividedDifferenceRat p w w = p.derivative.eval w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [dividedDifferenceRat_add, Polynomial.derivative_add,
        Polynomial.eval_add, hp, hq]
  | monomial n a =>
      rw [dividedDifferenceRat_monomial, powerDividedDifferenceRat_self,
        Polynomial.derivative_monomial, Polynomial.eval_monomial]
      ring

/-- A second finite geometric sum factoring the change of the first divided
difference in its first argument. -/
def secondPowerDividedDifferenceRat (n : ℕ) (z w : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n,
    powerDividedDifferenceRat i z w * w ^ (n - 1 - i)

theorem powerDividedDifferenceRat_sub_self (n : ℕ) (z w : ℚ) :
    powerDividedDifferenceRat n z w - powerDividedDifferenceRat n w w =
      (z - w) * secondPowerDividedDifferenceRat n z w := by
  rw [powerDividedDifferenceRat, powerDividedDifferenceRat,
    secondPowerDividedDifferenceRat]
  calc
    (∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)) -
          ∑ i ∈ Finset.range n, w ^ i * w ^ (n - 1 - i) =
        ∑ i ∈ Finset.range n,
          (z ^ i * w ^ (n - 1 - i) - w ^ i * w ^ (n - 1 - i)) := by
      rw [← Finset.sum_sub_distrib]
    _ = ∑ i ∈ Finset.range n,
          (z - w) *
            (powerDividedDifferenceRat i z w * w ^ (n - 1 - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpower := mul_powerDividedDifferenceRat i z w
      calc
        z ^ i * w ^ (n - 1 - i) - w ^ i * w ^ (n - 1 - i) =
            (z ^ i - w ^ i) * w ^ (n - 1 - i) := by ring
        _ = ((z - w) * powerDividedDifferenceRat i z w) *
            w ^ (n - 1 - i) := by rw [hpower]
        _ = (z - w) *
            (powerDividedDifferenceRat i z w * w ^ (n - 1 - i)) := by ring
    _ = (z - w) * ∑ i ∈ Finset.range n,
          powerDividedDifferenceRat i z w * w ^ (n - 1 - i) := by
      rw [Finset.mul_sum]

/-- Exact finite second-order factor of a rational polynomial. -/
def secondDividedDifferenceRat (p : Polynomial ℚ) (z w : ℚ) : ℚ :=
  p.sum fun n a => a * secondPowerDividedDifferenceRat n z w

@[simp] theorem secondDividedDifferenceRat_add
    (p q : Polynomial ℚ) (z w : ℚ) :
    secondDividedDifferenceRat (p + q) z w =
      secondDividedDifferenceRat p z w +
        secondDividedDifferenceRat q z w := by
  rw [secondDividedDifferenceRat, Polynomial.sum_add_index]
  · rfl
  · intro n
    simp
  · intro n a b
    rw [add_mul]

@[simp] theorem secondDividedDifferenceRat_monomial
    (n : ℕ) (a z w : ℚ) :
    secondDividedDifferenceRat (Polynomial.monomial n a) z w =
      a * secondPowerDividedDifferenceRat n z w := by
  simp [secondDividedDifferenceRat]

theorem dividedDifferenceRat_sub_self (p : Polynomial ℚ) (z w : ℚ) :
    dividedDifferenceRat p z w - dividedDifferenceRat p w w =
      (z - w) * secondDividedDifferenceRat p z w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [dividedDifferenceRat_add, dividedDifferenceRat_add,
        secondDividedDifferenceRat_add]
      calc
        dividedDifferenceRat p z w + dividedDifferenceRat q z w -
            (dividedDifferenceRat p w w + dividedDifferenceRat q w w) =
          (dividedDifferenceRat p z w - dividedDifferenceRat p w w) +
            (dividedDifferenceRat q z w - dividedDifferenceRat q w w) := by ring
        _ = (z - w) * secondDividedDifferenceRat p z w +
            (z - w) * secondDividedDifferenceRat q z w := by rw [hp, hq]
        _ = (z - w) * (secondDividedDifferenceRat p z w +
            secondDividedDifferenceRat q z w) := by ring
  | monomial n a =>
      rw [dividedDifferenceRat_monomial, dividedDifferenceRat_monomial,
        secondDividedDifferenceRat_monomial]
      have hpower := powerDividedDifferenceRat_sub_self n z w
      calc
        a * powerDividedDifferenceRat n z w -
            a * powerDividedDifferenceRat n w w =
          a * (powerDividedDifferenceRat n z w -
            powerDividedDifferenceRat n w w) := by ring
        _ = a * ((z - w) * secondPowerDividedDifferenceRat n z w) := by
          rw [hpower]
        _ = (z - w) * (a * secondPowerDividedDifferenceRat n z w) := by ring

/-- Exact first-order Taylor identity over `ℚ`, proved by finite polynomial
identities rather than differentiation or completion. -/
theorem taylor_sub_eq_sq_mul_secondDividedDifferenceRat
    (p : Polynomial ℚ) (z w : ℚ) :
    p.eval z - p.eval w - p.derivative.eval w * (z - w) =
      (z - w) ^ 2 * secondDividedDifferenceRat p z w := by
  rw [eval_sub_eq_mul_dividedDifferenceRat, ← dividedDifferenceRat_self p w]
  have hsecond := dividedDifferenceRat_sub_self p z w
  calc
    (z - w) * dividedDifferenceRat p z w -
        dividedDifferenceRat p w w * (z - w) =
      (z - w) *
        (dividedDifferenceRat p z w - dividedDifferenceRat p w w) := by ring
    _ = (z - w) *
        ((z - w) * secondDividedDifferenceRat p z w) := by rw [hsecond]
    _ = (z - w) ^ 2 * secondDividedDifferenceRat p z w := by ring

/-- Absolute coefficient bound for one first divided-difference monomial on
`[-B,B]`. -/
def powerDividedDifferenceAbsBound (n : ℕ) (B : ℚ) : ℚ :=
  (n : ℚ) * B ^ (n - 1)

theorem powerDividedDifferenceAbsBound_nonneg (n : ℕ) {B : ℚ}
    (hB : 0 ≤ B) : 0 ≤ powerDividedDifferenceAbsBound n B := by
  exact mul_nonneg (by positivity) (pow_nonneg hB _)

theorem abs_powerDividedDifferenceRat_le (n : ℕ) {B z w : ℚ}
    (hB : 0 ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) :
    |powerDividedDifferenceRat n z w| ≤
      powerDividedDifferenceAbsBound n B := by
  rw [powerDividedDifferenceRat]
  calc
    |∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)| ≤
        ∑ i ∈ Finset.range n, |z ^ i * w ^ (n - 1 - i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, B ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      rw [abs_mul, abs_pow, abs_pow]
      calc
        |z| ^ i * |w| ^ (n - 1 - i) ≤
            B ^ i * B ^ (n - 1 - i) := by
          exact mul_le_mul
            (pow_le_pow_left₀ (abs_nonneg z) hz i)
            (pow_le_pow_left₀ (abs_nonneg w) hw (n - 1 - i))
            (pow_nonneg (abs_nonneg w) _)
            (pow_nonneg hB _)
        _ = B ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
    _ = powerDividedDifferenceAbsBound n B := by
      simp [powerDividedDifferenceAbsBound]

/-- Absolute coefficient bound for the second finite geometric sum of one
monomial. -/
def secondPowerDividedDifferenceAbsBound (n : ℕ) (B : ℚ) : ℚ :=
  ∑ i ∈ Finset.range n,
    powerDividedDifferenceAbsBound i B * B ^ (n - 1 - i)

theorem secondPowerDividedDifferenceAbsBound_nonneg (n : ℕ) {B : ℚ}
    (hB : 0 ≤ B) : 0 ≤ secondPowerDividedDifferenceAbsBound n B := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (powerDividedDifferenceAbsBound_nonneg i hB)
    (pow_nonneg hB _)

theorem abs_secondPowerDividedDifferenceRat_le (n : ℕ) {B z w : ℚ}
    (hB : 0 ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) :
    |secondPowerDividedDifferenceRat n z w| ≤
      secondPowerDividedDifferenceAbsBound n B := by
  rw [secondPowerDividedDifferenceRat,
    secondPowerDividedDifferenceAbsBound]
  calc
    |∑ i ∈ Finset.range n,
        powerDividedDifferenceRat i z w * w ^ (n - 1 - i)| ≤
      ∑ i ∈ Finset.range n,
        |powerDividedDifferenceRat i z w * w ^ (n - 1 - i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        powerDividedDifferenceAbsBound i B * B ^ (n - 1 - i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      exact mul_le_mul
        (abs_powerDividedDifferenceRat_le i hB hz hw)
        (pow_le_pow_left₀ (abs_nonneg w) hw (n - 1 - i))
        (pow_nonneg (abs_nonneg w) _)
        (powerDividedDifferenceAbsBound_nonneg i hB)

/-- Finite coefficient sum bounding the exact second-order Taylor factor on
`[-B,B]`. -/
def secondDividedDifferenceAbsBound (p : Polynomial ℚ) (B : ℚ) : ℚ :=
  ∑ n ∈ p.support,
    |p.coeff n| * secondPowerDividedDifferenceAbsBound n B

theorem secondDividedDifferenceAbsBound_nonneg (p : Polynomial ℚ) {B : ℚ}
    (hB : 0 ≤ B) : 0 ≤ secondDividedDifferenceAbsBound p B := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (abs_nonneg _)
    (secondPowerDividedDifferenceAbsBound_nonneg n hB)

theorem abs_secondDividedDifferenceRat_le (p : Polynomial ℚ) {B z w : ℚ}
    (hB : 0 ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) :
    |secondDividedDifferenceRat p z w| ≤
      secondDividedDifferenceAbsBound p B := by
  rw [secondDividedDifferenceRat, Polynomial.sum_def,
    secondDividedDifferenceAbsBound]
  calc
    |∑ n ∈ p.support,
        p.coeff n * secondPowerDividedDifferenceRat n z w| ≤
      ∑ n ∈ p.support,
        |p.coeff n * secondPowerDividedDifferenceRat n z w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support,
        |p.coeff n| * secondPowerDividedDifferenceAbsBound n B := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_secondPowerDividedDifferenceRat_le n hB hz hw)
        (abs_nonneg _)

/-- Strictly positive rational Taylor-remainder constant computed from a
finite coefficient list. -/
def rationalTaylorRemainderBound (p : Polynomial ℚ) (B : ℚ) : ℚ :=
  max 1 (secondDividedDifferenceAbsBound p B)

theorem rationalTaylorRemainderBound_pos (p : Polynomial ℚ) (B : ℚ) :
    0 < rationalTaylorRemainderBound p B :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Quadratic Taylor remainder estimate over the rationals.  Both the exact
factor and its bound are finite coefficient computations. -/
theorem abs_taylor_sub_le_rationalTaylorRemainderBound_mul_sq
    (p : Polynomial ℚ) {B z w : ℚ}
    (hB : 0 ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) :
    |p.eval z - p.eval w - p.derivative.eval w * (z - w)| ≤
      rationalTaylorRemainderBound p B * |z - w| ^ 2 := by
  rw [taylor_sub_eq_sq_mul_secondDividedDifferenceRat, abs_mul, abs_pow]
  calc
    |z - w| ^ 2 * |secondDividedDifferenceRat p z w| ≤
        |z - w| ^ 2 * secondDividedDifferenceAbsBound p B :=
      mul_le_mul_of_nonneg_left
        (abs_secondDividedDifferenceRat_le p hB hz hw) (sq_nonneg _)
    _ ≤ |z - w| ^ 2 * rationalTaylorRemainderBound p B := by
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _)
    _ = rationalTaylorRemainderBound p B * |z - w| ^ 2 := by ring

/-! ## Executable second-order Horner scan -/

/-- Value, derivative, and quadratic-remainder bounds propagated by one
high-to-low Horner scan. -/
structure TaylorHornerBounds where
  value : ℚ
  slope : ℚ
  remainder : ℚ
deriving DecidableEq, Repr

def TaylorHornerBounds.step (B : ℚ) (bounds : TaylorHornerBounds)
    (coefficient : ℚ) : TaylorHornerBounds where
  value := bounds.value * B + |coefficient|
  slope := bounds.slope * B + bounds.value
  remainder := bounds.remainder * B + bounds.slope

/-- Numeric automatic-differentiation step matching the polynomial-valued
step in `FTA.DenseDerivative`. -/
def evalDerivativeStep (x : ℚ) (state : ℚ × ℚ) (coefficient : ℚ) : ℚ × ℚ :=
  (state.1 * x + coefficient, state.2 * x + state.1)

def evalDerivativeCoeffs (x : ℚ) (coeffs : List ℚ) : ℚ × ℚ :=
  coeffs.foldl (evalDerivativeStep x) (0, 0)

private theorem evalDerivativeCoeffs_value (x : ℚ) (coeffs : List ℚ) :
    (evalDerivativeCoeffs x coeffs).1 = evalCoeffs x coeffs := by
  rw [evalDerivativeCoeffs, evalCoeffs]
  suffices ∀ (state : ℚ × ℚ) (acc : ℚ), state.1 = acc →
      (coeffs.foldl (evalDerivativeStep x) state).1 =
        coeffs.foldl (fun value coefficient => value * x + coefficient) acc by
    exact this (0, 0) 0 rfl
  intro state acc hstate
  induction coeffs generalizing state acc with
  | nil => exact hstate
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      simp [evalDerivativeStep, hstate]

private theorem evalDerivativeFold_eq_denseFold (x : ℚ) (coeffs : List ℚ)
    (state : RatPolynomial × RatPolynomial) :
    (coeffs.foldl FTA.DenseDerivative.derivativeStep state).1.eval x =
        (coeffs.foldl (evalDerivativeStep x)
          (state.1.eval x, state.2.eval x)).1 ∧
      (coeffs.foldl FTA.DenseDerivative.derivativeStep state).2.eval x =
        (coeffs.foldl (evalDerivativeStep x)
          (state.1.eval x, state.2.eval x)).2 := by
  induction coeffs generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      have hnext :
          ((FTA.DenseDerivative.derivativeStep state coefficient).1.eval x,
            (FTA.DenseDerivative.derivativeStep state coefficient).2.eval x) =
          evalDerivativeStep x (state.1.eval x, state.2.eval x) coefficient := by
        simp [FTA.DenseDerivative.derivativeStep, evalDerivativeStep]
      have hih := ih (FTA.DenseDerivative.derivativeStep state coefficient)
      rw [hnext] at hih
      exact hih

theorem evalDerivativeCoeffs_derivative (p : RatPolynomial) (x : ℚ) :
    (evalDerivativeCoeffs x p.coeffs).2 = (derivative p).eval x := by
  have hfold := (evalDerivativeFold_eq_denseFold x p.coeffs (0, 0)).2
  simpa [evalDerivativeCoeffs, derivative, derivativeState] using hfold.symm

/-- Executable second-order bounds for a dense polynomial on `[-B,B]`. -/
def denseTaylorHornerBounds (p : RatPolynomial) (B : ℚ) : TaylorHornerBounds :=
  p.coeffs.foldl (TaylorHornerBounds.step B) ⟨0, 0, 0⟩

def denseTaylorHornerRemainderBound (p : RatPolynomial) (B : ℚ) : ℚ :=
  (denseTaylorHornerBounds p B).remainder

/-- Strictly positive executable dense Taylor bound.  The maximum supplies
the positive default needed by radius formulas; the Horner scan is the actual
coefficient bound. -/
def denseTaylorRemainderBound (p : RatPolynomial) (B : ℚ) : ℚ :=
  max 1 (denseTaylorHornerRemainderBound p B)

theorem denseTaylorRemainderBound_pos (p : RatPolynomial) (B : ℚ) :
    0 < denseTaylorRemainderBound p B :=
  zero_lt_one.trans_le (le_max_left _ _)

private theorem taylorBoundsCoeffs_spec (coeffs : List ℚ) {B x y : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (accX : ℚ) (stateY : ℚ × ℚ) (bounds : TaylorHornerBounds)
    (hvalue : 0 ≤ bounds.value) (hslope : 0 ≤ bounds.slope)
    (hremainder : 0 ≤ bounds.remainder)
    (haccX : |accX| ≤ bounds.value)
    (haccY : |stateY.1| ≤ bounds.value)
    (hderivativeY : |stateY.2| ≤ bounds.slope)
    (hresidual :
      |accX - stateY.1 - stateY.2 * (x - y)| ≤
        bounds.remainder * |x - y| ^ 2) :
    let finalX := coeffs.foldl
      (fun value coefficient => value * x + coefficient) accX
    let finalY := coeffs.foldl (evalDerivativeStep y) stateY
    let finalBounds := coeffs.foldl (TaylorHornerBounds.step B) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      0 ≤ finalBounds.remainder ∧
      |finalX| ≤ finalBounds.value ∧
      |finalY.1| ≤ finalBounds.value ∧
      |finalY.2| ≤ finalBounds.slope ∧
      |finalX - finalY.1 - finalY.2 * (x - y)| ≤
        finalBounds.remainder * |x - y| ^ 2 := by
  induction coeffs generalizing accX stateY bounds with
  | nil =>
      exact ⟨hvalue, hslope, hremainder, haccX, haccY,
        hderivativeY, hresidual⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        calc
          |accX * x + coefficient| ≤ |accX * x| + |coefficient| :=
            abs_add_le _ _
          _ = |accX| * |x| + |coefficient| := by rw [abs_mul]
          _ ≤ bounds.value * B + |coefficient| := by gcongr
      · dsimp [TaylorHornerBounds.step, evalDerivativeStep]
        calc
          |stateY.1 * y + coefficient| ≤
              |stateY.1 * y| + |coefficient| := abs_add_le _ _
          _ = |stateY.1| * |y| + |coefficient| := by rw [abs_mul]
          _ ≤ bounds.value * B + |coefficient| := by gcongr
      · dsimp [TaylorHornerBounds.step, evalDerivativeStep]
        calc
          |stateY.2 * y + stateY.1| ≤
              |stateY.2 * y| + |stateY.1| := abs_add_le _ _
          _ = |stateY.2| * |y| + |stateY.1| := by rw [abs_mul]
          _ ≤ bounds.slope * B + bounds.value := by gcongr
      · dsimp only [evalDerivativeStep, TaylorHornerBounds.step]
        have hidentity :
            (accX * x + coefficient) - (stateY.1 * y + coefficient) -
                (stateY.2 * y + stateY.1) * (x - y) =
              x * (accX - stateY.1 - stateY.2 * (x - y)) +
                stateY.2 * (x - y) ^ 2 := by ring
        rw [hidentity]
        calc
          |x * (accX - stateY.1 - stateY.2 * (x - y)) +
              stateY.2 * (x - y) ^ 2| ≤
            |x * (accX - stateY.1 - stateY.2 * (x - y))| +
              |stateY.2 * (x - y) ^ 2| := abs_add_le _ _
          _ = |x| * |accX - stateY.1 - stateY.2 * (x - y)| +
              |stateY.2| * |x - y| ^ 2 := by
            rw [abs_mul, abs_mul, abs_pow]
          _ ≤ B * (bounds.remainder * |x - y| ^ 2) +
              bounds.slope * |x - y| ^ 2 := by gcongr
          _ = (bounds.remainder * B + bounds.slope) * |x - y| ^ 2 := by
            ring

theorem denseTaylorHornerBounds_nonneg (p : RatPolynomial) {B : ℚ}
    (hB : 0 ≤ B) :
    0 ≤ (denseTaylorHornerBounds p B).value ∧
      0 ≤ (denseTaylorHornerBounds p B).slope ∧
      0 ≤ denseTaylorHornerRemainderBound p B := by
  have hspec := taylorBoundsCoeffs_spec p.coeffs hB
    (x := 0) (y := 0) (by positivity) (by positivity)
    0 (0, 0) ⟨0, 0, 0⟩
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

private theorem taylorHornerBoundsFold_mono (coeffs : List ℚ) {B C : ℚ}
    (hB : 0 ≤ B) (hBC : B ≤ C)
    (boundsB boundsC : TaylorHornerBounds)
    (hvalueB : 0 ≤ boundsB.value) (hslopeB : 0 ≤ boundsB.slope)
    (hremainderB : 0 ≤ boundsB.remainder)
    (hvalueC : 0 ≤ boundsC.value) (hslopeC : 0 ≤ boundsC.slope)
    (hremainderC : 0 ≤ boundsC.remainder)
    (hvalue : boundsB.value ≤ boundsC.value)
    (hslope : boundsB.slope ≤ boundsC.slope)
    (hremainder : boundsB.remainder ≤ boundsC.remainder) :
    let finalB := coeffs.foldl (TaylorHornerBounds.step B) boundsB
    let finalC := coeffs.foldl (TaylorHornerBounds.step C) boundsC
    0 ≤ finalB.value ∧ 0 ≤ finalB.slope ∧ 0 ≤ finalB.remainder ∧
      0 ≤ finalC.value ∧ 0 ≤ finalC.slope ∧ 0 ≤ finalC.remainder ∧
      finalB.value ≤ finalC.value ∧ finalB.slope ≤ finalC.slope ∧
      finalB.remainder ≤ finalC.remainder := by
  have hC : 0 ≤ C := hB.trans hBC
  induction coeffs generalizing boundsB boundsC with
  | nil =>
      exact ⟨hvalueB, hslopeB, hremainderB, hvalueC, hslopeC,
        hremainderC, hvalue, hslope, hremainder⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        positivity
      · dsimp [TaylorHornerBounds.step]
        have hmul : boundsB.value * B ≤ boundsC.value * C := by
          calc
            boundsB.value * B ≤ boundsC.value * B :=
              mul_le_mul_of_nonneg_right hvalue hB
            _ ≤ boundsC.value * C :=
              mul_le_mul_of_nonneg_left hBC hvalueC
        linarith
      · dsimp [TaylorHornerBounds.step]
        have hmul : boundsB.slope * B ≤ boundsC.slope * C := by
          calc
            boundsB.slope * B ≤ boundsC.slope * B :=
              mul_le_mul_of_nonneg_right hslope hB
            _ ≤ boundsC.slope * C :=
              mul_le_mul_of_nonneg_left hBC hslopeC
        linarith
      · dsimp [TaylorHornerBounds.step]
        have hmul : boundsB.remainder * B ≤ boundsC.remainder * C := by
          calc
            boundsB.remainder * B ≤ boundsC.remainder * B :=
              mul_le_mul_of_nonneg_right hremainder hB
            _ ≤ boundsC.remainder * C :=
              mul_le_mul_of_nonneg_left hBC hremainderC
        linarith

/-- The executable quadratic Taylor factor bound is monotone in the
nonnegative ambient radius. -/
theorem denseTaylorHornerRemainderBound_mono (p : RatPolynomial) {B C : ℚ}
    (hB : 0 ≤ B) (hBC : B ≤ C) :
    denseTaylorHornerRemainderBound p B ≤
      denseTaylorHornerRemainderBound p C := by
  have hspec := taylorHornerBoundsFold_mono p.coeffs hB hBC
    ⟨0, 0, 0⟩ ⟨0, 0, 0⟩
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact hspec.2.2.2.2.2.2.2.2

/-- Fully executable dense Taylor bound proved directly from the same Horner
scan used for evaluation and formal differentiation. -/
theorem abs_dense_taylor_sub_le_horner (p : RatPolynomial) {B z w : ℚ}
    (hB : 0 ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) :
    |p.eval z - p.eval w - (derivative p).eval w * (z - w)| ≤
      denseTaylorHornerRemainderBound p B * |z - w| ^ 2 := by
  have hspec := taylorBoundsCoeffs_spec p.coeffs hB hz hw
    0 (0, 0) ⟨0, 0, 0⟩
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hvalue :
      (evalDerivativeCoeffs w p.coeffs).1 = p.eval w := by
    rw [evalDerivativeCoeffs_value, DensePolynomial.eval]
  have hderivative := evalDerivativeCoeffs_derivative p w
  have hresidual := hspec.2.2.2.2.2.2
  change
    |p.eval z - (evalDerivativeCoeffs w p.coeffs).1 -
        (evalDerivativeCoeffs w p.coeffs).2 * (z - w)| ≤
      denseTaylorHornerRemainderBound p B * |z - w| ^ 2 at hresidual
  rw [hvalue, hderivative] at hresidual
  exact hresidual

/-- Public Taylor estimate using the strictly positive executable wrapper. -/
theorem abs_dense_taylor_sub_le (p : RatPolynomial) {B z w : ℚ}
    (hB : 0 ≤ B) (hz : |z| ≤ B) (hw : |w| ≤ B) :
    |p.eval z - p.eval w - (derivative p).eval w * (z - w)| ≤
      denseTaylorRemainderBound p B * |z - w| ^ 2 := by
  exact (abs_dense_taylor_sub_le_horner p hB hz hw).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

/-- A perturbation smaller than the magnitude of a nonzero rational value
cannot cross zero. -/
theorem mul_pos_of_abs_sub_lt_abs_left {x y : ℚ}
    (hxy : |x - y| < |x|) : 0 < x * y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hbound : |x - y| < -x := by simpa [abs_of_neg hx] using hxy
    have hy : y < 0 := by
      have := (abs_lt.mp hbound).1
      linarith
    exact mul_pos_of_neg_of_neg hx hy
  · exact (not_lt_of_ge (abs_nonneg y) (by simpa using hxy)).elim
  · have hbound : |x - y| < x := by simpa [abs_of_pos hx] using hxy
    have hy : 0 < y := by
      have := (abs_lt.mp hbound).2
      linarith
    exact mul_pos hx hy

/-- A number is no farther from zero than from a number of opposite or zero
sign. -/
theorem abs_le_abs_sub_of_mul_nonpos {x y : ℚ} (hxy : x * y ≤ 0) :
    |x| ≤ |x - y| := by
  rcases mul_nonpos_iff.mp hxy with hposneg | hnegpos
  · rw [abs_of_nonneg hposneg.1,
      abs_of_nonneg (sub_nonneg.mpr (hposneg.2.trans hposneg.1))]
    linarith
  · rw [abs_of_nonpos hnegpos.1,
      abs_of_nonpos (sub_nonpos.mpr (hnegpos.1.trans hnegpos.2))]
    linarith

theorem mul_pos_of_mul_pos_left {a b c : ℚ}
    (hab : 0 < a * b) (hac : 0 < a * c) : 0 < b * c := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases mul_pos_iff.mp hac with ⟨-, hc⟩ | ⟨ha', -⟩
    · exact mul_pos hb hc
    · exact (not_lt_of_ge ha.le ha').elim
  · rcases mul_pos_iff.mp hac with ⟨ha', -⟩ | ⟨-, hc⟩
    · exact (not_lt_of_ge ha'.le ha).elim
    · exact mul_pos_of_neg_of_neg hb hc

theorem mul_neg_of_same_sign_transfers {a b c d : ℚ}
    (hab : 0 < a * b) (hcd : 0 < c * d) (hac : a * c < 0) : b * d < 0 := by
  rcases mul_neg_iff.mp hac with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · rcases mul_pos_iff.mp hab with ⟨-, hb⟩ | ⟨ha', -⟩
    · rcases mul_pos_iff.mp hcd with ⟨hc', -⟩ | ⟨-, hd⟩
      · exfalso
        linarith
      · exact mul_neg_of_pos_of_neg hb hd
    · exfalso
      linarith
  · rcases mul_pos_iff.mp hab with ⟨ha', -⟩ | ⟨-, hb⟩
    · exfalso
      linarith
    · rcases mul_pos_iff.mp hcd with ⟨-, hd⟩ | ⟨hc', -⟩
      · exact mul_neg_of_neg_of_pos hb hd
      · exfalso
        linarith

/-- Opposite endpoint signs plus an oriented endpoint difference determine
the two endpoint signs relative to the orienting slope. -/
theorem endpoint_orientation_of_crossing_and_difference
    {lower upper slope : ℚ} (hcrossing : lower * upper < 0)
    (hdifference : 0 < (upper - lower) * slope) :
    lower * slope < 0 ∧ 0 < upper * slope := by
  rcases mul_neg_iff.mp hcrossing with hposneg | hnegpos
  · have hdifferenceNeg : upper - lower < 0 := by linarith [hposneg.1, hposneg.2]
    rcases mul_pos_iff.mp hdifference with hbothPos | hbothNeg
    · exact (not_lt_of_ge hbothPos.1.le hdifferenceNeg).elim
    · exact ⟨mul_neg_of_pos_of_neg hposneg.1 hbothNeg.2,
        mul_pos_of_neg_of_neg hposneg.2 hbothNeg.2⟩
  · have hdifferencePos : 0 < upper - lower := by linarith [hnegpos.1, hnegpos.2]
    rcases mul_pos_iff.mp hdifference with hbothPos | hbothNeg
    · exact ⟨mul_neg_of_neg_of_pos hnegpos.1 hbothPos.2,
        mul_pos hnegpos.2 hbothPos.2⟩
    · exact (not_lt_of_ge hdifferencePos.le hbothNeg.1).elim

/-- A strict coefficient margin certifies that two evaluations have the same
nonzero sign. -/
theorem eval_mul_pos_of_lipschitz_margin (p : Polynomial ℚ) {B x y : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hmargin : evalLipschitzBound p B * |x - y| < |p.eval x|) :
    0 < p.eval x * p.eval y := by
  apply mul_pos_of_abs_sub_lt_abs_left
  exact (abs_eval_sub_eval_le p hB hx hy).trans_lt hmargin

/-- Maximum endpoint magnitude, enlarged to one so every power bound is
nonnegative and nontrivial. -/
def intervalMagnitude (a b : ℚ) : ℚ := max 1 (max |a| |b|)

theorem intervalMagnitude_pos (a b : ℚ) : 0 < intervalMagnitude a b :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem abs_le_intervalMagnitude {a b t : ℚ} (hat : a ≤ t) (htb : t ≤ b) :
    |t| ≤ intervalMagnitude a b := by
  apply (abs_le.mpr ?_).trans (le_max_right _ _)
  constructor
  · calc
      -max |a| |b| ≤ -|a| := neg_le_neg (le_max_left _ _)
      _ ≤ a := neg_abs_le a
      _ ≤ t := hat
  · calc
      t ≤ b := htb
      _ ≤ |b| := le_abs_self b
      _ ≤ max |a| |b| := le_max_right _ _

/-- Farthest endpoint distance from a sample point. -/
def intervalRadius (a b sample : ℚ) : ℚ :=
  max |sample - a| |sample - b|

/-- A nested interval has no larger symmetric endpoint magnitude. -/
theorem intervalMagnitude_mono_of_nested {a b c d : ℚ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    intervalMagnitude c d ≤ intervalMagnitude a b := by
  apply max_le
  · exact le_max_left _ _
  · apply max_le
    · exact abs_le_intervalMagnitude hac (hcd.trans hdb)
    · exact abs_le_intervalMagnitude (hac.trans hcd) hdb

theorem abs_sample_sub_le_intervalRadius {a b sample t : ℚ}
    (hat : a ≤ t) (htb : t ≤ b) :
    |sample - t| ≤ intervalRadius a b sample := by
  apply abs_le.mpr
  constructor
  · calc
      -intervalRadius a b sample ≤ -|sample - b| := by
        exact neg_le_neg (le_max_right _ _)
      _ ≤ -(b - sample) := by
        rw [abs_sub_comm]
        exact neg_le_neg (le_abs_self (b - sample : ℚ))
      _ ≤ sample - t := by linarith
  · calc
      sample - t ≤ sample - a := by linarith
      _ ≤ |sample - a| := le_abs_self _
      _ ≤ intervalRadius a b sample := le_max_left _ _

/-- A strict endpoint sign crossing forces every interior sample value below
the finite Lipschitz displacement to one of the two endpoints. -/
theorem abs_dense_eval_sample_le_lipschitz_radius_of_endpoint_crossing
    (p : RatPolynomial) {a b sample : ℚ}
    (hab : a < b) (has : a ≤ sample) (hsb : sample ≤ b)
    (hcrossing : p.eval a * p.eval b < 0) :
    |p.eval sample| ≤
      denseEvalLipschitzBound p (intervalMagnitude a b) *
        intervalRadius a b sample := by
  let B := intervalMagnitude a b
  let radius := intervalRadius a b sample
  have hB : 0 ≤ B := (intervalMagnitude_pos a b).le
  have hsampleB : |sample| ≤ B := abs_le_intervalMagnitude has hsb
  have haB : |a| ≤ B := abs_le_intervalMagnitude le_rfl hab.le
  have hbB : |b| ≤ B := abs_le_intervalMagnitude hab.le le_rfl
  have hslope : 0 ≤ denseEvalLipschitzBound p B :=
    (denseHornerBounds_nonneg p hB).2
  have hchoice :
      p.eval sample * p.eval a ≤ 0 ∨ p.eval sample * p.eval b ≤ 0 := by
    rcases mul_neg_iff.mp hcrossing with habSigns | habSigns
    · by_cases hsample : p.eval sample ≤ 0
      · exact Or.inl (mul_nonpos_of_nonpos_of_nonneg hsample habSigns.1.le)
      · exact Or.inr (mul_nonpos_of_nonneg_of_nonpos
          (lt_of_not_ge hsample).le habSigns.2.le)
    · by_cases hsample : p.eval sample ≤ 0
      · exact Or.inr (mul_nonpos_of_nonpos_of_nonneg hsample habSigns.2.le)
      · exact Or.inl (mul_nonpos_of_nonneg_of_nonpos
          (lt_of_not_ge hsample).le habSigns.1.le)
  rcases hchoice with haOpposite | hbOpposite
  · calc
      |p.eval sample| ≤ |p.eval sample - p.eval a| :=
        abs_le_abs_sub_of_mul_nonpos haOpposite
      _ ≤ denseEvalLipschitzBound p B * |sample - a| :=
        abs_dense_eval_sub_eval_le_dense p hB hsampleB haB
      _ ≤ denseEvalLipschitzBound p B * radius := by
        apply mul_le_mul_of_nonneg_left _ hslope
        exact abs_sample_sub_le_intervalRadius le_rfl hab.le
  · calc
      |p.eval sample| ≤ |p.eval sample - p.eval b| :=
        abs_le_abs_sub_of_mul_nonpos hbOpposite
      _ ≤ denseEvalLipschitzBound p B * |sample - b| :=
        abs_dense_eval_sub_eval_le_dense p hB hsampleB hbB
      _ ≤ denseEvalLipschitzBound p B * radius := by
        apply mul_le_mul_of_nonneg_left _ hslope
        exact abs_sample_sub_le_intervalRadius hab.le le_rfl

/-- If the quadratic Taylor error across an interval is smaller than the
linear midpoint displacement, the endpoint difference has the derivative's
strict sign. -/
theorem endpointDifference_mul_derivative_pos_of_taylor_margin
    (p : RatPolynomial) {a b sample : ℚ}
    (hab : a < b) (has : a ≤ sample) (hsb : sample ≤ b)
    (hmargin :
      2 * denseTaylorHornerRemainderBound p (intervalMagnitude a b) *
          intervalRadius a b sample ^ 2 <
        |(derivative p).eval sample| * (b - a)) :
    0 < (p.eval b - p.eval a) * (derivative p).eval sample := by
  let B := intervalMagnitude a b
  let radius := intervalRadius a b sample
  let slope := (derivative p).eval sample
  let remainder := denseTaylorHornerRemainderBound p B
  have hB : 0 ≤ B := (intervalMagnitude_pos a b).le
  have haB : |a| ≤ B := abs_le_intervalMagnitude le_rfl hab.le
  have hbB : |b| ≤ B := abs_le_intervalMagnitude hab.le le_rfl
  have hsampleB : |sample| ≤ B := abs_le_intervalMagnitude has hsb
  have haRadius : |a - sample| ≤ radius := by
    rw [abs_sub_comm]
    exact abs_sample_sub_le_intervalRadius le_rfl hab.le
  have hbRadius : |b - sample| ≤ radius := by
    rw [abs_sub_comm]
    exact abs_sample_sub_le_intervalRadius hab.le le_rfl
  have hremainder : 0 ≤ remainder := by
    exact (denseTaylorHornerBounds_nonneg p hB).2.2
  have haTaylor := abs_dense_taylor_sub_le_horner p hB haB hsampleB
  have hbTaylor := abs_dense_taylor_sub_le_horner p hB hbB hsampleB
  have haBound :
      |p.eval a - p.eval sample - slope * (a - sample)| ≤
        remainder * radius ^ 2 := by
    apply haTaylor.trans
    apply mul_le_mul_of_nonneg_left _ hremainder
    exact pow_le_pow_left₀ (abs_nonneg _) haRadius 2
  have hbBound :
      |p.eval b - p.eval sample - slope * (b - sample)| ≤
        remainder * radius ^ 2 := by
    apply hbTaylor.trans
    apply mul_le_mul_of_nonneg_left _ hremainder
    exact pow_le_pow_left₀ (abs_nonneg _) hbRadius 2
  have hidentity :
      (p.eval b - p.eval a) - slope * (b - a) =
        (p.eval b - p.eval sample - slope * (b - sample)) -
          (p.eval a - p.eval sample - slope * (a - sample)) := by ring
  have herror :
      |(p.eval b - p.eval a) - slope * (b - a)| ≤
        2 * remainder * radius ^ 2 := by
    rw [hidentity]
    calc
      |(p.eval b - p.eval sample - slope * (b - sample)) -
          (p.eval a - p.eval sample - slope * (a - sample))| ≤
        |p.eval b - p.eval sample - slope * (b - sample)| +
          |p.eval a - p.eval sample - slope * (a - sample)| :=
        abs_sub _ _
      _ ≤ remainder * radius ^ 2 + remainder * radius ^ 2 :=
        add_le_add hbBound haBound
      _ = 2 * remainder * radius ^ 2 := by ring
  have hwidth : 0 < b - a := sub_pos.mpr hab
  have hclose :
      |slope * (b - a) - (p.eval b - p.eval a)| <
        |slope * (b - a)| := by
    rw [abs_sub_comm, abs_mul, abs_of_pos hwidth]
    exact herror.trans_lt (by simpa [B, radius, slope, remainder] using hmargin)
  have hproduct :
      0 < (slope * (b - a)) * (p.eval b - p.eval a) :=
    mul_pos_of_abs_sub_lt_abs_left hclose
  have hfactored :
      0 < (b - a) * (slope * (p.eval b - p.eval a)) := by
    nlinarith
  rcases mul_pos_iff.mp hfactored with hpositive | hnegative
  · simpa [slope, mul_comm] using hpositive.2
  · exact (not_lt_of_ge hwidth.le hnegative.1).elim

/-- A single exact sample plus a coefficient margin certifies one strict sign
throughout the whole rational interval. -/
theorem dense_eval_mul_pos_on_interval (p : RatPolynomial)
    {a b sample : ℚ} (has : a ≤ sample) (hsb : sample ≤ b)
    (hmargin : denseEvalLipschitzBound p (intervalMagnitude a b) *
        intervalRadius a b sample < |p.eval sample|) :
    ∀ t : ℚ, a ≤ t → t ≤ b → 0 < p.eval sample * p.eval t := by
  intro t hat htb
  have hB : 0 ≤ intervalMagnitude a b := (intervalMagnitude_pos a b).le
  have hsample := abs_le_intervalMagnitude has hsb
  have ht := abs_le_intervalMagnitude hat htb
  apply mul_pos_of_abs_sub_lt_abs_left
  apply (abs_dense_eval_sub_eval_le_dense p hB hsample ht).trans_lt
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left
      (abs_sample_sub_le_intervalRadius hat htb)
      (denseHornerBounds_nonneg p hB).2)
    hmargin

/-- Positive pointwise exclusion margin computed from a displayed dense
Bézout identity. -/
def coprimeExclusionMargin {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) (B : ℚ) : ℚ :=
  1 / (2 * max 1
    (denseEvalAbsBound certificate.left B +
      denseEvalAbsBound certificate.right B))

theorem coprimeExclusionMargin_pos {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {B : ℚ}
    (_hB : 0 ≤ B) : 0 < coprimeExclusionMargin certificate B := by
  have hmajorant : 0 < max 1
      (denseEvalAbsBound certificate.left B +
        denseEvalAbsBound certificate.right B) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [coprimeExclusionMargin]
  exact div_pos zero_lt_one (mul_pos (by norm_num) hmajorant)

/-- Enlarging the ambient evaluation radius can only decrease the displayed
Bézout exclusion margin. -/
theorem coprimeExclusionMargin_anti {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {B C : ℚ}
    (hB : 0 ≤ B) (hBC : B ≤ C) :
    coprimeExclusionMargin certificate C ≤
      coprimeExclusionMargin certificate B := by
  let majorantB := max 1
    (denseEvalAbsBound certificate.left B +
      denseEvalAbsBound certificate.right B)
  let majorantC := max 1
    (denseEvalAbsBound certificate.left C +
      denseEvalAbsBound certificate.right C)
  have hleft := (denseHornerBounds_mono certificate.left hB hBC).1
  have hright := (denseHornerBounds_mono certificate.right hB hBC).1
  have hmajorant : majorantB ≤ majorantC := by
    exact max_le_max le_rfl (add_le_add hleft hright)
  have hmajorantBPos : 0 < majorantB :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply one_div_le_one_div_of_le (mul_pos (by norm_num) hmajorantBPos)
  exact mul_le_mul_of_nonneg_left hmajorant (by norm_num)

/-- At every bounded rational point, a Bézout-coprime pair cannot have both
evaluations smaller than the displayed coefficient-computable margin. -/
theorem coprimeExclusionMargin_le_max_abs_eval {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {B x : ℚ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) :
    coprimeExclusionMargin certificate B ≤ max |p.eval x| |q.eval x| := by
  let leftBound := denseEvalAbsBound certificate.left B
  let rightBound := denseEvalAbsBound certificate.right B
  let majorant := max 1 (leftBound + rightBound)
  have hleftBound : 0 ≤ leftBound := (denseHornerBounds_nonneg _ hB).1
  have hrightBound : 0 ≤ rightBound := (denseHornerBounds_nonneg _ hB).1
  have hmajorant : 0 < majorant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hleftEval : |certificate.left.eval x| ≤ majorant := by
    apply (abs_dense_eval_le_denseEvalAbsBound certificate.left hB hx).trans
    exact le_trans (le_add_of_nonneg_right hrightBound) (le_max_right _ _)
  have hrightEval : |certificate.right.eval x| ≤ majorant := by
    apply (abs_dense_eval_le_denseEvalAbsBound certificate.right hB hx).trans
    exact le_trans (le_add_of_nonneg_left hleftBound) (le_max_right _ _)
  by_contra hmargin
  have hsmall : max |p.eval x| |q.eval x| <
      coprimeExclusionMargin certificate B := lt_of_not_ge hmargin
  have hpSmall : |p.eval x| < coprimeExclusionMargin certificate B :=
    (le_max_left _ _).trans_lt hsmall
  have hqSmall : |q.eval x| < coprimeExclusionMargin certificate B :=
    (le_max_right _ _).trans_lt hsmall
  have hleftTerm : |certificate.left.eval x| * |p.eval x| <
      majorant * coprimeExclusionMargin certificate B := by
    calc
      |certificate.left.eval x| * |p.eval x| ≤ majorant * |p.eval x| :=
        mul_le_mul_of_nonneg_right hleftEval (abs_nonneg _)
      _ < majorant * coprimeExclusionMargin certificate B :=
        mul_lt_mul_of_pos_left hpSmall hmajorant
  have hrightTerm : |certificate.right.eval x| * |q.eval x| <
      majorant * coprimeExclusionMargin certificate B := by
    calc
      |certificate.right.eval x| * |q.eval x| ≤ majorant * |q.eval x| :=
        mul_le_mul_of_nonneg_right hrightEval (abs_nonneg _)
      _ < majorant * coprimeExclusionMargin certificate B :=
        mul_lt_mul_of_pos_left hqSmall hmajorant
  have hidentity := certificate.identity x
  have honeLe : (1 : ℚ) ≤
      |certificate.left.eval x| * |p.eval x| +
        |certificate.right.eval x| * |q.eval x| := by
    calc
      (1 : ℚ) = |certificate.left.eval x * p.eval x +
          certificate.right.eval x * q.eval x| := by rw [hidentity]; norm_num
      _ ≤ |certificate.left.eval x * p.eval x| +
          |certificate.right.eval x * q.eval x| := abs_add_le _ _
      _ = |certificate.left.eval x| * |p.eval x| +
          |certificate.right.eval x| * |q.eval x| := by rw [abs_mul, abs_mul]
  have htwo : majorant * coprimeExclusionMargin certificate B +
      majorant * coprimeExclusionMargin certificate B = 1 := by
    dsimp [coprimeExclusionMargin, majorant, leftBound, rightBound]
    field_simp
    norm_num
  linarith

/-- Rational midpoint used by the deterministic interval classifier. -/
def midpoint (a b : ℚ) : ℚ := (a + b) / 2

theorem lower_lt_midpoint {a b : ℚ} (hab : a < b) : a < midpoint a b := by
  dsimp [midpoint]
  linarith

theorem midpoint_lt_upper {a b : ℚ} (hab : a < b) : midpoint a b < b := by
  dsimp [midpoint]
  linarith

theorem intervalRadius_midpoint {a b : ℚ} (hab : a ≤ b) :
    intervalRadius a b (midpoint a b) = (b - a) / 2 := by
  have hleft : midpoint a b - a = (b - a) / 2 := by
    dsimp [midpoint]
    ring
  have hright : midpoint a b - b = -((b - a) / 2) := by
    dsimp [midpoint]
    ring
  rw [intervalRadius, hleft, hright, abs_of_nonneg (by positivity), abs_neg,
    abs_of_nonneg (by positivity), max_self]

/-- Finite certificate that one dense polynomial keeps the sample's strict
sign throughout a rational interval. -/
structure IntervalSignCertificate (p : RatPolynomial) (a b : ℚ) where
  sample : ℚ
  lowerLe : a ≤ sample
  leUpper : sample ≤ b
  margin : denseEvalLipschitzBound p (intervalMagnitude a b) *
    intervalRadius a b sample < |p.eval sample|

theorem IntervalSignCertificate.eval_mul_pos {p : RatPolynomial} {a b : ℚ}
    (certificate : IntervalSignCertificate p a b) {t : ℚ}
    (hat : a ≤ t) (htb : t ≤ b) :
    0 < p.eval certificate.sample * p.eval t :=
  dense_eval_mul_pos_on_interval p certificate.lowerLe certificate.leUpper
    certificate.margin t hat htb

theorem IntervalSignCertificate.eval_ne_zero {p : RatPolynomial} {a b : ℚ}
    (certificate : IntervalSignCertificate p a b) {t : ℚ}
    (hat : a ≤ t) (htb : t ≤ b) : p.eval t ≠ 0 := by
  intro hzero
  have hpositive := certificate.eval_mul_pos hat htb
  rw [hzero, mul_zero] at hpositive
  norm_num at hpositive

theorem IntervalSignCertificate.eval_mul_pos_between
    {p : RatPolynomial} {a b : ℚ}
    (certificate : IntervalSignCertificate p a b) {s t : ℚ}
    (has : a ≤ s) (hsb : s ≤ b) (hat : a ≤ t) (htb : t ≤ b) :
    0 < p.eval s * p.eval t := by
  exact mul_pos_of_mul_pos_left
    (certificate.eval_mul_pos has hsb)
    (certificate.eval_mul_pos hat htb)

/-- Explicit positive absolute-value margin carried by a whole-cell sign
certificate. -/
def IntervalSignCertificate.absMargin {p : RatPolynomial} {a b : ℚ}
    (certificate : IntervalSignCertificate p a b) : ℚ :=
  |p.eval certificate.sample| -
    denseEvalLipschitzBound p (intervalMagnitude a b) *
      intervalRadius a b certificate.sample

theorem IntervalSignCertificate.absMargin_pos {p : RatPolynomial} {a b : ℚ}
    (certificate : IntervalSignCertificate p a b) :
    0 < certificate.absMargin := by
  exact sub_pos.mpr certificate.margin

/-- The stored rational margin lower-bounds the absolute value at every
rational point of the certified interval. -/
theorem IntervalSignCertificate.absMargin_le_abs_eval
    {p : RatPolynomial} {a b : ℚ}
    (certificate : IntervalSignCertificate p a b) {t : ℚ}
    (hat : a ≤ t) (htb : t ≤ b) :
    certificate.absMargin ≤ |p.eval t| := by
  let B := intervalMagnitude a b
  let slope := denseEvalLipschitzBound p B
  let radius := intervalRadius a b certificate.sample
  have hB : 0 ≤ B := (intervalMagnitude_pos a b).le
  have hsampleB : |certificate.sample| ≤ B :=
    abs_le_intervalMagnitude certificate.lowerLe certificate.leUpper
  have htB : |t| ≤ B := abs_le_intervalMagnitude hat htb
  have hslope : 0 ≤ slope := (denseHornerBounds_nonneg p hB).2
  have hdistance : |certificate.sample - t| ≤ radius :=
    abs_sample_sub_le_intervalRadius hat htb
  have hdifference : |p.eval certificate.sample - p.eval t| ≤
      slope * radius := by
    exact (abs_dense_eval_sub_eval_le_dense p hB hsampleB htB).trans
      (mul_le_mul_of_nonneg_left hdistance hslope)
  have htriangle : |p.eval certificate.sample| ≤
      |p.eval certificate.sample - p.eval t| + |p.eval t| := by
    calc
      |p.eval certificate.sample| =
          |(p.eval certificate.sample - p.eval t) + p.eval t| := by
        rw [sub_add_cancel]
      _ ≤ |p.eval certificate.sample - p.eval t| + |p.eval t| :=
        abs_add_le _ _
  dsimp only [IntervalSignCertificate.absMargin, B, slope, radius]
  linarith

theorem IntervalSignCertificate.absMargin_sq_le_eval_sq
    {p : RatPolynomial} {a b : ℚ}
    (certificate : IntervalSignCertificate p a b) {t : ℚ}
    (hat : a ≤ t) (htb : t ≤ b) :
    certificate.absMargin ^ 2 ≤ p.eval t ^ 2 := by
  have hlower := certificate.absMargin_le_abs_eval hat htb
  have hmargin := certificate.absMargin_pos.le
  have hsquare := pow_le_pow_left₀ hmargin hlower 2
  simpa [sq_abs] using hsquare

/-- Decidable midpoint classifier for one proper interval sign certificate. -/
def midpointSignCertificate? (p : RatPolynomial) (a b : ℚ) (hab : a < b) :
    Option (IntervalSignCertificate p a b) :=
  if hmargin : denseEvalLipschitzBound p (intervalMagnitude a b) *
      intervalRadius a b (midpoint a b) < |p.eval (midpoint a b)| then
    some
      { sample := midpoint a b
        lowerLe := (lower_lt_midpoint hab).le
        leUpper := (midpoint_lt_upper hab).le
        margin := hmargin }
  else none

/-- Slope majorant used to turn a Bézout pointwise exclusion margin into a
whole-cell sign certificate for at least one member of the pair. -/
def pairSlopeMajorant (p q : RatPolynomial) (a b : ℚ) : ℚ :=
  max 1 (max
    (denseEvalLipschitzBound p (intervalMagnitude a b))
    (denseEvalLipschitzBound q (intervalMagnitude a b)))

/-- The same pair-slope majorant at a fixed ambient magnitude. -/
def ambientPairSlopeMajorant (p q : RatPolynomial) (B : ℚ) : ℚ :=
  max 1 (max (denseEvalLipschitzBound p B)
    (denseEvalLipschitzBound q B))

theorem pairSlopeMajorant_pos (p q : RatPolynomial) (a b : ℚ) :
    0 < pairSlopeMajorant p q a b :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem ambientPairSlopeMajorant_pos (p q : RatPolynomial) (B : ℚ) :
    0 < ambientPairSlopeMajorant p q B :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem pairSlopeMajorant_le_ambient {p q : RatPolynomial} {a b B : ℚ}
    (hsub : intervalMagnitude a b ≤ B) :
    pairSlopeMajorant p q a b ≤ ambientPairSlopeMajorant p q B := by
  have hsubNonneg : 0 ≤ intervalMagnitude a b := (intervalMagnitude_pos a b).le
  have hp := (denseHornerBounds_mono p hsubNonneg hsub).2
  have hq := (denseHornerBounds_mono q hsubNonneg hsub).2
  exact max_le_max le_rfl (max_le_max hp hq)

/-- Explicit cell radius at which a coprime pair cannot have two unresolved
sign events. -/
def coprimeCellRadius {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) (a b : ℚ) : ℚ :=
  coprimeExclusionMargin certificate (intervalMagnitude a b) /
    pairSlopeMajorant p q a b

/-- Root-ambient version of the coprime cell radius. -/
def ambientCoprimeCellRadius {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) (B : ℚ) : ℚ :=
  coprimeExclusionMargin certificate B / ambientPairSlopeMajorant p q B

theorem coprimeCellRadius_pos {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) (a b : ℚ) :
    0 < coprimeCellRadius certificate a b := by
  exact div_pos
    (coprimeExclusionMargin_pos certificate (intervalMagnitude_pos a b).le)
    (pairSlopeMajorant_pos p q a b)

theorem ambientCoprimeCellRadius_pos {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {B : ℚ}
    (hB : 0 ≤ B) : 0 < ambientCoprimeCellRadius certificate B := by
  exact div_pos (coprimeExclusionMargin_pos certificate hB)
    (ambientPairSlopeMajorant_pos p q B)

/-- The ambient radius is conservative for every subinterval whose endpoint
magnitude is bounded by `B`. -/
theorem ambientCoprimeCellRadius_le_cellRadius {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q)
    {a b B : ℚ} (hsub : intervalMagnitude a b ≤ B) :
    ambientCoprimeCellRadius certificate B ≤
      coprimeCellRadius certificate a b := by
  let subB := intervalMagnitude a b
  let subSlope := pairSlopeMajorant p q a b
  let ambientSlope := ambientPairSlopeMajorant p q B
  let subMajorant := max 1
    (denseEvalAbsBound certificate.left subB +
      denseEvalAbsBound certificate.right subB)
  let ambientMajorant := max 1
    (denseEvalAbsBound certificate.left B +
      denseEvalAbsBound certificate.right B)
  have hsubNonneg : 0 ≤ subB := (intervalMagnitude_pos a b).le
  have hleft := (denseHornerBounds_mono certificate.left hsubNonneg hsub).1
  have hright := (denseHornerBounds_mono certificate.right hsubNonneg hsub).1
  have hmajorant : subMajorant ≤ ambientMajorant := by
    exact max_le_max le_rfl (add_le_add hleft hright)
  have hsubMajorantPos : 0 < subMajorant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hexclusion : coprimeExclusionMargin certificate B ≤
      coprimeExclusionMargin certificate subB := by
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) hsubMajorantPos)
    exact mul_le_mul_of_nonneg_left hmajorant (by norm_num)
  have hsubSlopePos : 0 < subSlope := pairSlopeMajorant_pos p q a b
  have hambientSlopePos : 0 < ambientSlope :=
    ambientPairSlopeMajorant_pos p q B
  have hslope : subSlope ≤ ambientSlope :=
    pairSlopeMajorant_le_ambient hsub
  have hsubExclusionNonneg :
      0 ≤ coprimeExclusionMargin certificate subB :=
    (coprimeExclusionMargin_pos certificate hsubNonneg).le
  rw [ambientCoprimeCellRadius, coprimeCellRadius,
    div_le_div_iff₀ hambientSlopePos hsubSlopePos]
  exact mul_le_mul hexclusion hslope hsubSlopePos.le hsubExclusionNonneg

/-- Fixed-ambient majorant for the quotient-weighted unresolved middle
member in one signed Euclidean step. -/
def ambientSignedStepDominanceMajorant (p q : RatPolynomial) (B : ℚ) : ℚ :=
  max 1 (denseEvalLipschitzBound q B *
    denseEvalAbsBound (divMod p q).quotient B)

def ambientSignedStepRadius {p q : RatPolynomial}
    (coprime : FTA.DenseSquarefree.CoprimeCertificate p q) (B : ℚ) : ℚ :=
  min (ambientCoprimeCellRadius coprime.swap B)
    (min (ambientCoprimeCellRadius coprime.signedStep B)
      (coprimeExclusionMargin coprime.signedStep B /
        ambientSignedStepDominanceMajorant p q B))

theorem ambientSignedStepDominanceMajorant_pos (p q : RatPolynomial) (B : ℚ) :
    0 < ambientSignedStepDominanceMajorant p q B :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem ambientSignedStepRadius_pos {p q : RatPolynomial}
    (coprime : FTA.DenseSquarefree.CoprimeCertificate p q) {B : ℚ}
    (hB : 0 ≤ B) : 0 < ambientSignedStepRadius coprime B := by
  apply lt_min
  · exact ambientCoprimeCellRadius_pos coprime.swap hB
  · apply lt_min
    · exact ambientCoprimeCellRadius_pos coprime.signedStep hB
    · exact div_pos (coprimeExclusionMargin_pos coprime.signedStep hB)
        (ambientSignedStepDominanceMajorant_pos p q B)

/-- One ambient radius simultaneously implies both transported Bézout tests
and the quotient-dominance test on every nested cell. -/
theorem signedStep_inequalities_of_ambient_radius {p q : RatPolynomial}
    (coprime : FTA.DenseSquarefree.CoprimeCertificate p q)
    {a b B radius : ℚ} (hsub : intervalMagnitude a b ≤ B)
    (hradiusNonneg : 0 ≤ radius)
    (hradius : radius < ambientSignedStepRadius coprime B) :
    radius < coprimeCellRadius coprime.swap a b ∧
      radius < coprimeCellRadius coprime.signedStep a b ∧
      denseEvalLipschitzBound q (intervalMagnitude a b) * radius *
          denseEvalAbsBound (divMod p q).quotient (intervalMagnitude a b) <
        coprimeExclusionMargin coprime.signedStep (intervalMagnitude a b) := by
  let subB := intervalMagnitude a b
  let dominanceMajorant := ambientSignedStepDominanceMajorant p q B
  have hsubNonneg : 0 ≤ subB := (intervalMagnitude_pos a b).le
  have hB : 0 ≤ B := hsubNonneg.trans hsub
  have hleftAmbient : radius < ambientCoprimeCellRadius coprime.swap B :=
    hradius.trans_le (min_le_left _ _)
  have hrightAmbient : radius < ambientCoprimeCellRadius coprime.signedStep B :=
    hradius.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hleft : radius < coprimeCellRadius coprime.swap a b :=
    hleftAmbient.trans_le
      (ambientCoprimeCellRadius_le_cellRadius coprime.swap hsub)
  have hright : radius < coprimeCellRadius coprime.signedStep a b :=
    hrightAmbient.trans_le
      (ambientCoprimeCellRadius_le_cellRadius coprime.signedStep hsub)
  have hdominanceRadius : radius <
      coprimeExclusionMargin coprime.signedStep B / dominanceMajorant :=
    hradius.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hdominanceMajorant : 0 < dominanceMajorant :=
    ambientSignedStepDominanceMajorant_pos p q B
  have hscaled : dominanceMajorant * radius <
      coprimeExclusionMargin coprime.signedStep B := by
    have := (lt_div_iff₀ hdominanceMajorant).mp hdominanceRadius
    simpa [mul_comm] using this
  have hslope := (denseHornerBounds_mono q hsubNonneg hsub).2
  have hquotient :=
    (denseHornerBounds_mono (divMod p q).quotient hsubNonneg hsub).1
  have hambientSlopeNonneg : 0 ≤ denseEvalLipschitzBound q B :=
    (denseHornerBounds_nonneg q hB).2
  have hquotientNonneg : 0 ≤ denseEvalAbsBound (divMod p q).quotient subB :=
    (denseHornerBounds_nonneg (divMod p q).quotient hsubNonneg).1
  have hfactor :
      denseEvalLipschitzBound q subB *
          denseEvalAbsBound (divMod p q).quotient subB ≤
        dominanceMajorant := by
    apply (mul_le_mul hslope hquotient hquotientNonneg
      hambientSlopeNonneg).trans
    exact le_max_right _ _
  have hexclusion := coprimeExclusionMargin_anti coprime.signedStep
    hsubNonneg hsub
  refine ⟨hleft, hright, ?_⟩
  calc
    denseEvalLipschitzBound q subB * radius *
        denseEvalAbsBound (divMod p q).quotient subB =
      (denseEvalLipschitzBound q subB *
        denseEvalAbsBound (divMod p q).quotient subB) * radius := by ring
    _ ≤ dominanceMajorant * radius :=
      mul_le_mul_of_nonneg_right hfactor hradiusNonneg
    _ < coprimeExclusionMargin coprime.signedStep B := hscaled
    _ ≤ coprimeExclusionMargin coprime.signedStep subB := hexclusion

/-- Ambient radius making a represented nonzero constant pass every nested
midpoint sign test. -/
def ambientConstantSignRadius (p : RatPolynomial) (B : ℚ) : ℚ :=
  |p.eval 0| / max 1 (denseEvalLipschitzBound p B)

theorem ambientConstantSignRadius_pos {p : RatPolynomial} {B : ℚ}
    (hp : p.isZero = false) (hdegree : p.natDegree = 0) :
    0 < ambientConstantSignRadius p B := by
  have heval : p.eval 0 ≠ 0 := by
    rw [FTA.DenseSquarefree.eval_eq_leadingCoeff_of_natDegree_eq_zero
      hp hdegree]
    exact leadingCoeff_ne_zero hp
  exact div_pos (abs_pos.mpr heval)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem constant_midpoint_resolved_of_ambient_radius {p : RatPolynomial}
    {a b B radius : ℚ} (hp : p.isZero = false) (hdegree : p.natDegree = 0)
    (hsub : intervalMagnitude a b ≤ B) (hradiusNonneg : 0 ≤ radius)
    (hradius : radius < ambientConstantSignRadius p B) :
    denseEvalLipschitzBound p (intervalMagnitude a b) * radius <
      |p.eval (midpoint a b)| := by
  let slopeMajorant := max 1 (denseEvalLipschitzBound p B)
  have hsubNonneg : 0 ≤ intervalMagnitude a b := (intervalMagnitude_pos a b).le
  have hslope := (denseHornerBounds_mono p hsubNonneg hsub).2
  have hslopeLe : denseEvalLipschitzBound p (intervalMagnitude a b) ≤
      slopeMajorant := hslope.trans (le_max_right _ _)
  have hslopeMajorantPos : 0 < slopeMajorant :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hscaled : slopeMajorant * radius < |p.eval 0| := by
    have := (lt_div_iff₀ hslopeMajorantPos).mp
      (by simpa [ambientConstantSignRadius, slopeMajorant] using hradius)
    simpa [mul_comm] using this
  calc
    denseEvalLipschitzBound p (intervalMagnitude a b) * radius ≤
        slopeMajorant * radius :=
      mul_le_mul_of_nonneg_right hslopeLe hradiusNonneg
    _ < |p.eval 0| := hscaled
    _ = |p.eval (midpoint a b)| := by
      rw [FTA.DenseSquarefree.eval_eq_leadingCoeff_of_natDegree_eq_zero
          hp hdegree,
        FTA.DenseSquarefree.eval_eq_leadingCoeff_of_natDegree_eq_zero
          hp hdegree]

/-- The finite local Bézout rule: below the displayed radius, decidably select
one member of a coprime pair with a certified constant strict sign on the
cell. -/
def midpointPairSignCertificate {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {a b : ℚ}
    (hab : a < b)
    (hradius : intervalRadius a b (midpoint a b) <
      coprimeCellRadius certificate a b) :
    Sum (IntervalSignCertificate p a b) (IntervalSignCertificate q a b) := by
  have hB : 0 ≤ intervalMagnitude a b := (intervalMagnitude_pos a b).le
  have hmidpoint : |midpoint a b| ≤ intervalMagnitude a b :=
    abs_le_intervalMagnitude (lower_lt_midpoint hab).le (midpoint_lt_upper hab).le
  have hevaluation : coprimeExclusionMargin certificate (intervalMagnitude a b) ≤
      max |p.eval (midpoint a b)| |q.eval (midpoint a b)| :=
    coprimeExclusionMargin_le_max_abs_eval certificate hB hmidpoint
  have hmajorant : 0 < pairSlopeMajorant p q a b :=
    pairSlopeMajorant_pos p q a b
  have hscaled : pairSlopeMajorant p q a b *
      intervalRadius a b (midpoint a b) <
        coprimeExclusionMargin certificate (intervalMagnitude a b) := by
    have hproduct := (lt_div_iff₀ hmajorant).mp
      (show intervalRadius a b (midpoint a b) <
        coprimeExclusionMargin certificate (intervalMagnitude a b) /
          pairSlopeMajorant p q a b by
        simpa [coprimeCellRadius] using hradius)
    simpa [mul_comm] using hproduct
  have hradiusNonneg : 0 ≤ intervalRadius a b (midpoint a b) := by
    dsimp [intervalRadius]
    positivity
  if hp : coprimeExclusionMargin certificate (intervalMagnitude a b) ≤
      |p.eval (midpoint a b)| then
    apply Sum.inl
    refine
      { sample := midpoint a b
        lowerLe := (lower_lt_midpoint hab).le
        leUpper := (midpoint_lt_upper hab).le
        margin := ?_ }
    have hslope : denseEvalLipschitzBound p (intervalMagnitude a b) ≤
        pairSlopeMajorant p q a b := by
      exact (le_max_left _ _).trans (le_max_right _ _)
    exact (mul_le_mul_of_nonneg_right hslope hradiusNonneg).trans_lt
      (hscaled.trans_le hp)
  else
    have hq : coprimeExclusionMargin certificate (intervalMagnitude a b) ≤
        |q.eval (midpoint a b)| := by
      rcases le_max_iff.mp hevaluation with hp' | hq'
      · exact (hp hp').elim
      · exact hq'
    apply Sum.inr
    refine
      { sample := midpoint a b
        lowerLe := (lower_lt_midpoint hab).le
        leUpper := (midpoint_lt_upper hab).le
        margin := ?_ }
    have hslope : denseEvalLipschitzBound q (intervalMagnitude a b) ≤
        pairSlopeMajorant p q a b := by
      exact (le_max_right _ _).trans (le_max_right _ _)
    exact (mul_le_mul_of_nonneg_right hslope hradiusNonneg).trans_lt
      (hscaled.trans_le hq)

/-- Failure of the first midpoint sign test is itself a quantitative smallness
certificate.  Below the pair radius, the second member must therefore carry
the full Bézout exclusion margin. -/
theorem coprimeExclusionMargin_le_abs_second_midpoint_of_first_unresolved
    {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {a b : ℚ}
    (hab : a < b)
    (hradius : intervalRadius a b (midpoint a b) <
      coprimeCellRadius certificate a b)
    (hunresolved : ¬(denseEvalLipschitzBound p (intervalMagnitude a b) *
        intervalRadius a b (midpoint a b) < |p.eval (midpoint a b)|)) :
    coprimeExclusionMargin certificate (intervalMagnitude a b) ≤
      |q.eval (midpoint a b)| := by
  let B := intervalMagnitude a b
  let radius := intervalRadius a b (midpoint a b)
  let majorant := pairSlopeMajorant p q a b
  let exclusion := coprimeExclusionMargin certificate B
  have hB : 0 ≤ B := (intervalMagnitude_pos a b).le
  have hmidpoint : |midpoint a b| ≤ B :=
    abs_le_intervalMagnitude (lower_lt_midpoint hab).le
      (midpoint_lt_upper hab).le
  have hevaluation : exclusion ≤
      max |p.eval (midpoint a b)| |q.eval (midpoint a b)| :=
    coprimeExclusionMargin_le_max_abs_eval certificate hB hmidpoint
  have hmajorant : 0 < majorant := pairSlopeMajorant_pos p q a b
  have hscaled : majorant * radius < exclusion := by
    have hproduct := (lt_div_iff₀ hmajorant).mp
      (show radius < exclusion / majorant by
        simpa [radius, exclusion, majorant, B, coprimeCellRadius] using hradius)
    simpa [mul_comm] using hproduct
  have hradiusNonneg : 0 ≤ radius := by
    dsimp [radius, intervalRadius]
    positivity
  have hpSlope : denseEvalLipschitzBound p B ≤ majorant := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hpSmall : |p.eval (midpoint a b)| < exclusion := by
    have hpLe : |p.eval (midpoint a b)| ≤
        denseEvalLipschitzBound p B * radius := by
      exact le_of_not_gt (by simpa [B, radius] using hunresolved)
    exact hpLe.trans_lt
      ((mul_le_mul_of_nonneg_right hpSlope hradiusNonneg).trans_lt hscaled)
  rcases le_max_iff.mp hevaluation with hp | hq
  · exact (not_lt_of_ge hp hpSmall).elim
  · exact hq

/-- Consequently an unresolved first member forces a successful midpoint sign
margin for the second member. -/
theorem secondMidpointMarginOfFirstUnresolved {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {a b : ℚ}
    (hab : a < b)
    (hradius : intervalRadius a b (midpoint a b) <
      coprimeCellRadius certificate a b)
    (hunresolved : ¬(denseEvalLipschitzBound p (intervalMagnitude a b) *
        intervalRadius a b (midpoint a b) < |p.eval (midpoint a b)|)) :
    denseEvalLipschitzBound q (intervalMagnitude a b) *
        intervalRadius a b (midpoint a b) <
      |q.eval (midpoint a b)| := by
  let B := intervalMagnitude a b
  let radius := intervalRadius a b (midpoint a b)
  let majorant := pairSlopeMajorant p q a b
  let exclusion := coprimeExclusionMargin certificate B
  have hmajorant : 0 < majorant := pairSlopeMajorant_pos p q a b
  have hscaled : majorant * radius < exclusion := by
    have hproduct := (lt_div_iff₀ hmajorant).mp
      (show radius < exclusion / majorant by
        simpa [radius, exclusion, majorant, B, coprimeCellRadius] using hradius)
    simpa [mul_comm] using hproduct
  have hradiusNonneg : 0 ≤ radius := by
    dsimp [radius, intervalRadius]
    positivity
  have hqSlope : denseEvalLipschitzBound q B ≤ majorant := by
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hmargin :=
    coprimeExclusionMargin_le_abs_second_midpoint_of_first_unresolved
      certificate hab hradius hunresolved
  exact (mul_le_mul_of_nonneg_right hqSlope hradiusNonneg).trans_lt
    (hscaled.trans_le (by simpa [B, exclusion] using hmargin))

/-- A crossing of the first member makes the second member carry the full
pointwise Bézout exclusion margin at the midpoint. -/
theorem coprimeExclusionMargin_le_abs_second_midpoint_of_first_crossing
    {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {a b : ℚ}
    (hab : a < b)
    (hradius : intervalRadius a b (midpoint a b) <
      coprimeCellRadius certificate a b)
    (hcrossing : p.eval a * p.eval b < 0) :
    coprimeExclusionMargin certificate (intervalMagnitude a b) ≤
      |q.eval (midpoint a b)| := by
  let B := intervalMagnitude a b
  let radius := intervalRadius a b (midpoint a b)
  let majorant := pairSlopeMajorant p q a b
  let exclusion := coprimeExclusionMargin certificate B
  have hB : 0 ≤ B := (intervalMagnitude_pos a b).le
  have hmidpoint : |midpoint a b| ≤ B :=
    abs_le_intervalMagnitude (lower_lt_midpoint hab).le
      (midpoint_lt_upper hab).le
  have hevaluation : exclusion ≤
      max |p.eval (midpoint a b)| |q.eval (midpoint a b)| :=
    coprimeExclusionMargin_le_max_abs_eval certificate hB hmidpoint
  have hmajorant : 0 < majorant := pairSlopeMajorant_pos p q a b
  have hscaled : majorant * radius < exclusion := by
    have hproduct := (lt_div_iff₀ hmajorant).mp
      (show radius < exclusion / majorant by
        simpa [radius, exclusion, majorant, B, coprimeCellRadius] using hradius)
    simpa [mul_comm] using hproduct
  have hradiusNonneg : 0 ≤ radius := by
    dsimp [radius, intervalRadius]
    positivity
  have hpSlope : denseEvalLipschitzBound p B ≤ majorant := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hpSmall : |p.eval (midpoint a b)| < exclusion := by
    apply (abs_dense_eval_sample_le_lipschitz_radius_of_endpoint_crossing p
      hab (lower_lt_midpoint hab).le (midpoint_lt_upper hab).le
      hcrossing).trans_lt
    exact (mul_le_mul_of_nonneg_right hpSlope hradiusNonneg).trans_lt hscaled
  rcases le_max_iff.mp hevaluation with hp | hq
  · exact (not_lt_of_ge hp hpSmall).elim
  · exact hq

/-- Quantitative form of the same Bézout rule: if the first member changes
sign, then the second member satisfies the explicit midpoint sign margin. -/
theorem secondMidpointMarginOfFirstEndpointCrossing {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {a b : ℚ}
    (hab : a < b)
    (hradius : intervalRadius a b (midpoint a b) <
      coprimeCellRadius certificate a b)
    (hcrossing : p.eval a * p.eval b < 0) :
    denseEvalLipschitzBound q (intervalMagnitude a b) *
        intervalRadius a b (midpoint a b) <
      |q.eval (midpoint a b)| := by
  let B := intervalMagnitude a b
  let radius := intervalRadius a b (midpoint a b)
  let majorant := pairSlopeMajorant p q a b
  let exclusion := coprimeExclusionMargin certificate B
  have hB : 0 ≤ B := (intervalMagnitude_pos a b).le
  have hmidpoint : |midpoint a b| ≤ B :=
    abs_le_intervalMagnitude (lower_lt_midpoint hab).le
      (midpoint_lt_upper hab).le
  have hevaluation : exclusion ≤
      max |p.eval (midpoint a b)| |q.eval (midpoint a b)| :=
    coprimeExclusionMargin_le_max_abs_eval certificate hB hmidpoint
  have hmajorant : 0 < majorant := pairSlopeMajorant_pos p q a b
  have hscaled : majorant * radius < exclusion := by
    have hproduct := (lt_div_iff₀ hmajorant).mp
      (show radius < exclusion / majorant by
        simpa [radius, exclusion, majorant, B, coprimeCellRadius] using hradius)
    simpa [mul_comm] using hproduct
  have hradiusNonneg : 0 ≤ radius := by
    dsimp [radius, intervalRadius]
    positivity
  have hpSlope : denseEvalLipschitzBound p B ≤ majorant := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hqSlope : denseEvalLipschitzBound q B ≤ majorant := by
    exact (le_max_right _ _).trans (le_max_right _ _)
  by_contra hqMargin
  have hqSmall : |q.eval (midpoint a b)| < exclusion := by
    have hqLe : |q.eval (midpoint a b)| ≤
        denseEvalLipschitzBound q B * radius := le_of_not_gt hqMargin
    exact hqLe.trans_lt
      ((mul_le_mul_of_nonneg_right hqSlope hradiusNonneg).trans_lt hscaled)
  have hpLarge : exclusion ≤ |p.eval (midpoint a b)| := by
    rcases le_max_iff.mp hevaluation with hp | hq
    · exact hp
    · exact (not_lt_of_ge hq hqSmall).elim
  have hpMargin : denseEvalLipschitzBound p B * radius <
      |p.eval (midpoint a b)| :=
    (mul_le_mul_of_nonneg_right hpSlope hradiusNonneg).trans_lt
      (hscaled.trans_le hpLarge)
  have hsame := dense_eval_mul_pos_on_interval p
    (lower_lt_midpoint hab).le (midpoint_lt_upper hab).le
    (by simpa [B, radius] using hpMargin) b hab.le le_rfl
  have hsameEndpoints := mul_pos_of_mul_pos_left
    (dense_eval_mul_pos_on_interval p
      (lower_lt_midpoint hab).le (midpoint_lt_upper hab).le
      (by simpa [B, radius] using hpMargin) a le_rfl hab.le)
    hsame
  exact (not_lt_of_ge hsameEndpoints.le hcrossing).elim

/-- If one member of a coprime pair changes sign across a sufficiently small
cell, the finite Bézout selector must return a whole-cell sign certificate for
the other member. -/
def secondSignCertificateOfFirstEndpointCrossing {p q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate p q) {a b : ℚ}
    (hab : a < b)
    (hradius : intervalRadius a b (midpoint a b) <
      coprimeCellRadius certificate a b)
    (hcrossing : p.eval a * p.eval b < 0) :
    IntervalSignCertificate q a b := by
  cases midpointPairSignCertificate certificate hab hradius with
  | inl pStable =>
      have hsame := pStable.eval_mul_pos_between le_rfl hab.le hab.le le_rfl
      exact (not_lt_of_ge hsame.le hcrossing).elim
  | inr qStable => exact qStable

/-- Native regression for the executable Horner scan: on `[-2,2]`, the
polynomial `T² - 2` has value bound six and slope bound four. -/
theorem denseHornerBounds_quadratic_example :
    denseHornerBounds ⟨[1, 0, -2]⟩ 2 = ⟨6, 4⟩ := by
  native_decide

/-- The same scan computes the exact unit quadratic Taylor factor. -/
theorem denseTaylorHornerBounds_quadratic_example :
    denseTaylorHornerBounds ⟨[1, 0, -2]⟩ 2 = ⟨6, 4, 1⟩ := by
  native_decide

end FTA.RationalPolynomialBounds
