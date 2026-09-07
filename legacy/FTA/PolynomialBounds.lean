import CCL.Boxes
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Coprime.Basic

/-!
# Finite polynomial bounds over the Gaussian rationals

This module formalizes the coefficient-arithmetic layer of Sections 1--2 and
Appendix B of *A Finite Constructive Fundamental Theorem of Algebra over the
Gaussian Rationals*.  All bounds are rational expressions over finite sums.
-/

namespace FTA

open CCL CCL.GaussianRat Polynomial
open scoped BigOperators

/-- The coefficient field used by the paper. -/
abbrev QI := CCL.GaussianRat

/-- Finite Bezout data witnessing `gcd(f,f') = 1` (Definition 1.2). -/
structure SquarefreeCert (f : Polynomial QI) where
  U : Polynomial QI
  V : Polynomial QI
  bezout : U * f + V * f.derivative = 1

theorem SquarefreeCert.isCoprime {f : Polynomial QI} (h : SquarefreeCert f) :
    IsCoprime f f.derivative := by
  exact ⟨h.U, h.V, h.bezout⟩

/-- The paper's convention for a primitive polynomial (Definition 1.1). -/
def Primitive (f : Polynomial QI) : Prop := f.Monic ∧ Irreducible f

end FTA

namespace CCL.RatBox

/-- Strict endpoint conditions used for root-isolation boxes. -/
def Proper (B : CCL.RatBox) : Prop :=
  B.xLower < B.xUpper ∧ B.yLower < B.yUpper

end CCL.RatBox

namespace FTA

open CCL CCL.GaussianRat Polynomial
open scoped BigOperators

/-- A rational norm bound for a box, equivalent to taking twice the maximum
of the four squared endpoint coordinates and one. -/
def boxNormBound (B : CCL.RatBox) : ℚ :=
  2 * max (B.coordinateRadius ^ 2) 1

theorem boxNormBound_nonneg (B : CCL.RatBox) : 0 ≤ boxNormBound B := by
  dsimp [boxNormBound]
  positivity

theorem one_le_boxNormBound (B : CCL.RatBox) : 1 ≤ boxNormBound B := by
  dsimp [boxNormBound]
  have h : (1 : ℚ) ≤ max (B.coordinateRadius ^ 2) 1 := le_max_right _ _
  linarith

theorem normSq_le_boxNormBound {B : CCL.RatBox} {z : QI}
    (hz : B.Contains z) : normSq z ≤ boxNormBound B := by
  rcases B.abs_coordinates_le_radius hz with ⟨hre, him⟩
  have hR : 0 ≤ B.coordinateRadius := B.coordinateRadius_nonneg
  have hreSq : z.re ^ 2 ≤ B.coordinateRadius ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg hR] using hre
  have himSq : z.im ^ 2 ≤ B.coordinateRadius ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg hR] using him
  have hmax : B.coordinateRadius ^ 2 ≤ max (B.coordinateRadius ^ 2) 1 :=
    le_max_left _ _
  dsimp [normSq, boxNormBound]
  linarith

/-- Real coordinates commute with a finite Gaussian-rational sum. -/
theorem finsetSum_re {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → QI) :
    (∑ j ∈ s, u j).re = ∑ j ∈ s, (u j).re := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Imaginary coordinates commute with a finite Gaussian-rational sum. -/
theorem finsetSum_im {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → QI) :
    (∑ j ∈ s, u j).im = ∑ j ∈ s, (u j).im := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Finite Cauchy--Schwarz in the exact norm used by the paper, equation (1). -/
theorem normSq_finset_sum_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → QI) :
    normSq (∑ j ∈ s, u j) ≤
      (s.card : ℚ) * ∑ j ∈ s, normSq (u j) := by
  have hreSq : (∑ j ∈ s, (u j).re) ^ 2 ≤
      (s.card : ℚ) * ∑ j ∈ s, (u j).re ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun j => (u j).re) (fun _ => (1 : ℚ))
    simp only [_root_.mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
    exact h.trans_eq (_root_.mul_comm _ _)
  have himSq : (∑ j ∈ s, (u j).im) ^ 2 ≤
      (s.card : ℚ) * ∑ j ∈ s, (u j).im ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun j => (u j).im) (fun _ => (1 : ℚ))
    simp only [_root_.mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
    exact h.trans_eq (_root_.mul_comm _ _)
  rw [normSq, finsetSum_re, finsetSum_im]
  calc
    (∑ j ∈ s, (u j).re) ^ 2 + (∑ j ∈ s, (u j).im) ^ 2 ≤
        (s.card : ℚ) * ∑ j ∈ s, (u j).re ^ 2 +
          (s.card : ℚ) * ∑ j ∈ s, (u j).im ^ 2 := add_le_add hreSq himSq
    _ = (s.card : ℚ) * ∑ j ∈ s, normSq (u j) := by
      simp only [normSq, Finset.mul_sum, mul_add, Finset.sum_add_distrib]

/-- The coefficient-computable right side of Lemma 2.1. -/
def evalBound (p : Polynomial QI) (B : CCL.RatBox) : ℚ :=
  (p.natDegree + 1 : ℕ) *
    ∑ j ∈ Finset.range (p.natDegree + 1),
      normSq (p.coeff j) * boxNormBound B ^ j

theorem evalBound_nonneg (p : Polynomial QI) (B : CCL.RatBox) :
    0 ≤ evalBound p B := by
  dsimp [evalBound]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (normSq_nonneg _) (pow_nonneg (boxNormBound_nonneg B) _)

/-- Lemma 2.1: exact finite evaluation is bounded by a rational coefficient sum. -/
theorem normSq_eval_le_evalBound (p : Polynomial QI) {B : CCL.RatBox} {z : QI}
    (hz : B.Contains z) : normSq (p.eval z) ≤ evalBound p B := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    normSq (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * z ^ j) ≤
        ((Finset.range (p.natDegree + 1)).card : ℚ) *
          ∑ j ∈ Finset.range (p.natDegree + 1), normSq (p.coeff j * z ^ j) :=
      normSq_finset_sum_le _ _
    _ = (p.natDegree + 1 : ℕ) *
          ∑ j ∈ Finset.range (p.natDegree + 1),
            normSq (p.coeff j) * normSq z ^ j := by
      simp only [Finset.card_range, normSq_mul, normSq_pow, Nat.cast_add,
        Nat.cast_one]
    _ ≤ (p.natDegree + 1 : ℕ) *
          ∑ j ∈ Finset.range (p.natDegree + 1),
            normSq (p.coeff j) * boxNormBound B ^ j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (normSq_nonneg _)
      exact pow_le_pow_left₀ (normSq_nonneg z) (normSq_le_boxNormBound hz) j
    _ = evalBound p B := rfl

/-! ## Exact finite difference identities -/

/-- The finite geometric sum `(z^n - w^n) / (z - w)`, defined without
division so that it remains valid when `z = w`. -/
def powerDividedDifferenceValue (n : ℕ) (z w : QI) : QI :=
  ∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)

theorem mul_powerDividedDifferenceValue (n : ℕ) (z w : QI) :
    (z - w) * powerDividedDifferenceValue n z w = z ^ n - w ^ n := by
  simpa only [powerDividedDifferenceValue, GaussianRat.sub_eq_add_neg,
    _root_.sub_eq_add_neg] using
    (Commute.all z w).mul_geom_sum₂ n

theorem powerDividedDifferenceValue_self (n : ℕ) (w : QI) :
    powerDividedDifferenceValue n w w = (n : QI) * w ^ (n - 1) := by
  rw [powerDividedDifferenceValue]
  calc
    ∑ i ∈ Finset.range n, w ^ i * w ^ (n - 1 - i) =
        ∑ _i ∈ Finset.range n, w ^ (n - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add]
      congr 1
      have hin : i < n := Finset.mem_range.mp hi
      omega
    _ = (n : QI) * w ^ (n - 1) := by simp [nsmul_eq_mul]

/-- Equation (2)'s explicit divided difference, as a finite coefficient sum. -/
def dividedDifferenceValue (p : Polynomial QI) (z w : QI) : QI :=
  p.sum fun n a => a * powerDividedDifferenceValue n z w

@[simp] theorem dividedDifferenceValue_add (p q : Polynomial QI) (z w : QI) :
    dividedDifferenceValue (p + q) z w =
      dividedDifferenceValue p z w + dividedDifferenceValue q z w := by
  rw [dividedDifferenceValue, Polynomial.sum_add_index]
  · rfl
  · intro n
    simp
  · intro n a b
    rw [add_mul]

@[simp] theorem dividedDifferenceValue_monomial (n : ℕ) (a z w : QI) :
    dividedDifferenceValue (Polynomial.monomial n a) z w =
      a * powerDividedDifferenceValue n z w := by
  simp [dividedDifferenceValue]

/-- Equation (2), proved coefficient-by-coefficient without division or a
completed complex field. -/
theorem eval_sub_eq_mul_dividedDifferenceValue (p : Polynomial QI) (z w : QI) :
    p.eval z - p.eval w = (z - w) * dividedDifferenceValue p z w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval_add, Polynomial.eval_add,
        dividedDifferenceValue_add]
      calc
        p.eval z + q.eval z - (p.eval w + q.eval w) =
            (p.eval z - p.eval w) + (q.eval z - q.eval w) := by
          simp only [GaussianRat.sub_eq_add_neg]
          ring
        _ = (z - w) * dividedDifferenceValue p z w +
            (z - w) * dividedDifferenceValue q z w := by rw [hp, hq]
        _ = (z - w) *
            (dividedDifferenceValue p z w + dividedDifferenceValue q z w) := by ring
  | monomial n a =>
      rw [Polynomial.eval_monomial, Polynomial.eval_monomial,
        dividedDifferenceValue_monomial]
      have hpower := mul_powerDividedDifferenceValue n z w
      calc
        a * z ^ n - a * w ^ n = a * (z ^ n - w ^ n) := by
          simp only [GaussianRat.sub_eq_add_neg]
          ring
        _ = a * ((z - w) * powerDividedDifferenceValue n z w) := by rw [hpower]
        _ = (z - w) * (a * powerDividedDifferenceValue n z w) := by ring

/-- The divided difference on the diagonal is the exact formal derivative. -/
theorem dividedDifferenceValue_self (p : Polynomial QI) (w : QI) :
    dividedDifferenceValue p w w = p.derivative.eval w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [dividedDifferenceValue_add, Polynomial.derivative_add,
        Polynomial.eval_add, hp, hq]
  | monomial n a =>
      rw [dividedDifferenceValue_monomial,
        powerDividedDifferenceValue_self,
        Polynomial.derivative_monomial, Polynomial.eval_monomial]
      ring

/-- A second finite geometric sum which factors the change of the first
divided difference in its first argument. -/
def secondPowerDividedDifferenceValue (n : ℕ) (z w : QI) : QI :=
  ∑ i ∈ Finset.range n,
    powerDividedDifferenceValue i z w * w ^ (n - 1 - i)

theorem powerDividedDifferenceValue_sub_self (n : ℕ) (z w : QI) :
    powerDividedDifferenceValue n z w - powerDividedDifferenceValue n w w =
      (z - w) * secondPowerDividedDifferenceValue n z w := by
  rw [powerDividedDifferenceValue, powerDividedDifferenceValue,
    secondPowerDividedDifferenceValue]
  calc
    (∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)) -
          ∑ i ∈ Finset.range n, w ^ i * w ^ (n - 1 - i) =
        ∑ i ∈ Finset.range n,
          (z ^ i * w ^ (n - 1 - i) - w ^ i * w ^ (n - 1 - i)) := by
      simp only [GaussianRat.sub_eq_add_neg, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
    _ = ∑ i ∈ Finset.range n,
          (z - w) *
            (powerDividedDifferenceValue i z w * w ^ (n - 1 - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpower := mul_powerDividedDifferenceValue i z w
      calc
        z ^ i * w ^ (n - 1 - i) - w ^ i * w ^ (n - 1 - i) =
            (z ^ i - w ^ i) * w ^ (n - 1 - i) := by
          simp only [GaussianRat.sub_eq_add_neg]
          ring
        _ = ((z - w) * powerDividedDifferenceValue i z w) *
            w ^ (n - 1 - i) := by rw [hpower]
        _ = (z - w) *
            (powerDividedDifferenceValue i z w * w ^ (n - 1 - i)) := by ring
    _ = (z - w) * ∑ i ∈ Finset.range n,
          powerDividedDifferenceValue i z w * w ^ (n - 1 - i) := by
      rw [Finset.mul_sum]

/-- Equation (4)'s finite second-order factor. -/
def secondDividedDifferenceValue (p : Polynomial QI) (z w : QI) : QI :=
  p.sum fun n a => a * secondPowerDividedDifferenceValue n z w

@[simp] theorem secondDividedDifferenceValue_add
    (p q : Polynomial QI) (z w : QI) :
    secondDividedDifferenceValue (p + q) z w =
      secondDividedDifferenceValue p z w +
        secondDividedDifferenceValue q z w := by
  rw [secondDividedDifferenceValue, Polynomial.sum_add_index]
  · rfl
  · intro n
    simp
  · intro n a b
    rw [add_mul]

@[simp] theorem secondDividedDifferenceValue_monomial
    (n : ℕ) (a z w : QI) :
    secondDividedDifferenceValue (Polynomial.monomial n a) z w =
      a * secondPowerDividedDifferenceValue n z w := by
  simp [secondDividedDifferenceValue]

theorem dividedDifferenceValue_sub_self (p : Polynomial QI) (z w : QI) :
    dividedDifferenceValue p z w - dividedDifferenceValue p w w =
      (z - w) * secondDividedDifferenceValue p z w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [dividedDifferenceValue_add, dividedDifferenceValue_add,
        secondDividedDifferenceValue_add]
      calc
        dividedDifferenceValue p z w + dividedDifferenceValue q z w -
            (dividedDifferenceValue p w w + dividedDifferenceValue q w w) =
          (dividedDifferenceValue p z w - dividedDifferenceValue p w w) +
            (dividedDifferenceValue q z w - dividedDifferenceValue q w w) := by
          simp only [GaussianRat.sub_eq_add_neg]
          ring
        _ = (z - w) * secondDividedDifferenceValue p z w +
            (z - w) * secondDividedDifferenceValue q z w := by rw [hp, hq]
        _ = (z - w) * (secondDividedDifferenceValue p z w +
            secondDividedDifferenceValue q z w) := by ring
  | monomial n a =>
      rw [dividedDifferenceValue_monomial,
        dividedDifferenceValue_monomial,
        secondDividedDifferenceValue_monomial]
      have hpower := powerDividedDifferenceValue_sub_self n z w
      calc
        a * powerDividedDifferenceValue n z w -
            a * powerDividedDifferenceValue n w w =
          a * (powerDividedDifferenceValue n z w -
            powerDividedDifferenceValue n w w) := by
          simp only [GaussianRat.sub_eq_add_neg]
          ring
        _ = a * ((z - w) * secondPowerDividedDifferenceValue n z w) := by
          rw [hpower]
        _ = (z - w) * (a * secondPowerDividedDifferenceValue n z w) := by ring

/-- Equation (4): the first-order Taylor residual is exactly a square times
an explicit finite coefficient expression. -/
theorem taylor_sub_eq_sq_mul_secondDividedDifferenceValue
    (p : Polynomial QI) (z w : QI) :
    p.eval z - p.eval w - p.derivative.eval w * (z - w) =
      (z - w) ^ 2 * secondDividedDifferenceValue p z w := by
  rw [eval_sub_eq_mul_dividedDifferenceValue,
    ← dividedDifferenceValue_self p w]
  have hsecond := dividedDifferenceValue_sub_self p z w
  calc
    (z - w) * dividedDifferenceValue p z w -
        dividedDifferenceValue p w w * (z - w) =
      (z - w) *
        (dividedDifferenceValue p z w - dividedDifferenceValue p w w) := by
      simp only [GaussianRat.sub_eq_add_neg]
      ring
    _ = (z - w) *
        ((z - w) * secondDividedDifferenceValue p z w) := by rw [hsecond]
    _ = (z - w) ^ 2 * secondDividedDifferenceValue p z w := by ring

/-! ## Coefficient-computable bounds for the difference identities -/

/-- A rational bound for one finite power divided difference on a box. -/
def powerDividedDifferenceBound (n : ℕ) (B : CCL.RatBox) : ℚ :=
  (n : ℚ) ^ 2 * boxNormBound B ^ (n - 1)

theorem powerDividedDifferenceBound_nonneg (n : ℕ) (B : CCL.RatBox) :
    0 ≤ powerDividedDifferenceBound n B := by
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (boxNormBound_nonneg B) _)

theorem normSq_powerDividedDifferenceValue_le
    (n : ℕ) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (powerDividedDifferenceValue n z w) ≤
      powerDividedDifferenceBound n B := by
  rw [powerDividedDifferenceValue]
  calc
    normSq (∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)) ≤
        (n : ℚ) * ∑ i ∈ Finset.range n,
          normSq (z ^ i * w ^ (n - 1 - i)) := by
      simpa using normSq_finset_sum_le (Finset.range n)
        (fun i => z ^ i * w ^ (n - 1 - i))
    _ = (n : ℚ) * ∑ i ∈ Finset.range n,
          normSq z ^ i * normSq w ^ (n - 1 - i) := by
      simp only [normSq_mul, normSq_pow]
    _ ≤ (n : ℚ) * ∑ _i ∈ Finset.range n,
          boxNormBound B ^ (n - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      calc
        normSq z ^ i * normSq w ^ (n - 1 - i) ≤
            boxNormBound B ^ i * boxNormBound B ^ (n - 1 - i) := by
          exact mul_le_mul
            (pow_le_pow_left₀ (normSq_nonneg z)
              (normSq_le_boxNormBound hz) i)
            (pow_le_pow_left₀ (normSq_nonneg w)
              (normSq_le_boxNormBound hw) (n - 1 - i))
            (pow_nonneg (normSq_nonneg w) _)
            (pow_nonneg (boxNormBound_nonneg B) _)
        _ = boxNormBound B ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
    _ = powerDividedDifferenceBound n B := by
      simp [powerDividedDifferenceBound]
      ring

/-- Exact finite coefficient bound for equation (2)'s divided difference. -/
def dividedDifferenceBound (p : Polynomial QI) (B : CCL.RatBox) : ℚ :=
  (p.support.card : ℚ) *
    ∑ n ∈ p.support,
      normSq (p.coeff n) * powerDividedDifferenceBound n B

theorem dividedDifferenceBound_nonneg (p : Polynomial QI) (B : CCL.RatBox) :
    0 ≤ dividedDifferenceBound p B := by
  dsimp only [dividedDifferenceBound]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (normSq_nonneg _)
    (powerDividedDifferenceBound_nonneg n B)

theorem normSq_dividedDifferenceValue_le (p : Polynomial QI)
    {B : CCL.RatBox} {z w : QI} (hz : B.Contains z) (hw : B.Contains w) :
    normSq (dividedDifferenceValue p z w) ≤ dividedDifferenceBound p B := by
  rw [dividedDifferenceValue, Polynomial.sum_def]
  calc
    normSq (∑ n ∈ p.support,
        p.coeff n * powerDividedDifferenceValue n z w) ≤
      (p.support.card : ℚ) * ∑ n ∈ p.support,
        normSq (p.coeff n * powerDividedDifferenceValue n z w) :=
      normSq_finset_sum_le p.support _
    _ = (p.support.card : ℚ) * ∑ n ∈ p.support,
        normSq (p.coeff n) *
          normSq (powerDividedDifferenceValue n z w) := by
      simp only [normSq_mul]
    _ ≤ (p.support.card : ℚ) * ∑ n ∈ p.support,
        normSq (p.coeff n) * powerDividedDifferenceBound n B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (normSq_powerDividedDifferenceValue_le n hz hw)
        (normSq_nonneg _)
    _ = dividedDifferenceBound p B := rfl

/-- A strictly positive rational Lipschitz constant computed from coefficients
and box endpoints. -/
def lipschitzBound (p : Polynomial QI) (B : CCL.RatBox) : ℚ :=
  max 1 (dividedDifferenceBound p B)

theorem lipschitzBound_pos (p : Polynomial QI) (B : CCL.RatBox) :
    0 < lipschitzBound p B :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Equation (3): the exact finite divided difference supplies a rational
Lipschitz certificate on every rational box. -/
theorem normSq_eval_sub_le_lipschitzBound_mul
    (p : Polynomial QI) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (p.eval z - p.eval w) ≤
      lipschitzBound p B * normSq (z - w) := by
  rw [eval_sub_eq_mul_dividedDifferenceValue, normSq_mul]
  calc
    normSq (z - w) * normSq (dividedDifferenceValue p z w) ≤
        normSq (z - w) * dividedDifferenceBound p B :=
      mul_le_mul_of_nonneg_left
        (normSq_dividedDifferenceValue_le p hz hw)
        (normSq_nonneg _)
    _ ≤ normSq (z - w) * lipschitzBound p B := by
      apply mul_le_mul_of_nonneg_left (le_max_right _ _) (normSq_nonneg _)
    _ = lipschitzBound p B * normSq (z - w) := by ring

/-- A rational bound for the second finite geometric sum of one monomial. -/
def secondPowerDividedDifferenceBound (n : ℕ) (B : CCL.RatBox) : ℚ :=
  (n : ℚ) * ∑ i ∈ Finset.range n,
    powerDividedDifferenceBound i B * boxNormBound B ^ (n - 1 - i)

theorem secondPowerDividedDifferenceBound_nonneg
    (n : ℕ) (B : CCL.RatBox) :
    0 ≤ secondPowerDividedDifferenceBound n B := by
  dsimp only [secondPowerDividedDifferenceBound]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (powerDividedDifferenceBound_nonneg i B)
    (pow_nonneg (boxNormBound_nonneg B) _)

theorem normSq_secondPowerDividedDifferenceValue_le
    (n : ℕ) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (secondPowerDividedDifferenceValue n z w) ≤
      secondPowerDividedDifferenceBound n B := by
  rw [secondPowerDividedDifferenceValue]
  calc
    normSq (∑ i ∈ Finset.range n,
        powerDividedDifferenceValue i z w * w ^ (n - 1 - i)) ≤
      (n : ℚ) * ∑ i ∈ Finset.range n,
        normSq (powerDividedDifferenceValue i z w * w ^ (n - 1 - i)) := by
      simpa using normSq_finset_sum_le (Finset.range n)
        (fun i => powerDividedDifferenceValue i z w * w ^ (n - 1 - i))
    _ = (n : ℚ) * ∑ i ∈ Finset.range n,
        normSq (powerDividedDifferenceValue i z w) *
          normSq w ^ (n - 1 - i) := by
      simp only [normSq_mul, normSq_pow]
    _ ≤ (n : ℚ) * ∑ i ∈ Finset.range n,
        powerDividedDifferenceBound i B *
          boxNormBound B ^ (n - 1 - i) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact normSq_powerDividedDifferenceValue_le i hz hw
      · exact pow_le_pow_left₀ (normSq_nonneg w)
          (normSq_le_boxNormBound hw) _
      · exact pow_nonneg (normSq_nonneg w) _
      · exact powerDividedDifferenceBound_nonneg i B
    _ = secondPowerDividedDifferenceBound n B := rfl

/-- Exact finite coefficient bound for equation (4)'s second-order factor. -/
def secondDividedDifferenceBound (p : Polynomial QI) (B : CCL.RatBox) : ℚ :=
  (p.support.card : ℚ) *
    ∑ n ∈ p.support,
      normSq (p.coeff n) * secondPowerDividedDifferenceBound n B

theorem secondDividedDifferenceBound_nonneg
    (p : Polynomial QI) (B : CCL.RatBox) :
    0 ≤ secondDividedDifferenceBound p B := by
  dsimp only [secondDividedDifferenceBound]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (normSq_nonneg _)
    (secondPowerDividedDifferenceBound_nonneg n B)

theorem normSq_secondDividedDifferenceValue_le (p : Polynomial QI)
    {B : CCL.RatBox} {z w : QI} (hz : B.Contains z) (hw : B.Contains w) :
    normSq (secondDividedDifferenceValue p z w) ≤
      secondDividedDifferenceBound p B := by
  rw [secondDividedDifferenceValue, Polynomial.sum_def]
  calc
    normSq (∑ n ∈ p.support,
        p.coeff n * secondPowerDividedDifferenceValue n z w) ≤
      (p.support.card : ℚ) * ∑ n ∈ p.support,
        normSq (p.coeff n * secondPowerDividedDifferenceValue n z w) :=
      normSq_finset_sum_le p.support _
    _ = (p.support.card : ℚ) * ∑ n ∈ p.support,
        normSq (p.coeff n) *
          normSq (secondPowerDividedDifferenceValue n z w) := by
      simp only [normSq_mul]
    _ ≤ (p.support.card : ℚ) * ∑ n ∈ p.support,
        normSq (p.coeff n) * secondPowerDividedDifferenceBound n B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (normSq_secondPowerDividedDifferenceValue_le n hz hw)
        (normSq_nonneg _)
    _ = secondDividedDifferenceBound p B := rfl

/-- A strictly positive rational Taylor-remainder constant computed from the
finite coefficient list and rational box. -/
def taylorRemainderBound (p : Polynomial QI) (B : CCL.RatBox) : ℚ :=
  max 1 (secondDividedDifferenceBound p B)

theorem taylorRemainderBound_pos (p : Polynomial QI) (B : CCL.RatBox) :
    0 < taylorRemainderBound p B :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Equation (5): the exact second-order factor supplies the rational
quadratic Taylor remainder bound used by the local extraction proof. -/
theorem normSq_taylor_sub_le_taylorRemainderBound_mul_sq
    (p : Polynomial QI) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w) :
    normSq (p.eval z - p.eval w - p.derivative.eval w * (z - w)) ≤
      taylorRemainderBound p B * normSq (z - w) ^ 2 := by
  rw [taylor_sub_eq_sq_mul_secondDividedDifferenceValue,
    normSq_mul, normSq_pow]
  calc
    normSq (z - w) ^ 2 * normSq (secondDividedDifferenceValue p z w) ≤
        normSq (z - w) ^ 2 * secondDividedDifferenceBound p B :=
      mul_le_mul_of_nonneg_left
        (normSq_secondDividedDifferenceValue_le p hz hw)
        (sq_nonneg _)
    _ ≤ normSq (z - w) ^ 2 * taylorRemainderBound p B := by
      apply mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _)
    _ = taylorRemainderBound p B * normSq (z - w) ^ 2 := by ring

/-- A strict finite Lipschitz margin certifies that evaluation cannot vanish
at the compared point.  This is the constant-path dominance test used in the
protected-strip and small-box arguments. -/
theorem eval_ne_zero_of_lipschitzBound_mul_lt
    (p : Polynomial QI) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w)
    (hmargin : lipschitzBound p B * normSq (z - w) < normSq (p.eval w)) :
    p.eval z ≠ 0 := by
  intro hzero
  have hbound := normSq_eval_sub_le_lipschitzBound_mul p hz hw
  have heq : p.eval z - p.eval w = -p.eval w := by
    rw [hzero, GaussianRat.zero_sub]
  rw [heq, normSq_neg] at hbound
  linarith

/-- Algebraic rearrangement of the affine first-order expression centered at
the rational point `w`. -/
theorem eval_sub_affineLinearization (p : Polynomial QI) (z w : QI) :
    p.eval z - (p.eval w + p.derivative.eval w * (z - w)) =
      p.eval z - p.eval w - p.derivative.eval w * (z - w) := by
  simp only [GaussianRat.sub_eq_add_neg]
  ring

/-- A strict quadratic remainder margin certifies that the polynomial and its
affine linearization are simultaneously nonzero at the tested point. -/
theorem eval_ne_zero_of_taylorRemainderBound_mul_sq_lt
    (p : Polynomial QI) {B : CCL.RatBox} {z w : QI}
    (hz : B.Contains z) (hw : B.Contains w)
    (hmargin : taylorRemainderBound p B * normSq (z - w) ^ 2 <
      normSq (p.eval w + p.derivative.eval w * (z - w))) :
    p.eval z ≠ 0 := by
  intro hzero
  have hbound := normSq_taylor_sub_le_taylorRemainderBound_mul_sq p hz hw
  rw [← eval_sub_affineLinearization] at hbound
  have heq : p.eval z - (p.eval w + p.derivative.eval w * (z - w)) =
      -(p.eval w + p.derivative.eval w * (z - w)) := by
    rw [hzero, GaussianRat.zero_sub]
  rw [heq, normSq_neg] at hbound
  linarith

/-- Evaluation bounds enlarged to at least one, as in equation (6). -/
def evalMajorant (p : Polynomial QI) (B : CCL.RatBox) : ℚ :=
  max 1 (evalBound p B)

theorem one_le_evalMajorant (p : Polynomial QI) (B : CCL.RatBox) :
    1 ≤ evalMajorant p B := le_max_left _ _

theorem normSq_eval_le_evalMajorant (p : Polynomial QI) {B : CCL.RatBox} {z : QI}
    (hz : B.Contains z) : normSq (p.eval z) ≤ evalMajorant p B :=
  (normSq_eval_le_evalBound p hz).trans (le_max_right _ _)

/-- The explicit reciprocal scan bound in Lemma 2.2. -/
theorem reciprocal_lt_nat_ratio (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (1 : ℚ) / (B + 1 : ℕ) < (A : ℚ) / (B : ℕ) := by
  rw [div_lt_div_iff₀ (by positivity : (0 : ℚ) < (B + 1 : ℕ))
    (by positivity : (0 : ℚ) < (B : ℕ))]
  norm_num
  exact_mod_cast (show B < A * (B + 1) by nlinarith)

def derivativeThreshold {f : Polynomial QI} (h : SquarefreeCert f)
    (B : CCL.RatBox) : ℚ :=
  1 / (8 * evalMajorant h.U B)

def derivativeMargin {f : Polynomial QI} (h : SquarefreeCert f)
    (B : CCL.RatBox) : ℚ :=
  1 / (4 * evalMajorant h.V B)

theorem derivativeThreshold_pos {f : Polynomial QI} (h : SquarefreeCert f)
    (B : CCL.RatBox) : 0 < derivativeThreshold h B := by
  dsimp [derivativeThreshold]
  exact div_pos zero_lt_one
    (mul_pos (by norm_num) (zero_lt_one.trans_le (one_le_evalMajorant h.U B)))

theorem derivativeMargin_pos {f : Polynomial QI} (h : SquarefreeCert f)
    (B : CCL.RatBox) : 0 < derivativeMargin h B := by
  dsimp [derivativeMargin]
  exact div_pos zero_lt_one
    (mul_pos (by norm_num) (zero_lt_one.trans_le (one_le_evalMajorant h.V B)))

/-- Lemma 2.3: the finite Bezout certificate turns a small residual into an
explicit positive derivative margin. -/
theorem derivative_margin_of_small_residual {f : Polynomial QI}
    (h : SquarefreeCert f) (B : CCL.RatBox) {z : QI} (hz : B.Contains z)
    (hsmall : normSq (f.eval z) ≤ derivativeThreshold h B) :
    derivativeMargin h B ≤ normSq (f.derivative.eval z) := by
  let MU := evalMajorant h.U B
  let MV := evalMajorant h.V B
  let fu := h.U.eval z
  let fv := h.V.eval z
  let fz := f.eval z
  let dfz := f.derivative.eval z
  have hMU : 1 ≤ MU := one_le_evalMajorant h.U B
  have hMV : 1 ≤ MV := one_le_evalMajorant h.V B
  have hU : normSq fu ≤ MU := normSq_eval_le_evalMajorant h.U hz
  have hV : normSq fv ≤ MV := normSq_eval_le_evalMajorant h.V hz
  have hbez : fu * fz + fv * dfz = 1 := by
    have heval := congrArg (Polynomial.eval z) h.bezout
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] using heval
  have hone : 1 ≤ 2 * (normSq fu * normSq fz + normSq fv * normSq dfz) := by
    calc
      1 = normSq (fu * fz + fv * dfz) := by rw [hbez, normSq_one]
      _ ≤ 2 * (normSq (fu * fz) + normSq (fv * dfz)) :=
        normSq_add_le_two _ _
      _ = 2 * (normSq fu * normSq fz + normSq fv * normSq dfz) := by
        rw [normSq_mul, normSq_mul]
  have hmain : 1 ≤ 2 * (MU * normSq fz + MV * normSq dfz) := by
    refine hone.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add
      (mul_le_mul_of_nonneg_right hU (normSq_nonneg fz))
      (mul_le_mul_of_nonneg_right hV (normSq_nonneg dfz))
  have hMUpos : 0 < MU := zero_lt_one.trans_le hMU
  have hMVpos : 0 < MV := zero_lt_one.trans_le hMV
  have hfirst : 2 * MU * normSq fz ≤ 1 / 4 := by
    calc
      2 * MU * normSq fz ≤ 2 * MU * derivativeThreshold h B := by
        gcongr
      _ = 1 / 4 := by
        change 2 * MU * (1 / (8 * MU)) = 1 / 4
        field_simp [ne_of_gt hMUpos]
        norm_num
  have hsecond : (3 : ℚ) / 4 ≤ 2 * MV * normSq dfz := by
    nlinarith
  have heta : 2 * MV * derivativeMargin h B = 1 / 2 := by
    change 2 * MV * (1 / (4 * MV)) = 1 / 2
    field_simp [ne_of_gt hMVpos]
    norm_num
  have hscaled : (2 * MV) * derivativeMargin h B ≤
      (2 * MV) * normSq dfz := by
    rw [heta]
    linarith
  exact le_of_mul_le_mul_left hscaled
    (mul_pos (by norm_num : (0 : ℚ) < 2) hMVpos)

/-! ## Rational Newton-center consequence -/

/-- Exact norm of the rational Newton displacement. -/
theorem normSq_newton_displacement {f : Polynomial QI} {a : QI}
    (hderivative : f.derivative.eval a ≠ 0) :
    normSq ((a - f.eval a / f.derivative.eval a) - a) =
      normSq (f.eval a) / normSq (f.derivative.eval a) := by
  have hdisplacement :
      (a - f.eval a / f.derivative.eval a) - a =
        -(f.eval a / f.derivative.eval a) := by
    simp only [GaussianRat.sub_eq_add_neg]
    ring
  rw [hdisplacement, normSq_neg,
    GaussianRat.normSq_div _ _ hderivative]

/-- The small-residual Bézout margin bounds the finite rational Newton step,
which is the numerical conclusion of Lemma 7.2 once nonzero winding has
supplied the small-residual premise. -/
theorem normSq_newton_displacement_le_of_small_residual
    {f : Polynomial QI} (h : SquarefreeCert f) (B : CCL.RatBox) {a : QI}
    (ha : B.Contains a)
    (hsmall : normSq (f.eval a) ≤ derivativeThreshold h B) :
    normSq ((a - f.eval a / f.derivative.eval a) - a) ≤
      normSq (f.eval a) / derivativeMargin h B := by
  have hmargin := derivative_margin_of_small_residual h B ha hsmall
  have heta := derivativeMargin_pos h B
  have hderivativeNorm : 0 < normSq (f.derivative.eval a) :=
    heta.trans_le hmargin
  have hderivative : f.derivative.eval a ≠ 0 := by
    intro hzero
    rw [hzero, normSq_zero] at hderivativeNorm
    exact lt_irrefl 0 hderivativeNorm
  rw [normSq_newton_displacement hderivative]
  exact div_le_div_of_nonneg_left (normSq_nonneg _) heta hmargin

theorem normSq_newton_displacement_le_of_residual_bound
    {f : Polynomial QI} (h : SquarefreeCert f) (B : CCL.RatBox) {a : QI}
    (ha : B.Contains a)
    (hsmall : normSq (f.eval a) ≤ derivativeThreshold h B)
    {residualBound : ℚ} (hresidual : normSq (f.eval a) ≤ residualBound) :
    normSq ((a - f.eval a / f.derivative.eval a) - a) ≤
      residualBound / derivativeMargin h B := by
  exact (normSq_newton_displacement_le_of_small_residual h B ha hsmall).trans
    (div_le_div_of_nonneg_right hresidual
      (derivativeMargin_pos h B).le)

end FTA
