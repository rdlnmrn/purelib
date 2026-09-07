import FTA.DensePolynomialBridge
import Mathlib.RingTheory.Coprime.Basic

/-!
# Executable dense extended Euclidean algorithm

The recursion follows the proved strict remainder-degree descent.  Besides the
gcd candidate it returns two dense Bézout coefficients, and the result type
stores the exact Horner-evaluation identity.  Thus every recursive result is a
finite certificate, not merely an unverified coefficient computation.
-/

namespace FTA.DenseGCD

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial

abbrev RatPolynomial := DensePolynomial ℚ

/-- Output of the executable extended Euclidean algorithm. -/
structure BezoutResult (p q : RatPolynomial) where
  gcd : RatPolynomial
  left : RatPolynomial
  right : RatPolynomial
  polynomialIdentity : gcd.toPolynomial =
    left.toPolynomial * p.toPolynomial + right.toPolynomial * q.toPolynomial
  pFactor : RatPolynomial
  qFactor : RatPolynomial
  pPolynomialIdentity : p.toPolynomial = gcd.toPolynomial * pFactor.toPolynomial
  qPolynomialIdentity : q.toPolynomial = gcd.toPolynomial * qFactor.toPolynomial
  nonzero : p.isZero = false ∨ q.isZero = false → gcd.isZero = false

theorem BezoutResult.identity {p q : RatPolynomial}
    (result : BezoutResult p q) (x : ℚ) :
    result.gcd.eval x = result.left.eval x * p.eval x +
      result.right.eval x * q.eval x := by
  have h := congrArg (Polynomial.eval x) result.polynomialIdentity
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, eval_toPolynomial] using h

theorem BezoutResult.pIdentity {p q : RatPolynomial}
    (result : BezoutResult p q) (x : ℚ) :
    p.eval x = result.gcd.eval x * result.pFactor.eval x := by
  have h := congrArg (Polynomial.eval x) result.pPolynomialIdentity
  simpa only [Polynomial.eval_mul, eval_toPolynomial] using h

theorem BezoutResult.qIdentity {p q : RatPolynomial}
    (result : BezoutResult p q) (x : ℚ) :
    q.eval x = result.gcd.eval x * result.qFactor.eval x := by
  have h := congrArg (Polynomial.eval x) result.qPolynomialIdentity
  simpa only [Polynomial.eval_mul, eval_toPolynomial] using h

/-- Extended Euclidean recursion with Lean-checked strict divisor-degree
descent. -/
def extendedGCD (p q : RatPolynomial) : BezoutResult p q :=
  if _hq : q.isZero then
    { gcd := p.normalize
      left := constant 1
      right := 0
      polynomialIdentity := by
        rw [toPolynomial_normalize, toPolynomial_constant, toPolynomial_zero]
        simp
      pFactor := constant 1
      qFactor := 0
      pPolynomialIdentity := by
        rw [toPolynomial_normalize, toPolynomial_constant]
        simp
      qPolynomialIdentity := by
        have hqZero : q.isZero = true := by simpa using _hq
        rw [(toPolynomial_eq_zero_iff_isZero q).2 hqZero,
          toPolynomial_zero, mul_zero]
      nonzero := by
        intro hnonzero
        have hp : p.isZero = false := by
          rcases hnonzero with hp | hq
          · exact hp
          · have hqZero : q.isZero = true := by simpa using _hq
            simp [hqZero] at hq
        simpa using hp }
  else
    let dm := divMod p q
    let recursiveResult := extendedGCD q dm.remainder
    { gcd := recursiveResult.gcd
      left := recursiveResult.right
      right := recursiveResult.left - recursiveResult.right * dm.quotient
      polynomialIdentity := by
        rw [toPolynomial_sub, toPolynomial_mul]
        calc
          recursiveResult.gcd.toPolynomial =
              recursiveResult.left.toPolynomial * q.toPolynomial +
                recursiveResult.right.toPolynomial * dm.remainder.toPolynomial :=
            recursiveResult.polynomialIdentity
          _ = recursiveResult.right.toPolynomial * p.toPolynomial +
              (recursiveResult.left.toPolynomial -
                recursiveResult.right.toPolynomial * dm.quotient.toPolynomial) *
                  q.toPolynomial := by
            rw [divMod_toPolynomial_equation p q]
            ring
      pFactor := recursiveResult.qFactor +
        recursiveResult.pFactor * dm.quotient
      qFactor := recursiveResult.pFactor
      pPolynomialIdentity := by
        rw [toPolynomial_add, toPolynomial_mul]
        calc
          p.toPolynomial = q.toPolynomial * dm.quotient.toPolynomial +
              dm.remainder.toPolynomial := divMod_toPolynomial_equation p q
          _ = recursiveResult.gcd.toPolynomial *
              (recursiveResult.qFactor.toPolynomial +
                recursiveResult.pFactor.toPolynomial * dm.quotient.toPolynomial) := by
            rw [recursiveResult.pPolynomialIdentity,
              recursiveResult.qPolynomialIdentity]
            ring
      qPolynomialIdentity := recursiveResult.pPolynomialIdentity
      nonzero := by
        intro _
        apply recursiveResult.nonzero
        left
        simpa using _hq }
termination_by q.degreeCount
decreasing_by
  have hqFalse : q.isZero = false := by simpa using _hq
  exact divMod_remainder_degreeCount_lt p q hqFalse

/-- The gcd projection, when Bézout coefficients are not needed by a caller. -/
def gcd (p q : RatPolynomial) : RatPolynomial := (extendedGCD p q).gcd

def leftCoefficient (p q : RatPolynomial) : RatPolynomial :=
  (extendedGCD p q).left

def rightCoefficient (p q : RatPolynomial) : RatPolynomial :=
  (extendedGCD p q).right

def leftFactor (p q : RatPolynomial) : RatPolynomial :=
  (extendedGCD p q).pFactor

def rightFactor (p q : RatPolynomial) : RatPolynomial :=
  (extendedGCD p q).qFactor

/-- Both quotient factors returned by extended Euclid are canonical dense
polynomials. -/
theorem extendedGCD_factors_normalized (p q : RatPolynomial) :
    (extendedGCD p q).pFactor.normalize = (extendedGCD p q).pFactor ∧
      (extendedGCD p q).qFactor.normalize = (extendedGCD p q).qFactor := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rw [extendedGCD]
      split
      · constructor
        · norm_num [DensePolynomial.constant, DensePolynomial.normalize]
        · rfl
      · rename_i hq
        let dm := divMod p q
        have hqFalse : q.isZero = false := by simpa using hq
        have hcount : dm.remainder.degreeCount < n := by
          rw [← hn]
          exact divMod_remainder_degreeCount_lt p q hqFalse
        have hrecursive := ih dm.remainder.degreeCount hcount q dm.remainder rfl
        dsimp only
        exact ⟨normalize_add _ _, hrecursive.1⟩

@[simp] theorem normalize_leftFactor (p q : RatPolynomial) :
    (leftFactor p q).normalize = leftFactor p q :=
  (extendedGCD_factors_normalized p q).1

@[simp] theorem normalize_rightFactor (p q : RatPolynomial) :
    (rightFactor p q).normalize = rightFactor p q :=
  (extendedGCD_factors_normalized p q).2

/-- A symmetric choice of reduced left factor.  The coefficient-list order
selects one Euclidean run for the unordered input pair; equal nonzero inputs
reduce canonically to `1/1`. -/
def symmetricLeftFactor (p q : RatPolynomial) : RatPolynomial :=
  if p = q then constant 1
  else if p.coeffs < q.coeffs then leftFactor p q else rightFactor q p

/-- The matching symmetric right factor. -/
def symmetricRightFactor (p q : RatPolynomial) : RatPolynomial :=
  if p = q then constant 1
  else if p.coeffs < q.coeffs then rightFactor p q else leftFactor q p

/-- The gcd belonging to the coefficient-order-independent quotient pair. -/
def symmetricGCD (p q : RatPolynomial) : RatPolynomial :=
  if p = q then p
  else if p.coeffs < q.coeffs then gcd p q else gcd q p

@[simp] theorem normalize_symmetricLeftFactor (p q : RatPolynomial) :
    (symmetricLeftFactor p q).normalize = symmetricLeftFactor p q := by
  by_cases hpq : p = q
  · simp [symmetricLeftFactor, hpq, DensePolynomial.constant,
      DensePolynomial.normalize]
  · by_cases hcoeffs : p.coeffs < q.coeffs
    · simp [symmetricLeftFactor, hpq, hcoeffs]
    · simp [symmetricLeftFactor, hpq, hcoeffs]

@[simp] theorem normalize_symmetricRightFactor (p q : RatPolynomial) :
    (symmetricRightFactor p q).normalize = symmetricRightFactor p q := by
  by_cases hpq : p = q
  · simp [symmetricRightFactor, hpq, DensePolynomial.constant,
      DensePolynomial.normalize]
  · by_cases hcoeffs : p.coeffs < q.coeffs
    · simp [symmetricRightFactor, hpq, hcoeffs]
    · simp [symmetricRightFactor, hpq, hcoeffs]

theorem symmetricLeftFactor_swap (p q : RatPolynomial) :
    symmetricLeftFactor q p = symmetricRightFactor p q := by
  by_cases hpq : p = q
  · subst q
    simp [symmetricLeftFactor, symmetricRightFactor]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · have hnrev : ¬q.coeffs < p.coeffs := not_lt_of_ge hlt.le
      simp [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hlt, hnrev]
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simp [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hgt,
        hnforward]

theorem symmetricRightFactor_swap (p q : RatPolynomial) :
    symmetricRightFactor q p = symmetricLeftFactor p q := by
  by_cases hpq : p = q
  · subst q
    simp [symmetricLeftFactor, symmetricRightFactor]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · have hnrev : ¬q.coeffs < p.coeffs := not_lt_of_ge hlt.le
      simp [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hlt, hnrev]
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simp [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hgt,
        hnforward]

theorem symmetricGCD_swap (p q : RatPolynomial) :
    symmetricGCD q p = symmetricGCD p q := by
  by_cases hpq : p = q
  · subst q
    simp [symmetricGCD]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · have hnreverse : ¬q.coeffs < p.coeffs := not_lt_of_ge hlt.le
      simp [symmetricGCD, hpq, hqp, hlt, hnreverse]
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simp [symmetricGCD, hpq, hqp, hgt, hnforward]

/-- Exact finite Bézout identity exposed without structure projections. -/
theorem gcd_eval_identity (p q : RatPolynomial) (x : ℚ) :
    (gcd p q).eval x =
      (leftCoefficient p q).eval x * p.eval x +
      (rightCoefficient p q).eval x * q.eval x :=
  (extendedGCD p q).identity x

/-- Sparse specification form of the returned Bézout identity. -/
theorem gcd_toPolynomial_identity (p q : RatPolynomial) :
    (gcd p q).toPolynomial =
      (leftCoefficient p q).toPolynomial * p.toPolynomial +
        (rightCoefficient p q).toPolynomial * q.toPolynomial := by
  exact (extendedGCD p q).polynomialIdentity

/-- The returned gcd candidate is an actual common divisor of the two sparse
specification polynomials. -/
theorem gcd_toPolynomial_dvd_left (p q : RatPolynomial) :
    (gcd p q).toPolynomial ∣ p.toPolynomial := by
  refine ⟨(leftFactor p q).toPolynomial, ?_⟩
  exact (extendedGCD p q).pPolynomialIdentity

theorem leftFactor_toPolynomial_identity (p q : RatPolynomial) :
    p.toPolynomial =
      (gcd p q).toPolynomial * (leftFactor p q).toPolynomial := by
  exact (extendedGCD p q).pPolynomialIdentity

theorem gcd_toPolynomial_dvd_right (p q : RatPolynomial) :
    (gcd p q).toPolynomial ∣ q.toPolynomial := by
  refine ⟨(rightFactor p q).toPolynomial, ?_⟩
  exact (extendedGCD p q).qPolynomialIdentity

theorem rightFactor_toPolynomial_identity (p q : RatPolynomial) :
    q.toPolynomial =
      (gcd p q).toPolynomial * (rightFactor p q).toPolynomial := by
  exact (extendedGCD p q).qPolynomialIdentity

/-- Exact factorization of the left input by the symmetric gcd and its
matching quotient. -/
theorem symmetricLeftFactor_toPolynomial_identity (p q : RatPolynomial) :
    p.toPolynomial =
      (symmetricGCD p q).toPolynomial *
        (symmetricLeftFactor p q).toPolynomial := by
  by_cases hpq : p = q
  · subst q
    simp [symmetricGCD, symmetricLeftFactor]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricGCD, symmetricLeftFactor, hpq, hlt] using
        leftFactor_toPolynomial_identity p q
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricGCD, symmetricLeftFactor, hpq, hqp, hnforward] using
        rightFactor_toPolynomial_identity q p

/-- Exact factorization of the right input by the same symmetric gcd. -/
theorem symmetricRightFactor_toPolynomial_identity (p q : RatPolynomial) :
    q.toPolynomial =
      (symmetricGCD p q).toPolynomial *
        (symmetricRightFactor p q).toPolynomial := by
  by_cases hpq : p = q
  · subst q
    simp [symmetricGCD, symmetricRightFactor]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricGCD, symmetricRightFactor, hpq, hlt] using
        rightFactor_toPolynomial_identity p q
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricGCD, symmetricRightFactor, hpq, hqp, hnforward] using
        leftFactor_toPolynomial_identity q p

theorem symmetricLeftFactor_eval_identity (p q : RatPolynomial) (x : ℚ) :
    p.eval x = (symmetricGCD p q).eval x *
      (symmetricLeftFactor p q).eval x := by
  have h := congrArg (Polynomial.eval x)
    (symmetricLeftFactor_toPolynomial_identity p q)
  simpa [Polynomial.eval_mul, eval_toPolynomial] using h

theorem symmetricRightFactor_eval_identity (p q : RatPolynomial) (x : ℚ) :
    q.eval x = (symmetricGCD p q).eval x *
      (symmetricRightFactor p q).eval x := by
  have h := congrArg (Polynomial.eval x)
    (symmetricRightFactor_toPolynomial_identity p q)
  simpa [Polynomial.eval_mul, eval_toPolynomial] using h

theorem symmetricGCD_isZero_false {p q : RatPolynomial}
    (hnonzero : p.isZero = false ∨ q.isZero = false) :
    (symmetricGCD p q).isZero = false := by
  by_cases hpq : p = q
  · subst q
    rcases hnonzero with hp | hp <;> simpa [symmetricGCD] using hp
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricGCD, hpq, hlt, gcd] using
        (extendedGCD p q).nonzero hnonzero
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricGCD, hpq, hqp, hnforward, gcd] using
        (extendedGCD q p).nonzero hnonzero.symm

theorem symmetricGCD_toPolynomial_dvd_left (p q : RatPolynomial) :
    (symmetricGCD p q).toPolynomial ∣ p.toPolynomial := by
  refine ⟨(symmetricLeftFactor p q).toPolynomial, ?_⟩
  exact symmetricLeftFactor_toPolynomial_identity p q

theorem symmetricGCD_toPolynomial_dvd_right (p q : RatPolynomial) :
    (symmetricGCD p q).toPolynomial ∣ q.toPolynomial := by
  refine ⟨(symmetricRightFactor p q).toPolynomial, ?_⟩
  exact symmetricRightFactor_toPolynomial_identity p q

theorem leftFactor_isZero_false {p q : RatPolynomial} (hp : p.isZero = false) :
    (leftFactor p q).isZero = false := by
  cases hfactor : (leftFactor p q).isZero with
  | false => rfl
  | true =>
      have hfactorZero := (toPolynomial_eq_zero_iff_isZero _).mpr hfactor
      have hpZero : p.toPolynomial = 0 := by
        rw [leftFactor_toPolynomial_identity p q, hfactorZero, mul_zero]
      exact (toPolynomial_ne_zero_of_isZero_false hp hpZero).elim

theorem rightFactor_isZero_false {p q : RatPolynomial} (hq : q.isZero = false) :
    (rightFactor p q).isZero = false := by
  cases hfactor : (rightFactor p q).isZero with
  | false => rfl
  | true =>
      have hfactorZero := (toPolynomial_eq_zero_iff_isZero _).mpr hfactor
      have hqZero : q.toPolynomial = 0 := by
        rw [rightFactor_toPolynomial_identity p q, hfactorZero, mul_zero]
      exact (toPolynomial_ne_zero_of_isZero_false hq hqZero).elim

theorem leftFactor_eval_ne_zero {p q : RatPolynomial} {x : ℚ}
    (hp : p.eval x ≠ 0) : (leftFactor p q).eval x ≠ 0 := by
  intro hfactor
  have hfactor' : (extendedGCD p q).pFactor.eval x = 0 := by
    simpa [leftFactor] using hfactor
  have hidentity := (extendedGCD p q).pIdentity x
  rw [hfactor', mul_zero] at hidentity
  exact hp hidentity

theorem rightFactor_eval_ne_zero {p q : RatPolynomial} {x : ℚ}
    (hq : q.eval x ≠ 0) : (rightFactor p q).eval x ≠ 0 := by
  intro hfactor
  have hfactor' : (extendedGCD p q).qFactor.eval x = 0 := by
    simpa [rightFactor] using hfactor
  have hidentity := (extendedGCD p q).qIdentity x
  rw [hfactor', mul_zero] at hidentity
  exact hq hidentity

theorem symmetricLeftFactor_isZero_false {p q : RatPolynomial}
    (hp : p.isZero = false) : (symmetricLeftFactor p q).isZero = false := by
  by_cases hpq : p = q
  · simp [symmetricLeftFactor, hpq, constant, isZero, DensePolynomial.normalize]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricLeftFactor, hpq, hlt] using leftFactor_isZero_false hp
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricLeftFactor, hpq, hqp, hnforward] using
        rightFactor_isZero_false (p := q) (q := p) hp

theorem symmetricRightFactor_isZero_false {p q : RatPolynomial}
    (hq : q.isZero = false) : (symmetricRightFactor p q).isZero = false := by
  by_cases hpq : p = q
  · simp [symmetricRightFactor, hpq, constant, isZero, DensePolynomial.normalize]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricRightFactor, hpq, hlt] using rightFactor_isZero_false hq
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricRightFactor, hpq, hqp, hnforward] using
        leftFactor_isZero_false (p := q) (q := p) hq

theorem symmetricLeftFactor_eval_ne_zero {p q : RatPolynomial} {x : ℚ}
    (hp : p.eval x ≠ 0) : (symmetricLeftFactor p q).eval x ≠ 0 := by
  by_cases hpq : p = q
  · simp [symmetricLeftFactor, hpq]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricLeftFactor, hpq, hlt] using
        leftFactor_eval_ne_zero (q := q) hp
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricLeftFactor, hpq, hqp, hnforward] using
        rightFactor_eval_ne_zero (p := q) (q := p) hp

theorem symmetricRightFactor_eval_ne_zero {p q : RatPolynomial} {x : ℚ}
    (hq : q.eval x ≠ 0) : (symmetricRightFactor p q).eval x ≠ 0 := by
  by_cases hpq : p = q
  · simp [symmetricRightFactor, hpq]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricRightFactor, hpq, hlt] using
        rightFactor_eval_ne_zero (p := p) hq
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricRightFactor, hpq, hqp, hnforward] using
        leftFactor_eval_ne_zero (p := q) (q := p) hq

/-- For a coprime pair, removing the executable gcd preserves a strict
endpoint sign relation of the left input.  The returned gcd is a nonzero
constant, so its two endpoint values contribute a positive square. -/
theorem leftFactor_endpoint_mul_pos_of_isCoprime {p q : RatPolynomial}
    (hp : p.isZero = false) (hcoprime : IsCoprime p.toPolynomial q.toPolynomial)
    {a b : ℚ} (hinput : 0 < p.eval a * p.eval b) :
    0 < (leftFactor p q).eval a * (leftFactor p q).eval b := by
  have hgNonzero : (gcd p q).isZero = false :=
    (extendedGCD p q).nonzero (Or.inl hp)
  have hgUnit := hcoprime.isUnit_of_dvd'
    (gcd_toPolynomial_dvd_left p q) (gcd_toPolynomial_dvd_right p q)
  have hgDegreePolynomial := Polynomial.natDegree_eq_zero_of_isUnit hgUnit
  have hgDegree : (gcd p q).natDegree = 0 := by
    rwa [natDegree_toPolynomial hgNonzero] at hgDegreePolynomial
  have hgSame := eval_eq_of_natDegree_zero hgNonzero hgDegree a b
  have hpIdentityA : p.eval a =
      (gcd p q).eval a * (leftFactor p q).eval a := by
    simpa [gcd, leftFactor] using (extendedGCD p q).pIdentity a
  have hpIdentityB : p.eval b =
      (gcd p q).eval b * (leftFactor p q).eval b := by
    simpa [gcd, leftFactor] using (extendedGCD p q).pIdentity b
  have hgEvalNonzero : (gcd p q).eval a ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hpIdentityA
    have hpEval : p.eval a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hinput
      exact (lt_irrefl 0 hinput).elim
    exact hpEval hpIdentityA
  have hgProduct : 0 < (gcd p q).eval a * (gcd p q).eval b := by
    rw [← hgSame]
    exact mul_self_pos.mpr hgEvalNonzero
  have hfactored : 0 <
      ((gcd p q).eval a * (gcd p q).eval b) *
        ((leftFactor p q).eval a * (leftFactor p q).eval b) := by
    calc
      0 < p.eval a * p.eval b := hinput
      _ = ((gcd p q).eval a * (gcd p q).eval b) *
          ((leftFactor p q).eval a * (leftFactor p q).eval b) := by
        rw [hpIdentityA, hpIdentityB]
        ring
  exact (mul_pos_iff_of_pos_left hgProduct).mp hfactored

/-- The analogous endpoint-sign preservation for the right quotient factor. -/
theorem rightFactor_endpoint_mul_pos_of_isCoprime {p q : RatPolynomial}
    (hq : q.isZero = false) (hcoprime : IsCoprime p.toPolynomial q.toPolynomial)
    {a b : ℚ} (hinput : 0 < q.eval a * q.eval b) :
    0 < (rightFactor p q).eval a * (rightFactor p q).eval b := by
  have hgNonzero : (gcd p q).isZero = false :=
    (extendedGCD p q).nonzero (Or.inr hq)
  have hgUnit := hcoprime.isUnit_of_dvd'
    (gcd_toPolynomial_dvd_left p q) (gcd_toPolynomial_dvd_right p q)
  have hgDegreePolynomial := Polynomial.natDegree_eq_zero_of_isUnit hgUnit
  have hgDegree : (gcd p q).natDegree = 0 := by
    rwa [natDegree_toPolynomial hgNonzero] at hgDegreePolynomial
  have hgSame := eval_eq_of_natDegree_zero hgNonzero hgDegree a b
  have hqIdentityA : q.eval a =
      (gcd p q).eval a * (rightFactor p q).eval a := by
    simpa [gcd, rightFactor] using (extendedGCD p q).qIdentity a
  have hqIdentityB : q.eval b =
      (gcd p q).eval b * (rightFactor p q).eval b := by
    simpa [gcd, rightFactor] using (extendedGCD p q).qIdentity b
  have hgEvalNonzero : (gcd p q).eval a ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hqIdentityA
    have hqEval : q.eval a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hinput
      exact (lt_irrefl 0 hinput).elim
    exact hqEval hqIdentityA
  have hgProduct : 0 < (gcd p q).eval a * (gcd p q).eval b := by
    rw [← hgSame]
    exact mul_self_pos.mpr hgEvalNonzero
  have hfactored : 0 <
      ((gcd p q).eval a * (gcd p q).eval b) *
        ((rightFactor p q).eval a * (rightFactor p q).eval b) := by
    calc
      0 < q.eval a * q.eval b := hinput
      _ = ((gcd p q).eval a * (gcd p q).eval b) *
          ((rightFactor p q).eval a * (rightFactor p q).eval b) := by
        rw [hqIdentityA, hqIdentityB]
        ring
  exact (mul_pos_iff_of_pos_left hgProduct).mp hfactored

/-- Symmetric gcd reduction preserves a strict endpoint sign relation of the
right input, independently of which coefficient ordering selects the shared
Euclidean run. -/
theorem symmetricRightFactor_endpoint_mul_pos_of_isCoprime
    {p q : RatPolynomial} (hq : q.isZero = false)
    (hcoprime : IsCoprime p.toPolynomial q.toPolynomial)
    {a b : ℚ} (hinput : 0 < q.eval a * q.eval b) :
    0 < (symmetricRightFactor p q).eval a *
      (symmetricRightFactor p q).eval b := by
  by_cases hpq : p = q
  · simp [symmetricRightFactor, hpq]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricRightFactor, hpq, hlt] using
        rightFactor_endpoint_mul_pos_of_isCoprime hq hcoprime hinput
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricRightFactor, hpq, hqp, hnforward] using
        leftFactor_endpoint_mul_pos_of_isCoprime (p := q) (q := p) hq
          hcoprime.symm hinput

/-- For a coprime pair, removing the constant executable gcd also preserves
an opposite endpoint sign relation of the left input. -/
theorem leftFactor_endpoint_mul_neg_of_isCoprime {p q : RatPolynomial}
    (hp : p.isZero = false) (hcoprime : IsCoprime p.toPolynomial q.toPolynomial)
    {a b : ℚ} (hinput : p.eval a * p.eval b < 0) :
    (leftFactor p q).eval a * (leftFactor p q).eval b < 0 := by
  have hgNonzero : (gcd p q).isZero = false :=
    (extendedGCD p q).nonzero (Or.inl hp)
  have hgUnit := hcoprime.isUnit_of_dvd'
    (gcd_toPolynomial_dvd_left p q) (gcd_toPolynomial_dvd_right p q)
  have hgDegreePolynomial := Polynomial.natDegree_eq_zero_of_isUnit hgUnit
  have hgDegree : (gcd p q).natDegree = 0 := by
    rwa [natDegree_toPolynomial hgNonzero] at hgDegreePolynomial
  have hgSame := eval_eq_of_natDegree_zero hgNonzero hgDegree a b
  have hpIdentityA : p.eval a =
      (gcd p q).eval a * (leftFactor p q).eval a := by
    simpa [gcd, leftFactor] using (extendedGCD p q).pIdentity a
  have hpIdentityB : p.eval b =
      (gcd p q).eval b * (leftFactor p q).eval b := by
    simpa [gcd, leftFactor] using (extendedGCD p q).pIdentity b
  have hgEvalNonzero : (gcd p q).eval a ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hpIdentityA
    have hpEval : p.eval a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hinput
      exact (lt_irrefl 0 hinput).elim
    exact hpEval hpIdentityA
  have hgProduct : 0 < (gcd p q).eval a * (gcd p q).eval b := by
    rw [← hgSame]
    exact mul_self_pos.mpr hgEvalNonzero
  have hfactored :
      ((gcd p q).eval a * (gcd p q).eval b) *
          ((leftFactor p q).eval a * (leftFactor p q).eval b) < 0 := by
    calc
      _ = p.eval a * p.eval b := by
        rw [hpIdentityA, hpIdentityB]
        ring
      _ < 0 := hinput
  nlinarith

/-- The analogous opposite-endpoint-sign preservation for the right quotient
factor. -/
theorem rightFactor_endpoint_mul_neg_of_isCoprime {p q : RatPolynomial}
    (hq : q.isZero = false) (hcoprime : IsCoprime p.toPolynomial q.toPolynomial)
    {a b : ℚ} (hinput : q.eval a * q.eval b < 0) :
    (rightFactor p q).eval a * (rightFactor p q).eval b < 0 := by
  have hgNonzero : (gcd p q).isZero = false :=
    (extendedGCD p q).nonzero (Or.inr hq)
  have hgUnit := hcoprime.isUnit_of_dvd'
    (gcd_toPolynomial_dvd_left p q) (gcd_toPolynomial_dvd_right p q)
  have hgDegreePolynomial := Polynomial.natDegree_eq_zero_of_isUnit hgUnit
  have hgDegree : (gcd p q).natDegree = 0 := by
    rwa [natDegree_toPolynomial hgNonzero] at hgDegreePolynomial
  have hgSame := eval_eq_of_natDegree_zero hgNonzero hgDegree a b
  have hqIdentityA : q.eval a =
      (gcd p q).eval a * (rightFactor p q).eval a := by
    simpa [gcd, rightFactor] using (extendedGCD p q).qIdentity a
  have hqIdentityB : q.eval b =
      (gcd p q).eval b * (rightFactor p q).eval b := by
    simpa [gcd, rightFactor] using (extendedGCD p q).qIdentity b
  have hgEvalNonzero : (gcd p q).eval a ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hqIdentityA
    have hqEval : q.eval a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hinput
      exact (lt_irrefl 0 hinput).elim
    exact hqEval hqIdentityA
  have hgProduct : 0 < (gcd p q).eval a * (gcd p q).eval b := by
    rw [← hgSame]
    exact mul_self_pos.mpr hgEvalNonzero
  have hfactored :
      ((gcd p q).eval a * (gcd p q).eval b) *
          ((rightFactor p q).eval a * (rightFactor p q).eval b) < 0 := by
    calc
      _ = q.eval a * q.eval b := by
        rw [hqIdentityA, hqIdentityB]
        ring
      _ < 0 := hinput
  nlinarith

/-- Symmetric gcd reduction preserves an opposite endpoint sign relation of
the right input for either coefficient-order branch. -/
theorem symmetricRightFactor_endpoint_mul_neg_of_isCoprime
    {p q : RatPolynomial} (hq : q.isZero = false)
    (hcoprime : IsCoprime p.toPolynomial q.toPolynomial)
    {a b : ℚ} (hinput : q.eval a * q.eval b < 0) :
    (symmetricRightFactor p q).eval a *
      (symmetricRightFactor p q).eval b < 0 := by
  by_cases hpq : p = q
  · subst q
    have hunit := hcoprime.isUnit_of_dvd dvd_rfl
    have hdegreePolynomial := Polynomial.natDegree_eq_zero_of_isUnit hunit
    have hdegree : p.natDegree = 0 := by
      rwa [natDegree_toPolynomial hq] at hdegreePolynomial
    have heval := eval_eq_of_natDegree_zero hq hdegree a b
    have hnonneg : 0 ≤ p.eval a * p.eval b := by
      rw [← heval]
      exact mul_self_nonneg _
    exact (not_lt_of_ge hnonneg hinput).elim
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricRightFactor, hpq, hlt] using
        rightFactor_endpoint_mul_neg_of_isCoprime hq hcoprime hinput
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricRightFactor, hpq, hqp, hnforward] using
        leftFactor_endpoint_mul_neg_of_isCoprime (p := q) (q := p) hq
          hcoprime.symm hinput

/-- Every common sparse-polynomial divisor divides the returned candidate, so
the executable result has the universal gcd property as well as explicit
factor witnesses. -/
theorem gcd_toPolynomial_isGreatest (p q : RatPolynomial)
    {d : Polynomial ℚ} (hdp : d ∣ p.toPolynomial)
    (hdq : d ∣ q.toPolynomial) : d ∣ (gcd p q).toPolynomial := by
  rcases hdp with ⟨pFactor, hpFactor⟩
  rcases hdq with ⟨qFactor, hqFactor⟩
  refine ⟨(leftCoefficient p q).toPolynomial * pFactor +
    (rightCoefficient p q).toPolynomial * qFactor, ?_⟩
  rw [gcd_toPolynomial_identity, hpFactor, hqFactor]
  ring

/-- The executable algorithm cannot return the zero polynomial unless both
inputs represent zero. -/
theorem gcd_isZero_false_of_nonzero (p q : RatPolynomial)
    (h : p.isZero = false ∨ q.isZero = false) : (gcd p q).isZero = false :=
  (extendedGCD p q).nonzero h

/-- Both quotient factors lose the same gcd degree. -/
theorem factor_natDegree_balance {p q : RatPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    p.natDegree + (rightFactor p q).natDegree =
      q.natDegree + (leftFactor p q).natDegree := by
  have hgDense := gcd_isZero_false_of_nonzero p q (Or.inl hp)
  have hleftDense := leftFactor_isZero_false (p := p) (q := q) hp
  have hrightDense := rightFactor_isZero_false (p := p) (q := q) hq
  have hg := toPolynomial_ne_zero_of_isZero_false hgDense
  have hleft := toPolynomial_ne_zero_of_isZero_false hleftDense
  have hright := toPolynomial_ne_zero_of_isZero_false hrightDense
  have hpDegree := congrArg Polynomial.natDegree
    (leftFactor_toPolynomial_identity p q)
  have hqDegree := congrArg Polynomial.natDegree
    (rightFactor_toPolynomial_identity p q)
  rw [Polynomial.natDegree_mul hg hleft, natDegree_toPolynomial hp,
    natDegree_toPolynomial hgDense, natDegree_toPolynomial hleftDense] at hpDegree
  rw [Polynomial.natDegree_mul hg hright, natDegree_toPolynomial hq,
    natDegree_toPolynomial hgDense, natDegree_toPolynomial hrightDense] at hqDegree
  omega

/-- Symmetric gcd reduction preserves strict degree order. -/
theorem symmetricFactor_natDegree_lt {p q : RatPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false)
    (hdegree : p.natDegree < q.natDegree) :
    (symmetricLeftFactor p q).natDegree <
      (symmetricRightFactor p q).natDegree := by
  by_cases hpq : p = q
  · subst q
    omega
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · have hbalance := factor_natDegree_balance hp hq
      simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hlt] using
        (show (leftFactor p q).natDegree < (rightFactor p q).natDegree by omega)
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hbalance := factor_natDegree_balance hq hp
      have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hnforward] using
        (show (rightFactor q p).natDegree < (leftFactor q p).natDegree by omega)

/-- After dividing both inputs by the returned nonzero gcd, the displayed
quotient factors are coprime.  Cancellation is justified by the checked
nonzeroness field of the Euclidean result. -/
theorem reducedFactors_isCoprime (p q : RatPolynomial)
    (hnonzero : p.isZero = false ∨ q.isZero = false) :
    IsCoprime (leftFactor p q).toPolynomial (rightFactor p q).toPolynomial := by
  have hgDense := gcd_isZero_false_of_nonzero p q hnonzero
  have hg : (gcd p q).toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false hgDense
  refine ⟨(leftCoefficient p q).toPolynomial,
    (rightCoefficient p q).toPolynomial, ?_⟩
  have hbezout := gcd_toPolynomial_identity p q
  rw [leftFactor_toPolynomial_identity p q,
    rightFactor_toPolynomial_identity p q] at hbezout
  have hfactored :
      (gcd p q).toPolynomial * 1 =
        (gcd p q).toPolynomial *
          ((leftCoefficient p q).toPolynomial * (leftFactor p q).toPolynomial +
            (rightCoefficient p q).toPolynomial * (rightFactor p q).toPolynomial) := by
    calc
      (gcd p q).toPolynomial * 1 = (gcd p q).toPolynomial := mul_one _
      _ = (leftCoefficient p q).toPolynomial *
          ((gcd p q).toPolynomial * (leftFactor p q).toPolynomial) +
        (rightCoefficient p q).toPolynomial *
          ((gcd p q).toPolynomial * (rightFactor p q).toPolynomial) := hbezout
      _ = (gcd p q).toPolynomial *
          ((leftCoefficient p q).toPolynomial * (leftFactor p q).toPolynomial +
            (rightCoefficient p q).toPolynomial * (rightFactor p q).toPolynomial) := by
        ring
  exact (mul_left_cancel₀ hg hfactored).symm

theorem symmetricFactors_isCoprime (p q : RatPolynomial)
    (hnonzero : p.isZero = false ∨ q.isZero = false) :
    IsCoprime (symmetricLeftFactor p q).toPolynomial
      (symmetricRightFactor p q).toPolynomial := by
  by_cases hpq : p = q
  · subst q
    simpa [symmetricLeftFactor, symmetricRightFactor] using
      (isCoprime_one_left : IsCoprime (1 : Polynomial ℚ) 1)
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hlt] using
        reducedFactors_isCoprime p q hnonzero
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hnforward] using
        (reducedFactors_isCoprime q p hnonzero.symm).symm

theorem gcd_eval_eq_zero_of_common_zero {p q : RatPolynomial} {x : ℚ}
    (hp : p.eval x = 0) (hq : q.eval x = 0) : (gcd p q).eval x = 0 := by
  rw [gcd_eval_identity, hp, hq]
  ring

/-- A displayed Bézout identity for one rules out an exact common rational
zero. -/
theorem no_common_zero_of_bezout_one {p q U V : RatPolynomial}
    (hbezout : ∀ x, U.eval x * p.eval x + V.eval x * q.eval x = 1) :
    ¬∃ x : ℚ, p.eval x = 0 ∧ q.eval x = 0 := by
  rintro ⟨x, hp, hq⟩
  have h := hbezout x
  rw [hp, hq] at h
  norm_num at h

private theorem factorProduct_eval_neg_of_inputProduct_neg
    (p q : RatPolynomial) (x : ℚ) (hproduct : p.eval x * q.eval x < 0) :
    (leftFactor p q).eval x * (rightFactor p q).eval x < 0 := by
  have hpIdentity : p.eval x =
      (gcd p q).eval x * (leftFactor p q).eval x := by
    simpa [gcd, leftFactor] using (extendedGCD p q).pIdentity x
  have hqIdentity : q.eval x =
      (gcd p q).eval x * (rightFactor p q).eval x := by
    simpa [gcd, rightFactor] using (extendedGCD p q).qIdentity x
  have hgcd : (gcd p q).eval x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hpIdentity hqIdentity
    rw [hpIdentity, hqIdentity] at hproduct
    norm_num at hproduct
  have hgcdSquare : 0 < (gcd p q).eval x * (gcd p q).eval x :=
    mul_self_pos.mpr hgcd
  have hfactored :
      ((gcd p q).eval x * (gcd p q).eval x) *
          ((leftFactor p q).eval x * (rightFactor p q).eval x) < 0 := by
    calc
      ((gcd p q).eval x * (gcd p q).eval x) *
          ((leftFactor p q).eval x * (rightFactor p q).eval x) =
          p.eval x * q.eval x := by rw [hpIdentity, hqIdentity]; ring
      _ < 0 := hproduct
  exact (mul_lt_mul_iff_right₀ hgcdSquare).mp (by simpa using hfactored)

private theorem factorProduct_eval_pos_of_inputProduct_pos
    (p q : RatPolynomial) (x : ℚ) (hproduct : 0 < p.eval x * q.eval x) :
    0 < (leftFactor p q).eval x * (rightFactor p q).eval x := by
  have hpIdentity : p.eval x =
      (gcd p q).eval x * (leftFactor p q).eval x := by
    simpa [gcd, leftFactor] using (extendedGCD p q).pIdentity x
  have hqIdentity : q.eval x =
      (gcd p q).eval x * (rightFactor p q).eval x := by
    simpa [gcd, rightFactor] using (extendedGCD p q).qIdentity x
  have hgcd : (gcd p q).eval x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hpIdentity hqIdentity
    rw [hpIdentity, hqIdentity] at hproduct
    norm_num at hproduct
  have hgcdSquare : 0 < (gcd p q).eval x * (gcd p q).eval x :=
    mul_self_pos.mpr hgcd
  have hfactored : 0 <
      ((gcd p q).eval x * (gcd p q).eval x) *
        ((leftFactor p q).eval x * (rightFactor p q).eval x) := by
    calc
      0 < p.eval x * q.eval x := hproduct
      _ = ((gcd p q).eval x * (gcd p q).eval x) *
          ((leftFactor p q).eval x * (rightFactor p q).eval x) := by
        rw [hpIdentity, hqIdentity]
        ring
  exact (mul_pos_iff_of_pos_left hgcdSquare).mp hfactored

/-- Dividing both inputs by the executable common gcd preserves an opposite
strict sign at every rational evaluation point: the removed factor occurs as
a positive square. -/
theorem symmetricFactors_eval_mul_neg_of_input_mul_neg
    (p q : RatPolynomial) (x : ℚ) (hproduct : p.eval x * q.eval x < 0) :
    (symmetricLeftFactor p q).eval x *
      (symmetricRightFactor p q).eval x < 0 := by
  by_cases hpq : p = q
  · subst q
    have hsquare : 0 ≤ p.eval x * p.eval x := mul_self_nonneg _
    linarith
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hlt] using
        factorProduct_eval_neg_of_inputProduct_neg p q x hproduct
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      have hreverse : q.eval x * p.eval x < 0 := by simpa [mul_comm] using hproduct
      simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hnforward,
        mul_comm] using factorProduct_eval_neg_of_inputProduct_neg q p x hreverse

/-- Symmetric gcd reduction likewise preserves equal strict signs. -/
theorem symmetricFactors_eval_mul_pos_of_input_mul_pos
    (p q : RatPolynomial) (x : ℚ) (hproduct : 0 < p.eval x * q.eval x) :
    0 < (symmetricLeftFactor p q).eval x *
      (symmetricRightFactor p q).eval x := by
  by_cases hpq : p = q
  · subst q
    simp [symmetricLeftFactor, symmetricRightFactor]
  · have hqp : q ≠ p := Ne.symm hpq
    rcases lt_trichotomy p.coeffs q.coeffs with hlt | heq | hgt
    · simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hlt] using
        factorProduct_eval_pos_of_inputProduct_pos p q x hproduct
    · exact (hpq (DensePolynomial.ext heq)).elim
    · have hnforward : ¬p.coeffs < q.coeffs := not_lt_of_ge hgt.le
      have hreverse : 0 < q.eval x * p.eval x := by simpa [mul_comm] using hproduct
      simpa [symmetricLeftFactor, symmetricRightFactor, hpq, hqp, hnforward,
        mul_comm] using factorProduct_eval_pos_of_inputProduct_pos q p x hreverse

/-- Native exact check of the executable gcd path for `T²-1` and `2T`. -/
theorem gcd_quadratic_example :
    gcd ⟨[1, 0, -1]⟩ ⟨[2, 0]⟩ = ⟨[-1]⟩ := by
  native_decide

end FTA.DenseGCD
