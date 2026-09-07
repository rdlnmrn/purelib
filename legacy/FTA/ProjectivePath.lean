import FTA.PathClearance

/-!
# Polynomial evaluation on rational projective paths

CCL branch curves are given by homogeneous rational parametrizations rather
than affine lines.  This module clears their denominator by an executable
finite Horner scan.  It returns rational coordinate polynomials whose common
zeros can be counted by Theorem 5.3, together with an exact evaluation theorem
away from the finite projective denominator zeros.
-/

namespace FTA
namespace ProjectivePath

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.PathClearance

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI
abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- Homogeneous numerator and denominator polynomials in one rational
parameter. -/
structure Path where
  numerator : GaussianPolynomial
  denominator : GaussianPolynomial
deriving DecidableEq, Repr

namespace Path

/-- Affine value of a projective path when its denominator is nonzero. -/
def value (path : Path) (t : ℚ) : QI :=
  path.numerator.eval (ofRat t) * inv (path.denominator.eval (ofRat t))

end Path

/-- Horner state carrying both the cleared value and the denominator power
used to clear the coefficients processed so far. -/
structure ClearState where
  value : GaussianPolynomial
  denominatorPower : GaussianPolynomial
deriving DecidableEq, Repr

/-- One denominator-clearing Horner step. -/
def ClearState.step (numerator denominator : GaussianPolynomial)
    (state : ClearState) (coefficient : QI) : ClearState :=
  let nextPower := state.denominatorPower * denominator
  { value := state.value * numerator + constant coefficient * nextPower
    denominatorPower := nextPower }

/-- The complete finite denominator-clearing scan. -/
def clearState (p : GaussianPolynomial) (path : Path) : ClearState :=
  p.coeffs.foldl (ClearState.step path.numerator path.denominator)
    ⟨0, constant 1⟩

/-- Gaussian polynomial equal to a denominator power times `p` on the
projective path. -/
def clearedEvaluation (p : GaussianPolynomial) (path : Path) : GaussianPolynomial :=
  (clearState p path).value

/-- The exact polynomial denominator power accumulated by the scan. -/
def clearedDenominatorPower
    (p : GaussianPolynomial) (path : Path) : GaussianPolynomial :=
  (clearState p path).denominatorPower

private theorem foldl_denominatorPower_eval_eq_pow
    (coefficients : List QI) (numerator denominator : GaussianPolynomial)
    (t : ℚ) (state : ClearState) :
    (coefficients.foldl
      (ClearState.step numerator denominator) state).denominatorPower.eval
        (ofRat t) =
      state.denominatorPower.eval (ofRat t) *
        denominator.eval (ofRat t) ^ coefficients.length := by
  induction coefficients generalizing state with
  | nil => simp
  | cons coefficient coefficients inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      simp only [ClearState.step, eval_mul, List.length_cons, pow_succ]
      ring

/-- The denominator-clearing Horner scan accumulates exactly one displayed
path-denominator factor per coefficient. -/
theorem clearedDenominatorPower_eval_eq_pow
    (p : GaussianPolynomial) (path : Path) (t : ℚ) :
    (clearedDenominatorPower p path).eval (ofRat t) =
      path.denominator.eval (ofRat t) ^ p.coeffs.length := by
  rw [clearedDenominatorPower, clearState,
    foldl_denominatorPower_eval_eq_pow]
  simp

private theorem foldl_denominatorPower_eval_ne
    (coefficients : List QI) (numerator denominator : GaussianPolynomial)
    (t : ℚ) (state : ClearState)
    (stateNonzero : state.denominatorPower.eval (ofRat t) ≠ 0)
    (denominatorNonzero : denominator.eval (ofRat t) ≠ 0) :
    (coefficients.foldl
      (ClearState.step numerator denominator) state).denominatorPower.eval
        (ofRat t) ≠ 0 := by
  induction coefficients generalizing state with
  | nil => exact stateNonzero
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · simp only [ClearState.step, eval_mul]
        exact mul_ne_zero stateNonzero denominatorNonzero

/-- Clearing accumulates only a finite power of the displayed path
denominator, so it remains nonzero at every affine path parameter. -/
theorem clearedDenominatorPower_eval_ne
    (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (denominatorNonzero : path.denominator.eval (ofRat t) ≠ 0) :
    (clearedDenominatorPower p path).eval (ofRat t) ≠ 0 := by
  apply foldl_denominatorPower_eval_ne p.coeffs path.numerator path.denominator
    t ⟨0, constant 1⟩
  · simp
  · exact denominatorNonzero

private theorem foldl_clear_spec
    (coefficients : List QI) (numerator denominator : GaussianPolynomial)
    (t : ℚ) (state : ClearState) (accumulator : QI)
    (hstate : state.value.eval (ofRat t) =
      state.denominatorPower.eval (ofRat t) * accumulator)
    (hden : denominator.eval (ofRat t) ≠ 0) :
    let final := coefficients.foldl (ClearState.step numerator denominator) state
    final.value.eval (ofRat t) =
      final.denominatorPower.eval (ofRat t) *
        coefficients.foldl
          (fun value coefficient =>
            value * (numerator.eval (ofRat t) *
              inv (denominator.eval (ofRat t))) + coefficient)
          accumulator := by
  induction coefficients generalizing state accumulator with
  | nil => exact hstate
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      apply ih
      dsimp only [ClearState.step]
      simp only [eval_add, eval_mul, eval_constant]
      rw [hstate]
      let power := state.denominatorPower.eval (ofRat t)
      let num := numerator.eval (ofRat t)
      let den := denominator.eval (ofRat t)
      have hdenInv : den * inv den = 1 := mul_inv den hden
      calc
        power * accumulator * num + coefficient * (power * den) =
            (power * den) *
              (accumulator * (num * inv den) + coefficient) := by
          rw [mul_add]
          congr 1
          · calc
              power * accumulator * num =
                  (power * accumulator * num) * (den * inv den) := by
                    rw [hdenInv, mul_one]
              _ = power * den * (accumulator * (num * inv den)) := by ring
          · ring
        _ = (state.denominatorPower.eval (ofRat t) *
              denominator.eval (ofRat t)) *
              (accumulator *
                (numerator.eval (ofRat t) *
                  inv (denominator.eval (ofRat t))) + coefficient) := by
          rfl

/-- Exact projective Horner identity away from a denominator zero. -/
theorem clearedEvaluation_spec (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (hden : path.denominator.eval (ofRat t) ≠ 0) :
    (clearedEvaluation p path).eval (ofRat t) =
      (clearedDenominatorPower p path).eval (ofRat t) *
        p.eval (path.value t) := by
  simpa only [clearedEvaluation, clearedDenominatorPower, clearState, Path.value,
    DensePolynomial.eval, DensePolynomial.evalCoeffs] using
      foldl_clear_spec p.coeffs path.numerator path.denominator t
        ⟨0, constant 1⟩ 0
        (by simp) hden

/-- Rational real-coordinate polynomial of the cleared evaluation. -/
def clearedReal (p : GaussianPolynomial) (path : Path) : RatPolynomial :=
  realPart (clearedEvaluation p path)

/-- Rational imaginary-coordinate polynomial of the cleared evaluation. -/
def clearedImag (p : GaussianPolynomial) (path : Path) : RatPolynomial :=
  imagPart (clearedEvaluation p path)

theorem eval_clearedReal (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (hden : path.denominator.eval (ofRat t) ≠ 0) :
    (clearedReal p path).eval t =
      ((clearedDenominatorPower p path).eval (ofRat t) *
        p.eval (path.value t)).re := by
  rw [clearedReal, eval_realPart, clearedEvaluation_spec p path t hden]

theorem eval_clearedImag (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (hden : path.denominator.eval (ofRat t) ≠ 0) :
    (clearedImag p path).eval t =
      ((clearedDenominatorPower p path).eval (ofRat t) *
        p.eval (path.value t)).im := by
  rw [clearedImag, eval_imagPart, clearedEvaluation_spec p path t hden]

/-- An affine root makes both rational coordinates of the cleared projective
evaluation vanish. -/
theorem eval_clearedReal_eq_zero_of_eval_eq_zero
    (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (hden : path.denominator.eval (ofRat t) ≠ 0)
    (root : p.eval (path.value t) = 0) :
    (clearedReal p path).eval t = 0 := by
  rw [eval_clearedReal p path t hden, root, mul_zero]
  rfl

theorem eval_clearedImag_eq_zero_of_eval_eq_zero
    (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (hden : path.denominator.eval (ofRat t) ≠ 0)
    (root : p.eval (path.value t) = 0) :
    (clearedImag p path).eval t = 0 := by
  rw [eval_clearedImag p path t hden, root, mul_zero]
  rfl

theorem eval_cleared_normSq (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (hden : path.denominator.eval (ofRat t) ≠ 0) :
    (clearedReal p path).eval t ^ 2 + (clearedImag p path).eval t ^ 2 =
      normSq ((clearedDenominatorPower p path).eval (ofRat t)) *
        normSq (p.eval (path.value t)) := by
  rw [eval_clearedReal p path t hden, eval_clearedImag p path t hden,
    ← normSq, normSq_mul]

/-- If both cleared coordinate polynomials vanish identically, every affine
parameter of the projective path is an exact rational root. -/
theorem eval_eq_zero_of_cleared_isZero
    (p : GaussianPolynomial) (path : Path) (t : ℚ)
    (denominatorNonzero : path.denominator.eval (ofRat t) ≠ 0)
    (realZero : (clearedReal p path).isZero = true)
    (imagZero : (clearedImag p path).isZero = true) :
    p.eval (path.value t) = 0 := by
  have clearedRealZero : (clearedReal p path).eval t = 0 :=
    eval_eq_zero_of_isZero realZero t
  have clearedImagZero : (clearedImag p path).eval t = 0 :=
    eval_eq_zero_of_isZero imagZero t
  have productZero :
      (clearedDenominatorPower p path).eval (ofRat t) *
        p.eval (path.value t) = 0 := by
    apply GaussianRat.ext
    · rw [← eval_clearedReal p path t denominatorNonzero,
        clearedRealZero]
      rfl
    · rw [← eval_clearedImag p path t denominatorNonzero,
        clearedImagZero]
      rfl
  exact (mul_eq_zero.mp productZero).resolve_left
    (clearedDenominatorPower_eval_ne p path t denominatorNonzero)

/-- Executable dichotomy for the two cleared coordinates. -/
inductive ClearedCoordinatesDecision (p : GaussianPolynomial) (path : Path) where
  | identicallyZero
      (realZero : (clearedReal p path).isZero = true)
      (imagZero : (clearedImag p path).isZero = true)
  | nonzero
      (proof : (clearedReal p path).isZero = false ∨
        (clearedImag p path).isZero = false)

def decideClearedCoordinates
    (p : GaussianPolynomial) (path : Path) :
    ClearedCoordinatesDecision p path := by
  by_cases realZero : (clearedReal p path).isZero = true
  · by_cases imagZero : (clearedImag p path).isZero = true
    · exact .identicallyZero realZero imagZero
    · exact .nonzero (Or.inr (Bool.eq_false_of_not_eq_true imagZero))
  · exact .nonzero (Or.inl (Bool.eq_false_of_not_eq_true realZero))

/-- The finite common-factor root count consumed by Theorem 5.3 on one
projective parameter interval. -/
def commonFactorRootCount2 (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) (a b : ℚ) : ℤ :=
  PathClearance.commonFactorRootCount2
    (clearedReal p path) (clearedImag p path) hnonzero a b

/-- Quantitative zero-count branch of Theorem 5.3 for a projectively
parametrized arc. -/
def computeClearance (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p path) (clearedImag p path)).eval
        interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p path) (clearedImag p path)).eval
        interval.upper ≠ 0)
    (countZero : commonFactorRootCount2 p path hnonzero
      interval.lower interval.upper = 0) :
    PathClearance.Certificate (clearedReal p path) (clearedImag p path) interval :=
  PathClearance.compute hnonzero interval proper lowerClear upperClear countZero

theorem computeClearance_lower_clearedNormSq
    (p : GaussianPolynomial) (path : Path)
    (hnonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false)
    (interval : RationalInterval) (proper : interval.Proper)
    (lowerClear :
      (PathClearance.commonFactor (clearedReal p path) (clearedImag p path)).eval
        interval.lower ≠ 0)
    (upperClear :
      (PathClearance.commonFactor (clearedReal p path) (clearedImag p path)).eval
        interval.upper ≠ 0)
    (countZero : commonFactorRootCount2 p path hnonzero
      interval.lower interval.upper = 0)
    {t : ℚ} (hLower : interval.lower ≤ t) (hUpper : t ≤ interval.upper)
    (hden : path.denominator.eval (ofRat t) ≠ 0) :
    (computeClearance p path hnonzero interval proper lowerClear upperClear
      countZero).bound ≤
        normSq ((clearedDenominatorPower p path).eval (ofRat t)) *
          normSq (p.eval (path.value t)) := by
  have hlower := (computeClearance p path hnonzero interval proper lowerClear
    upperClear countZero).lower t hLower hUpper
  rwa [eval_cleared_normSq p path t hden] at hlower

end ProjectivePath
end FTA
