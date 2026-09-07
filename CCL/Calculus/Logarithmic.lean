import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Calculus.Exponential

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace CCL.LogarithmicCalculus

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent
abbrev Polynomial := CCL.FinitePolynomial.Polynomial

open RFAP.ConstructiveGaussian.Gaussian
open CCL.FinitePolynomial

private theorem mul_scale (u v : Gaussian) (coefficient : Coordinate) :
    u * CCL.FiniteExp.scale coefficient v =
      CCL.FiniteExp.scale coefficient (u * v) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im] <;> ring1

private theorem scale_scale (left right : Coordinate) (u : Gaussian) :
    CCL.FiniteExp.scale left
        (CCL.FiniteExp.scale right u) =
      CCL.FiniteExp.scale (left * right) u := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im] <;> ring1

/-- The alternating sign is computed by natural recursion rather than by a
parity oracle. -/
def alternatingSign : Nat → Coordinate
  | 0 => 1
  | index + 1 => -alternatingSign index

def alternatingCoefficient (index : Nat) : Coordinate :=
  alternatingSign index / ((index + 1 : Nat) : Coordinate)

theorem negPower_eq_scaledPower (u : Gaussian) : ∀ index,
    (-u) ^ index =
      CCL.FiniteExp.scale (alternatingSign index) (u ^ index)
  | 0 => by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [pow_zero, alternatingSign,
          CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, one_re, one_im] <;> ring1
  | index + 1 => by
      rw [pow_succ, negPower_eq_scaledPower u index, pow_succ,
        alternatingSign]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, mul_re, mul_im, neg_re,
          neg_im] <;> ring1

theorem degree_mul_alternatingCoefficient (index : Nat) :
    (((index + 1 : Nat) : Coordinate) * alternatingCoefficient index) =
      alternatingSign index := by
  have denominatorPositive :
      0 < ((index + 1 : Nat) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct (by omega)
  rw [alternatingCoefficient]
  calc
    ((index + 1 : Nat) : Coordinate) *
          (alternatingSign index / ((index + 1 : Nat) : Coordinate)) =
        (alternatingSign index / ((index + 1 : Nat) : Coordinate)) *
          ((index + 1 : Nat) : Coordinate) :=
      RFAP.ConstructiveFraction.mul_comm _ _
    _ = alternatingSign index :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        denominatorPositive.ne'

/-- The actual finite polynomial whose value is the local `log(1+u)` sample. -/
def log1pPolynomial : Nat → Polynomial
  | 0 => monomial 1 1
  | index + 1 =>
      add (log1pPolynomial index)
        (monomial (index + 2) (alternatingCoefficient (index + 1)))

/-- The formal derivative target, a finite alternating geometric polynomial. -/
def log1pGeometricPolynomial : Nat → Polynomial
  | 0 => constant 1
  | index + 1 =>
      add (log1pGeometricPolynomial index)
        (monomial (index + 1) (alternatingSign (index + 1)))

theorem derivative_log1pPolynomial : ∀ index,
    CoefficientwiseEqual (derivative (log1pPolynomial index))
      (log1pGeometricPolynomial index)
  | 0 => by
      exact coefficientwise_trans
        (derivative_monomial_succ 0 1)
        (coefficientwise_trans
          (coefficientwise_monomial_value 0
            (degree_mul_alternatingCoefficient 0))
          (coefficientwise_monomial_zero 1))
  | index + 1 => by
      exact coefficientwise_trans
        (derivative_add _ _)
        (coefficientwise_trans
          (coefficientwise_add (derivative_log1pPolynomial index)
            (derivative_monomial_succ (index + 1)
              (alternatingCoefficient (index + 1))))
          (coefficientwise_add (coefficientwise_refl _)
            (coefficientwise_monomial_value (index + 1)
              (degree_mul_alternatingCoefficient (index + 1)))))

def log1pRelTerm (u : Gaussian) (index : Nat) : Gaussian :=
  CCL.FiniteExp.scale
    (1 / ((index + 1 : Nat) : Coordinate)) ((-u) ^ index)

def log1pRelSample (u : Gaussian) (index : Nat) : Gaussian :=
  CCL.TranscendentalLaws.finiteSum
    (log1pRelTerm u) (index + 1)

@[simp] theorem log1pRelTerm_zero (u : Gaussian) :
    log1pRelTerm u 0 = 1 := by
  rw [log1pRelTerm, pow_zero]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, one_re, one_im] <;>
    rw [show (1 / ((0 + 1 : Nat) : Coordinate)) = 1 by decide] <;> ring1

private theorem reciprocalNatSq_le_one (index : Nat) :
    (1 / ((index + 1 : Nat) : Coordinate)) ^ 2 ≤ 1 := by
  have denominatorPositive :
      0 < ((index + 1 : Nat) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct (by omega)
  have oneLeDenominator :
      (1 : Coordinate) ≤ ((index + 1 : Nat) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct
      (show 1 ≤ index + 1 by omega)
  have inverseOrder :
      (((index + 1 : Nat) : Coordinate))⁻¹ ≤ (1 : Coordinate)⁻¹ :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct (by decide)
      oneLeDenominator
  have inverseNonnegative :
      0 ≤ (((index + 1 : Nat) : Coordinate))⁻¹ :=
    (RFAP.ConstructiveFraction.inv_pos_direct denominatorPositive).le
  have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
    inverseNonnegative inverseOrder 2
  rw [show (1 : Coordinate)⁻¹ = 1 by decide, one_pow] at squared
  simpa only [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.one_mul] using squared

theorem log1pRelTerm_bound {u : Gaussian} (disk : normSq u ≤ 1 / 4)
    (index : Nat) :
    normSq (log1pRelTerm u index) ≤ (1 / 4 : Coordinate) ^ index := by
  rw [log1pRelTerm, CCL.FiniteExp.normSq_scale,
    normSq_pow, normSq_neg]
  have powerBound := RFAP.ConstructiveFraction.pow_le_pow_direct
    (normSq_nonneg u) disk index
  calc
    (1 / ((index + 1 : Nat) : Coordinate)) ^ 2 * normSq u ^ index ≤
        1 * (1 / 4 : Coordinate) ^ index :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (reciprocalNatSq_le_one index) powerBound
        (RFAP.ConstructiveFraction.pow_nonneg_direct (normSq_nonneg u) index)
        (by decide)
    _ = (1 / 4 : Coordinate) ^ index :=
      RFAP.ConstructiveFraction.one_mul _

theorem log1pRelSample_bounded {u : Gaussian} (disk : normSq u ≤ 1 / 4)
    (index : Nat) : normSq (log1pRelSample u index) ≤ 4 := by
  exact CCL.TranscendentalLaws.finiteSum_geometric_normSq_le
    (log1pRelTerm u) (index + 1) 1 (by decide)
      (fun termIndex => by
        simpa only [RFAP.ConstructiveFraction.one_mul] using
          log1pRelTerm_bound disk termIndex)

private theorem quarterPower_shift (earlier index : Nat) :
    (1 / 4 : Coordinate) ^ (earlier + 1 + index) =
      (1 / 4 : Coordinate) ^ (earlier + 1) *
        (1 / 4 : Coordinate) ^ index := by
  rw [pow_add]

private theorem four_mul_quarterPower_succ (index : Nat) :
    4 * (1 / 4 : Coordinate) ^ (index + 1) =
      (1 / 4 : Coordinate) ^ index := by
  rw [pow_succ]
  calc
    4 * ((1 / 4 : Coordinate) ^ index * (1 / 4)) =
        (1 / 4 : Coordinate) ^ index * (4 * (1 / 4)) := by ring1
    _ = (1 / 4 : Coordinate) ^ index * 1 := by
      rw [show (4 : Coordinate) * (1 / 4) = 1 by decide]
    _ = (1 / 4 : Coordinate) ^ index :=
      RFAP.ConstructiveFraction.mul_one_direct _

theorem log1pRelSample_later_close {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) {earlier later : Nat}
    (order : earlier ≤ later) :
    normSq (log1pRelSample u later - log1pRelSample u earlier) ≤
      CCL.FiniteGeometric.quarterRadius 1 earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [log1pRelSample, log1pRelSample,
    show earlier + extra + 1 = earlier + 1 + extra by ring1,
    CCL.TranscendentalLaws.finiteSum_append]
  have tailBound :
      normSq
          (CCL.TranscendentalLaws.finiteSum
            (fun index => log1pRelTerm u (earlier + 1 + index)) extra) ≤
        4 * (1 / 4 : Coordinate) ^ (earlier + 1) := by
    exact CCL.TranscendentalLaws.finiteSum_geometric_normSq_le
      (fun index => log1pRelTerm u (earlier + 1 + index)) extra
      ((1 / 4 : Coordinate) ^ (earlier + 1))
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
      (fun index => by
        calc
          normSq (log1pRelTerm u (earlier + 1 + index)) ≤
              (1 / 4 : Coordinate) ^ (earlier + 1 + index) :=
            log1pRelTerm_bound disk _
          _ = (1 / 4 : Coordinate) ^ (earlier + 1) *
              (1 / 4 : Coordinate) ^ index :=
            quarterPower_shift earlier index)
  calc
    normSq
        (CCL.TranscendentalLaws.finiteSum (log1pRelTerm u)
              (earlier + 1) +
            CCL.TranscendentalLaws.finiteSum
              (fun index => log1pRelTerm u (earlier + 1 + index)) extra -
          CCL.TranscendentalLaws.finiteSum (log1pRelTerm u)
            (earlier + 1)) =
      normSq
        (CCL.TranscendentalLaws.finiteSum
          (fun index => log1pRelTerm u (earlier + 1 + index)) extra) := by
        congr 1
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im] <;> ring1
    _ ≤ 4 * (1 / 4 : Coordinate) ^ (earlier + 1) := tailBound
    _ = CCL.FiniteGeometric.quarterRadius 1 earlier := by
      rw [four_mul_quarterPower_succ,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        RFAP.ConstructiveFraction.one_mul]

def log1pRelApproximation (u : Gaussian)
    (disk : normSq u ≤ 1 / 4) : Approximation where
  sample := log1pRelSample u
  radiusSq := CCL.FiniteGeometric.quarterRadius 1
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := log1pRelSample_later_close disk
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 1 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 1 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := log1pRelSample_bounded disk

def log1pRelNamed (u : Gaussian) (disk : normSq u ≤ 1 / 4) : Named :=
  (log1pRelApproximation u disk).toNamed

theorem log1pRelNamed_productive (u : Gaussian) (disk : normSq u ≤ 1 / 4)
    (count : Nat) :
    (log1pRelNamed u disk).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (log1pRelNamed u disk).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (log1pRelNamed u disk).machine count).emitted.length = count :=
  (log1pRelApproximation u disk).output_productive count

/-- The finite local-log sample is defined by its factor, so its value at
zero is exact without selecting a quotient. -/
def log1pSample (u : Gaussian) (index : Nat) : Gaussian :=
  u * log1pRelSample u index

theorem log1pSample_factor (u : Gaussian) (index : Nat) :
    log1pSample u index = u * log1pRelSample u index := rfl

theorem log1pSample_zero (index : Nat) : log1pSample 0 index = 0 := by
  rw [log1pSample, RFAP.ConstructiveGaussian.Gaussian.zero_mul]

theorem mul_log1pRelTerm_eq_monomial (u : Gaussian) (index : Nat) :
    u * log1pRelTerm u index =
      CCL.FiniteExp.scale (alternatingCoefficient index)
        (u ^ (index + 1)) := by
  have coefficientIdentity :
      (1 / ((index + 1 : Nat) : Coordinate)) * alternatingSign index =
        alternatingCoefficient index := by
    rw [alternatingCoefficient,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.one_mul]
    exact RFAP.ConstructiveFraction.mul_comm _ _
  calc
    u * log1pRelTerm u index =
        u * CCL.FiniteExp.scale
          (1 / ((index + 1 : Nat) : Coordinate)) ((-u) ^ index) := rfl
    _ = u * CCL.FiniteExp.scale
          (1 / ((index + 1 : Nat) : Coordinate))
          (CCL.FiniteExp.scale (alternatingSign index)
            (u ^ index)) := by
      rw [negPower_eq_scaledPower]
    _ = CCL.FiniteExp.scale
          (1 / ((index + 1 : Nat) : Coordinate))
          (u * CCL.FiniteExp.scale (alternatingSign index)
            (u ^ index)) := mul_scale _ _ _
    _ = CCL.FiniteExp.scale
          (1 / ((index + 1 : Nat) : Coordinate))
          (CCL.FiniteExp.scale (alternatingSign index)
            (u * u ^ index)) := by
      rw [mul_scale]
    _ = CCL.FiniteExp.scale
          ((1 / ((index + 1 : Nat) : Coordinate)) * alternatingSign index)
          (u * u ^ index) := scale_scale _ _ _
    _ = CCL.FiniteExp.scale (alternatingCoefficient index)
          (u ^ (index + 1)) := by
      rw [coefficientIdentity, pow_succ,
        RFAP.ConstructiveGaussian.Gaussian.mul_comm]

/-- The relative-logarithm program is exactly the evaluation of the finite
polynomial used by the divided-difference calculus. -/
theorem eval_log1pPolynomial (u : Gaussian) : ∀ index,
    eval (log1pPolynomial index) u = log1pSample u index
  | 0 => by
      rw [log1pPolynomial, eval_monomial, log1pSample, log1pRelSample,
        CCL.TranscendentalLaws.finiteSum_succ,
        CCL.TranscendentalLaws.finiteSum_zero,
        log1pRelTerm_zero, RFAP.ConstructiveGaussian.Gaussian.zero_add]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, mul_re, mul_im, pow_one,
          one_re, one_im] <;> ring1
  | index + 1 => by
      calc
        eval (log1pPolynomial (index + 1)) u =
            eval (log1pPolynomial index) u +
              CCL.FiniteExp.scale
                (alternatingCoefficient (index + 1))
                (u ^ (index + 2)) := by
          rw [log1pPolynomial, eval_add, eval_monomial]
        _ = log1pSample u index +
              u * log1pRelTerm u (index + 1) := by
          rw [eval_log1pPolynomial u index,
            mul_log1pRelTerm_eq_monomial]
        _ = u *
            (log1pRelSample u index + log1pRelTerm u (index + 1)) := by
          rw [log1pSample]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, mul_re, mul_im] <;> ring1
        _ = log1pSample u (index + 1) := by
          rw [log1pSample]
          apply congrArg (fun value : Gaussian => u * value)
          rw [log1pRelSample, log1pRelSample]
          exact
            (CCL.TranscendentalLaws.finiteSum_succ
              (log1pRelTerm u) (index + 1)).symm

/-! ## The second relative logarithm -/

def log1pSecondRelTerm (u : Gaussian) (index : Nat) : Gaussian :=
  CCL.FiniteExp.scale
    (-(1 / ((index + 2 : Nat) : Coordinate))) ((-u) ^ index)

def log1pSecondRelSample (u : Gaussian) (index : Nat) : Gaussian :=
  CCL.TranscendentalLaws.finiteSum
    (log1pSecondRelTerm u) (index + 1)

theorem log1pSecondRelTerm_bound {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) (index : Nat) :
    normSq (log1pSecondRelTerm u index) ≤
      (1 / 4 : Coordinate) ^ index := by
  rw [log1pSecondRelTerm, CCL.FiniteExp.normSq_scale,
    normSq_pow, normSq_neg]
  have coefficientBound :
      (-(1 / ((index + 2 : Nat) : Coordinate))) ^ 2 ≤ 1 := by
    calc
      (-(1 / ((index + 2 : Nat) : Coordinate))) ^ 2 =
          (1 / ((index + 2 : Nat) : Coordinate)) ^ 2 := by ring1
      _ = (1 / (((index + 1) + 1 : Nat) : Coordinate)) ^ 2 := by
        rw [show index + 2 = (index + 1) + 1 by ring1]
      _ ≤ 1 := reciprocalNatSq_le_one (index + 1)
  have powerBound := RFAP.ConstructiveFraction.pow_le_pow_direct
    (normSq_nonneg u) disk index
  calc
    (-(1 / ((index + 2 : Nat) : Coordinate))) ^ 2 *
          normSq u ^ index ≤
        1 * (1 / 4 : Coordinate) ^ index :=
      RFAP.ConstructiveFraction.mul_le_mul_direct coefficientBound powerBound
        (RFAP.ConstructiveFraction.pow_nonneg_direct (normSq_nonneg u) index)
        (by decide)
    _ = (1 / 4 : Coordinate) ^ index :=
      RFAP.ConstructiveFraction.one_mul _

theorem log1pSecondRelSample_bounded {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) (index : Nat) :
    normSq (log1pSecondRelSample u index) ≤ 4 := by
  exact CCL.TranscendentalLaws.finiteSum_geometric_normSq_le
    (log1pSecondRelTerm u) (index + 1) 1 (by decide)
      (fun termIndex => by
        simpa only [RFAP.ConstructiveFraction.one_mul] using
          log1pSecondRelTerm_bound disk termIndex)

theorem log1pSecondRelSample_later_close {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) {earlier later : Nat}
    (order : earlier ≤ later) :
    normSq
        (log1pSecondRelSample u later -
          log1pSecondRelSample u earlier) ≤
      CCL.FiniteGeometric.quarterRadius 1 earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [log1pSecondRelSample, log1pSecondRelSample,
    show earlier + extra + 1 = earlier + 1 + extra by ring1,
    CCL.TranscendentalLaws.finiteSum_append]
  have tailBound :
      normSq
          (CCL.TranscendentalLaws.finiteSum
            (fun index => log1pSecondRelTerm u (earlier + 1 + index))
              extra) ≤
        4 * (1 / 4 : Coordinate) ^ (earlier + 1) := by
    exact CCL.TranscendentalLaws.finiteSum_geometric_normSq_le
      (fun index => log1pSecondRelTerm u (earlier + 1 + index)) extra
      ((1 / 4 : Coordinate) ^ (earlier + 1))
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
      (fun index => by
        calc
          normSq (log1pSecondRelTerm u (earlier + 1 + index)) ≤
              (1 / 4 : Coordinate) ^ (earlier + 1 + index) :=
            log1pSecondRelTerm_bound disk _
          _ = (1 / 4 : Coordinate) ^ (earlier + 1) *
              (1 / 4 : Coordinate) ^ index :=
            quarterPower_shift earlier index)
  calc
    normSq
        (CCL.TranscendentalLaws.finiteSum
              (log1pSecondRelTerm u) (earlier + 1) +
            CCL.TranscendentalLaws.finiteSum
              (fun index => log1pSecondRelTerm u (earlier + 1 + index))
                extra -
          CCL.TranscendentalLaws.finiteSum
            (log1pSecondRelTerm u) (earlier + 1)) =
      normSq
        (CCL.TranscendentalLaws.finiteSum
          (fun index => log1pSecondRelTerm u (earlier + 1 + index))
            extra) := by
        congr 1
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im] <;> ring1
    _ ≤ 4 * (1 / 4 : Coordinate) ^ (earlier + 1) := tailBound
    _ = CCL.FiniteGeometric.quarterRadius 1 earlier := by
      rw [four_mul_quarterPower_succ,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        RFAP.ConstructiveFraction.one_mul]

def log1pSecondRelApproximation (u : Gaussian)
    (disk : normSq u ≤ 1 / 4) : Approximation where
  sample := log1pSecondRelSample u
  radiusSq := CCL.FiniteGeometric.quarterRadius 1
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := log1pSecondRelSample_later_close disk
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 1 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 1 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := log1pSecondRelSample_bounded disk

def log1pSecondRelNamed (u : Gaussian)
    (disk : normSq u ≤ 1 / 4) : Named :=
  (log1pSecondRelApproximation u disk).toNamed

theorem log1pSecondRelNamed_productive (u : Gaussian)
    (disk : normSq u ≤ 1 / 4) (count : Nat) :
    (log1pSecondRelNamed u disk).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (log1pSecondRelNamed u disk).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (log1pSecondRelNamed u disk).machine count).emitted.length = count :=
  (log1pSecondRelApproximation u disk).output_productive count

theorem log1pRelTerm_succ_factor (u : Gaussian) (index : Nat) :
    log1pRelTerm u (index + 1) =
      u * log1pSecondRelTerm u index := by
  rw [log1pRelTerm, log1pSecondRelTerm, pow_succ]
  rw [show index + 1 + 1 = index + 2 by ring1]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, mul_re, mul_im, neg_re, neg_im,
      Nat.cast_add] <;> ring1

theorem log1pRelSample_succ_sub_one_factor (u : Gaussian) (index : Nat) :
    log1pRelSample u (index + 1) - 1 =
      u * log1pSecondRelSample u index := by
  rw [log1pRelSample,
    CCL.TranscendentalLaws.finiteSum_succ_front,
    log1pRelTerm_zero]
  calc
    1 + CCL.TranscendentalLaws.finiteSum
          (fun termIndex => log1pRelTerm u (termIndex + 1)) (index + 1) - 1 =
        CCL.TranscendentalLaws.finiteSum
          (fun termIndex => log1pRelTerm u (termIndex + 1)) (index + 1) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, one_re, one_im] <;> ring1
    _ = CCL.TranscendentalLaws.finiteSum
        (fun termIndex => u * log1pSecondRelTerm u termIndex) (index + 1) :=
      CCL.TranscendentalLaws.finiteSum_congr
        (fun termIndex => log1pRelTerm_succ_factor u termIndex) (index + 1)
    _ = u * log1pSecondRelSample u index := by
      exact (CCL.TranscendentalLaws.mul_finiteSum_left
        u (log1pSecondRelTerm u) (index + 1)).symm

theorem log1pSample_second_order_factor (u : Gaussian) (index : Nat) :
    log1pSample u (index + 1) - u =
      u ^ 2 * log1pSecondRelSample u index := by
  rw [log1pSample]
  calc
    u * log1pRelSample u (index + 1) - u =
        u * (log1pRelSample u (index + 1) - 1) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im, one_re, one_im] <;> ring1
    _ = u * (u * log1pSecondRelSample u index) := by
      rw [log1pRelSample_succ_sub_one_factor]
    _ = u ^ 2 * log1pSecondRelSample u index := by
      rw [pow_two, RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

/-- On the certified quarter disk, the quadrance of the finite local-log
linearization remainder is bounded by four times the square of the input
quadrance. -/
theorem log1pSample_second_order_normSq_le {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) (index : Nat) :
    normSq (log1pSample u (index + 1) - u) ≤
      4 * normSq u ^ 2 := by
  rw [log1pSample_second_order_factor, normSq_mul, normSq_pow]
  calc
    normSq u ^ 2 * normSq (log1pSecondRelSample u index) ≤
        normSq u ^ 2 * 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (log1pSecondRelSample_bounded disk index)
        (RFAP.ConstructiveFraction.pow_nonneg_direct (normSq_nonneg u) 2)
    _ = 4 * normSq u ^ 2 :=
      RFAP.ConstructiveFraction.mul_comm _ _

/-! ## The derivative and its reciprocal law -/

def log1pDerivativeSample (u : Gaussian) (index : Nat) : Gaussian :=
  CCL.TranscendentalLaws.finiteSum
    (fun termIndex => (-u) ^ termIndex) (index + 1)

theorem eval_log1pGeometricPolynomial (u : Gaussian) : ∀ index,
    eval (log1pGeometricPolynomial index) u =
      log1pDerivativeSample u index
  | 0 => by
      change
        CCL.FiniteExp.scale 1 1 + u * 0 =
          CCL.TranscendentalLaws.finiteSum
            (fun termIndex => (-u) ^ termIndex) (0 + 1)
      rw [CCL.TranscendentalLaws.finiteSum_succ,
        CCL.TranscendentalLaws.finiteSum_zero, pow_zero]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CCL.FiniteExp.scale_re,
          CCL.FiniteExp.scale_im, add_re, add_im, mul_re, mul_im,
          zero_re, zero_im, one_re, one_im] <;> ring1
  | index + 1 => by
      calc
        eval (log1pGeometricPolynomial (index + 1)) u =
            eval (log1pGeometricPolynomial index) u +
              CCL.FiniteExp.scale
                (alternatingSign (index + 1)) (u ^ (index + 1)) := by
          rw [log1pGeometricPolynomial, eval_add, eval_monomial]
        _ = log1pDerivativeSample u index + (-u) ^ (index + 1) := by
          rw [eval_log1pGeometricPolynomial u index,
            negPower_eq_scaledPower]
        _ = log1pDerivativeSample u (index + 1) := by
          unfold log1pDerivativeSample
          exact
            (CCL.TranscendentalLaws.finiteSum_succ
              (fun termIndex => (-u) ^ termIndex) (index + 1)).symm

/-- The actual two-input secant kernel for the same finite local-log
polynomial used by `log1pSample`. -/
def log1pSecantKernel (x y : Gaussian) (index : Nat) : Gaussian :=
  CCL.DividedDifference.polynomialKernel
    (log1pPolynomial index) x y

theorem log1pSample_sub_factor (x y : Gaussian) (index : Nat) :
    log1pSample x index - log1pSample y index =
      (x - y) * log1pSecantKernel x y index := by
  calc
    log1pSample x index - log1pSample y index =
        eval (log1pPolynomial index) x -
          eval (log1pPolynomial index) y := by
      rw [eval_log1pPolynomial, eval_log1pPolynomial]
    _ = (x - y) *
        CCL.DividedDifference.polynomialKernel
          (log1pPolynomial index) x y :=
      CCL.DividedDifference.eval_sub_factor
        (log1pPolynomial index) x y

/-- Diagonal substitution in the constructed local-log secant kernel is
exactly the finite geometric derivative program. -/
theorem log1pSecantKernel_diagonal (u : Gaussian) (index : Nat) :
    log1pSecantKernel u u index = log1pDerivativeSample u index := by
  calc
    log1pSecantKernel u u index =
        eval (derivative (log1pPolynomial index)) u :=
      CCL.DividedDifference.polynomialKernel_diagonal
        (log1pPolynomial index) u
    _ = eval (log1pGeometricPolynomial index) u :=
      eval_eq_of_coefficientwise (derivative_log1pPolynomial index) u
    _ = log1pDerivativeSample u index :=
      eval_log1pGeometricPolynomial u index

theorem log1pDerivativeSample_bounded {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) (index : Nat) :
    normSq (log1pDerivativeSample u index) ≤ 4 := by
  exact CCL.TranscendentalLaws.finiteSum_geometric_normSq_le
    (fun termIndex => (-u) ^ termIndex) (index + 1) 1 (by decide)
      (fun termIndex => by
        rw [normSq_pow, normSq_neg]
        simpa only [RFAP.ConstructiveFraction.one_mul] using
          RFAP.ConstructiveFraction.pow_le_pow_direct
            (normSq_nonneg u) disk termIndex)

theorem log1pDerivativeSample_later_close {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) {earlier later : Nat}
    (order : earlier ≤ later) :
    normSq
        (log1pDerivativeSample u later -
          log1pDerivativeSample u earlier) ≤
      CCL.FiniteGeometric.quarterRadius 1 earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [log1pDerivativeSample, log1pDerivativeSample,
    show earlier + extra + 1 = earlier + 1 + extra by ring1,
    CCL.TranscendentalLaws.finiteSum_append]
  have tailBound :=
    CCL.TranscendentalLaws.finiteSum_geometric_normSq_le
      (fun index => (-u) ^ (earlier + 1 + index)) extra
      ((1 / 4 : Coordinate) ^ (earlier + 1))
      (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
      (fun index => by
        rw [normSq_pow, normSq_neg]
        calc
          normSq u ^ (earlier + 1 + index) ≤
              (1 / 4 : Coordinate) ^ (earlier + 1 + index) :=
            RFAP.ConstructiveFraction.pow_le_pow_direct
              (normSq_nonneg u) disk _
          _ = (1 / 4 : Coordinate) ^ (earlier + 1) *
              (1 / 4 : Coordinate) ^ index :=
            quarterPower_shift earlier index)
  calc
    normSq
        (CCL.TranscendentalLaws.finiteSum
              (fun termIndex => (-u) ^ termIndex) (earlier + 1) +
            CCL.TranscendentalLaws.finiteSum
              (fun index => (-u) ^ (earlier + 1 + index)) extra -
          CCL.TranscendentalLaws.finiteSum
            (fun termIndex => (-u) ^ termIndex) (earlier + 1)) =
      normSq
        (CCL.TranscendentalLaws.finiteSum
          (fun index => (-u) ^ (earlier + 1 + index)) extra) := by
        congr 1
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im] <;> ring1
    _ ≤ 4 * (1 / 4 : Coordinate) ^ (earlier + 1) := tailBound
    _ = CCL.FiniteGeometric.quarterRadius 1 earlier := by
      rw [four_mul_quarterPower_succ,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        RFAP.ConstructiveFraction.one_mul]

def log1pDerivativeApproximation (u : Gaussian)
    (disk : normSq u ≤ 1 / 4) : Approximation where
  sample := log1pDerivativeSample u
  radiusSq := CCL.FiniteGeometric.quarterRadius 1
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := log1pDerivativeSample_later_close disk
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 1 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 1 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := log1pDerivativeSample_bounded disk

theorem log1pDerivative_geometric_remainder (u : Gaussian) (index : Nat) :
    (1 + u) * log1pDerivativeSample u index =
      1 - (-u) ^ (index + 1) := by
  rw [log1pDerivativeSample]
  induction index with
  | zero =>
      rw [CCL.TranscendentalLaws.finiteSum_succ,
        CCL.TranscendentalLaws.finiteSum_zero, pow_zero, pow_one]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im, neg_re,
          neg_im, zero_re, zero_im, one_re, one_im] <;> ring1
  | succ index inductionHypothesis =>
      rw [CCL.TranscendentalLaws.finiteSum_succ]
      calc
        (1 + u) *
            (CCL.TranscendentalLaws.finiteSum
                (fun termIndex => (-u) ^ termIndex) (index + 1) +
              (-u) ^ (index + 1)) =
          (1 - (-u) ^ (index + 1)) +
            (1 + u) * (-u) ^ (index + 1) := by
              rw [mul_add, inductionHypothesis]
        _ = 1 - (-u) ^ (index + 1 + 1) := by
          rw [show (-u) ^ (index + 1 + 1) =
            (-u) ^ (index + 1) * (-u) by
              exact pow_succ (-u) (index + 1)]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
              neg_re, neg_im, one_re, one_im] <;> ring1

theorem one_add_normSq_lower {u : Gaussian} (disk : normSq u ≤ 1 / 4) :
    (1 / 4 : Coordinate) ≤ normSq (1 + u) := by
  have realSquare : u.re ^ 2 ≤ (1 / 2 : Coordinate) ^ 2 := by
    calc
      u.re ^ 2 ≤ u.re ^ 2 + u.im ^ 2 :=
        le_add_of_nonneg_right (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ = normSq u := rfl
      _ ≤ 1 / 4 := disk
      _ = (1 / 2 : Coordinate) ^ 2 := by decide
  have realLower : -(1 / 2 : Coordinate) ≤ u.re :=
    RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct (by decide) realSquare
  have shifted : (1 / 2 : Coordinate) ≤ 1 + u.re := by
    calc
      (1 / 2 : Coordinate) = 1 + -(1 / 2) := by decide
      _ ≤ 1 + u.re := by
        simpa only [RFAP.ConstructiveFraction.add_comm] using
          add_le_add_right realLower 1
  have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
    (by decide : (0 : Coordinate) ≤ 1 / 2) shifted 2
  calc
    (1 / 4 : Coordinate) = (1 / 2 : Coordinate) ^ 2 := by decide
    _ ≤ (1 + u.re) ^ 2 := squared
    _ ≤ (1 + u.re) ^ 2 + u.im ^ 2 :=
      le_add_of_nonneg_right (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    _ = normSq (1 + u) := by
      simp only [normSq, add_re, add_im, one_re, one_im]
      ring1

theorem one_add_ne_zero {u : Gaussian} (disk : normSq u ≤ 1 / 4) :
    1 + u ≠ 0 := by
  intro zero
  have lower := one_add_normSq_lower disk
  rw [zero, normSq_zero] at lower
  exact (by decide : ¬ ((1 / 4 : Coordinate) ≤ 0)) lower

theorem one_add_inverse_normSq_le_four {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) : normSq ((1 + u)⁻¹) ≤ 4 := by
  have nonzero := one_add_ne_zero disk
  rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
    RFAP.ConstructiveGaussian.Gaussian.normSq_inv (1 + u) nonzero]
  have inverseOrder := RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct
    (by decide : (0 : Coordinate) < 1 / 4) (one_add_normSq_lower disk)
  simpa only [show (1 / 4 : Coordinate)⁻¹ = 4 by decide] using inverseOrder

theorem log1pDerivative_sub_inverse {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) (index : Nat) :
    log1pDerivativeSample u index - (1 + u)⁻¹ =
      -((-u) ^ (index + 1)) * (1 + u)⁻¹ := by
  have nonzero := one_add_ne_zero disk
  have inverseCancel : (1 + u)⁻¹ * (1 + u) = 1 := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
      RFAP.ConstructiveGaussian.Gaussian.inv_mul (1 + u) nonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne nonzero
  calc
    (log1pDerivativeSample u index - (1 + u)⁻¹) * (1 + u) =
        log1pDerivativeSample u index * (1 + u) -
          (1 + u)⁻¹ * (1 + u) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = log1pDerivativeSample u index * (1 + u) - 1 := by
      rw [inverseCancel]
    _ = (1 + u) * log1pDerivativeSample u index - 1 := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]
    _ = -((-u) ^ (index + 1)) := by
      rw [log1pDerivative_geometric_remainder]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im, one_re, one_im] <;> ring1
    _ = (-((-u) ^ (index + 1)) * (1 + u)⁻¹) * (1 + u) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc, inverseCancel,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]

theorem log1pDerivative_sub_inverse_bound {u : Gaussian}
    (disk : normSq u ≤ 1 / 4) (index : Nat) :
    normSq (log1pDerivativeSample u index - (1 + u)⁻¹) ≤
      CCL.FiniteGeometric.quarterRadius 1 index := by
  rw [log1pDerivative_sub_inverse disk, normSq_mul, normSq_neg,
    normSq_pow, normSq_neg]
  calc
    normSq u ^ (index + 1) * normSq ((1 + u)⁻¹) ≤
        (1 / 4 : Coordinate) ^ (index + 1) * 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_direct
        (RFAP.ConstructiveFraction.pow_le_pow_direct
          (normSq_nonneg u) disk (index + 1))
        (one_add_inverse_normSq_le_four disk)
        (normSq_nonneg _)
        (show 0 ≤ (1 / 4 : Coordinate) ^ (index + 1) from
          RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _)
    _ = CCL.FiniteGeometric.quarterRadius 1 index := by
      rw [RFAP.ConstructiveFraction.mul_comm,
        four_mul_quarterPower_succ,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        RFAP.ConstructiveFraction.one_mul]

private theorem quarterRadius_one_antitone {earlier later : Nat}
    (order : earlier ≤ later) :
    CCL.FiniteGeometric.quarterRadius 1 later ≤
      CCL.FiniteGeometric.quarterRadius 1 earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    simpa only [one_pow] using RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 4)
      (by decide : (1 / 4 : Coordinate) ≤ 1) extra
  have nonnegative : 0 ≤ (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  simpa only [RFAP.ConstructiveFraction.one_mul,
    RFAP.ConstructiveFraction.mul_one_direct] using
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      extraLe nonnegative

/-- Finite-request statement of `d log(1+u)/du = 1/(1+u)`.  The right side
is an exact Gaussian rational for this displayed rational input; every
requested positive squared tolerance is met by a computed finite truncation
index on the left. -/
def log1p_derivative_equivalent_inverse (u : Gaussian)
    (disk : normSq u ≤ 1 / 4) :
    Equivalent (log1pDerivativeApproximation u disk)
      (CCL.TranscendentalLaws.constantApproximation
        ((1 + u)⁻¹)) where
  compare := by
    intro leftStart rightStart target positive
    let index := (log1pDerivativeApproximation u disk).refineIndex
      leftStart target positive
    have radiusSmall :
        CCL.FiniteGeometric.quarterRadius 1 index < target :=
      (log1pDerivativeApproximation u disk).refineIndex_accurate
        leftStart target positive
    exact
      { leftIndex := index
        rightIndex := rightStart
        left_ge := (log1pDerivativeApproximation u disk).refineIndex_ge
          leftStart target positive
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change normSq
              (log1pDerivativeSample u leftLater - (1 + u)⁻¹) < target
          exact (log1pDerivative_sub_inverse_bound disk leftLater).trans_lt
            ((quarterRadius_one_antitone leftOrder).trans_lt radiusSmall) }

/-! ## From a local coordinate to an anchored logarithm branch -/

/-- For `x = anchor * (1+u)`, the local derivative target followed by the
affine chart derivative is exactly `x⁻¹`.  A branch correction is constant
with respect to `x`, so it contributes the exact zero derivative. -/
theorem anchoredLogDerivative_inverse (anchor u : Gaussian)
    (anchorNonzero : anchor ≠ 0) (disk : normSq u ≤ 1 / 4) :
    (1 + u)⁻¹ * anchor⁻¹ = (anchor * (1 + u))⁻¹ := by
  have oneAddNonzero := one_add_ne_zero disk
  have productNonzero :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      anchorNonzero oneAddNonzero
  have anchorCancel : anchor⁻¹ * anchor = 1 := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
      RFAP.ConstructiveGaussian.Gaussian.inv_mul anchor anchorNonzero
  have oneAddCancel : (1 + u)⁻¹ * (1 + u) = 1 := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
      RFAP.ConstructiveGaussian.Gaussian.inv_mul (1 + u) oneAddNonzero
  have productCancel :
      (anchor * (1 + u))⁻¹ * (anchor * (1 + u)) = 1 := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.inv_eq] using
      RFAP.ConstructiveGaussian.Gaussian.inv_mul
        (anchor * (1 + u)) productNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    productNonzero
  calc
    ((1 + u)⁻¹ * anchor⁻¹) * (anchor * (1 + u)) =
        ((1 + u)⁻¹ * (1 + u)) * (anchor⁻¹ * anchor) := by
      ring1
    _ = 1 := by
      rw [oneAddCancel, anchorCancel,
        RFAP.ConstructiveGaussian.Gaussian.one_mul]
    _ = (anchor * (1 + u))⁻¹ * (anchor * (1 + u)) :=
      productCancel.symm

end CCL.LogarithmicCalculus
