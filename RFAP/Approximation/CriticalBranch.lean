import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.FiniteWindowSharpness

/-!
# Finite recurrence of the critical Pell branch

The critical sharpness pairs are not unrelated witnesses.  Successive pair
bases are connected by one fixed Gaussian-integral unimodular matrix.  This
is the finite algebraic dynamics underlying the candidate coherent critical
branch; it introduces neither its omitted irrational endpoint nor an
infinite sequence object beyond evaluation at a supplied natural stage.
-/

namespace RFAP.CriticalBranch

abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation

/-- Coefficient of the old lower pair in the next lower pair. -/
def lowerFromLower : GaussianInt := ⟨0, 1⟩

/-- Coefficient of the old upper pair in the next lower pair. -/
def lowerFromUpper : GaussianInt := ⟨0, -2⟩

/-- Coefficient of the old lower pair in the next upper pair. -/
def upperFromLower : GaussianInt := ⟨-2, 0⟩

/-- Coefficient of the old upper pair in the next upper pair. -/
def upperFromUpper : GaussianInt := ⟨4, -1⟩

/-- The fixed critical-branch coefficient matrix has Gaussian determinant
one. -/
theorem transitionDeterminant :
    lowerFromLower * upperFromUpper -
      lowerFromUpper * upperFromLower = 1 := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [lowerFromLower, lowerFromUpper, upperFromLower,
      upperFromUpper,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_im] <;>
    ring1

/-- The next lower critical pair is the same fixed Gaussian-integral linear
combination of the preceding pair basis at every supplied stage. -/
theorem criticalLowerPair_succ (stage : Nat) :
    RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 1) =
      linearCombination
        (RFAP.FiniteWindowSharpness.criticalLowerPair stage)
        (RFAP.FiniteWindowSharpness.criticalUpperPair stage)
        lowerFromLower lowerFromUpper := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [RFAP.FiniteWindowSharpness.criticalLowerPair,
      RFAP.FiniteWindowSharpness.criticalUpperPair, linearCombination,
      lowerFromLower, lowerFromUpper,
      RFAP.FiniteWindowSharpness.pellNumerator_succ,
      RFAP.FiniteWindowSharpness.pellDifference_succ,
      RFAP.FiniteWindowSharpness.pellDenominator,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- The next upper critical pair is the same fixed Gaussian-integral linear
combination of the preceding pair basis at every supplied stage. -/
theorem criticalUpperPair_succ (stage : Nat) :
    RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 1) =
      linearCombination
        (RFAP.FiniteWindowSharpness.criticalLowerPair stage)
        (RFAP.FiniteWindowSharpness.criticalUpperPair stage)
        upperFromLower upperFromUpper := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [RFAP.FiniteWindowSharpness.criticalLowerPair,
      RFAP.FiniteWindowSharpness.criticalUpperPair, linearCombination,
      upperFromLower, upperFromUpper,
      RFAP.FiniteWindowSharpness.pellNumerator_succ,
      RFAP.FiniteWindowSharpness.pellDifference_succ,
      RFAP.FiniteWindowSharpness.pellDenominator,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- The next Pell numerator is the current denominator. -/
theorem pellNumerator_succ_eq_denominator (stage : Nat) :
    RFAP.FiniteWindowSharpness.pellNumerator (stage + 1) =
      RFAP.FiniteWindowSharpness.pellDenominator stage := by
  rw [RFAP.FiniteWindowSharpness.pellNumerator_succ]
  rfl

/-- Subtraction-free denominator form of `n_(k+1)=4n_k-m_k`. -/
theorem pellDenominator_succ_add_numerator (stage : Nat) :
    RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) +
        RFAP.FiniteWindowSharpness.pellNumerator stage =
      4 * RFAP.FiniteWindowSharpness.pellDenominator stage := by
  unfold RFAP.FiniteWindowSharpness.pellDenominator
  rw [RFAP.FiniteWindowSharpness.pellNumerator_succ,
    RFAP.FiniteWindowSharpness.pellDifference_succ]
  ring1

/-- Division-free form of the finite Pell parameter transition. -/
theorem four_sub_parameter_mul_denominator (stage : Nat) :
    (4 - RFAP.FiniteWindowSharpness.pellParameter stage) *
        (RFAP.FiniteWindowSharpness.pellDenominator stage :
          RFAP.ConstructiveFraction.Rational) =
      (RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) :
        RFAP.ConstructiveFraction.Rational) := by
  have castIdentity := congrArg
    (fun value : Nat => (value : RFAP.ConstructiveFraction.Rational))
    (pellDenominator_succ_add_numerator stage)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at castIdentity
  calc
    (4 - RFAP.FiniteWindowSharpness.pellParameter stage) *
          (RFAP.FiniteWindowSharpness.pellDenominator stage :
            RFAP.ConstructiveFraction.Rational) =
        4 * (RFAP.FiniteWindowSharpness.pellDenominator stage :
            RFAP.ConstructiveFraction.Rational) -
          RFAP.FiniteWindowSharpness.pellParameter stage *
            (RFAP.FiniteWindowSharpness.pellDenominator stage :
              RFAP.ConstructiveFraction.Rational) := by ring1
    _ = 4 * (RFAP.FiniteWindowSharpness.pellDenominator stage :
            RFAP.ConstructiveFraction.Rational) -
          (RFAP.FiniteWindowSharpness.pellNumerator stage :
            RFAP.ConstructiveFraction.Rational) := by
      rw [RFAP.FiniteWindowSharpness.pellParameter_mul_denominator]
    _ = ((RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) : Nat) :
          RFAP.ConstructiveFraction.Rational) := by
      rw [← castIdentity]
      ring1

/-- Exact Möbius recurrence for the supplied finite Pell parameter. -/
theorem pellParameter_succ_mul_four_sub (stage : Nat) :
    RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
        (4 - RFAP.FiniteWindowSharpness.pellParameter stage) = 1 := by
  have denominatorPositive :
      (0 : RFAP.ConstructiveFraction.Rational) <
        (RFAP.FiniteWindowSharpness.pellDenominator stage :
          RFAP.ConstructiveFraction.Rational) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (RFAP.FiniteWindowSharpness.pellDenominator_pos stage)
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    (RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
          (4 - RFAP.FiniteWindowSharpness.pellParameter stage)) *
        (RFAP.FiniteWindowSharpness.pellDenominator stage :
          RFAP.ConstructiveFraction.Rational) =
      RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
        ((4 - RFAP.FiniteWindowSharpness.pellParameter stage) *
          (RFAP.FiniteWindowSharpness.pellDenominator stage :
            RFAP.ConstructiveFraction.Rational)) := by ring1
    _ = RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
        (RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) :
          RFAP.ConstructiveFraction.Rational) := by
      rw [four_sub_parameter_mul_denominator]
    _ = (RFAP.FiniteWindowSharpness.pellNumerator (stage + 1) :
          RFAP.ConstructiveFraction.Rational) :=
      RFAP.FiniteWindowSharpness.pellParameter_mul_denominator (stage + 1)
    _ = (RFAP.FiniteWindowSharpness.pellDenominator stage :
          RFAP.ConstructiveFraction.Rational) := by
      rw [pellNumerator_succ_eq_denominator]
    _ = 1 * (RFAP.FiniteWindowSharpness.pellDenominator stage :
          RFAP.ConstructiveFraction.Rational) := by ring1

/-- Polynomial form of the inverse parameter transition, used by the error
coordinate of the next pair basis. -/
theorem four_mul_pellParameter_succ_sub_one (stage : Nat) :
    4 * RFAP.FiniteWindowSharpness.pellParameter (stage + 1) - 1 =
      RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
        RFAP.FiniteWindowSharpness.pellParameter stage := by
  calc
    4 * RFAP.FiniteWindowSharpness.pellParameter (stage + 1) - 1 =
        4 * RFAP.FiniteWindowSharpness.pellParameter (stage + 1) -
          RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
            (4 - RFAP.FiniteWindowSharpness.pellParameter stage) := by
      rw [pellParameter_succ_mul_four_sub]
    _ = RFAP.FiniteWindowSharpness.pellParameter (stage + 1) *
        RFAP.FiniteWindowSharpness.pellParameter stage := by ring1

/-- The finite Pell parameters increase strictly at each supplied stage. -/
theorem pellParameter_lt_succ (stage : Nat) :
    RFAP.FiniteWindowSharpness.pellParameter stage <
      RFAP.FiniteWindowSharpness.pellParameter (stage + 1) := by
  let current := RFAP.FiniteWindowSharpness.pellParameter stage
  let next := RFAP.FiniteWindowSharpness.pellParameter (stage + 1)
  have factorPositive : (0 : RFAP.ConstructiveFraction.Rational) <
      4 - current := by
    apply RFAP.ConstructiveFraction.sub_pos_direct
    exact (RFAP.FiniteWindowSharpness.pellParameter_lt_oneThird stage).trans
      (by decide)
  have productPositive :
      (0 : RFAP.ConstructiveFraction.Rational) <
        (4 - current) * (next - current) := by
    calc
      (0 : RFAP.ConstructiveFraction.Rational) <
          RFAP.FiniteWindowSharpness.parameterPolynomial current := by
        exact RFAP.FiniteWindowSharpness.parameterPolynomial_pellParameter_pos
          stage
      _ = 1 - current * (4 - current) := by
        unfold RFAP.FiniteWindowSharpness.parameterPolynomial
        ring1
      _ = next * (4 - current) - current * (4 - current) := by
        dsimp only [current, next]
        rw [pellParameter_succ_mul_four_sub]
      _ = (4 - current) * (next - current) := by ring1
  exact RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    (RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      productPositive factorPositive.le)

/-- Pointwise monotonicity of finite Pell evaluation, proved by induction on
the supplied natural-stage comparison. -/
theorem pellParameter_le_of_le {first second : Nat}
    (stageOrder : first ≤ second) :
    RFAP.FiniteWindowSharpness.pellParameter first ≤
      RFAP.FiniteWindowSharpness.pellParameter second := by
  induction stageOrder with
  | refl => exact le_refl _
  | @step second stageOrder inductionHypothesis =>
      exact inductionHypothesis.trans
        (pellParameter_lt_succ second).le

/-- The upper scale of one critical window lies strictly below the lower
scale of the next.  Together with the within-stage ordering, this makes the
finite Pell branch strictly ordered without an appeal to a limit. -/
theorem criticalUpper_lt_nextLower_denominatorQuadrance (stage : Nat) :
    denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair stage) <
      denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalLowerPair (stage + 1)) := by
  have numeratorPositive :=
    RFAP.FiniteWindowSharpness.pellNumerator_pos stage
  have differencePositive :=
    RFAP.FiniteWindowSharpness.pellDifference_pos stage
  have numeratorLtDouble :
      RFAP.FiniteWindowSharpness.pellNumerator stage <
        2 * RFAP.FiniteWindowSharpness.pellNumerator stage := by
    simpa only [one_mul] using
      Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) numeratorPositive
  have differenceLtTriple :
      RFAP.FiniteWindowSharpness.pellDifference stage <
        3 * RFAP.FiniteWindowSharpness.pellDifference stage := by
    simpa only [one_mul] using
      Nat.mul_lt_mul_of_pos_right (by decide : 1 < 3) differencePositive
  have denominatorLtDifferenceSucc :
      RFAP.FiniteWindowSharpness.pellNumerator stage +
          RFAP.FiniteWindowSharpness.pellDifference stage <
        2 * RFAP.FiniteWindowSharpness.pellNumerator stage +
          3 * RFAP.FiniteWindowSharpness.pellDifference stage :=
    Nat.add_lt_add numeratorLtDouble differenceLtTriple
  have doubledDenominatorLtNext :
      2 * RFAP.FiniteWindowSharpness.pellDenominator stage <
        RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) := by
    unfold RFAP.FiniteWindowSharpness.pellDenominator
    rw [RFAP.FiniteWindowSharpness.pellNumerator_succ,
      RFAP.FiniteWindowSharpness.pellDifference_succ]
    calc
      2 * (RFAP.FiniteWindowSharpness.pellNumerator stage +
          RFAP.FiniteWindowSharpness.pellDifference stage) =
          (RFAP.FiniteWindowSharpness.pellNumerator stage +
              RFAP.FiniteWindowSharpness.pellDifference stage) +
            (RFAP.FiniteWindowSharpness.pellNumerator stage +
              RFAP.FiniteWindowSharpness.pellDifference stage) := by ring1
      _ < (RFAP.FiniteWindowSharpness.pellNumerator stage +
              RFAP.FiniteWindowSharpness.pellDifference stage) +
            (2 * RFAP.FiniteWindowSharpness.pellNumerator stage +
              3 * RFAP.FiniteWindowSharpness.pellDifference stage) :=
        Nat.add_lt_add_left denominatorLtDifferenceSucc _
  have squareStrict :
      (2 * RFAP.FiniteWindowSharpness.pellDenominator stage) ^ 2 <
        RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) ^ 2 := by
    simpa only [pow_two] using
      RFAP.FiniteWindowSharpness.natMulSelf_lt_natMulSelf
        doubledDenominatorLtNext
  rw [RFAP.FiniteWindowSharpness.criticalUpper_denominatorQuadrance,
    RFAP.FiniteWindowSharpness.criticalLower_denominatorQuadrance]
  calc
    4 * RFAP.FiniteWindowSharpness.pellDenominator stage ^ 2 =
        (2 * RFAP.FiniteWindowSharpness.pellDenominator stage) ^ 2 := by
      ring1
    _ < RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) ^ 2 :=
      squareStrict
    _ ≤ RFAP.FiniteWindowSharpness.pellNumerator (stage + 1) ^ 2 +
          RFAP.FiniteWindowSharpness.pellDenominator (stage + 1) ^ 2 :=
      Nat.le_add_left _ _

/-- Upper critical-window scales increase at every finite branch step. -/
theorem criticalUpper_denominatorQuadrance_lt_succ (stage : Nat) :
    denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair stage) <
      denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair (stage + 1)) :=
  (criticalUpper_lt_nextLower_denominatorQuadrance stage).trans
    (RFAP.FiniteWindowSharpness.critical_denominatorQuadrance_ordered
      (stage + 1))

/-- Monotonicity of upper critical-window scale between two supplied finite
stages. -/
theorem criticalUpper_denominatorQuadrance_le_of_le
    {first second : Nat} (stageOrder : first ≤ second) :
    denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair first) ≤
      denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair second) := by
  induction stageOrder with
  | refl => exact le_refl _
  | @step second stageOrder inductionHypothesis =>
      exact inductionHypothesis.trans
        (criticalUpper_denominatorQuadrance_lt_succ second).le

/-- Strict upper-scale growth between strictly ordered finite stages. -/
theorem criticalUpper_denominatorQuadrance_lt_of_lt
    {first second : Nat} (stageOrder : first < second) :
    denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair first) <
      denominatorQuadrance
        (RFAP.FiniteWindowSharpness.criticalUpperPair second) :=
  (criticalUpper_denominatorQuadrance_lt_succ first).trans_le
    (criticalUpper_denominatorQuadrance_le_of_le stageOrder)

end RFAP.CriticalBranch
