import mathlib.Tactic.QuotientFreeRing
import CCL.Calculus.DividedDifference

/-!
# Executable, limit-free differential laws for the exponential

The relative exponential is not introduced by dividing by its argument.
Instead, `expRelSample z n` is the already finite inner Horner program, and
the factorization

`expSample z n - 1 = z * expRelSample z n`

is proved at every displayed depth, including `z = 0`.  A second shifted
Horner program gives a quadratic remainder.  All approximation objects below
contain only Gaussian-rational samples, rational squared-error allowances,
and terminating natural-number refinement programs.
-/

namespace CCL.ExponentialCalculus

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent

open RFAP.ConstructiveGaussian.Gaussian

/-! ## The first relative exponential -/

/-- The finite program for `(exp z - 1) / z`, defined without division by
`z`.  At zero it evaluates directly to one. -/
def expRelSample (z : Gaussian) (index : Nat) : Gaussian :=
  CCL.FiniteExp.horner z 2 index

theorem expRelSample_zero (index : Nat) : expRelSample 0 index = 1 :=
  CCL.FiniteExp.horner_zero_input index 2

theorem expRelSample_later_close {z : Gaussian}
    (unitInput : normSq z ≤ 1) {earlier later : Nat}
    (order : earlier ≤ later) :
    normSq (expRelSample z later - expRelSample z earlier) ≤
      CCL.FiniteGeometric.quarterRadius 10 earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  simpa only [expRelSample,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow] using
      CCL.FiniteExp.horner_add_depth_close z unitInput
        earlier extra 2 (by decide)

theorem expRelSample_bounded {z : Gaussian}
    (unitInput : normSq z ≤ 1) (index : Nat) :
    normSq (expRelSample z index) ≤ 4 :=
  CCL.FiniteExp.horner_bounded z unitInput index 2 (by decide)

/-- Progressive CCL-ready relative-exponential computation on the rational
unit disk. -/
def expRelApproximation (z : Gaussian)
    (unitInput : normSq z ≤ 1) : Approximation where
  sample := expRelSample z
  radiusSq := CCL.FiniteGeometric.quarterRadius 10
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg (by decide)
  later_close := expRelSample_later_close unitInput
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 10 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 10 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 10 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := expRelSample_bounded unitInput

def expRelNamed (z : Gaussian) (unitInput : normSq z ≤ 1) : Named :=
  (expRelApproximation z unitInput).toNamed

theorem expRelNamed_productive (z : Gaussian) (unitInput : normSq z ≤ 1)
    (count : Nat) :
    (expRelNamed z unitInput).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (expRelNamed z unitInput).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (expRelNamed z unitInput).machine count).emitted.length = count :=
  (expRelApproximation z unitInput).output_productive count

/-- Exact finite-depth factorization.  It is valid at zero because no
division has been performed. -/
theorem expSample_sub_one_factor (z : Gaussian) (index : Nat) :
    CCL.FiniteExp.sample z index - 1 =
      z * expRelSample z index := by
  rw [CCL.FiniteExp.sample,
    CCL.FiniteExp.step_eq]
  rw [show (1 / ((1 : Nat) : Coordinate)) = 1 by decide]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, add_re, add_im, sub_re, sub_im,
      mul_re, mul_im, one_re, one_im, expRelSample] <;> ring1

/-! ## A quadratic relative remainder -/

/-- The finite program for the second relative exponential.  Its intended
identity is `expRel z - 1 = z * expSecondRel z`; the definition itself is a
shifted finite Horner program, not a quotient. -/
def expSecondRelSample (z : Gaussian) (index : Nat) : Gaussian :=
  CCL.FiniteExp.scale (1 / 2)
    (CCL.FiniteExp.horner z 3 index)

def expSecondRelErrorScale : Coordinate := 5 / 2

theorem expSecondRelErrorScale_nonneg :
    0 ≤ expSecondRelErrorScale := by decide

private theorem expSecondRelSample_sub (z : Gaussian) (left right : Nat) :
    expSecondRelSample z left - expSecondRelSample z right =
      CCL.FiniteExp.scale (1 / 2)
        (CCL.FiniteExp.horner z 3 left -
          CCL.FiniteExp.horner z 3 right) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [expSecondRelSample, CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, sub_re, sub_im] <;> ring1

theorem expSecondRelSample_later_close {z : Gaussian}
    (unitInput : normSq z ≤ 1) {earlier later : Nat}
    (order : earlier ≤ later) :
    normSq
        (expSecondRelSample z later - expSecondRelSample z earlier) ≤
      CCL.FiniteGeometric.quarterRadius
        expSecondRelErrorScale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [expSecondRelSample_sub, CCL.FiniteExp.normSq_scale]
  have close := CCL.FiniteExp.horner_add_depth_close z unitInput
    earlier extra 3 (by decide)
  calc
    (1 / 2 : Coordinate) ^ 2 *
          normSq
            (CCL.FiniteExp.horner z 3 (earlier + extra) -
              CCL.FiniteExp.horner z 3 earlier) ≤
        (1 / 2 : Coordinate) ^ 2 *
          (10 * (1 / 4 : Coordinate) ^ earlier) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct close
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    _ = CCL.FiniteGeometric.quarterRadius
        expSecondRelErrorScale earlier := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      dsimp only [expSecondRelErrorScale]
      rw [← RFAP.ConstructiveFraction.mul_assoc,
        show (1 / 2 : Coordinate) ^ 2 * 10 = 5 / 2 by decide]

theorem expSecondRelSample_bounded {z : Gaussian}
    (unitInput : normSq z ≤ 1) (index : Nat) :
    normSq (expSecondRelSample z index) ≤ 1 := by
  rw [expSecondRelSample, CCL.FiniteExp.normSq_scale]
  calc
    (1 / 2 : Coordinate) ^ 2 *
          normSq (CCL.FiniteExp.horner z 3 index) ≤
        (1 / 2 : Coordinate) ^ 2 * 4 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (CCL.FiniteExp.horner_bounded z unitInput index 3
          (by decide))
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    _ = 1 := by decide

def expSecondRelApproximation (z : Gaussian)
    (unitInput : normSq z ≤ 1) : Approximation where
  sample := expSecondRelSample z
  radiusSq := CCL.FiniteGeometric.quarterRadius
    expSecondRelErrorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      expSecondRelErrorScale_nonneg
  later_close := expSecondRelSample_later_close unitInput
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      expSecondRelErrorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      expSecondRelErrorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      expSecondRelErrorScale expSecondRelErrorScale_nonneg
  centerBound := 1
  centerBound_nonneg := by decide
  sample_bounded := expSecondRelSample_bounded unitInput

def expSecondRelNamed (z : Gaussian) (unitInput : normSq z ≤ 1) : Named :=
  (expSecondRelApproximation z unitInput).toNamed

theorem expSecondRelNamed_productive (z : Gaussian)
    (unitInput : normSq z ≤ 1) (count : Nat) :
    (expSecondRelNamed z unitInput).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (expSecondRelNamed z unitInput).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (expSecondRelNamed z unitInput).machine count).emitted.length = count :=
  (expSecondRelApproximation z unitInput).output_productive count

theorem expRelSample_succ_sub_one_factor (z : Gaussian) (index : Nat) :
    expRelSample z (index + 1) - 1 =
      z * expSecondRelSample z index := by
  rw [expRelSample, CCL.FiniteExp.horner_succ,
    CCL.FiniteExp.step_eq]
  rw [show (1 / ((2 : Nat) : Coordinate)) = 1 / 2 by decide]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [expSecondRelSample, CCL.FiniteExp.scale_re,
      CCL.FiniteExp.scale_im, add_re, add_im, sub_re, sub_im,
      mul_re, mul_im, one_re, one_im, Nat.reduceAdd] <;> ring1

theorem expSample_second_order_factor (z : Gaussian) (index : Nat) :
    CCL.FiniteExp.sample z (index + 1) - 1 - z =
      z ^ 2 * expSecondRelSample z index := by
  calc
    CCL.FiniteExp.sample z (index + 1) - 1 - z =
        z * expRelSample z (index + 1) - z := by
      rw [expSample_sub_one_factor]
    _ = z * (expRelSample z (index + 1) - 1) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im, one_re, one_im] <;> ring1
    _ = z * (z * expSecondRelSample z index) := by
      rw [expRelSample_succ_sub_one_factor]
    _ = z ^ 2 * expSecondRelSample z index := by
      rw [pow_two, RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

/-- On the rational unit disk, the quadrance of the finite linearization
remainder is at most the square of the input quadrance.  This is the explicit
finite meaning of the ordinary-magnitude phrase "quadratic error". -/
theorem expSample_second_order_normSq_le {z : Gaussian}
    (unitInput : normSq z ≤ 1) (index : Nat) :
    normSq (CCL.FiniteExp.sample z (index + 1) - 1 - z) ≤
      normSq z ^ 2 := by
  rw [expSample_second_order_factor, normSq_mul, normSq_pow]
  calc
    normSq z ^ 2 * normSq (expSecondRelSample z index) ≤
        normSq z ^ 2 * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (expSecondRelSample_bounded unitInput index)
        (RFAP.ConstructiveFraction.pow_nonneg_direct (normSq_nonneg z) 2)
    _ = normSq z ^ 2 :=
      RFAP.ConstructiveFraction.mul_one_direct _

/-! ## Differential law for the executable exponential -/

/-- The finite secant factor for translating the exponential computation by
`increment`.  On its diagonal (`increment = 0`) it is the displayed
exponential sample itself. -/
def expDifferentialSample (base increment : Gaussian) (index : Nat) : Gaussian :=
  CCL.FiniteExp.sample base index * expRelSample increment index

theorem expDifferentialSample_diagonal (base : Gaussian) (index : Nat) :
    expDifferentialSample base 0 index =
      CCL.FiniteExp.sample base index := by
  rw [expDifferentialSample, expRelSample_zero,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- The product computation of `exp(base) * exp(increment)` has an exact
finite first-order factorization at every sample depth. -/
theorem expProductSample_sub_base_factor (base increment : Gaussian)
    (index : Nat) :
    CCL.TranscendentalLaws.expProductSample base increment index -
        CCL.FiniteExp.sample base index =
      increment * expDifferentialSample base increment index := by
  rw [CCL.TranscendentalLaws.expProductSample,
    expDifferentialSample]
  calc
    CCL.FiniteExp.sample base index *
          CCL.FiniteExp.sample increment index -
        CCL.FiniteExp.sample base index =
      CCL.FiniteExp.sample base index *
        (CCL.FiniteExp.sample increment index - 1) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, mul_re, mul_im, one_re, one_im] <;> ring1
    _ = CCL.FiniteExp.sample base index *
        (increment * expRelSample increment index) := by
      rw [expSample_sub_one_factor]
    _ = increment *
        (CCL.FiniteExp.sample base index *
          expRelSample increment index) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im] <;> ring1

/-- After subtracting its diagonal factor, the translated exponential
computation has an exact quadratic remainder at each positive displayed
depth. -/
theorem expProductSample_second_order (base increment : Gaussian)
    (index : Nat) :
    CCL.TranscendentalLaws.expProductSample base increment
          (index + 1) -
        CCL.FiniteExp.sample base (index + 1) -
        increment * CCL.FiniteExp.sample base (index + 1) =
      increment ^ 2 *
        (CCL.FiniteExp.sample base (index + 1) *
          expSecondRelSample increment index) := by
  rw [CCL.TranscendentalLaws.expProductSample]
  calc
    CCL.FiniteExp.sample base (index + 1) *
          CCL.FiniteExp.sample increment (index + 1) -
        CCL.FiniteExp.sample base (index + 1) -
        increment * CCL.FiniteExp.sample base (index + 1) =
      CCL.FiniteExp.sample base (index + 1) *
        (CCL.FiniteExp.sample increment (index + 1) - 1 -
          increment) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, mul_re, mul_im, one_re, one_im] <;> ring1
    _ = CCL.FiniteExp.sample base (index + 1) *
        (increment ^ 2 * expSecondRelSample increment index) := by
      rw [expSample_second_order_factor]
    _ = increment ^ 2 *
        (CCL.FiniteExp.sample base (index + 1) *
          expSecondRelSample increment index) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im, pow_two] <;> ring1

/-- The translated product program has a uniform, wholly rational quadratic
quadrance bound on the two displayed unit disks. -/
theorem expProductSample_second_order_normSq_le {base increment : Gaussian}
    (baseUnit : normSq base ≤ 1) (incrementUnit : normSq increment ≤ 1)
    (index : Nat) :
    normSq
        (CCL.TranscendentalLaws.expProductSample base increment
              (index + 1) -
            CCL.FiniteExp.sample base (index + 1) -
            increment * CCL.FiniteExp.sample base (index + 1)) ≤
      10 * normSq increment ^ 2 := by
  rw [expProductSample_second_order, normSq_mul, normSq_pow, normSq_mul]
  have cofactorBound :
      normSq (CCL.FiniteExp.sample base (index + 1)) *
          normSq (expSecondRelSample increment index) ≤ 10 := by
    calc
      normSq (CCL.FiniteExp.sample base (index + 1)) *
            normSq (expSecondRelSample increment index) ≤ 10 * 1 :=
        RFAP.ConstructiveFraction.mul_le_mul_direct
          (CCL.FiniteExp.sample_bounded base baseUnit (index + 1))
          (expSecondRelSample_bounded incrementUnit index)
          (normSq_nonneg (expSecondRelSample increment index)) (by decide)
      _ = 10 := RFAP.ConstructiveFraction.mul_one_direct _
  calc
    normSq increment ^ 2 *
          (normSq (CCL.FiniteExp.sample base (index + 1)) *
            normSq (expSecondRelSample increment index)) ≤
        normSq increment ^ 2 * 10 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct cofactorBound
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          (normSq_nonneg increment) 2)
    _ = 10 * normSq increment ^ 2 :=
      RFAP.ConstructiveFraction.mul_comm _ _

/-- The translated product computation used in the exact secant identities
is operationally the direct `exp(base + increment)` computation.  Thus the
factorization is about the CCL-computable exponential, not a separate formal
surrogate. -/
def expDifferential_equivalent_direct {base increment : Gaussian}
    (baseUnit : normSq base ≤ 1) (incrementUnit : normSq increment ≤ 1)
    (sumUnit : normSq (base + increment) ≤ 1) :
    Equivalent
      (CCL.TranscendentalLaws.expProductApproximation
        base increment baseUnit incrementUnit)
      (CCL.FiniteExp.approximation
        (base + increment) sumUnit) :=
  CCL.TranscendentalLaws.exp_add_equivalent
    baseUnit incrementUnit sumUnit

end CCL.ExponentialCalculus
