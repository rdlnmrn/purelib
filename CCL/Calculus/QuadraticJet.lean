import mathlib.Tactic.QuotientFreeRing
import CCL.Calculus.Logarithmic

/-!
# Compositional quadratic-remainder certificates

A certificate is a finite tuple of displayed Gaussian rationals.  It records
an exact first-order expansion at one displayed increment and a rational
quadrance bound for its remainder.  Addition, negation, scalar multiplication,
and composition compute new factors from old ones.  Thus a composite
calculation retains an executable remainder budget instead of appealing to
limits, infinitesimals, or an unspecified big-O relation.
-/

namespace CCL.QuadraticJet

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

/-- A finite first-order expansion with a displayed quadratic quadrance
factor at the indexed increment. -/
structure Certificate (increment : Gaussian) where
  base : Gaussian
  slope : Gaussian
  output : Gaussian
  remainder : Gaussian
  expansion : output - base - increment * slope = remainder
  factor : Coordinate
  factor_nonneg : 0 ≤ factor
  remainder_le : normSq remainder ≤ factor * normSq increment ^ 2

namespace Certificate

theorem remainder_zero_of_increment_zero {increment : Gaussian}
    (certificate : Certificate increment) (zero : increment = 0) :
    certificate.remainder = 0 := by
  subst increment
  have bound := certificate.remainder_le
  rw [normSq_zero, zero_pow (by decide : (2 : Nat) ≠ 0),
    RFAP.ConstructiveFraction.mul_zero_direct] at bound
  exact normSq_eq_zero.mp
    (le_antisymm bound (normSq_nonneg certificate.remainder))

theorem output_eq_base_of_increment_zero {increment : Gaussian}
    (certificate : Certificate increment) (zero : increment = 0) :
    certificate.output = certificate.base := by
  subst increment
  have expansion := certificate.expansion
  have remainderZero := certificate.remainder_zero_of_increment_zero rfl
  rw [remainderZero] at expansion
  have difference : certificate.output - certificate.base = 0 := by
    simpa using expansion
  exact sub_eq_zero.mp difference

/-- The exact displayed remainder ratio.  Its zero-increment branch is
handled separately, so the definition never divides by a possible zero. -/
def exactFactor (increment remainder : Gaussian) : Coordinate :=
  if increment = 0 then 0
  else normSq remainder / normSq increment ^ 2

theorem exactFactor_nonneg (increment remainder : Gaussian) :
    0 ≤ exactFactor increment remainder := by
  unfold exactFactor
  split
  · exact le_rfl
  · exact RFAP.ConstructiveFraction.div_nonneg_direct
      (normSq_nonneg remainder)
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        (normSq_nonneg increment) 2)

theorem exactFactor_bound (increment remainder : Gaussian)
    (zeroRemainder : increment = 0 → remainder = 0) :
    normSq remainder ≤ exactFactor increment remainder *
      normSq increment ^ 2 := by
  by_cases zero : increment = 0
  · rw [zeroRemainder zero, normSq_zero]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (exactFactor_nonneg increment 0)
      (RFAP.ConstructiveFraction.pow_nonneg_direct (normSq_nonneg increment) 2)
  · rw [exactFactor, if_neg zero]
    have denominatorPositive : 0 < normSq increment ^ 2 :=
      RFAP.ConstructiveFraction.pow_pos_direct (normSq_pos zero) 2
    calc
      normSq remainder ≤ normSq remainder := le_rfl
      _ = normSq remainder / normSq increment ^ 2 *
          normSq increment ^ 2 :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          (normSq remainder) (normSq increment ^ 2)
            denominatorPositive.ne').symm

/-- Construct a certificate from one exact displayed expansion.  For a
nonzero increment the rational factor is the exact remainder ratio; at zero
the caller supplies the algebraic zero-remainder proof. -/
def ofExpansion (increment base slope output remainder : Gaussian)
    (expansion : output - base - increment * slope = remainder)
    (zeroRemainder : increment = 0 → remainder = 0) :
    Certificate increment :=
  { base := base
    slope := slope
    output := output
    remainder := remainder
    expansion := expansion
    factor := exactFactor increment remainder
    factor_nonneg := exactFactor_nonneg increment remainder
    remainder_le := exactFactor_bound increment remainder zeroRemainder }

/-- An exact affine calculation has zero quadratic remainder. -/
def affine (increment base slope : Gaussian) : Certificate increment :=
  { base := base
    slope := slope
    output := base + increment * slope
    remainder := 0
    expansion := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im,
          zero_re, zero_im] <;> ring1
    factor := 0
    factor_nonneg := le_rfl
    remainder_le := by
      rw [normSq_zero, RFAP.ConstructiveFraction.zero_mul_direct] }

/-- Sum two certificates at the same displayed increment. -/
def add {increment : Gaussian}
    (left right : Certificate increment) : Certificate increment :=
  { base := left.base + right.base
    slope := left.slope + right.slope
    output := left.output + right.output
    remainder := left.remainder + right.remainder
    expansion := by
      rw [← left.expansion, ← right.expansion]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;> ring1
    factor := 2 * (left.factor + right.factor)
    factor_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg left.factor_nonneg right.factor_nonneg)
    remainder_le := by
      calc
        normSq (left.remainder + right.remainder) ≤
            2 * (normSq left.remainder + normSq right.remainder) :=
          normSq_add_le_two _ _
        _ ≤ 2 *
            (left.factor * normSq increment ^ 2 +
              right.factor * normSq increment ^ 2) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add left.remainder_le right.remainder_le) (by decide)
        _ = 2 * (left.factor + right.factor) * normSq increment ^ 2 := by
          ring1 }

def neg {increment : Gaussian}
    (certificate : Certificate increment) : Certificate increment :=
  { base := -certificate.base
    slope := -certificate.slope
    output := -certificate.output
    remainder := -certificate.remainder
    expansion := by
      rw [← certificate.expansion]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [neg_re, neg_im, sub_re, sub_im, mul_re, mul_im] <;> ring1
    factor := certificate.factor
    factor_nonneg := certificate.factor_nonneg
    remainder_le := by
      rw [normSq_neg]
      exact certificate.remainder_le }

/-- Product rule with an exact rational quadratic factor for the whole
displayed product node. -/
def mul {increment : Gaussian}
    (left right : Certificate increment) : Certificate increment := by
  let base := left.base * right.base
  let slope := left.slope * right.base + left.base * right.slope
  let output := left.output * right.output
  let remainder := output - base - increment * slope
  apply ofExpansion increment base slope output remainder rfl
  intro zero
  subst increment
  have leftAtBase := left.output_eq_base_of_increment_zero rfl
  have rightAtBase := right.output_eq_base_of_increment_zero rfl
  dsimp only [remainder, output, base, slope]
  rw [leftAtBase, rightAtBase]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, mul_re, mul_im, add_re, add_im,
      zero_re, zero_im] <;> ring1

/-- Reciprocal rule at a displayed non-vanishing base and output.  The
factor is computed from the exact rational remainder of this node. -/
def reciprocal {increment : Gaussian}
    (certificate : Certificate increment)
    (_baseNonzero : certificate.base ≠ 0)
    (_outputNonzero : certificate.output ≠ 0) : Certificate increment := by
  let base := certificate.base⁻¹
  let slope := -(certificate.slope *
    (certificate.base⁻¹ * certificate.base⁻¹))
  let output := certificate.output⁻¹
  let remainder := output - base - increment * slope
  apply ofExpansion increment base slope output remainder rfl
  intro zero
  subst increment
  have atBase := certificate.output_eq_base_of_increment_zero rfl
  dsimp only [remainder, output, base, slope]
  rw [atBase]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, mul_re, mul_im, neg_re, neg_im,
      zero_re, zero_im] <;> ring1

def div {increment : Gaussian}
    (numerator denominator : Certificate increment)
    (baseNonzero : denominator.base ≠ 0)
    (outputNonzero : denominator.output ≠ 0) : Certificate increment :=
  numerator.mul (denominator.reciprocal baseNonzero outputNonzero)

/-- Multiply the complete expansion by one displayed Gaussian rational. -/
def scale (scalar : Gaussian) {increment : Gaussian}
    (certificate : Certificate increment) : Certificate increment :=
  { base := scalar * certificate.base
    slope := scalar * certificate.slope
    output := scalar * certificate.output
    remainder := scalar * certificate.remainder
    expansion := by
      rw [← certificate.expansion]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    factor := normSq scalar * certificate.factor
    factor_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (normSq_nonneg scalar)
        certificate.factor_nonneg
    remainder_le := by
      rw [normSq_mul]
      calc
        normSq scalar * normSq certificate.remainder ≤
            normSq scalar *
              (certificate.factor * normSq increment ^ 2) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            certificate.remainder_le (normSq_nonneg scalar)
        _ = (normSq scalar * certificate.factor) *
            normSq increment ^ 2 := by ring1 }

/-- A coarse displayed sensitivity sufficient for composing two quadratic
certificates on the rational unit increment disk. -/
def sensitivity {increment : Gaussian}
    (certificate : Certificate increment) : Coordinate :=
  2 * (normSq certificate.slope + certificate.factor)

theorem sensitivity_nonneg {increment : Gaussian}
    (certificate : Certificate increment) :
    0 ≤ certificate.sensitivity :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (normSq_nonneg certificate.slope)
      certificate.factor_nonneg)

/-- The exact output displacement is linearly bounded on the displayed unit
increment disk.  This is the finite estimate consumed by composition. -/
theorem movement_le {increment : Gaussian}
    (certificate : Certificate increment)
    (unit : normSq increment ≤ 1) :
    normSq (certificate.output - certificate.base) ≤
      certificate.sensitivity * normSq increment := by
  have identity : certificate.output - certificate.base =
      increment * certificate.slope + certificate.remainder := by
    rw [← certificate.expansion]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;> ring1
  have squareLe : normSq increment ^ 2 ≤ normSq increment := by
    calc
      normSq increment ^ 2 = normSq increment * normSq increment :=
        pow_two _
      _ ≤ normSq increment * 1 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct unit
          (normSq_nonneg increment)
      _ = normSq increment := RFAP.ConstructiveFraction.mul_one_direct _
  rw [identity]
  calc
    normSq (increment * certificate.slope + certificate.remainder) ≤
        2 * (normSq (increment * certificate.slope) +
          normSq certificate.remainder) := normSq_add_le_two _ _
    _ ≤ 2 *
        (normSq increment * normSq certificate.slope +
          certificate.factor * normSq increment ^ 2) := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl certificate.remainder_le) (by decide)
    _ ≤ 2 *
        (normSq increment * normSq certificate.slope +
          certificate.factor * normSq increment) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      exact add_le_add le_rfl
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          squareLe certificate.factor_nonneg)
    _ = certificate.sensitivity * normSq increment := by
      unfold sensitivity
      ring1

/-- Compose two displayed expansions.  The outer certificate is indexed by
the inner output displacement, so no hidden substitution or limiting step is
present. -/
def compose {increment : Gaussian}
    (inner : Certificate increment)
    (outer : Certificate (inner.output - inner.base))
    (unit : normSq increment ≤ 1) : Certificate increment := by
  let sensitivity := inner.sensitivity
  let factor := 2 *
    (normSq outer.slope * inner.factor + outer.factor * sensitivity ^ 2)
  let remainder := inner.remainder * outer.slope + outer.remainder
  have factorNonnegative : 0 ≤ factor := by
    dsimp only [factor]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (normSq_nonneg outer.slope) inner.factor_nonneg)
        (RFAP.ConstructiveFraction.mul_nonneg_direct outer.factor_nonneg
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            inner.sensitivity_nonneg 2)))
  refine
    { base := outer.base
      slope := inner.slope * outer.slope
      output := outer.output
      remainder := remainder
      expansion := ?_
      factor := factor
      factor_nonneg := factorNonnegative
      remainder_le := ?_ }
  · dsimp only [remainder]
    rw [← outer.expansion, ← inner.expansion]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;> ring1
  · have innerMovement := inner.movement_le unit
    have movementSquare :
        normSq (inner.output - inner.base) ^ 2 ≤
          (sensitivity * normSq increment) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (normSq_nonneg (inner.output - inner.base)) innerMovement 2
    have firstBound :
        normSq (inner.remainder * outer.slope) ≤
          (normSq outer.slope * inner.factor) * normSq increment ^ 2 := by
      rw [normSq_mul]
      calc
        normSq inner.remainder * normSq outer.slope ≤
            (inner.factor * normSq increment ^ 2) *
              normSq outer.slope :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            inner.remainder_le (normSq_nonneg outer.slope)
        _ = (normSq outer.slope * inner.factor) *
            normSq increment ^ 2 := by ring1
    have secondBound : normSq outer.remainder ≤
        (outer.factor * sensitivity ^ 2) * normSq increment ^ 2 := by
      calc
        normSq outer.remainder ≤
            outer.factor * normSq (inner.output - inner.base) ^ 2 :=
          outer.remainder_le
        _ ≤ outer.factor * (sensitivity * normSq increment) ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            movementSquare outer.factor_nonneg
        _ = (outer.factor * sensitivity ^ 2) *
            normSq increment ^ 2 := by ring1
    dsimp only [remainder, factor]
    calc
      normSq (inner.remainder * outer.slope + outer.remainder) ≤
          2 * (normSq (inner.remainder * outer.slope) +
            normSq outer.remainder) := normSq_add_le_two _ _
      _ ≤ 2 *
          (((normSq outer.slope * inner.factor) *
              normSq increment ^ 2) +
            ((outer.factor * sensitivity ^ 2) *
              normSq increment ^ 2)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstBound secondBound) (by decide)
      _ = 2 *
          (normSq outer.slope * inner.factor +
            outer.factor * sensitivity ^ 2) * normSq increment ^ 2 := by
        ring1

/-- Primitive certificate for the finite translated exponential program. -/
def exponential {base increment : Gaussian}
    (baseUnit : normSq base ≤ 1) (incrementUnit : normSq increment ≤ 1)
    (index : Nat) : Certificate increment :=
  { base := CCL.FiniteExp.sample base (index + 1)
    slope := CCL.FiniteExp.sample base (index + 1)
    output := CCL.TranscendentalLaws.expProductSample
      base increment (index + 1)
    remainder :=
      CCL.TranscendentalLaws.expProductSample
          base increment (index + 1) -
        CCL.FiniteExp.sample base (index + 1) -
        increment * CCL.FiniteExp.sample base (index + 1)
    expansion := rfl
    factor := 10
    factor_nonneg := by decide
    remainder_le :=
      CCL.ExponentialCalculus.expProductSample_second_order_normSq_le
        baseUnit incrementUnit index }

/-- Primitive certificate for the finite local logarithm at its rational
origin. -/
def logarithm1p {increment : Gaussian}
    (disk : normSq increment ≤ 1 / 4) (index : Nat) :
    Certificate increment :=
  { base := 0
    slope := 1
    output := CCL.LogarithmicCalculus.log1pSample
      increment (index + 1)
    remainder := CCL.LogarithmicCalculus.log1pSample
      increment (index + 1) - increment
    expansion := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im, zero_re, zero_im,
          one_re, one_im] <;> ring1
    factor := 4
    factor_nonneg := by decide
    remainder_le :=
      CCL.LogarithmicCalculus.log1pSample_second_order_normSq_le
        disk index }

end Certificate

end CCL.QuadraticJet
