import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.CanonicalLCM
import mathlib.RFAP.ConstructiveGaussianHeight
import mathlib.RFAP.ConstructivePolynomial

/-!
# Finite denominator-height lower bounds for polynomial residuals

The finite coefficient list is cleared to Gaussian integers by a structural
product of the canonical coordinate denominators.  Homogeneous evaluation at
a displayed common-denominator Gaussian fraction then gives an integral
numerator.  If the residual is nonzero, its integral norm is at least one.
-/

namespace RFAP.DenominatorHeight

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Fraction := RFAP.ConstructiveGaussianHeight.Fraction
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight
open RFAP.ComputablePolynomial.DensePolynomial

namespace GaussianInt

/-- Multiplication by a displayed natural regarded as a real Gaussian integer. -/
def scale (factor : Nat) (value : GaussianInt) : GaussianInt :=
  RFAP.ConstructiveGaussianHeight.GaussianInt.ofNat factor * value

@[simp] theorem toGaussian_scale (factor : Nat) (value : GaussianInt) :
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
        (scale factor value) =
      ⟨(factor : Coordinate), 0⟩ *
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian value := by
  exact RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_mul _ _

@[simp] theorem toGaussian_pow (value : GaussianInt) (exponent : Nat) :
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
        (value ^ exponent) =
      RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian value ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [pow_succ, pow_succ,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_mul,
        inductionHypothesis]

end GaussianInt

/-- Gaussian-integer coefficients together with the positive real scale by
which the original finite Gaussian-rational list was multiplied. -/
structure ClearedCoefficients where
  scale : Nat
  scalePositive : 0 < scale
  coefficients : List GaussianInt

/-- Clear a finite Gaussian-rational coefficient list by structural recursion. -/
def clear : List Gaussian → ClearedCoefficients
  | [] => ⟨1, by decide, []⟩
  | coefficient :: remaining =>
      let head := Fraction.ofGaussian coefficient
      let tail := clear remaining
      { scale := head.denominator * tail.scale
        scalePositive := Nat.mul_pos head.denominatorPositive tail.scalePositive
        coefficients :=
          GaussianInt.scale tail.scale head.numerator ::
            tail.coefficients.map (GaussianInt.scale head.denominator) }

@[simp] theorem clear_length (coefficients : List Gaussian) :
    (clear coefficients).coefficients.length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [clear, List.length_cons, List.length_map, inductionHypothesis]

/-- Horner evaluation after embedding a Gaussian-integer coefficient list. -/
def evalIntegers (point : Gaussian) (coefficients : List GaussianInt) : Gaussian :=
  evalCoeffs point (coefficients.map
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian)

@[simp] theorem evalIntegers_nil (point : Gaussian) :
    evalIntegers point [] = 0 := rfl

theorem evalIntegers_cons (point : Gaussian) (coefficient : GaussianInt)
    (remaining : List GaussianInt) :
    evalIntegers point (coefficient :: remaining) =
      RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian coefficient *
          point ^ remaining.length +
        evalIntegers point remaining := by
  simp only [evalIntegers, List.map_cons, evalCoeffs_cons_expansion,
    List.length_map]

theorem evalIntegers_map_scale (point : Gaussian) (factor : Nat)
    (coefficients : List GaussianInt) :
    evalIntegers point (coefficients.map (GaussianInt.scale factor)) =
      ⟨(factor : Coordinate), 0⟩ * evalIntegers point coefficients := by
  induction coefficients with
  | nil =>
      simp only [List.map_nil, evalIntegers_nil, mul_zero]
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.map_cons, evalIntegers_cons, List.length_map,
        GaussianInt.toGaussian_scale, inductionHypothesis]
      ring1

/-- Clearing coefficients multiplies evaluation by exactly the displayed
positive real scale. -/
theorem eval_clear (point : Gaussian) (coefficients : List Gaussian) :
    evalIntegers point (clear coefficients).coefficients =
      ⟨((clear coefficients).scale : Coordinate), 0⟩ *
        evalCoeffs point coefficients := by
  induction coefficients with
  | nil => simp [clear, evalIntegers, evalCoeffs]
  | cons coefficient remaining inductionHypothesis =>
      let head := Fraction.ofGaussian coefficient
      let tail := clear remaining
      have headValue : head.value = coefficient :=
        Fraction.ofGaussian_value coefficient
      have headClear := head.value_mul_denominator
      rw [show (clear (coefficient :: remaining)).coefficients =
          GaussianInt.scale tail.scale head.numerator ::
            tail.coefficients.map (GaussianInt.scale head.denominator)
        from rfl]
      rw [evalIntegers_cons, List.length_map, clear_length,
        evalIntegers_map_scale, inductionHypothesis]
      rw [GaussianInt.toGaussian_scale]
      change
        (⟨(tail.scale : Coordinate), 0⟩ *
              RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
                head.numerator) * point ^ remaining.length +
            ⟨(head.denominator : Coordinate), 0⟩ *
              (⟨(tail.scale : Coordinate), 0⟩ *
                evalCoeffs point remaining) =
          ⟨((head.denominator * tail.scale : Nat) : Coordinate), 0⟩ *
            evalCoeffs point (coefficient :: remaining)
      have headIdentity :
          coefficient * ⟨(head.denominator : Coordinate), 0⟩ =
            RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
              head.numerator := by
        rw [← headValue]
        exact headClear
      rw [evalCoeffs_cons_expansion, ← headIdentity, Nat.cast_mul]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [mul_re, mul_im, add_re, add_im] <;>
        ring1

/-! ## Least common-denominator coefficient clearing -/

/-- The least positive common denominator of the two reduced rational
coordinates of one Gaussian coefficient. -/
def coefficientDenominator (coefficient : Gaussian) : Nat :=
  RFAP.CanonicalLCM.lcm
    (RFAP.ConstructiveFraction.representative coefficient.re).den
    (RFAP.ConstructiveFraction.representative coefficient.im).den

/-- The global least common multiple of all reduced coefficient-coordinate
denominators.  Unlike `clear`, this does not multiply denominators that have
already been cleared. -/
def lcmScale : List Gaussian → Nat
  | [] => 1
  | coefficient :: remaining =>
      RFAP.CanonicalLCM.lcm
        (coefficientDenominator coefficient) (lcmScale remaining)

theorem coefficientDenominator_pos (coefficient : Gaussian) :
    0 < coefficientDenominator coefficient := by
  exact RFAP.CanonicalLCM.lcm_pos
    (RFAP.ConstructiveFraction.representative coefficient.re).den_pos
    (RFAP.ConstructiveFraction.representative coefficient.im).den_pos

theorem lcmScale_pos (coefficients : List Gaussian) :
    0 < lcmScale coefficients := by
  induction coefficients with
  | nil => decide
  | cons coefficient remaining inductionHypothesis =>
      exact RFAP.CanonicalLCM.lcm_pos
        (coefficientDenominator_pos coefficient) inductionHypothesis

/-- A natural scale is a common multiple of every reduced real and imaginary
coordinate denominator in the displayed coefficient list. -/
def ClearsCoefficientDenominators
    (coefficients : List Gaussian) (scale : Nat) : Prop :=
  ∀ coefficient ∈ coefficients,
    (RFAP.ConstructiveFraction.representative coefficient.re).den ∣ scale ∧
      (RFAP.ConstructiveFraction.representative coefficient.im).den ∣ scale

theorem lcmScale_clears (coefficients : List Gaussian) :
    ClearsCoefficientDenominators coefficients (lcmScale coefficients) := by
  induction coefficients with
  | nil =>
      intro coefficient member
      exact (List.not_mem_nil member).elim
  | cons coefficient remaining inductionHypothesis =>
      intro candidate member
      rcases List.mem_cons.mp member with identity | tailMember
      · subst candidate
        exact
          ⟨(RFAP.CanonicalLCM.left_dvd_lcm _ _).trans
              (RFAP.CanonicalLCM.left_dvd_lcm _ _),
            (RFAP.CanonicalLCM.right_dvd_lcm _ _).trans
              (RFAP.CanonicalLCM.left_dvd_lcm _ _)⟩
      · have tailCleared := inductionHypothesis candidate tailMember
        exact
          ⟨tailCleared.1.trans (RFAP.CanonicalLCM.right_dvd_lcm _ _),
            tailCleared.2.trans (RFAP.CanonicalLCM.right_dvd_lcm _ _)⟩

/-- The computed LCM scale divides every other displayed common multiple of
all reduced coefficient-coordinate denominators. -/
theorem lcmScale_dvd_of_clears {coefficients : List Gaussian} {scale : Nat}
    (clears : ClearsCoefficientDenominators coefficients scale) :
    lcmScale coefficients ∣ scale := by
  induction coefficients with
  | nil => exact one_dvd _
  | cons coefficient remaining inductionHypothesis =>
      have head := clears coefficient List.mem_cons_self
      have tail : ClearsCoefficientDenominators remaining scale := by
        intro candidate member
        exact clears candidate (List.mem_cons_of_mem _ member)
      exact RFAP.CanonicalLCM.lcm_dvd
        (RFAP.CanonicalLCM.lcm_dvd head.1 head.2)
        (inductionHypothesis tail)

/-- Integer numerator obtained by multiplying a reduced rational coordinate
by a natural scale.  Correctness is asserted when its reduced denominator
divides that scale. -/
def scaledCoordinateNumerator (scale : Nat) (value : Coordinate) : Int :=
  let reduced := RFAP.ConstructiveFraction.representative value
  reduced.num * (scale / reduced.den : Nat)

theorem scaledCoordinateNumerator_spec (scale : Nat) (value : Coordinate)
    (divides : (RFAP.ConstructiveFraction.representative value).den ∣ scale) :
    (scaledCoordinateNumerator scale value : Coordinate) =
      (scale : Coordinate) * value := by
  let reduced := RFAP.ConstructiveFraction.representative value
  rcases divides with ⟨factor, scaleIdentity⟩
  have denominatorPositive := reduced.den_pos
  have recovered := RFAP.ConstructiveFraction.representative_mul_den value
  change value * (reduced.den : Coordinate) =
    (reduced.num : Coordinate) at recovered
  unfold scaledCoordinateNumerator
  rw [scaleIdentity]
  change
    ((reduced.num *
      ((reduced.den * factor) / reduced.den : Nat) : Int) : Coordinate) =
      ((reduced.den * factor : Nat) : Coordinate) * value
  rw [Nat.mul_comm reduced.den factor,
    Nat.mul_div_left _ denominatorPositive, QuotientFreeRing.intCast_mul,
    Int.cast_natCast, Nat.cast_mul, ← recovered]
  ring1

/-- Gaussian-integer coefficient obtained from one common natural scale. -/
def scaledGaussianCoefficient
    (scale : Nat) (coefficient : Gaussian) : GaussianInt :=
  ⟨scaledCoordinateNumerator scale coefficient.re,
    scaledCoordinateNumerator scale coefficient.im⟩

theorem toGaussian_scaledGaussianCoefficient
    (scale : Nat) (coefficient : Gaussian)
    (realDivides :
      (RFAP.ConstructiveFraction.representative coefficient.re).den ∣ scale)
    (imaginaryDivides :
      (RFAP.ConstructiveFraction.representative coefficient.im).den ∣ scale) :
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
        (scaledGaussianCoefficient scale coefficient) =
      ⟨(scale : Coordinate), 0⟩ * coefficient := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change
      (scaledCoordinateNumerator scale coefficient.re : Coordinate) =
        (scale : Coordinate) * coefficient.re - 0 * coefficient.im
    rw [scaledCoordinateNumerator_spec scale coefficient.re realDivides]
    ring1
  · change
      (scaledCoordinateNumerator scale coefficient.im : Coordinate) =
        (scale : Coordinate) * coefficient.im + 0 * coefficient.re
    rw [scaledCoordinateNumerator_spec scale coefficient.im imaginaryDivides]
    ring1

/-- Coefficients cleared with the global least common denominator. -/
def lcmClear (coefficients : List Gaussian) : ClearedCoefficients :=
  let scale := lcmScale coefficients
  { scale := scale
    scalePositive := lcmScale_pos coefficients
    coefficients := coefficients.map (scaledGaussianCoefficient scale) }

@[simp] theorem lcmClear_length (coefficients : List Gaussian) :
    (lcmClear coefficients).coefficients.length = coefficients.length := by
  simp only [lcmClear, List.length_map]

theorem evalIntegers_map_scaled
    (point : Gaussian) (coefficients : List Gaussian) (scale : Nat)
    (clears : ClearsCoefficientDenominators coefficients scale) :
    evalIntegers point
        (coefficients.map (scaledGaussianCoefficient scale)) =
      ⟨(scale : Coordinate), 0⟩ * evalCoeffs point coefficients := by
  induction coefficients with
  | nil =>
      simp only [List.map_nil, evalIntegers_nil, evalCoeffs, List.foldl_nil,
        mul_zero]
  | cons coefficient remaining inductionHypothesis =>
      have head := clears coefficient List.mem_cons_self
      have tail : ClearsCoefficientDenominators remaining scale := by
        intro candidate member
        exact clears candidate (List.mem_cons_of_mem _ member)
      rw [List.map_cons, evalIntegers_cons, List.length_map,
        toGaussian_scaledGaussianCoefficient scale coefficient head.1 head.2,
        inductionHypothesis tail, evalCoeffs_cons_expansion]
      ring1

/-- LCM coefficient clearing multiplies evaluation by exactly its displayed
least common denominator. -/
theorem eval_lcmClear (point : Gaussian) (coefficients : List Gaussian) :
    evalIntegers point (lcmClear coefficients).coefficients =
      ⟨((lcmClear coefficients).scale : Coordinate), 0⟩ *
        evalCoeffs point coefficients := by
  exact evalIntegers_map_scaled point coefficients (lcmScale coefficients)
    (lcmScale_clears coefficients)

/-- High-to-low homogeneous Gaussian-integer evaluation. -/
def homogeneousEval (numerator : GaussianInt) (denominator : Nat) :
    List GaussianInt → GaussianInt
  | [] => 0
  | coefficient :: remaining =>
      coefficient * numerator ^ remaining.length +
        RFAP.ConstructiveGaussianHeight.GaussianInt.ofNat denominator *
          homogeneousEval numerator denominator remaining

/-- Homogeneous evaluation is ordinary evaluation multiplied by the exact
denominator power. -/
theorem homogeneousEval_cons_eq_scaled
    (fraction : Fraction) (coefficient : GaussianInt)
    (remaining : List GaussianInt) :
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
        (homogeneousEval fraction.numerator fraction.denominator
          (coefficient :: remaining)) =
      ⟨(fraction.denominator : Coordinate), 0⟩ ^ remaining.length *
        evalIntegers fraction.value (coefficient :: remaining) := by
  induction remaining generalizing coefficient with
  | nil =>
      simp [homogeneousEval, evalIntegers]
  | cons next remaining inductionHypothesis =>
      have cleared := fraction.value_mul_denominator
      change fraction.value * ⟨(fraction.denominator : Coordinate), 0⟩ =
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
          fraction.numerator at cleared
      rw [homogeneousEval,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_add,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_mul]
      rw [GaussianInt.toGaussian_pow,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_mul,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_ofNat,
        inductionHypothesis]
      rw [evalIntegers_cons fraction.value coefficient (next :: remaining),
        List.length_cons, pow_succ]
      rw [← cleared]
      rw [mul_pow, pow_succ]
      ring1

/-- Coefficient scale used by the lower residual theorem. -/
def coefficientScale (p : GaussianPolynomial) : Nat :=
  (lcmClear p.normalize.coeffs).scale

theorem coefficientScale_pos (p : GaussianPolynomial) :
    0 < coefficientScale p := by
  exact (lcmClear p.normalize.coeffs).scalePositive

/-- The polynomial coefficient scale divides every natural number that clears
all reduced real and imaginary coefficient-coordinate denominators. -/
theorem coefficientScale_dvd_of_clears (p : GaussianPolynomial) {scale : Nat}
    (clears : ClearsCoefficientDenominators p.normalize.coeffs scale) :
    coefficientScale p ∣ scale := by
  exact lcmScale_dvd_of_clears clears

/-- Integral homogeneous numerator of a polynomial evaluation at a displayed
common-denominator Gaussian fraction. -/
def residualNumerator (p : GaussianPolynomial) (fraction : Fraction) :
    GaussianInt :=
  homogeneousEval fraction.numerator fraction.denominator
    (lcmClear p.normalize.coeffs).coefficients

theorem residualNumerator_identity
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : Fraction) :
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
        (residualNumerator p fraction) =
      ⟨(fraction.denominator : Coordinate), 0⟩ ^ p.natDegree *
        (⟨(coefficientScale p : Coordinate), 0⟩ *
          p.eval fraction.value) := by
  obtain ⟨tail, coefficients, tailLength⟩ :=
    normalized_coeffs_shape nonzero
  unfold residualNumerator coefficientScale
  rw [show p.normalize.coeffs = p.leadingCoeff :: tail from coefficients]
  change
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian
        (homogeneousEval fraction.numerator fraction.denominator
          (lcmClear (p.leadingCoeff :: tail)).coefficients) = _
  rw [show (lcmClear (p.leadingCoeff :: tail)).coefficients =
      scaledGaussianCoefficient (lcmScale (p.leadingCoeff :: tail))
          p.leadingCoeff ::
        tail.map
          (scaledGaussianCoefficient (lcmScale (p.leadingCoeff :: tail)))
    from rfl]
  rw [homogeneousEval_cons_eq_scaled]
  have remainingLength :
      (tail.map
        (scaledGaussianCoefficient (lcmScale (p.leadingCoeff :: tail)))).length =
          p.natDegree := by
    simp only [List.length_map, tailLength]
  rw [remainingLength]
  change
    ⟨(fraction.denominator : Coordinate), 0⟩ ^ p.natDegree *
        evalIntegers fraction.value
          (lcmClear (p.leadingCoeff :: tail)).coefficients = _
  rw [eval_lcmClear]
  rw [← eval_normalize]
  unfold eval
  rw [coefficients]

/-- A nonzero displayed residual produces a nonzero integral homogeneous
numerator. -/
theorem residualNumerator_ne_zero
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : Fraction) (residualNonzero : p.eval fraction.value ≠ 0) :
    residualNumerator p fraction ≠ 0 := by
  intro numeratorZero
  have embeddedZero := congrArg
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian numeratorZero
  rw [RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_zero,
    residualNumerator_identity p nonzero fraction] at embeddedZero
  have denominatorNonzero :
      (⟨(fraction.denominator : Coordinate), 0⟩ : Gaussian) ≠ 0 := by
    intro zero
    have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
    have denominatorZero := RFAP.ConstructiveFraction.natCast_injective_direct
      (realZero.trans (Nat.cast_zero).symm)
    exact (Nat.ne_of_gt fraction.denominatorPositive) denominatorZero
  have scalePositive : 0 < coefficientScale p := coefficientScale_pos p
  have scaleNonzero :
      (⟨(coefficientScale p : Coordinate), 0⟩ : Gaussian) ≠ 0 := by
    intro zero
    have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
    have scaleZero := RFAP.ConstructiveFraction.natCast_injective_direct
      (realZero.trans (Nat.cast_zero).symm)
    exact (Nat.ne_of_gt scalePositive) scaleZero
  have productNonzero := RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
    (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct _
      denominatorNonzero p.natDegree)
    (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct scaleNonzero
      residualNonzero)
  exact productNonzero embeddedZero

/-- Exact finite residual identity underlying the denominator-height bound.
The scaled residual is not merely bounded below: it is the norm of the
explicit homogeneous Gaussian-integer numerator. -/
theorem scaled_height_mul_residual_eq_normNat
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : Fraction) :
    (coefficientScale p : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ p.natDegree *
        normSq (p.eval fraction.value) =
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (residualNumerator p fraction) : Coordinate) := by
  have denominatorNorm :
      normSq (⟨(fraction.denominator : Coordinate), 0⟩ : Gaussian) =
        (fraction.height : Coordinate) := by
    change (fraction.denominator : Coordinate) ^ 2 + 0 ^ 2 =
      (fraction.denominator ^ 2 : Nat)
    rw [Nat.cast_pow]
    ring1
  have scaleNorm :
      normSq (⟨(coefficientScale p : Coordinate), 0⟩ : Gaussian) =
        (coefficientScale p : Coordinate) ^ 2 := by
    change (coefficientScale p : Coordinate) ^ 2 + 0 ^ 2 = _
    ring1
  rw [← RFAP.ConstructiveGaussianHeight.GaussianInt.normSq_toGaussian,
    residualNumerator_identity p nonzero fraction, normSq_mul, normSq_mul,
    normSq_pow, denominatorNorm, scaleNorm]
  ring1

/-- Equality in the unit lower bound occurs exactly when the displayed
integral residual numerator has Gaussian norm one. -/
theorem scaled_height_mul_residual_eq_one_iff
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : Fraction) :
    (coefficientScale p : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ p.natDegree *
        normSq (p.eval fraction.value) = 1 ↔
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (residualNumerator p fraction) = 1 := by
  rw [scaled_height_mul_residual_eq_normNat p nonzero fraction]
  constructor
  · intro equality
    apply RFAP.ConstructiveFraction.natCast_injective_direct
    simpa only [Nat.cast_one] using equality
  · intro equality
    rw [equality, Nat.cast_one]

/-- Finite Liouville-type lower bound in multiplied form.  No root object is
used: the proof is only coefficient clearing, homogeneous evaluation, and the
fact that a nonzero Gaussian integer has norm at least one. -/
theorem one_le_scaled_height_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : Fraction) (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (coefficientScale p : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ p.natDegree *
          normSq (p.eval fraction.value) := by
  have numeratorNonzero :=
    residualNumerator_ne_zero p nonzero fraction residualNonzero
  have numeratorPositive :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos numeratorNonzero
  have oneLeNat : 1 ≤
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (residualNumerator p fraction) := numeratorPositive
  have oneLeCast : (1 : Coordinate) ≤
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (residualNumerator p fraction) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct oneLeNat
  rw [← scaled_height_mul_residual_eq_normNat p nonzero fraction]
    at oneLeCast
  exact oneLeCast

end RFAP.DenominatorHeight
