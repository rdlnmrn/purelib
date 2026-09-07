import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.PathClearance

/-!
# Constructive interval sign certificates

Finite Horner folds compute simultaneous square bounds for values and finite
differences.  A displayed sample whose squared value exceeds the resulting
Lipschitz margin certifies one strict sign throughout a closed constructive
interval.  No root set, compactness argument, or completed real object is
used.
-/

namespace RFAP.IntervalSign

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathClearance

structure HornerSqBounds where
  value : Coordinate
  slope : Coordinate
deriving DecidableEq

def HornerSqBounds.step (radiusSq : Coordinate)
    (bounds : HornerSqBounds) (coefficient : Coordinate) : HornerSqBounds where
  value := 2 * (bounds.value * radiusSq + coefficient ^ 2)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)

def denseHornerSqBounds (p : Polynomial) (interval : Interval) :
    HornerSqBounds :=
  p.coeffs.foldl (HornerSqBounds.step interval.squareBound) ⟨0, 0⟩

def denseEvalSqBound (p : Polynomial) (interval : Interval) : Coordinate :=
  (denseHornerSqBounds p interval).value

def denseEvalSqLipschitzBound
    (p : Polynomial) (interval : Interval) : Coordinate :=
  (denseHornerSqBounds p interval).slope

private theorem twice_nonneg {a : Coordinate} (nonnegative : 0 ≤ a) :
    0 ≤ 2 * a := by
  calc
    0 = 0 + 0 := by ring1
    _ ≤ a + a := add_le_add nonnegative nonnegative
    _ = 2 * a := by ring1

private theorem twice_le_twice {a b : Coordinate} (less : a ≤ b) :
    2 * a ≤ 2 * b := by
  calc
    2 * a = a + a := by ring1
    _ ≤ b + b := add_le_add less less
    _ = 2 * b := by ring1

private theorem hornerSqBoundsCoeffs_monotone
    (coefficients : List Coordinate) {smallRadius largeRadius : Coordinate}
    {smallBounds largeBounds : HornerSqBounds}
    (smallRadiusNonnegative : 0 ≤ smallRadius)
    (largeRadiusNonnegative : 0 ≤ largeRadius)
    (smallValueNonnegative : 0 ≤ smallBounds.value)
    (smallSlopeNonnegative : 0 ≤ smallBounds.slope)
    (largeValueNonnegative : 0 ≤ largeBounds.value)
    (largeSlopeNonnegative : 0 ≤ largeBounds.slope)
    (radiusLe : smallRadius ≤ largeRadius)
    (valueLe : smallBounds.value ≤ largeBounds.value)
    (slopeLe : smallBounds.slope ≤ largeBounds.slope) :
    let smallFinal := coefficients.foldl
      (HornerSqBounds.step smallRadius) smallBounds
    let largeFinal := coefficients.foldl
      (HornerSqBounds.step largeRadius) largeBounds
    smallFinal.value ≤ largeFinal.value ∧
      smallFinal.slope ≤ largeFinal.slope := by
  induction coefficients generalizing smallBounds largeBounds with
  | nil => exact ⟨valueLe, slopeLe⟩
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      have valueProductLe : smallBounds.value * smallRadius ≤
          largeBounds.value * largeRadius :=
        RFAP.ConstructiveFraction.mul_le_mul_direct valueLe radiusLe
          smallRadiusNonnegative largeValueNonnegative
      have slopeProductLe : smallBounds.slope * smallRadius ≤
          largeBounds.slope * largeRadius :=
        RFAP.ConstructiveFraction.mul_le_mul_direct slopeLe radiusLe
          smallRadiusNonnegative largeSlopeNonnegative
      have nextValueLe :
          (HornerSqBounds.step smallRadius smallBounds coefficient).value ≤
            (HornerSqBounds.step largeRadius largeBounds coefficient).value :=
        twice_le_twice (add_le_add valueProductLe (le_refl _))
      have nextSlopeLe :
          (HornerSqBounds.step smallRadius smallBounds coefficient).slope ≤
            (HornerSqBounds.step largeRadius largeBounds coefficient).slope :=
        twice_le_twice (add_le_add slopeProductLe valueLe)
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            smallValueNonnegative smallRadiusNonnegative)
          (RFAP.ConstructiveFraction.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            smallSlopeNonnegative smallRadiusNonnegative)
          smallValueNonnegative
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            largeValueNonnegative largeRadiusNonnegative)
          (RFAP.ConstructiveFraction.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            largeSlopeNonnegative largeRadiusNonnegative)
          largeValueNonnegative
      · exact nextValueLe
      · exact nextSlopeLe

theorem denseHornerSqBounds_le_of_refines (p : Polynomial)
    {interval root : Interval} (refines : interval.Refines root) :
    denseEvalSqBound p interval ≤ denseEvalSqBound p root ∧
      denseEvalSqLipschitzBound p interval ≤
        denseEvalSqLipschitzBound p root := by
  exact hornerSqBoundsCoeffs_monotone p.coeffs
    interval.squareBound_nonneg root.squareBound_nonneg
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0)
    (interval.squareBound_le_of_refines refines) (le_refl 0) (le_refl 0)

theorem denseEvalSqBound_le_of_refines (p : Polynomial)
    {interval root : Interval} (refines : interval.Refines root) :
    denseEvalSqBound p interval ≤ denseEvalSqBound p root :=
  (denseHornerSqBounds_le_of_refines p refines).1

theorem denseEvalSqLipschitzBound_le_of_refines (p : Polynomial)
    {interval root : Interval} (refines : interval.Refines root) :
    denseEvalSqLipschitzBound p interval ≤
      denseEvalSqLipschitzBound p root :=
  (denseHornerSqBounds_le_of_refines p refines).2

private theorem add_sq_le_two (a b : Coordinate) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (a - b) ^ 2 := RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 := by ring1

private theorem evalSqBoundsCoeffs_spec
    (coefficients : List Coordinate) {radiusSq x y : Coordinate}
    (radiusNonnegative : 0 ≤ radiusSq)
    (xBound : x ^ 2 ≤ radiusSq) (yBound : y ^ 2 ≤ radiusSq)
    (accumulatorX accumulatorY : Coordinate) (bounds : HornerSqBounds)
    (valueNonnegative : 0 ≤ bounds.value)
    (slopeNonnegative : 0 ≤ bounds.slope)
    (accumulatorXBound : accumulatorX ^ 2 ≤ bounds.value)
    (accumulatorYBound : accumulatorY ^ 2 ≤ bounds.value)
    (differenceBound : (accumulatorX - accumulatorY) ^ 2 ≤
      bounds.slope * (x - y) ^ 2) :
    let finalX := coefficients.foldl
      (fun value coefficient => value * x + coefficient) accumulatorX
    let finalY := coefficients.foldl
      (fun value coefficient => value * y + coefficient) accumulatorY
    let finalBounds := coefficients.foldl
      (HornerSqBounds.step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      finalX ^ 2 ≤ finalBounds.value ∧
      finalY ^ 2 ≤ finalBounds.value ∧
      (finalX - finalY) ^ 2 ≤ finalBounds.slope * (x - y) ^ 2 := by
  induction coefficients generalizing accumulatorX accumulatorY bounds with
  | nil => exact ⟨valueNonnegative, slopeNonnegative,
      accumulatorXBound, accumulatorYBound, differenceBound⟩
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            valueNonnegative radiusNonnegative)
          (RFAP.ConstructiveFraction.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            slopeNonnegative radiusNonnegative)
          valueNonnegative
      · have productBound : (accumulatorX * x) ^ 2 ≤
            bounds.value * radiusSq := by
          rw [mul_pow]
          exact RFAP.ConstructiveFraction.mul_le_mul_direct
            accumulatorXBound xBound
            (RFAP.ConstructiveFraction.sq_nonneg_direct x)
            valueNonnegative
        exact (add_sq_le_two (accumulatorX * x) coefficient).trans
          (twice_le_twice
            (add_le_add productBound (le_refl (coefficient ^ 2))))
      · have productBound : (accumulatorY * y) ^ 2 ≤
            bounds.value * radiusSq := by
          rw [mul_pow]
          exact RFAP.ConstructiveFraction.mul_le_mul_direct
            accumulatorYBound yBound
            (RFAP.ConstructiveFraction.sq_nonneg_direct y)
            valueNonnegative
        exact (add_sq_le_two (accumulatorY * y) coefficient).trans
          (twice_le_twice
            (add_le_add productBound (le_refl (coefficient ^ 2))))
      · have identity :
            (accumulatorX * x + coefficient) -
                (accumulatorY * y + coefficient) =
              (accumulatorX - accumulatorY) * x +
                accumulatorY * (x - y) := by ring1
        rw [identity]
        have firstBound :
            (accumulatorX - accumulatorY) ^ 2 * x ^ 2 ≤
              (bounds.slope * (x - y) ^ 2) * radiusSq :=
          RFAP.ConstructiveFraction.mul_le_mul_direct differenceBound xBound
            (RFAP.ConstructiveFraction.sq_nonneg_direct x)
            (RFAP.ConstructiveFraction.mul_nonneg_direct slopeNonnegative
              (RFAP.ConstructiveFraction.sq_nonneg_direct (x - y)))
        have secondBound : accumulatorY ^ 2 * (x - y) ^ 2 ≤
            bounds.value * (x - y) ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            accumulatorYBound
            (RFAP.ConstructiveFraction.sq_nonneg_direct (x - y))
        calc
          ((accumulatorX - accumulatorY) * x +
              accumulatorY * (x - y)) ^ 2 ≤
              2 * (((accumulatorX - accumulatorY) * x) ^ 2 +
                (accumulatorY * (x - y)) ^ 2) := add_sq_le_two _ _
          _ = 2 * ((accumulatorX - accumulatorY) ^ 2 * x ^ 2 +
                accumulatorY ^ 2 * (x - y) ^ 2) := by
            rw [mul_pow, mul_pow]
          _ ≤ 2 * ((bounds.slope * (x - y) ^ 2) * radiusSq +
                bounds.value * (x - y) ^ 2) :=
            twice_le_twice (add_le_add firstBound secondBound)
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                (x - y) ^ 2 := by ring1

theorem denseHornerSqBounds_nonneg (p : Polynomial) (interval : Interval) :
    0 ≤ denseEvalSqBound p interval ∧
      0 ≤ denseEvalSqLipschitzBound p interval := by
  have specification := evalSqBoundsCoeffs_spec p.coeffs
    (radiusSq := interval.squareBound) (x := 0) (y := 0)
    interval.squareBound_nonneg interval.squareBound_nonneg
    interval.squareBound_nonneg 0 0 ⟨0, 0⟩
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0) (by
      change (0 : Coordinate) ≤ 0 * 0 ^ 2
      rw [zero_mul])
  exact ⟨specification.1, specification.2.1⟩

theorem eval_sub_sq_le
    (p : Polynomial) (interval : Interval) {x y : Coordinate}
    (xInside : interval.Contains x) (yInside : interval.Contains y) :
    (p.eval x - p.eval y) ^ 2 ≤
      denseEvalSqLipschitzBound p interval * (x - y) ^ 2 := by
  have specification := evalSqBoundsCoeffs_spec p.coeffs
    (radiusSq := interval.squareBound) (x := x) (y := y)
    interval.squareBound_nonneg (interval.sq_le_squareBound xInside)
    (interval.sq_le_squareBound yInside) 0 0 ⟨0, 0⟩
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0) (by
      change (0 : Coordinate) ≤ 0 * (x - y) ^ 2
      rw [zero_mul])
  simpa only [eval, evalCoeffs, denseEvalSqLipschitzBound,
    denseHornerSqBounds] using specification.2.2.2.2

/-- Squared radius around a displayed sample, computed from the two interval
endpoints. -/
def sampleRadiusSq (interval : Interval) (sample : Coordinate) : Coordinate :=
  max ((interval.lower - sample) ^ 2) ((interval.upper - sample) ^ 2)

/-- The two endpoint-centered squared radii of a one-dimensional interval
are the same displayed width square. -/
theorem sampleRadiusSq_upper_eq_lower (interval : Interval) :
    sampleRadiusSq interval interval.upper =
      sampleRadiusSq interval interval.lower := by
  unfold sampleRadiusSq
  have forwardNonnegative :
      0 ≤ (interval.upper - interval.lower) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have reverseNonnegative :
      0 ≤ (interval.lower - interval.upper) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have zeroSq : (0 : Coordinate) ^ 2 = 0 := by ring1
  simp only [sub_self, zeroSq]
  rw [max_eq_left reverseNonnegative, max_eq_right forwardNonnegative]
  ring1

/-- At the lower endpoint the squared sample radius is exactly the displayed
interval-width square. -/
theorem sampleRadiusSq_lower_eq_widthSq (interval : Interval) :
    sampleRadiusSq interval interval.lower =
      (interval.upper - interval.lower) ^ 2 := by
  unfold sampleRadiusSq
  have nonnegative : 0 ≤ (interval.upper - interval.lower) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  have zeroSq : (0 : Coordinate) ^ 2 = 0 := by ring1
  simp only [sub_self, zeroSq]
  exact max_eq_right nonnegative

theorem sub_sq_le_sampleRadiusSq
    (interval : Interval) {sample x : Coordinate}
    (inside : interval.Contains x) :
    (x - sample) ^ 2 ≤ sampleRadiusSq interval sample := by
  exact RFAP.Boxes.Box.sq_le_endpoint_max
    (RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.1 sample) (RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2 sample)

theorem mul_pos_of_sub_sq_lt_sq {x sample : Coordinate}
    (close : (x - sample) ^ 2 < sample ^ 2) : 0 < x * sample := by
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy sample 0 with sampleNegative | rfl | samplePositive
  · exact RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
      xNegative sampleNegative
  · rw [sub_zero] at close
    exact ((not_lt_of_ge
      (RFAP.ConstructiveFraction.sq_nonneg_direct x)) close).elim
  · have twiceSamplePositive : 0 < 2 * sample := by
      calc
        0 = 0 + 0 := by ring1
        _ < sample + 0 :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct samplePositive 0
        _ < sample + sample :=
          RFAP.ConstructiveFraction.add_lt_add_left_direct samplePositive sample
        _ = 2 * sample := by ring1
    have reverseDifferencePositive : 0 < 2 * sample - x :=
      RFAP.ConstructiveFraction.sub_pos_direct
        (xNegative.trans twiceSamplePositive)
    have differenceNegative : x - 2 * sample < 0 := by
      calc
        x - 2 * sample = -(2 * sample - x) := by ring1
        _ < 0 := neg_neg_of_pos reverseDifferencePositive
    have factorPositive :=
      RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
        xNegative differenceNegative
    have reverse : sample ^ 2 < (x - sample) ^ 2 := by
      have positiveDifference :
          0 < (x - sample) ^ 2 - sample ^ 2 := by
        calc
          0 < x * (x - 2 * sample) := factorPositive
          _ = (x - sample) ^ 2 - sample ^ 2 := by ring1
      have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
        positiveDifference (sample ^ 2)
      calc
        sample ^ 2 = 0 + sample ^ 2 := by ring1
        _ < ((x - sample) ^ 2 - sample ^ 2) + sample ^ 2 := shifted
        _ = (x - sample) ^ 2 := by ring1
    exact (lt_asymm close reverse).elim
  · rw [zero_sub, neg_sq] at close
    exact (lt_irrefl _ close).elim
  · rw [zero_sub, neg_sq] at close
    exact (lt_irrefl _ close).elim
  · rw [zero_sub, neg_sq] at close
    exact (lt_irrefl _ close).elim
  · have twiceSampleNegative : 2 * sample < 0 := by
      calc
        2 * sample = sample + sample := by ring1
        _ < 0 + sample :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct
            sampleNegative sample
        _ < 0 + 0 :=
          RFAP.ConstructiveFraction.add_lt_add_left_direct sampleNegative 0
        _ = 0 := by ring1
    have differencePositive : 0 < x - 2 * sample :=
      RFAP.ConstructiveFraction.sub_pos_direct
        (twiceSampleNegative.trans xPositive)
    have factorPositive := RFAP.ConstructiveFraction.mul_pos_direct
      xPositive differencePositive
    have reverse : sample ^ 2 < (x - sample) ^ 2 := by
      have positiveDifference :
          0 < (x - sample) ^ 2 - sample ^ 2 := by
        calc
          0 < x * (x - 2 * sample) := factorPositive
          _ = (x - sample) ^ 2 - sample ^ 2 := by ring1
      have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
        positiveDifference (sample ^ 2)
      calc
        sample ^ 2 = 0 + sample ^ 2 := by ring1
        _ < ((x - sample) ^ 2 - sample ^ 2) + sample ^ 2 := shifted
        _ = (x - sample) ^ 2 := by ring1
    exact (lt_asymm close reverse).elim
  · rw [sub_zero] at close
    exact ((not_lt_of_ge
      (RFAP.ConstructiveFraction.sq_nonneg_direct x)) close).elim
  · exact RFAP.ConstructiveFraction.mul_pos_direct xPositive samplePositive

/-- Proof-bearing finite strict-sign certificate. -/
structure Certificate (p : Polynomial) (interval : Interval) where
  sample : Coordinate
  sampleInside : interval.Contains sample
  margin : denseEvalSqLipschitzBound p interval *
      sampleRadiusSq interval sample < p.eval sample ^ 2

namespace Certificate

theorem eval_mul_sample_pos {p : Polynomial} {interval : Interval}
    (certificate : Certificate p interval) {x : Coordinate}
    (inside : interval.Contains x) :
    0 < p.eval x * p.eval certificate.sample := by
  have difference := eval_sub_sq_le p interval inside certificate.sampleInside
  have radius := sub_sq_le_sampleRadiusSq interval
    (sample := certificate.sample) (x := x) inside
  have slopeNonnegative := (denseHornerSqBounds_nonneg p interval).2
  have scaledRadius :
      denseEvalSqLipschitzBound p interval *
          (x - certificate.sample) ^ 2 ≤
        denseEvalSqLipschitzBound p interval *
          sampleRadiusSq interval certificate.sample :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      radius slopeNonnegative
  exact mul_pos_of_sub_sq_lt_sq
    (difference.trans_lt (scaledRadius.trans_lt certificate.margin))

theorem eval_mul_pos {p : Polynomial} {interval : Interval}
    (certificate : Certificate p interval) {x y : Coordinate}
    (xInside : interval.Contains x) (yInside : interval.Contains y) :
    0 < p.eval x * p.eval y := by
  have xSample := certificate.eval_mul_sample_pos xInside
  have ySample := certificate.eval_mul_sample_pos yInside
  rcases lt_trichotomy (p.eval certificate.sample) 0 with
      sampleNegative | sampleZero | samplePositive
  · have xNegative : p.eval x < 0 := by
      rcases lt_trichotomy (p.eval x) 0 with xNegative | xZero | xPositive
      · exact xNegative
      · rw [xZero, zero_mul] at xSample
        exact (lt_irrefl 0 xSample).elim
      · have productNegative :=
          RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
            xPositive sampleNegative
        exact (lt_asymm xSample productNegative).elim
    have yNegative : p.eval y < 0 := by
      rcases lt_trichotomy (p.eval y) 0 with yNegative | yZero | yPositive
      · exact yNegative
      · rw [yZero, zero_mul] at ySample
        exact (lt_irrefl 0 ySample).elim
      · have productNegative :=
          RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
            yPositive sampleNegative
        exact (lt_asymm ySample productNegative).elim
    exact RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
      xNegative yNegative
  · rw [sampleZero, mul_zero] at xSample
    exact (lt_irrefl 0 xSample).elim
  · have xPositive : 0 < p.eval x := by
      rcases lt_trichotomy (p.eval x) 0 with xNegative | xZero | xPositive
      · have productNegative :=
          RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
            xNegative samplePositive
        exact (lt_asymm xSample productNegative).elim
      · rw [xZero, zero_mul] at xSample
        exact (lt_irrefl 0 xSample).elim
      · exact xPositive
    have yPositive : 0 < p.eval y := by
      rcases lt_trichotomy (p.eval y) 0 with yNegative | yZero | yPositive
      · have productNegative :=
          RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
            yNegative samplePositive
        exact (lt_asymm ySample productNegative).elim
      · rw [yZero, zero_mul] at ySample
        exact (lt_irrefl 0 ySample).elim
      · exact yPositive
    exact RFAP.ConstructiveFraction.mul_pos_direct xPositive yPositive

theorem endpoint_stable {p : Polynomial} {interval : Interval}
    (certificate : Certificate p interval) :
    0 < p.eval interval.lower * p.eval interval.upper :=
  certificate.eval_mul_pos ⟨le_rfl, interval.valid⟩ ⟨interval.valid, le_rfl⟩

theorem eval_ne_zero {p : Polynomial} {interval : Interval}
    (certificate : Certificate p interval) {x : Coordinate}
    (inside : interval.Contains x) : p.eval x ≠ 0 := by
  intro zero
  have positive := certificate.eval_mul_sample_pos inside
  rw [zero, zero_mul] at positive
  exact (lt_irrefl 0 positive).elim

theorem polynomial_nonzero {p : Polynomial} {interval : Interval}
    (certificate : Certificate p interval) : p.isZero = false :=
  isZero_false_of_eval_ne
    (certificate.eval_ne_zero certificate.sampleInside)

end Certificate

/-- Executable left-endpoint sign classifier.  The successful branch returns
the proof-bearing certificate whose tested inequality is definitionally the
Boolean comparison just performed. -/
def certificate? (p : Polynomial) (interval : Interval) :
    Option (Certificate p interval) :=
  if margin : denseEvalSqLipschitzBound p interval *
      sampleRadiusSq interval interval.lower < p.eval interval.lower ^ 2 then
    some
      { sample := interval.lower
        sampleInside := ⟨le_rfl, interval.valid⟩
        margin := margin }
  else none

theorem certificate?_some_margin {p : Polynomial} {interval : Interval}
    {certificate : Certificate p interval}
    (found : certificate? p interval = some certificate) :
    denseEvalSqLipschitzBound p interval *
        sampleRadiusSq interval interval.lower <
      p.eval interval.lower ^ 2 := by
  unfold certificate? at found
  split at found
  · assumption
  · contradiction

theorem certificate?_isSome_iff (p : Polynomial) (interval : Interval) :
    (certificate? p interval).isSome = true ↔
      denseEvalSqLipschitzBound p interval *
          sampleRadiusSq interval interval.lower <
        p.eval interval.lower ^ 2 := by
  unfold certificate?
  split
  · simp_all
  · simp_all

end RFAP.IntervalSign
