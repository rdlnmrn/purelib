import RFAP.Polynomial.DenominatorHeight
import mathlib.RFAP.NormalizedGaussian

/-!
# Finite resource bounds for coefficient clearing

The least-common-denominator construction is bounded by the displayed product
of the canonical coordinate denominators.  This is deliberately coarse, but
it bounds the scale and every Gaussian-integer coefficient produced by the
actual finite clearing routine.
-/

namespace RFAP.ClearingCalculationSize

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt

def coefficientDenominatorProduct : List Gaussian → Nat
  | [] => 1
  | coefficient :: remaining =>
      let realDen :=
        (RFAP.ConstructiveFraction.representative coefficient.re).den
      let imaginaryDen :=
        (RFAP.ConstructiveFraction.representative coefficient.im).den
      realDen * imaginaryDen * coefficientDenominatorProduct remaining

theorem coefficientDenominator_le_product (coefficient : Gaussian) :
    RFAP.DenominatorHeight.coefficientDenominator coefficient ≤
      (RFAP.ConstructiveFraction.representative coefficient.re).den *
        (RFAP.ConstructiveFraction.representative coefficient.im).den := by
  apply Nat.le_of_dvd
  · exact Nat.mul_pos
      (RFAP.ConstructiveFraction.representative coefficient.re).den_pos
      (RFAP.ConstructiveFraction.representative coefficient.im).den_pos
  · exact RFAP.CanonicalLCM.lcm_dvd_mul _ _

theorem lcmScale_le_denominatorProduct : ∀ coefficients : List Gaussian,
    RFAP.DenominatorHeight.lcmScale coefficients ≤
      coefficientDenominatorProduct coefficients
  | [] => le_refl 1
  | coefficient :: remaining => by
      unfold RFAP.DenominatorHeight.lcmScale coefficientDenominatorProduct
      have lcmBound : RFAP.CanonicalLCM.lcm
          (RFAP.DenominatorHeight.coefficientDenominator coefficient)
          (RFAP.DenominatorHeight.lcmScale remaining) ≤
          RFAP.DenominatorHeight.coefficientDenominator coefficient *
            RFAP.DenominatorHeight.lcmScale remaining := by
        apply Nat.le_of_dvd
        · exact Nat.mul_pos
            (RFAP.DenominatorHeight.coefficientDenominator_pos coefficient)
            (RFAP.DenominatorHeight.lcmScale_pos remaining)
        · exact RFAP.CanonicalLCM.lcm_dvd_mul _ _
      exact lcmBound.trans (Nat.mul_le_mul
        (coefficientDenominator_le_product coefficient)
        (lcmScale_le_denominatorProduct remaining))

def coefficientComponentMagnitude (coefficient : Gaussian) : Nat :=
  max
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational coefficient.re))
    (RFAP.NormalizedFraction.componentMagnitude
      (RFAP.NormalizedFraction.ofRational coefficient.im))

theorem scaledCoordinateNumerator_le (scale : Nat)
    (coordinate : RFAP.ConstructiveFraction.Rational) :
    (RFAP.DenominatorHeight.scaledCoordinateNumerator scale coordinate).natAbs ≤
      RFAP.NormalizedFraction.componentMagnitude
          (RFAP.NormalizedFraction.ofRational coordinate) * scale := by
  let reduced := RFAP.ConstructiveFraction.representative coordinate
  change (reduced.num * ((scale / reduced.den : Nat) : Int)).natAbs ≤ _
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul
    (RFAP.NormalizedFraction.numerator_le_componentMagnitude reduced)
    (Nat.div_le_self scale reduced.den)

def clearedCoefficientMagnitudeEnvelope
    (coefficients : List Gaussian) : Nat :=
  coefficients.foldl (fun bound coefficient =>
    max bound (coefficientComponentMagnitude coefficient *
      coefficientDenominatorProduct coefficients)) 0

private theorem foldl_max_initial_le (weight : Gaussian → Nat) :
    ∀ (coefficients : List Gaussian) (initial : Nat),
      initial ≤ coefficients.foldl
        (fun bound coefficient => max bound (weight coefficient)) initial
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      (le_max_left _ _).trans (foldl_max_initial_le weight remaining _)

private theorem member_le_foldl_max (weight : Gaussian → Nat) :
    ∀ (coefficients : List Gaussian) (initial : Nat)
      (candidate : Gaussian), candidate ∈ coefficients →
      weight candidate ≤ coefficients.foldl
        (fun bound coefficient => max bound (weight coefficient)) initial
  | [], _, _, member => by simp at member
  | coefficient :: remaining, initial, candidate, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | tail
      · rw [equal]
        exact (le_max_right _ _).trans
          (foldl_max_initial_le weight remaining _)
      · exact member_le_foldl_max weight remaining
          (max initial (weight coefficient)) candidate tail

private theorem member_le_clearedEnvelope
    (coefficients : List Gaussian) (candidate : Gaussian)
    (member : candidate ∈ coefficients) :
    coefficientComponentMagnitude candidate *
        coefficientDenominatorProduct coefficients ≤
      clearedCoefficientMagnitudeEnvelope coefficients := by
  exact member_le_foldl_max
    (fun value => coefficientComponentMagnitude value *
      coefficientDenominatorProduct coefficients)
    coefficients 0 candidate member

/-- Every integral component in the cleared coefficient corresponding to a
displayed source coefficient fits the product-scale envelope. -/
theorem scaledGaussianCoefficient_component_le
    (coefficients : List Gaussian) (coefficient : Gaussian)
    (member : coefficient ∈ coefficients) :
    max
        (RFAP.DenominatorHeight.scaledGaussianCoefficient
          (RFAP.DenominatorHeight.lcmScale coefficients) coefficient).re.natAbs
        (RFAP.DenominatorHeight.scaledGaussianCoefficient
          (RFAP.DenominatorHeight.lcmScale coefficients) coefficient).im.natAbs ≤
      clearedCoefficientMagnitudeEnvelope coefficients := by
  apply max_le
  · exact (scaledCoordinateNumerator_le
      (RFAP.DenominatorHeight.lcmScale coefficients) coefficient.re).trans
      ((Nat.mul_le_mul
        (le_max_left _ _)
        (lcmScale_le_denominatorProduct coefficients)).trans
        (member_le_clearedEnvelope coefficients coefficient member))
  · exact (scaledCoordinateNumerator_le
      (RFAP.DenominatorHeight.lcmScale coefficients) coefficient.im).trans
      ((Nat.mul_le_mul
        (le_max_right _ _)
        (lcmScale_le_denominatorProduct coefficients)).trans
        (member_le_clearedEnvelope coefficients coefficient member))

def coefficientClearingOperationBudget (coefficients : List Gaussian) : Nat :=
  6 * coefficients.length

@[simp] theorem lcmClear_output_length (coefficients : List Gaussian) :
    (RFAP.DenominatorHeight.lcmClear coefficients).coefficients.length =
      coefficients.length :=
  RFAP.DenominatorHeight.lcmClear_length coefficients

end RFAP.ClearingCalculationSize
