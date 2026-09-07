import CCL.Riemann.LegendreSignedGap

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
-/

namespace CCL.Riemann.LegendreSeparatedPreparation

open CCL.Riemann.LegendreModularMonodromy
open CCL.Riemann.LegendreGaussManin (integralGaussian)
open CCL.Riemann.LegendreAutomaticPreparation (Q affine rowLower rowLower_positive)
open RFAP.ConstructiveGaussian.Gaussian

/-- A retained candidate separation, weaker than a signed whole-ball
enclosure. The squared form avoids extracting square roots or deciding sign. -/
structure Separation (tau : CoherentNamed) where
  state : tau.name.process.State
  gap : Q
  positive : 0 < gap
  squared_lower : ∀ {value : Gaussian}, tau.name.process.Possible state value → gap ^ 2 ≤ value.im ^ 2

def Separation.based {tau : CoherentNamed} (certificate : Separation tau) : CoherentNamed :=
  tau.based certificate.state

theorem Separation.possible_squared_lower {tau : CoherentNamed} (certificate : Separation tau)
    (state : certificate.based.name.process.State) {value : Gaussian}
    (possible : certificate.based.name.process.Possible state value) :
    certificate.gap ^ 2 ≤ value.im ^ 2 := certificate.squared_lower (state.persists possible)

def Separation.after {tau : CoherentNamed} (certificate : Separation tau)
    (state : tau.name.process.State)
    (persists : ∀ {value : Gaussian}, tau.name.process.Possible state value →
      tau.name.process.Possible certificate.state value) : Separation tau :=
  { state := state
    gap := certificate.gap
    positive := certificate.positive
    squared_lower := fun possible => certificate.squared_lower (persists possible) }

theorem square_lower_of_negative {gap height : Q} (positive : 0 < gap) (upper : height ≤ -gap) :
    gap ^ 2 ≤ height ^ 2 := by
  have lower : gap ≤ -height := by
    simpa only [neg_neg] using RFAP.ConstructiveFraction.neg_le_neg_direct upper
  have square := RFAP.ConstructiveFraction.pow_le_pow_direct positive.le lower 2
  have same : (-height) ^ 2 = height ^ 2 := by ring1
  rwa [same] at square

/-- The familiar absolute-coordinate hypothesis supplies the squared datum. -/
def Separation.ofAbsolute {tau : CoherentNamed} (state : tau.name.process.State)
    (gap : Q) (positive : 0 < gap)
    (lower : ∀ {value : Gaussian}, tau.name.process.Possible state value → gap ≤ |value.im|) :
    Separation tau :=
  { state := state
    gap := gap
    positive := positive
    squared_lower := by
      intro value possible
      have square := RFAP.ConstructiveFraction.pow_le_pow_direct positive.le (lower possible) 2
      by_cases nonnegative : 0 ≤ value.im
      · rwa [abs_of_nonneg nonnegative] at square
      · rw [abs_of_nonpos (le_of_not_ge nonnegative)] at square
        have same : (-value.im) ^ 2 = value.im ^ 2 := by ring1
        rwa [same] at square }

def Separation.ofPositive {tau : CoherentNamed}
    (certificate : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau) : Separation tau :=
  { state := certificate.state
    gap := certificate.lower
    positive := certificate.positive
    squared_lower := fun possible => RFAP.ConstructiveFraction.pow_le_pow_direct
      certificate.positive.le (certificate.inside_lower (tau.name.process.possible_inside possible)) 2 }

/-- A negative acquisition result obstructs positivity but still supplies
all nonzero-row denominator preparations. -/
def Separation.ofNegative {tau : CoherentNamed}
    {state : CCL.Riemann.LegendrePositivityAcquisition.State tau} {delta : Q}
    (positive : 0 < delta)
    (certificate : CCL.Riemann.LegendreSignedAcquisition.Negative tau state delta) : Separation tau :=
  { state := state.retained.source
    gap := delta / 4
    positive := CCL.SignedDecision.quarter_positive positive
    squared_lower := fun possible => square_lower_of_negative
      (CCL.SignedDecision.quarter_positive positive) (certificate.upper possible) }

/-- The unsigned gap itself suffices, before running a sign classifier. -/
def Separation.ofGap {tau : CoherentNamed}
    (state : CCL.Riemann.LegendrePositivityAcquisition.State tau) (delta : Q) (positive : 0 < delta)
    (gap : CCL.Riemann.LegendreSignedGap.Gap tau state delta) : Separation tau :=
  { state := state.retained.source
    gap := delta
    positive := positive
    squared_lower := fun possible => (gap possible).elim
      (square_lower_of_negative positive)
      (fun lower => RFAP.ConstructiveFraction.pow_le_pow_direct positive.le lower 2) }

theorem rowLower_le_of_squared (a b : Int) (gap : Q) (value : Gaussian)
    (lower : gap ^ 2 ≤ value.im ^ 2) :
    rowLower a b gap ≤ normSq (integralGaussian a + integralGaussian b * value) := by
  unfold rowLower
  split
  next equal =>
    subst b
    change (a : Q) ^ 2 ≤
      ((a : Q) + (0 * value.re - 0 * value.im)) ^ 2 +
      (0 + (0 * value.im + 0 * value.re)) ^ 2
    simp only [MulZeroClass.zero_mul, _root_.sub_zero, _root_.add_zero,
      zero_pow (by decide : 2 ≠ 0)]
    exact le_rfl
  next _ =>
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      lower (RFAP.ConstructiveFraction.sq_nonneg_direct (b : Q))
    apply scaled.trans
    change (b : Q) ^ 2 * value.im ^ 2 ≤
      ((a : Q) + ((b : Q) * value.re - 0 * value.im)) ^ 2 +
      (0 + ((b : Q) * value.im + 0 * value.re)) ^ 2
    simp only [MulZeroClass.zero_mul, _root_.add_zero, _root_.zero_add, _root_.sub_zero]
    calc
      (b : Q) ^ 2 * value.im ^ 2 = ((b : Q) * value.im) ^ 2 := by ring1
      _ ≤ ((a : Q) + (b : Q) * value.re) ^ 2 + ((b : Q) * value.im) ^ 2 :=
        le_add_of_nonneg_left (RFAP.ConstructiveFraction.sq_nonneg_direct _)

def affineApart {tau : CoherentNamed} (certificate : Separation tau)
    (a b : Int) (nonzero : a ≠ 0 ∨ b ≠ 0) :
    CCL.ProgressiveCharts.PossibleApart (affine a b certificate.based).name.process where
  lowerSq := rowLower a b certificate.gap
  positive := rowLower_positive a b certificate.gap certificate.positive nonzero
  lower := by
    intro state value possible
    rcases possible with ⟨x, y, hx, hy, rfl⟩
    rcases hy with ⟨z, w, hz, hw, rfl⟩
    change x = integralGaussian a at hx
    change z = integralGaussian b at hz
    subst x
    subst z
    exact rowLower_le_of_squared a b certificate.gap w (certificate.possible_squared_lower _ hw)

def denominator_affine {tau : CoherentNamed} (certificate : Separation tau) (matrix : IntegralMatrix) :
    NamedEquivalent (fractionalDenominator matrix tau).name
      (affine (matrix 0 0) (matrix 0 1) certificate.based).name := by
  have expanded := matrixAction_row_two matrix (fractionalVector tau) 0
  rw [fractionalVector_zero, fractionalVector_one] at expanded
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (CCL.TranscendentalCoherence.coherentAdd_respects _ _ _ _
      (CCL.OperationalFieldLaws.coherentMul_one_right _)
      (CCL.TranscendentalCoherence.coherentMul_respects _ _ _ _
        (CCL.OperationalEquivalence.NamedEquivalent.refl _)
        (tau.basedEquivalent certificate.state)))

/-- The existing finite apartifier, now independent of imaginary sign. -/
def prepare {tau : CoherentNamed} (certificate : Separation tau)
    (matrix : IntegralMatrix) (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    DenominatorPreparation (fractionalDenominator matrix tau) :=
  let prepared := DenominatorPreparation.ofPossibleApart
    (affine (matrix 0 0) (matrix 0 1) certificate.based)
    (affineApart certificate (matrix 0 0) (matrix 0 1) nonzero)
  { prepared := prepared.prepared
    apart := prepared.apart
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (denominator_affine certificate matrix) prepared.equivalent }

theorem prepare_lowerSq {tau : CoherentNamed} (certificate : Separation tau)
    (matrix : IntegralMatrix) (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    (prepare certificate matrix nonzero).apart.certificate.lowerSq =
      rowLower (matrix 0 0) (matrix 0 1) certificate.gap / 8 := rfl

def provider {tau : CoherentNamed} (certificate : Separation tau) :
    CCL.Riemann.LegendrePreparationClosure.Provider tau :=
  fun matrix inverse => prepare certificate matrix
    (CCL.Riemann.LegendreAutomaticPreparation.row_nonzero_of_inverse _ _ inverse.identity)

end CCL.Riemann.LegendreSeparatedPreparation
