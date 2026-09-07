import CCL.Riemann.LegendreAutomaticPreparation

/-!
# Denominator preparation survives fractional composition

A preparation provider for all invertible integral matrices can be carried
through a prepared fractional action. An outer denominator is represented as
the quotient of the combined and inner denominators. Both are already apart;
one retained base state supplies a uniform upper bound for the divisor.
-/

namespace CCL.Riemann.LegendrePreparationClosure

open CCL.Riemann.LegendreModularMonodromy
open CCL.Riemann.LegendreFractionalAction

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev IntegralMatrix := CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev DenominatorPreparation := CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation

/-- Restrict an already prepared denominator to its retained initial state.
This supplies both lower and upper bounds for all later possible readings. -/
def basedPreparation {denominator : CoherentNamed}
    (preparation : DenominatorPreparation denominator) : DenominatorPreparation denominator where
  prepared := preparation.prepared.based preparation.prepared.name.state
  apart := { certificate :=
    { lowerSq := preparation.apart.certificate.lowerSq
      positive := preparation.apart.certificate.positive
      lower := by
        intro state value inside
        exact preparation.apart.certificate.lower state.source inside } }
  equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans preparation.equivalent
    (preparation.prepared.basedEquivalent preparation.prepared.name.state)

def divisorUpper {denominator : CoherentNamed}
    (preparation : DenominatorPreparation denominator) : Q :=
  2 * (preparation.prepared.coherent.allowance preparation.prepared.name.state +
    preparation.prepared.name.process.centerBound) + 1

theorem divisorUpper_positive {denominator : CoherentNamed}
    (preparation : DenominatorPreparation denominator) : 0 < divisorUpper preparation := by
  have nonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct (by decide : (0 : Q) ≤ 2)
    (add_nonneg (preparation.prepared.coherent.allowance_nonneg preparation.prepared.name.state)
      preparation.prepared.name.process.centerBound_nonneg)
  exact lt_of_lt_of_le (by decide : (0 : Q) < 1)
    (le_add_of_nonneg_left nonnegative)

theorem divisor_bounded {denominator : CoherentNamed}
    (preparation : DenominatorPreparation denominator)
    (state : (basedPreparation preparation).prepared.name.process.State)
    {value : Gaussian}
    (possible : (basedPreparation preparation).prepared.name.process.Possible state value) :
    RFAP.ConstructiveGaussian.Gaussian.normSq value ≤ divisorUpper preparation :=
  (CCL.ProgressiveCoherence.Coherent.possible_normSq_le preparation.prepared.coherent
    (state.persists possible)).trans (le_add_of_nonneg_right (by decide : (0 : Q) ≤ 1))

def quotient {numerator denominator : CoherentNamed}
    (top : DenominatorPreparation numerator) (bottom : DenominatorPreparation denominator) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.div top.prepared
    (basedPreparation bottom).prepared (basedPreparation bottom).apart

/-- Apartness of the quotient needs only the numerator lower bound and the
retained denominator upper bound; no new search is performed. -/
def quotientApart {numerator denominator : CoherentNamed}
    (top : DenominatorPreparation numerator) (bottom : DenominatorPreparation denominator) :
    CCL.ProgressiveCharts.PossibleApart (quotient top bottom).name.process where
  lowerSq := top.apart.certificate.lowerSq / divisorUpper bottom
  positive := RFAP.ConstructiveFraction.div_pos_direct top.apart.certificate.positive
    (divisorUpper_positive bottom)
  lower := by
    intro state value possible
    rcases possible with ⟨x, y, hx, hy, rfl⟩
    have xLower := top.apart.certificate.lower _
      (top.prepared.name.process.possible_inside hx)
    have yPositive := (basedPreparation bottom).apart.certificate.positive.trans_le
      ((basedPreparation bottom).apart.certificate.lower _
        ((basedPreparation bottom).prepared.name.process.possible_inside hy))
    have yNonzero : y ≠ 0 := by
      intro zero
      rw [zero, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at yPositive
      exact lt_irrefl _ yPositive
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _ yNonzero]
    apply (RFAP.ConstructiveFraction.le_div_iff_pos yPositive).2
    calc
      (top.apart.certificate.lowerSq / divisorUpper bottom) *
          RFAP.ConstructiveGaussian.Gaussian.normSq y ≤
        (top.apart.certificate.lowerSq / divisorUpper bottom) * divisorUpper bottom :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (divisor_bounded bottom _ hy)
            (RFAP.ConstructiveFraction.div_nonneg_direct top.apart.certificate.positive.le
              (divisorUpper_positive bottom).le)
      _ = top.apart.certificate.lowerSq :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          (divisorUpper_positive bottom).ne'
      _ ≤ RFAP.ConstructiveGaussian.Gaussian.normSq x := xLower

/-- An executable right inverse is sufficient throughout. -/
structure RightInverse (matrix : IntegralMatrix) where
  inverse : IntegralMatrix
  identity : RFAP.ConstructiveFiniteMatrix.mul matrix inverse =
    RFAP.ConstructiveFiniteMatrix.identity

def identityInverse : RightInverse RFAP.ConstructiveFiniteMatrix.identity :=
  ⟨RFAP.ConstructiveFiniteMatrix.identity,
    CCL.Riemann.LegendrePicardLefschetz.identity_mul_int _⟩

def mulInverse {left right : IntegralMatrix}
    (leftInverse : RightInverse left) (rightInverse : RightInverse right) :
    RightInverse (RFAP.ConstructiveFiniteMatrix.mul left right) where
  inverse := RFAP.ConstructiveFiniteMatrix.mul rightInverse.inverse leftInverse.inverse
  identity := by
    rw [RFAP.ConstructiveFiniteMatrix.mul_assoc,
      ← RFAP.ConstructiveFiniteMatrix.mul_assoc right,
      rightInverse.identity, CCL.Riemann.LegendrePicardLefschetz.identity_mul_int,
      leftInverse.identity]

/-- A uniform constructive preparation provider, with no per-word analytic
requirements once it has been built from the initial positive enclosure. -/
def Provider (tau : CoherentNamed) : Type 1 :=
  (matrix : IntegralMatrix) → RightInverse matrix →
    DenominatorPreparation (fractionalDenominator matrix tau)

def ofPositiveEnclosure {tau : CoherentNamed}
    (positive : CCL.Riemann.LegendreAutomaticPreparation.PositiveEnclosure tau) : Provider tau :=
  fun matrix inverse => CCL.Riemann.LegendreAutomaticPreparation.prepare positive matrix
    (CCL.Riemann.LegendreAutomaticPreparation.row_nonzero_of_inverse _ _ inverse.identity)

/-- Carry the provider through an actual prepared fractional output. This
avoids assuming independent numerator/denominator readings are synchronized. -/
def after {tau : CoherentNamed} (provider : Provider tau)
    (right : IntegralMatrix) (rightInverse : RightInverse right)
    (inner : DenominatorPreparation (fractionalDenominator right tau)) :
    Provider (fractionalLinear right tau inner) := by
  intro left leftInverse
  let combined := provider (RFAP.ConstructiveFiniteMatrix.mul left right)
    (mulInverse leftInverse rightInverse)
  let bottom := basedPreparation inner
  let outer := fractionalDenominator left (fractionalLinear right tau inner)
  let value := quotient combined inner
  let ready := DenominatorPreparation.ofPossibleApart value (quotientApart combined inner)
  have scaled := fractionalRows_mul_scaled left right tau inner 0
  have leftScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul bottom.prepared outer).name
      combined.prepared.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects _ _ _ _
        (CCL.OperationalEquivalence.NamedEquivalent.symm bottom.equivalent)
        (CCL.OperationalEquivalence.NamedEquivalent.refl _))
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.OperationalEquivalence.NamedEquivalent.symm scaled) combined.equivalent)
  have rightScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul bottom.prepared value).name
      combined.prepared.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_comm _ _)
      (CCL.Riemann.OperationalQuotients.coherentDiv_mul_cancel _ _ bottom.apart)
  have equal := CCL.Riemann.OperationalQuotients.coherentMul_cancel_left
    bottom.prepared outer value bottom.apart
    (CCL.OperationalEquivalence.NamedEquivalent.trans leftScaled
      (CCL.OperationalEquivalence.NamedEquivalent.symm rightScaled))
  exact
    { prepared := ready.prepared
      apart := ready.apart
      equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans equal ready.equivalent }

end CCL.Riemann.LegendrePreparationClosure
