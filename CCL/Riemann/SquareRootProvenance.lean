import CCL.Progressive.ExactProvenanceLaws
import CCL.Riemann.CertifiedSquareRoot

/-!
# Exact decisions from square-root provenance

The defining equation is operational: finite rational readings are not
assumed to solve the polynomial exactly. Its finite comparison modulus
instead produces sufficiently accurate square residuals. The audited
square-root residual bound then supplies nonzero separation, while a zero
radicand gives an operational identity to zero.
-/

namespace CCL.Riemann.SquareRootProvenance

open CCL.ProgressiveExactProvenance (Q Gaussian CoherentNamed NamedEquivalent Prepared ZeroIdentity)
open RFAP.ConstructiveGaussian.Gaussian

abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent

def SquareIdentity (channel : CoherentNamed) (parameter : Gaussian) :=
  NamedEquivalent (CCL.ProgressiveCoherence.CoherentNamed.mul channel channel).name
    (CCL.ProgressiveCoherence.CoherentNamed.exact parameter).name

/-- Convert the operational polynomial equation to residuals of the actual
canonical finite samples, without asserting that those samples are roots. -/
def sampled_square {channel : CoherentNamed} {parameter : Gaussian}
    (square : SquareIdentity channel parameter) :
    Equivalent (CCL.TranscendentalCoherence.sampledProductApproximation channel.name channel.name)
      (CCL.ProgressiveSampling.approximation
        (CCL.ProgressiveCoherence.CoherentNamed.exact parameter).name) :=
  CCL.OperationalEquivalence.Equivalent.trans
    (CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling _))
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (CCL.TranscendentalCoherence.coherentMul_toNamed channel channel)) square)

private theorem lt_of_square_lt {value target : Q} (positive : 0 < target)
    (small : value ^ 2 < target ^ 2) : value < target :=
  ⟨RFAP.ConstructiveFraction.le_of_sq_le_sq_direct positive.le small.le,
    fun reverse => (not_lt_of_ge
      (RFAP.ConstructiveFraction.pow_le_pow_direct positive.le reverse 2)) small⟩

/-- Squaring to zero forces operational zero via an explicit squared
tolerance request. Approximate candidates need not themselves be zero. -/
def zero_of_square {channel : CoherentNamed} (square : SquareIdentity channel 0) :
    ZeroIdentity channel where
  compare := by
    intro leftStart rightStart target positive
    let comparison := (sampled_square square).compare leftStart rightStart (target ^ 2)
      (RFAP.ConstructiveFraction.pow_pos_direct positive 2)
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have close := comparison.close leftOrder rightOrder
          change normSq ((CCL.ProgressiveSampling.approximation channel.name).sample leftLater *
            (CCL.ProgressiveSampling.approximation channel.name).sample leftLater - 0) <
              target ^ 2 at close
          rw [RFAP.ConstructiveGaussian.Gaussian.sub_zero, normSq_mul] at close
          change normSq ((CCL.ProgressiveSampling.approximation channel.name).sample leftLater - 0) <
            target
          rw [RFAP.ConstructiveGaussian.Gaussian.sub_zero]
          exact lt_of_square_lt positive (by simpa only [pow_two] using close) }

/-- A nonzero polynomial coefficient gives a prepared equivalent channel.
The selected sampled base and the apartified denominator are computed once
and retained. Separation comes from polynomial residuals, not exact roots
among the rational readings. -/
def prepared_of_square {channel : CoherentNamed} {parameter : Gaussian}
    (square : SquareIdentity channel parameter) (nonzero : parameter ≠ 0) : Prepared channel :=
  let source := CCL.ProgressiveSampling.approximation channel.name
  let sampled := CCL.ProgressiveCoherence.CoherentNamed.ofApproximation source
  let comparison := (sampled_square square).compare 0 0
    (CCL.Riemann.SquareRootSheets.residualTarget parameter)
    (CCL.Riemann.SquareRootSheets.residualTarget_positive nonzero)
  let state : CCL.ProgressivePartialDivision.State sampled :=
    { source := comparison.leftIndex
      nextIndex := 0
      persists := by
        intro value possible
        rcases possible with ⟨later, _order, equal⟩
        exact ⟨later, Nat.zero_le _, equal⟩ }
  let evidence : CCL.ProgressiveCharts.PossibleApart
      (CCL.ProgressiveCharts.based sampled.name.process state.source) :=
    { lowerSq := CCL.Riemann.SquareRootSheets.sampleNormLower parameter
      positive := CCL.Riemann.SquareRootSheets.sampleLower_positive nonzero
      lower := by
        intro laterState value possible
        have atBase := laterState.persists possible
        rcases atBase with ⟨later, order, equal⟩
        rw [equal]
        have residual := comparison.close order (Nat.le_refl comparison.rightIndex)
        change normSq (source.sample later * source.sample later - parameter) <
          CCL.Riemann.SquareRootSheets.residualTarget parameter at residual
        exact CCL.Riemann.SquareRootSheets.normSq_lower_of_square_residual residual.le }
  let prepared := CCL.ProgressiveExactProvenance.Prepared.ofEvidence state evidence
  { denominator := prepared.denominator
    apart := prepared.apart
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.Equivalent.symm
        (CCL.OperationalEquivalence.Equivalent.toNamed_sampling source)) prepared.equivalent }

/-- A positive residual request also in the repeated-root case `parameter = 0`.
For nonzero parameters it is the audited polynomial separation threshold. -/
def residualRequest (parameter : Gaussian) : Q :=
  if parameter = 0 then 1 else CCL.Riemann.SquareRootSheets.residualTarget parameter

theorem residualRequest_positive (parameter : Gaussian) : 0 < residualRequest parameter := by
  unfold residualRequest
  split
  · decide
  · exact CCL.Riemann.SquareRootSheets.residualTarget_positive ‹parameter ≠ 0›

/-- Coefficient-derived threshold below which an accurate square residual
identifies the zero case. This is not a pointwise gap on arbitrary samples. -/
def separationGap (parameter : Gaussian) : Q :=
  if parameter = 0 then 1 else CCL.Riemann.SquareRootSheets.sampleNormLower parameter

theorem separationGap_positive (parameter : Gaussian) : 0 < separationGap parameter := by
  unfold separationGap
  split
  · decide
  · exact CCL.Riemann.SquareRootSheets.sampleLower_positive ‹parameter ≠ 0›

/-- Cache a finite canonical reading and its certified polynomial residual.
The residual, not a claim that the reading is an exact root, licenses the
zero-identification theorem. -/
structure Observation (channel : CoherentNamed) (parameter : Gaussian) where
  index : Nat
  value : Gaussian
  value_eq : value = (CCL.ProgressiveSampling.approximation channel.name).sample index
  residual : normSq (value * value - parameter) < residualRequest parameter

def observe {channel : CoherentNamed} {parameter : Gaussian}
    (square : SquareIdentity channel parameter) : Observation channel parameter :=
  let comparison := (sampled_square square).compare 0 0 (residualRequest parameter)
    (residualRequest_positive parameter)
  { index := comparison.leftIndex
    value := (CCL.ProgressiveSampling.approximation channel.name).sample comparison.leftIndex
    value_eq := rfl
    residual := comparison.close (Nat.le_refl comparison.leftIndex)
      (Nat.le_refl comparison.rightIndex) }

/-- Sufficiently small *residual-certified* observations force the exact
zero coefficient. No equality test on an opaque channel is being assumed. -/
theorem Observation.parameter_zero_of_small {channel : CoherentNamed} {parameter : Gaussian}
    (observation : Observation channel parameter)
    (small : normSq observation.value < separationGap parameter) : parameter = 0 := by
  by_cases zero : parameter = 0
  · exact zero
  · have residual := observation.residual
    rw [residualRequest, if_neg zero] at residual
    rw [separationGap, if_neg zero] at small
    exact False.elim ((not_lt_of_ge
      (CCL.Riemann.SquareRootSheets.normSq_lower_of_square_residual residual.le)) small)

theorem Observation.small_of_parameter_zero {channel : CoherentNamed} {parameter : Gaussian}
    (observation : Observation channel parameter) (zero : parameter = 0) :
    normSq observation.value < separationGap parameter := by
  subst parameter
  have residual := observation.residual
  rw [residualRequest, if_pos rfl, RFAP.ConstructiveGaussian.Gaussian.sub_zero,
    normSq_mul] at residual
  rw [separationGap, if_pos rfl]
  apply lt_of_square_lt (by decide)
  rw [show (1 : Q) ^ 2 = 1 by decide, pow_two]
  exact residual

def Observation.zero_of_small {channel : CoherentNamed} {parameter : Gaussian}
    (observation : Observation channel parameter) (square : SquareIdentity channel parameter)
    (small : normSq observation.value < separationGap parameter) : ZeroIdentity channel :=
  zero_of_square (by simpa only [observation.parameter_zero_of_small small] using square)

/-- Exact coefficient arithmetic selects the answer; the operational square
equation supplies the finite correctness proof and comparison modulus.
There is no supplied positive/negative answer and no exhausted outcome.
Runtime depends on that modulus; these precision bounds are not CPU bounds. -/
def decide {channel : CoherentNamed} {parameter : Gaussian}
    (square : SquareIdentity channel parameter) : CCL.ProgressiveExactProvenance.Decision channel :=
  if zero : parameter = 0 then
    .excluded (zero_of_square (by simpa only [zero] using square))
  else .prepared (prepared_of_square square zero)

theorem decide_prepared {channel : CoherentNamed} {parameter : Gaussian}
    (square : SquareIdentity channel parameter) (nonzero : parameter ≠ 0) :
    decide square = .prepared (prepared_of_square square nonzero) := by
  unfold decide
  rw [dif_neg nonzero]

theorem decide_excluded {channel : CoherentNamed} (square : SquareIdentity channel 0) :
    decide square = .excluded (zero_of_square square) := by
  unfold decide
  rw [dif_pos rfl]
  rfl

end CCL.Riemann.SquareRootProvenance
