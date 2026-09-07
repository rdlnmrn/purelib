import CCL.Riemann.ExplicitLegendreGeneratedNormalization
import CCL.Riemann.ExplicitLegendreOneLoop
import CCL.Riemann.LegendrePeriodMonodromy

/-!
# Generated finite normalized Legendre monodromy

This final lightweight facade joins the generated finite A-period lower
certificate and normalized period data to the already certified rational
standard loops.  The resulting fraction-free monodromy theorem is closed
apart from a `Unit` initialization token and requires no denominator search.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.LegendreGaussManin
open CCL.Riemann.FiniteMatrixApproximation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

private theorem realSquare_le_normSq (value : Gaussian) :
    value.re ^ 2 <= RFAP.ConstructiveGaussian.Gaussian.normSq value := by
  have added := RFAP.ConstructiveFraction.add_le_add_right_direct
    (RFAP.ConstructiveFraction.sq_nonneg_direct value.im) (value.re ^ 2)
  calc
    value.re ^ 2 = 0 + value.re ^ 2 :=
      (RFAP.ConstructiveFraction.zero_add _).symm
    _ <= value.im ^ 2 + value.re ^ 2 := added
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq value :=
      RFAP.ConstructiveFraction.add_comm _ _

/-- The generated normalized period data, viewed on the exact rational base
frame used by the certified standard loops. -/
def generatedMonodromyBase (token : Unit) :
    CCL.Riemann.LegendrePeriodMonodromy.NormalizedData
      CCL.Riemann.ExplicitLegendreSegment.sourceFrame where
  normalized := generatedNormalizedPeriodData token

@[simp] theorem generatedMonodromyBase_ratio (token : Unit) :
    (generatedMonodromyBase token).ratio = generatedNormalizedRatio token :=
  rfl

/-- The generated normalized base fibre attached to the concrete zero and
one loops, and hence to their derived infinity and product paths. -/
def generatedMonodromyData (token : Unit) :
    CCL.Riemann.LegendrePeriodMonodromy.Data
      CCL.Riemann.ExplicitLegendreOneLoop.standardLoops where
  base := generatedMonodromyBase token

/-- The same generated base period programs, viewed through the generic
finite endpoint-continuation interface for the four standard closed loops. -/
def generatedStandardLoopContinuations (token : Unit) :
    CCL.Riemann.LegendreGaussManin.StandardLoopContinuations
      CCL.Riemann.ExplicitLegendreOneLoop.standardLoops where
  base := (generatedMonodromyBase token).toFibreData

/-- The period columns consumed by modular monodromy are exactly the columns
computed by finite endpoint continuation on the certified standard paths. -/
structure GeneratedLoopContinuationCertificate (token : Unit) : Prop where
  zero : (generatedMonodromyData token).zeroPeriods =
    (generatedStandardLoopContinuations token).zero
  one : (generatedMonodromyData token).onePeriods =
    (generatedStandardLoopContinuations token).one
  infinity : (generatedMonodromyData token).infinityPeriods =
    (generatedStandardLoopContinuations token).infinity
  product : (generatedMonodromyData token).productPeriods =
    (generatedStandardLoopContinuations token).product

/-- Closed provenance from the concrete standard paths to all four raw
transported period columns. -/
theorem generatedLoopContinuationCertificate (token : Unit) :
    GeneratedLoopContinuationCertificate token where
  zero := rfl
  one := rfl
  infinity := rfl
  product := rfl

/-- Closed topological Legendre monodromy for the same displayed paths:
root transport, exact homology and dual period matrices, symplecticity, and
the loop-product identity. -/
theorem generatedTopologicalMonodromyCertificate :
    CCL.Riemann.LegendreMonodromy.StandardLoops.Certificate
      CCL.Riemann.ExplicitLegendreOneLoop.standardLoops :=
  CCL.Riemann.LegendreMonodromy.StandardLoops.certificate
    CCL.Riemann.ExplicitLegendreOneLoop.standardLoops

/-- Headline closed monodromy result for the generated example: the actual
finite period column has the certified dual action around zero, one, and
infinity, the product loop returns it to the base column, and the displayed
integer matrices satisfy both inverse identities.  The statement remains
fraction-free, so it is unconditional at the normalized fibre. -/
def generatedFractionFreeMonodromyCertificate (token : Unit) :
    CCL.Riemann.LegendrePeriodMonodromy.FractionFreeCertificate
      (generatedMonodromyData token) :=
  CCL.Riemann.LegendrePeriodMonodromy.certificate
    (generatedMonodromyData token)

@[simp] theorem generatedMonodromyBase_aPeriod (token : Unit) :
    (generatedMonodromyBase token).aPeriod =
      (generatedSharpAPeriodProgram token).output := rfl

@[simp] theorem generatedMonodromyBase_bPeriod (token : Unit) :
    (generatedMonodromyBase token).bPeriod =
      (CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpBPeriodProgram
        token).output := rfl

/-! ## Synchronized finite lower certificates for transformed A-periods -/

/-- Canonical synchronized sampler for the generated A-period. -/
def generatedAPeriodSource (token : Unit) : GeometricApproximation :=
  GeometricApproximation.ofNamed (generatedMonodromyBase token).aPeriod.name

/-- Canonical synchronized sampler for the independently generated B-period. -/
def generatedBPeriodSource (token : Unit) : GeometricApproximation :=
  GeometricApproximation.ofNamed (generatedMonodromyBase token).bPeriod.name

theorem generatedAPeriodSource_sampleRealLower (token : Unit) (index : Nat) :
    generatedSharpUniformRealLower <=
      ((generatedAPeriodSource token).sample index).re := by
  simpa only [generatedAPeriodSource, GeometricApproximation.ofNamed_sample,
    generatedMonodromyBase_aPeriod] using
    generatedSharpAPeriodProgram_sampleRealLower token index

theorem generatedBPeriodSource_sampleRealLower (token : Unit) (index : Nat) :
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpUniformRealLower <=
      ((generatedBPeriodSource token).sample index).re := by
  simpa only [generatedBPeriodSource, GeometricApproximation.ofNamed_sample,
    generatedMonodromyBase_bPeriod] using
    CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpBPeriodProgram_sampleRealLower
      token index

/-- A positive real lower bound on every synchronized sample gives precisely
the possible-value apartness needed by constructive apartification. -/
def possibleApartOfPositiveRealSamples
    (source : GeometricApproximation) (lower : Coordinate)
    (positive : 0 < lower)
    (sampleLower : forall index, lower <= (source.sample index).re) :
    CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed source).name.process where
  lowerSq := lower ^ 2
  positive := RFAP.ConstructiveFraction.pow_pos_direct positive 2
  lower := by
    intro state value possible
    change source.toApproximation.Possible state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    change lower ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample later)
    have realSquare : lower ^ 2 <= (source.sample later).re ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct positive.le
        (sampleLower later) 2
    have projectionLower : (source.sample later).re ^ 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample later) :=
      realSquare_le_normSq (source.sample later)
    exact realSquare.trans projectionLower

def generatedAPeriodPossibleApart (token : Unit) :
    CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedAPeriodSource token)).name.process :=
  possibleApartOfPositiveRealSamples (generatedAPeriodSource token)
    generatedSharpUniformRealLower generatedSharpUniformRealLower_positive
    (generatedAPeriodSource_sampleRealLower token)

/-- Whole-ball-apart synchronized A-period used only as a cancellable finite
presentation; it is operationally the original generated A-period. -/
def generatedPreparedAPeriod (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (CCL.Riemann.PeriodMatrix.geometricNamed
      (generatedAPeriodSource token))
    (generatedAPeriodPossibleApart token)

def generatedPreparedAPeriodApart (token : Unit) :
    CCL.ProgressiveTransducer.Named.Apart
      (generatedPreparedAPeriod token).name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    (generatedAPeriodPossibleApart token)

def generatedAPeriod_equivalent_prepared (token : Unit) :
    NamedEquivalent (generatedMonodromyBase token).aPeriod.name
      (generatedPreparedAPeriod token).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.named_equivalent_geometricOfNamed
      (generatedMonodromyBase token).aPeriod)
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedAPeriodSource token))
      (generatedAPeriodPossibleApart token))

/-- Synchronized numerator `A + 2B` of the dual one-loop denominator. -/
def generatedOneDenominatorNumeratorSource (token : Unit) :
    GeometricApproximation :=
  GeometricApproximation.add (generatedAPeriodSource token)
    (GeometricApproximation.mul
      (GeometricApproximation.exact (show Gaussian from ⟨2, 0⟩))
      (generatedBPeriodSource token))

/-- Synchronized positive counterpart `3A + 2B` of the dual infinity-loop
denominator numerator `-3A - 2B`. -/
def generatedInfinityPositiveNumeratorSource (token : Unit) :
    GeometricApproximation :=
  GeometricApproximation.add
    (GeometricApproximation.mul
      (GeometricApproximation.exact (show Gaussian from ⟨3, 0⟩))
      (generatedAPeriodSource token))
    (GeometricApproximation.mul
      (GeometricApproximation.exact (show Gaussian from ⟨2, 0⟩))
      (generatedBPeriodSource token))

def generatedInfinityDenominatorNumeratorSource (token : Unit) :
    GeometricApproximation :=
  GeometricApproximation.add
    (GeometricApproximation.mul
      (GeometricApproximation.exact (show Gaussian from ⟨-3, 0⟩))
      (generatedAPeriodSource token))
    (GeometricApproximation.mul
      (GeometricApproximation.exact (show Gaussian from ⟨-2, 0⟩))
      (generatedBPeriodSource token))

def generatedOneNumeratorRealLower : Coordinate :=
  generatedSharpUniformRealLower +
    2 * CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpUniformRealLower

def generatedInfinityNumeratorRealMagnitudeLower : Coordinate :=
  3 * generatedSharpUniformRealLower +
    2 * CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpUniformRealLower

theorem generatedOneNumeratorRealLower_positive :
    0 < generatedOneNumeratorRealLower := by
  unfold generatedOneNumeratorRealLower
  exact add_pos generatedSharpUniformRealLower_positive
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpUniformRealLower_positive)

theorem generatedInfinityNumeratorRealMagnitudeLower_positive :
    0 < generatedInfinityNumeratorRealMagnitudeLower := by
  unfold generatedInfinityNumeratorRealMagnitudeLower
  exact add_pos
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      generatedSharpUniformRealLower_positive)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      CCL.Riemann.ExplicitLegendreGeneratedBCertificate.generatedSharpUniformRealLower_positive)

theorem generatedOneDenominatorNumeratorSource_sampleRealLower
    (token : Unit) (index : Nat) :
    generatedOneNumeratorRealLower <=
      ((generatedOneDenominatorNumeratorSource token).sample index).re := by
  have aLower := generatedAPeriodSource_sampleRealLower token index
  have bLower := generatedBPeriodSource_sampleRealLower token index
  have scaledB :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bLower
      (by decide : (0 : Coordinate) <= 2)
  simpa only [generatedOneNumeratorRealLower,
    generatedOneDenominatorNumeratorSource,
    GeometricApproximation.add_sample, GeometricApproximation.mul_sample,
    GeometricApproximation.exact_sample,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.re,
    RFAP.ConstructiveGaussian.Gaussian.im, zero_mul, sub_zero] using
    RFAP.ConstructiveFraction.add_le_add_direct aLower scaledB

theorem generatedInfinityPositiveNumeratorSource_sampleRealLower
    (token : Unit) (index : Nat) :
    generatedInfinityNumeratorRealMagnitudeLower <=
      ((generatedInfinityPositiveNumeratorSource token).sample index).re := by
  have aLower := generatedAPeriodSource_sampleRealLower token index
  have bLower := generatedBPeriodSource_sampleRealLower token index
  have scaledA :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct aLower
      (by decide : (0 : Coordinate) <= 3)
  have scaledB :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bLower
      (by decide : (0 : Coordinate) <= 2)
  simpa only [generatedInfinityNumeratorRealMagnitudeLower,
    generatedInfinityPositiveNumeratorSource,
    GeometricApproximation.add_sample, GeometricApproximation.mul_sample,
    GeometricApproximation.exact_sample,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.re,
    RFAP.ConstructiveGaussian.Gaussian.im, zero_mul, sub_zero] using
    RFAP.ConstructiveFraction.add_le_add_direct scaledA scaledB

/-- The negative-real counterpart of
`possibleApartOfPositiveRealSamples`. -/
def possibleApartOfNegativeRealSamples
    (source : GeometricApproximation) (magnitudeLower : Coordinate)
    (positive : 0 < magnitudeLower)
    (sampleUpper : forall index,
      (source.sample index).re <= -magnitudeLower) :
    CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed source).name.process where
  lowerSq := magnitudeLower ^ 2
  positive := RFAP.ConstructiveFraction.pow_pos_direct positive 2
  lower := by
    intro state value possible
    change source.toApproximation.Possible state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    change magnitudeLower ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample later)
    have magnitudeLe : magnitudeLower <= -(source.sample later).re := by
      simpa only [neg_neg] using
        RFAP.ConstructiveFraction.neg_le_neg_direct (sampleUpper later)
    have realSquare : magnitudeLower ^ 2 <=
        (-(source.sample later).re) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct positive.le magnitudeLe 2
    have projectionLower : (-(source.sample later).re) ^ 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq (source.sample later) := by
      rw [show (-(source.sample later).re) ^ 2 =
          (source.sample later).re ^ 2 by ring1]
      exact realSquare_le_normSq (source.sample later)
    exact realSquare.trans projectionLower

theorem generatedInfinityDenominatorNumeratorSource_sampleRealUpper
    (token : Unit) (index : Nat) :
    ((generatedInfinityDenominatorNumeratorSource token).sample index).re <=
      -generatedInfinityNumeratorRealMagnitudeLower := by
  have aLower := generatedAPeriodSource_sampleRealLower token index
  have bLower := generatedBPeriodSource_sampleRealLower token index
  have scaledA :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct aLower
      (by decide : (0 : Coordinate) <= 3)
  have scaledB :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bLower
      (by decide : (0 : Coordinate) <= 2)
  have positiveLower :=
    RFAP.ConstructiveFraction.add_le_add_direct scaledA scaledB
  have negativeUpper :=
    RFAP.ConstructiveFraction.neg_le_neg_direct positiveLower
  simp only [generatedInfinityDenominatorNumeratorSource,
    GeometricApproximation.add_sample, GeometricApproximation.mul_sample,
    GeometricApproximation.exact_sample,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.re,
    RFAP.ConstructiveGaussian.Gaussian.im, zero_mul, sub_zero]
  calc
    (-3 : Coordinate) * ((generatedAPeriodSource token).sample index).re +
        (-2 : Coordinate) * ((generatedBPeriodSource token).sample index).re =
        -(3 * ((generatedAPeriodSource token).sample index).re +
          2 * ((generatedBPeriodSource token).sample index).re) := by ring1
    _ <= -generatedInfinityNumeratorRealMagnitudeLower := by
      simpa only [generatedInfinityNumeratorRealMagnitudeLower] using
        negativeUpper

def generatedOneNumeratorPossibleApart (token : Unit) :
    CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedOneDenominatorNumeratorSource token)).name.process :=
  possibleApartOfPositiveRealSamples
    (generatedOneDenominatorNumeratorSource token)
    generatedOneNumeratorRealLower generatedOneNumeratorRealLower_positive
    (generatedOneDenominatorNumeratorSource_sampleRealLower token)

def generatedInfinityNumeratorPossibleApart (token : Unit) :
    CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedInfinityDenominatorNumeratorSource token)).name.process :=
  possibleApartOfNegativeRealSamples
    (generatedInfinityDenominatorNumeratorSource token)
    generatedInfinityNumeratorRealMagnitudeLower
    generatedInfinityNumeratorRealMagnitudeLower_positive
    (generatedInfinityDenominatorNumeratorSource_sampleRealUpper token)

def generatedOnePreparedNumerator (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (CCL.Riemann.PeriodMatrix.geometricNamed
      (generatedOneDenominatorNumeratorSource token))
    (generatedOneNumeratorPossibleApart token)

def generatedInfinityPreparedNumerator (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (CCL.Riemann.PeriodMatrix.geometricNamed
      (generatedInfinityDenominatorNumeratorSource token))
    (generatedInfinityNumeratorPossibleApart token)

def generatedOnePreparedNumeratorApart (token : Unit) :
    CCL.ProgressiveTransducer.Named.Apart
      (generatedOnePreparedNumerator token).name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    (generatedOneNumeratorPossibleApart token)

def generatedInfinityPreparedNumeratorApart (token : Unit) :
    CCL.ProgressiveTransducer.Named.Apart
      (generatedInfinityPreparedNumerator token).name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    (generatedInfinityNumeratorPossibleApart token)

def generatedOneRawNumerator (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (generatedMonodromyBase token).aPeriod
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact
        (show Gaussian from ⟨2, 0⟩))
      (generatedMonodromyBase token).bPeriod)

def generatedInfinityPositiveRawNumerator (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact
        (show Gaussian from ⟨3, 0⟩))
      (generatedMonodromyBase token).aPeriod)
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact
        (show Gaussian from ⟨2, 0⟩))
      (generatedMonodromyBase token).bPeriod)

def generatedInfinityRawNumerator (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact
        (show Gaussian from ⟨-3, 0⟩))
      (generatedMonodromyBase token).aPeriod)
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact
        (show Gaussian from ⟨-2, 0⟩))
      (generatedMonodromyBase token).bPeriod)

private def exactTwo_equivalent_geometric : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.exact
      (show Gaussian from ⟨2, 0⟩)).name
    (CCL.Riemann.PeriodMatrix.geometricNamed
      (GeometricApproximation.exact (show Gaussian from ⟨2, 0⟩))).name :=
  CCL.OperationalEquivalence.NamedEquivalent.symm
    (CCL.Riemann.FiniteBilinear.geometricExact_equivalent_exact
      (show Gaussian from ⟨2, 0⟩))

private def exactThree_equivalent_geometric : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.exact
      (show Gaussian from ⟨3, 0⟩)).name
    (CCL.Riemann.PeriodMatrix.geometricNamed
      (GeometricApproximation.exact (show Gaussian from ⟨3, 0⟩))).name :=
  CCL.OperationalEquivalence.NamedEquivalent.symm
    (CCL.Riemann.FiniteBilinear.geometricExact_equivalent_exact
      (show Gaussian from ⟨3, 0⟩))

private def exactMinusTwo_equivalent_geometric : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.exact
      (show Gaussian from ⟨-2, 0⟩)).name
    (CCL.Riemann.PeriodMatrix.geometricNamed
      (GeometricApproximation.exact (show Gaussian from ⟨-2, 0⟩))).name :=
  CCL.OperationalEquivalence.NamedEquivalent.symm
    (CCL.Riemann.FiniteBilinear.geometricExact_equivalent_exact
      (show Gaussian from ⟨-2, 0⟩))

private def exactMinusThree_equivalent_geometric : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.exact
      (show Gaussian from ⟨-3, 0⟩)).name
    (CCL.Riemann.PeriodMatrix.geometricNamed
      (GeometricApproximation.exact (show Gaussian from ⟨-3, 0⟩))).name :=
  CCL.OperationalEquivalence.NamedEquivalent.symm
    (CCL.Riemann.FiniteBilinear.geometricExact_equivalent_exact
      (show Gaussian from ⟨-3, 0⟩))

private def generatedBPeriod_equivalent_geometric (token : Unit) :
    NamedEquivalent (generatedMonodromyBase token).bPeriod.name
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedBPeriodSource token)).name :=
  CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.named_equivalent_geometricOfNamed
    (generatedMonodromyBase token).bPeriod

private def generatedAPeriod_equivalent_geometric (token : Unit) :
    NamedEquivalent (generatedMonodromyBase token).aPeriod.name
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedAPeriodSource token)).name :=
  CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.named_equivalent_geometricOfNamed
    (generatedMonodromyBase token).aPeriod

def generatedOneRawNumerator_equivalent_source (token : Unit) :
    NamedEquivalent (generatedOneRawNumerator token).name
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedOneDenominatorNumeratorSource token)).name := by
  apply CCL.Riemann.FiniteBilinear.coherentAdd_equivalent_geometricAdd
  · exact generatedAPeriod_equivalent_geometric token
  · apply
      CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.coherentMul_equivalent_geometricMul
    · exact exactTwo_equivalent_geometric
    · exact generatedBPeriod_equivalent_geometric token

def generatedInfinityPositiveRawNumerator_equivalent_source (token : Unit) :
    NamedEquivalent (generatedInfinityPositiveRawNumerator token).name
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedInfinityPositiveNumeratorSource token)).name := by
  apply CCL.Riemann.FiniteBilinear.coherentAdd_equivalent_geometricAdd
  · apply
      CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.coherentMul_equivalent_geometricMul
    · exact exactThree_equivalent_geometric
    · exact generatedAPeriod_equivalent_geometric token
  · apply
      CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.coherentMul_equivalent_geometricMul
    · exact exactTwo_equivalent_geometric
    · exact generatedBPeriod_equivalent_geometric token

def generatedInfinityRawNumerator_equivalent_source (token : Unit) :
    NamedEquivalent (generatedInfinityRawNumerator token).name
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedInfinityDenominatorNumeratorSource token)).name :=
  by
    apply CCL.Riemann.FiniteBilinear.coherentAdd_equivalent_geometricAdd
    · apply
        CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.coherentMul_equivalent_geometricMul
      · exact exactMinusThree_equivalent_geometric
      · exact generatedAPeriod_equivalent_geometric token
    · apply
        CCL.Riemann.PeriodMatrix.ScaledInverseCertificate.coherentMul_equivalent_geometricMul
      · exact exactMinusTwo_equivalent_geometric
      · exact generatedBPeriod_equivalent_geometric token

def generatedOneRawNumerator_equivalent_prepared (token : Unit) :
    NamedEquivalent (generatedOneRawNumerator token).name
      (generatedOnePreparedNumerator token).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (generatedOneRawNumerator_equivalent_source token)
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedOneDenominatorNumeratorSource token))
      (generatedOneNumeratorPossibleApart token))

def generatedInfinityRawNumerator_equivalent_prepared (token : Unit) :
    NamedEquivalent (generatedInfinityRawNumerator token).name
      (generatedInfinityPreparedNumerator token).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (generatedInfinityRawNumerator_equivalent_source token)
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
      (CCL.Riemann.PeriodMatrix.geometricNamed
        (generatedInfinityDenominatorNumeratorSource token))
      (generatedInfinityNumeratorPossibleApart token))

/-! ## Apart transformed-denominator presentations -/

/-- Quotient of two independently apartified synchronized sources. -/
def preparedGeometricQuotient
    (numerator denominator : GeometricApproximation)
    (numeratorApart : CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed numerator).name.process)
    (denominatorApart : CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed denominator).name.process) :
    CoherentNamed :=
  let preparedNumerator :=
    CCL.ProgressiveCoherence.CoherentNamed.apartify
      (CCL.Riemann.PeriodMatrix.geometricNamed numerator) numeratorApart
  let preparedDenominator :=
    CCL.ProgressiveCoherence.CoherentNamed.apartify
      (CCL.Riemann.PeriodMatrix.geometricNamed denominator) denominatorApart
  let apart : CCL.ProgressiveTransducer.Named.Apart
      preparedDenominator.name :=
    { certificate := CCL.ProgressiveCharts.apartifyApart denominatorApart }
  CCL.ProgressiveCoherence.CoherentNamed.div preparedNumerator
    preparedDenominator apart

/-- Possible quotient values inherit the numerator lower bound divided by
the denominator's global synchronized sample bound.  This remains a finite
possible-value theorem; apartification below performs the separate whole-ball
step required by productive division. -/
def preparedGeometricQuotientPossibleApart
    (numerator denominator : GeometricApproximation)
    (numeratorApart : CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed numerator).name.process)
    (denominatorApart : CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed denominator).name.process)
    (denominatorBoundPositive : 0 < denominator.centerBound) :
    CCL.ProgressiveCharts.PossibleApart
      (preparedGeometricQuotient numerator denominator numeratorApart
        denominatorApart).name.process where
  lowerSq := numeratorApart.lowerSq / denominator.centerBound
  positive := RFAP.ConstructiveFraction.div_pos_direct
    numeratorApart.positive denominatorBoundPositive
  lower := by
    intro state value possible
    rcases possible with ⟨x, y, xPossible, yPossible, rfl⟩
    have xLower : numeratorApart.lowerSq <=
        RFAP.ConstructiveGaussian.Gaussian.normSq x :=
      numeratorApart.lower _ xPossible
    have yLower : denominatorApart.lowerSq <=
        RFAP.ConstructiveGaussian.Gaussian.normSq y :=
      denominatorApart.lower _ yPossible
    have yNormPositive : 0 <
        RFAP.ConstructiveGaussian.Gaussian.normSq y :=
      denominatorApart.positive.trans_le yLower
    have yNonzero : y ≠ 0 := by
      intro zero
      rw [zero, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at yNormPositive
      exact (lt_irrefl _ yNormPositive).elim
    change denominator.toApproximation.Possible _ y at yPossible
    rcases yPossible with ⟨later, _order, rfl⟩
    have yUpper :
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominator.sample later) <= denominator.centerBound :=
      denominator.sample_bounded later
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _ yNonzero]
    change numeratorApart.lowerSq / denominator.centerBound <=
      RFAP.ConstructiveGaussian.Gaussian.normSq x /
        RFAP.ConstructiveGaussian.Gaussian.normSq (denominator.sample later)
    apply (RFAP.ConstructiveFraction.le_div_iff_pos yNormPositive).2
    calc
      (numeratorApart.lowerSq / denominator.centerBound) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (denominator.sample later) <=
          (numeratorApart.lowerSq / denominator.centerBound) *
            denominator.centerBound :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct yUpper
          (RFAP.ConstructiveFraction.div_nonneg_direct
            numeratorApart.positive.le denominatorBoundPositive.le)
      _ = numeratorApart.lowerSq :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
          denominatorBoundPositive.ne'
      _ <= RFAP.ConstructiveGaussian.Gaussian.normSq x := xLower

theorem generatedAPeriodSource_centerBound_positive (token : Unit) :
    0 < (generatedAPeriodSource token).centerBound := by
  let sample := (generatedAPeriodSource token).sample 0
  have realPositive : 0 < sample.re :=
    generatedSharpUniformRealLower_positive.trans_le
      (generatedAPeriodSource_sampleRealLower token 0)
  have realSquarePositive : 0 < sample.re ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct realPositive 2
  have realSquareLe : sample.re ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample :=
    realSquare_le_normSq sample
  exact (realSquarePositive.trans_le realSquareLe).trans_le
    ((generatedAPeriodSource token).sample_bounded 0)

def generatedOneRawDenominatorQuotient (token : Unit) : CoherentNamed :=
  preparedGeometricQuotient
    (generatedOneDenominatorNumeratorSource token)
    (generatedAPeriodSource token)
    (generatedOneNumeratorPossibleApart token)
    (generatedAPeriodPossibleApart token)

def generatedInfinityRawDenominatorQuotient (token : Unit) : CoherentNamed :=
  preparedGeometricQuotient
    (generatedInfinityDenominatorNumeratorSource token)
    (generatedAPeriodSource token)
    (generatedInfinityNumeratorPossibleApart token)
    (generatedAPeriodPossibleApart token)

def generatedOneRawDenominatorQuotientPossibleApart (token : Unit) :
    CCL.ProgressiveCharts.PossibleApart
      (generatedOneRawDenominatorQuotient token).name.process :=
  preparedGeometricQuotientPossibleApart
    (generatedOneDenominatorNumeratorSource token)
    (generatedAPeriodSource token)
    (generatedOneNumeratorPossibleApart token)
    (generatedAPeriodPossibleApart token)
    (generatedAPeriodSource_centerBound_positive token)

def generatedInfinityRawDenominatorQuotientPossibleApart (token : Unit) :
    CCL.ProgressiveCharts.PossibleApart
      (generatedInfinityRawDenominatorQuotient token).name.process :=
  preparedGeometricQuotientPossibleApart
    (generatedInfinityDenominatorNumeratorSource token)
    (generatedAPeriodSource token)
    (generatedInfinityNumeratorPossibleApart token)
    (generatedAPeriodPossibleApart token)
    (generatedAPeriodSource_centerBound_positive token)

def generatedOnePreparedDenominator (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (generatedOneRawDenominatorQuotient token)
    (generatedOneRawDenominatorQuotientPossibleApart token)

def generatedInfinityPreparedDenominator (token : Unit) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (generatedInfinityRawDenominatorQuotient token)
    (generatedInfinityRawDenominatorQuotientPossibleApart token)

def generatedOnePreparedDenominatorApart (token : Unit) :
    CCL.ProgressiveTransducer.Named.Apart
      (generatedOnePreparedDenominator token).name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    (generatedOneRawDenominatorQuotientPossibleApart token)

def generatedInfinityPreparedDenominatorApart (token : Unit) :
    CCL.ProgressiveTransducer.Named.Apart
      (generatedInfinityPreparedDenominator token).name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    (generatedInfinityRawDenominatorQuotientPossibleApart token)

/-! ## Provenance from normalized transport to the prepared denominators -/

/-- Reorder one middle factor without leaving operational coherent
arithmetic. -/
private def coherentMul_swap_middle
    (left middle right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul left
        (CCL.ProgressiveCoherence.CoherentNamed.mul middle right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul middle
        (CCL.ProgressiveCoherence.CoherentNamed.mul left right)).name := by
  let leftMiddle := CCL.ProgressiveCoherence.CoherentNamed.mul left middle
  let middleLeft := CCL.ProgressiveCoherence.CoherentNamed.mul middle left
  apply CCL.OperationalEquivalence.NamedEquivalent.trans
  · exact CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.TranscendentalCoherence.coherentMul_assoc left middle right)
  · apply CCL.OperationalEquivalence.NamedEquivalent.trans
    · exact CCL.TranscendentalCoherence.coherentMul_respects
        leftMiddle middleLeft right right
        (CCL.TranscendentalCoherence.coherentMul_comm left middle)
        (CCL.OperationalEquivalence.NamedEquivalent.refl right.name)
    · exact CCL.TranscendentalCoherence.coherentMul_assoc middle left right

def generatedOneDenominator_scaled (token : Unit) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (generatedMonodromyBase token).aPeriod
        (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
          CCL.Riemann.LegendreMonodromy.onePeriodMatrix
          (generatedMonodromyBase token).ratio)).name
      (generatedOneRawNumerator token).name := by
  let data := generatedMonodromyData token
  have homogeneous := data.one_homogeneous 0
  have scaledToPeriods : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        data.base.aPeriod
        (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
          CCL.Riemann.LegendreMonodromy.onePeriodMatrix
          data.base.ratio)).name
      (data.onePeriods 0).name := by
    exact CCL.OperationalEquivalence.NamedEquivalent.symm (by
      simpa only [CCL.Riemann.LegendreModularMonodromy.scaleVector,
        CCL.Riemann.LegendreModularMonodromy.fractionalDenominator,
        CCL.Riemann.LegendreModularMonodromy.fractionalRow] using homogeneous)
  have expanded := CCL.Riemann.LegendreModularMonodromy.matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.onePeriodMatrix
    data.base.toFibreData.rawPeriods 0
  rw [CCL.Riemann.LegendreMonodromy.onePeriodMatrix_explicit] at expanded
  have rawZero : data.base.toFibreData.rawPeriods 0 = data.base.aPeriod := rfl
  have rawOne : data.base.toFibreData.rawPeriods 1 = data.base.bPeriod := by
    unfold CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.toFibreData
      CCL.Riemann.LegendreGaussManin.FibreData.rawPeriods
      CCL.Riemann.LegendreGaussManin.FibreData.rawRefinement
      CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.bPeriod
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rfl
  rw [rawZero, rawOne] at expanded
  have periodsToMatrix : NamedEquivalent (data.onePeriods 0).name
      (CCL.Riemann.LegendreGaussManin.matrixAction
        CCL.Riemann.LegendreMonodromy.onePeriodMatrix
        data.base.toFibreData.rawPeriods 0).name := by
    unfold CCL.Riemann.LegendrePeriodMonodromy.Data.onePeriods
      CCL.Riemann.LegendrePeriodMonodromy.Data.periods
      CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.periods
      CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.continuation
      CCL.Riemann.LegendreGaussManin.EndpointContinuation.periods
    rw [CCL.Riemann.LegendreMonodromy.StandardLoops.onePath_periodMatrix]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  have matrixToNumerator : NamedEquivalent
      (CCL.Riemann.LegendreGaussManin.matrixAction
        CCL.Riemann.LegendreMonodromy.onePeriodMatrix
        data.base.toFibreData.rawPeriods 0).name
      (generatedOneRawNumerator token).name := by
    rw [CCL.Riemann.LegendreMonodromy.onePeriodMatrix_explicit]
    let one := CCL.ProgressiveCoherence.CoherentNamed.exact
      (show Gaussian from ⟨1, 0⟩)
    let two := CCL.ProgressiveCoherence.CoherentNamed.exact
      (show Gaussian from ⟨2, 0⟩)
    change NamedEquivalent
      (CCL.Riemann.LegendreGaussManin.matrixAction
        (CCL.Riemann.LegendrePicardLefschetz.matrix₂ 1 2 0 1)
        data.base.toFibreData.rawPeriods 0).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.mul one data.base.aPeriod)
        (CCL.ProgressiveCoherence.CoherentNamed.mul two data.base.bPeriod)).name
      at expanded
    have simplifyTerms : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add
          (CCL.ProgressiveCoherence.CoherentNamed.mul one data.base.aPeriod)
          (CCL.ProgressiveCoherence.CoherentNamed.mul two data.base.bPeriod)).name
        (CCL.ProgressiveCoherence.CoherentNamed.add data.base.aPeriod
          (CCL.ProgressiveCoherence.CoherentNamed.mul two data.base.bPeriod)).name :=
      CCL.TranscendentalCoherence.coherentAdd_respects _ _ _ _
        (CCL.OperationalFieldLaws.coherentMul_one_left data.base.aPeriod)
        (CCL.OperationalEquivalence.NamedEquivalent.refl _)
    exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded (by
      simpa only [generatedOneRawNumerator, data, generatedMonodromyData,
        one, two] using simplifyTerms)
  have periodsToNumerator : NamedEquivalent (data.onePeriods 0).name
      (generatedOneRawNumerator token).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans periodsToMatrix
      matrixToNumerator
  exact CCL.OperationalEquivalence.NamedEquivalent.trans scaledToPeriods
    periodsToNumerator

def generatedInfinityDenominator_scaled (token : Unit) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (generatedMonodromyBase token).aPeriod
        (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
          CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
          (generatedMonodromyBase token).ratio)).name
      (generatedInfinityRawNumerator token).name := by
  let data := generatedMonodromyData token
  have homogeneous := data.infinity_homogeneous 0
  have scaledToPeriods : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        data.base.aPeriod
        (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
          CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
          data.base.ratio)).name
      (data.infinityPeriods 0).name := by
    exact CCL.OperationalEquivalence.NamedEquivalent.symm (by
      simpa only [CCL.Riemann.LegendreModularMonodromy.scaleVector,
        CCL.Riemann.LegendreModularMonodromy.fractionalDenominator,
        CCL.Riemann.LegendreModularMonodromy.fractionalRow] using homogeneous)
  have expanded := CCL.Riemann.LegendreModularMonodromy.matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
    data.base.toFibreData.rawPeriods 0
  rw [CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix_explicit] at expanded
  have rawZero : data.base.toFibreData.rawPeriods 0 = data.base.aPeriod := rfl
  have rawOne : data.base.toFibreData.rawPeriods 1 = data.base.bPeriod := by
    unfold CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.toFibreData
      CCL.Riemann.LegendreGaussManin.FibreData.rawPeriods
      CCL.Riemann.LegendreGaussManin.FibreData.rawRefinement
      CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.bPeriod
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rfl
  rw [rawZero, rawOne] at expanded
  have periodsToMatrix : NamedEquivalent (data.infinityPeriods 0).name
      (CCL.Riemann.LegendreGaussManin.matrixAction
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
        data.base.toFibreData.rawPeriods 0).name := by
    unfold CCL.Riemann.LegendrePeriodMonodromy.Data.infinityPeriods
      CCL.Riemann.LegendrePeriodMonodromy.Data.periods
      CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.periods
      CCL.Riemann.LegendrePeriodMonodromy.NormalizedData.continuation
      CCL.Riemann.LegendreGaussManin.EndpointContinuation.periods
    rw [CCL.Riemann.LegendreMonodromy.StandardLoops.infinityPath_periodMatrix]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  have matrixToNumerator : NamedEquivalent
      (CCL.Riemann.LegendreGaussManin.matrixAction
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
        data.base.toFibreData.rawPeriods 0).name
      (generatedInfinityRawNumerator token).name := by
    rw [CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix_explicit]
    change NamedEquivalent
      (CCL.Riemann.LegendreGaussManin.matrixAction
        (CCL.Riemann.LegendrePicardLefschetz.matrix₂ (-3) (-2) 2 1)
        data.base.toFibreData.rawPeriods 0).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.exact
            (show Gaussian from ⟨-3, 0⟩)) data.base.aPeriod)
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.exact
            (show Gaussian from ⟨-2, 0⟩)) data.base.bPeriod)).name
      at expanded
    simpa only [generatedInfinityRawNumerator, data, generatedMonodromyData]
      using expanded
  have periodsToNumerator : NamedEquivalent (data.infinityPeriods 0).name
      (generatedInfinityRawNumerator token).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans periodsToMatrix
      matrixToNumerator
  exact CCL.OperationalEquivalence.NamedEquivalent.trans scaledToPeriods
    periodsToNumerator

/-- The raw prepared quotient cancels against the same apartified geometric
denominator from which it was constructed. -/
def preparedGeometricQuotient_mul_denominator
    (numerator denominator : GeometricApproximation)
    (numeratorApart : CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed numerator).name.process)
    (denominatorApart : CCL.ProgressiveCharts.PossibleApart
      (CCL.Riemann.PeriodMatrix.geometricNamed denominator).name.process) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (preparedGeometricQuotient numerator denominator numeratorApart
          denominatorApart)
        (CCL.ProgressiveCoherence.CoherentNamed.apartify
          (CCL.Riemann.PeriodMatrix.geometricNamed denominator)
          denominatorApart)).name
      (CCL.ProgressiveCoherence.CoherentNamed.apartify
        (CCL.Riemann.PeriodMatrix.geometricNamed numerator)
        numeratorApart).name := by
  unfold preparedGeometricQuotient
  exact CCL.Riemann.OperationalQuotients.coherentDiv_mul_cancel _ _ _

def generatedOneDenominator_equivalent_prepared (token : Unit) :
    NamedEquivalent
      (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
        CCL.Riemann.LegendreMonodromy.onePeriodMatrix
        (generatedMonodromyBase token).ratio).name
      (generatedOnePreparedDenominator token).name := by
  let denominator :=
    CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
      CCL.Riemann.LegendreMonodromy.onePeriodMatrix
      (generatedMonodromyBase token).ratio
  let quotient := generatedOneRawDenominatorQuotient token
  let preparedA := generatedPreparedAPeriod token
  have leftScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul preparedA denominator).name
      (generatedOnePreparedNumerator token).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects
        preparedA (generatedMonodromyBase token).aPeriod
        denominator denominator
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (generatedAPeriod_equivalent_prepared token))
        (CCL.OperationalEquivalence.NamedEquivalent.refl denominator.name))
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (generatedOneDenominator_scaled token)
        (generatedOneRawNumerator_equivalent_prepared token))
  have quotientCancels : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul quotient preparedA).name
      (generatedOnePreparedNumerator token).name := by
    simpa only [quotient, preparedA, generatedOneRawDenominatorQuotient,
      generatedPreparedAPeriod, generatedOnePreparedNumerator] using
      preparedGeometricQuotient_mul_denominator
        (generatedOneDenominatorNumeratorSource token)
        (generatedAPeriodSource token)
        (generatedOneNumeratorPossibleApart token)
        (generatedAPeriodPossibleApart token)
  have rightScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul preparedA quotient).name
      (generatedOnePreparedNumerator token).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_comm preparedA quotient)
      quotientCancels
  have quotientEquivalent : NamedEquivalent denominator.name quotient.name :=
    CCL.Riemann.OperationalQuotients.coherentMul_cancel_left
      preparedA denominator quotient (generatedPreparedAPeriodApart token)
      (CCL.OperationalEquivalence.NamedEquivalent.trans leftScaled
        (CCL.OperationalEquivalence.NamedEquivalent.symm rightScaled))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans quotientEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent quotient
      (generatedOneRawDenominatorQuotientPossibleApart token))

def generatedInfinityDenominator_equivalent_prepared (token : Unit) :
    NamedEquivalent
      (CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
        (generatedMonodromyBase token).ratio).name
      (generatedInfinityPreparedDenominator token).name := by
  let denominator :=
    CCL.Riemann.LegendreModularMonodromy.fractionalDenominator
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
      (generatedMonodromyBase token).ratio
  let quotient := generatedInfinityRawDenominatorQuotient token
  let preparedA := generatedPreparedAPeriod token
  have leftScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul preparedA denominator).name
      (generatedInfinityPreparedNumerator token).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects
        preparedA (generatedMonodromyBase token).aPeriod
        denominator denominator
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (generatedAPeriod_equivalent_prepared token))
        (CCL.OperationalEquivalence.NamedEquivalent.refl denominator.name))
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (generatedInfinityDenominator_scaled token)
        (generatedInfinityRawNumerator_equivalent_prepared token))
  have quotientCancels : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul quotient preparedA).name
      (generatedInfinityPreparedNumerator token).name := by
    simpa only [quotient, preparedA,
      generatedInfinityRawDenominatorQuotient,
      generatedPreparedAPeriod, generatedInfinityPreparedNumerator] using
      preparedGeometricQuotient_mul_denominator
        (generatedInfinityDenominatorNumeratorSource token)
        (generatedAPeriodSource token)
        (generatedInfinityNumeratorPossibleApart token)
        (generatedAPeriodPossibleApart token)
  have rightScaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul preparedA quotient).name
      (generatedInfinityPreparedNumerator token).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_comm preparedA quotient)
      quotientCancels
  have quotientEquivalent : NamedEquivalent denominator.name quotient.name :=
    CCL.Riemann.OperationalQuotients.coherentMul_cancel_left
      preparedA denominator quotient (generatedPreparedAPeriodApart token)
      (CCL.OperationalEquivalence.NamedEquivalent.trans leftScaled
        (CCL.OperationalEquivalence.NamedEquivalent.symm rightScaled))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans quotientEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent quotient
      (generatedInfinityRawDenominatorQuotientPossibleApart token))

/-- Closed, data-derived one-loop denominator preparation. -/
def generatedOnePreparation (token : Unit) :
    CCL.Riemann.LegendrePeriodMonodromy.OnePreparation
      (generatedMonodromyBase token).ratio where
  prepared := generatedOnePreparedDenominator token
  apart := generatedOnePreparedDenominatorApart token
  equivalent := generatedOneDenominator_equivalent_prepared token

/-- Closed, data-derived infinity-loop denominator preparation. -/
def generatedInfinityPreparation (token : Unit) :
    CCL.Riemann.LegendrePeriodMonodromy.InfinityPreparation
      (generatedMonodromyBase token).ratio where
  prepared := generatedInfinityPreparedDenominator token
  apart := generatedInfinityPreparedDenominatorApart token
  equivalent := generatedInfinityDenominator_equivalent_prepared token

/-- Both nonconstant dual denominators are ready, with each preparation
indexed by the exact generated fractional-denominator process it prepares. -/
def generatedStandardReady (token : Unit) :
    CCL.Riemann.LegendrePeriodMonodromy.StandardReady
      (generatedMonodromyBase token).ratio where
  one := generatedOnePreparation token
  infinity := generatedInfinityPreparation token

@[simp] theorem generatedStandardReady_one (token : Unit) :
    (generatedStandardReady token).one = generatedOnePreparation token := rfl

@[simp] theorem generatedStandardReady_infinity (token : Unit) :
    (generatedStandardReady token).infinity =
      generatedInfinityPreparation token := rfl

/-- Fully productive dual standard-loop theorem for the generated period
data.  Both nontrivial denominator certificates are derived above from the
actual generated A/B lower bounds. -/
def generatedProductiveMonodromyCertificate (token : Unit) :
    CCL.Riemann.LegendrePeriodMonodromy.ProductiveCertificate
      (generatedMonodromyData token) (generatedOnePreparation token)
        (generatedInfinityPreparation token) :=
  CCL.Riemann.LegendrePeriodMonodromy.productiveCertificateOfReady
    (generatedMonodromyData token) (generatedStandardReady token)

@[simp] theorem generatedProductiveMonodromyCertificate_fractionFree
    (token : Unit) :
    (generatedProductiveMonodromyCertificate token).fractionFree =
      generatedFractionFreeMonodromyCertificate token := rfl

/-- The generated affine zero transform is the ratio of the two actual
zero-loop transported period coordinates. -/
def generatedZeroProductiveTransport (token : Unit) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).zeroPeriods 0)
        (CCL.Riemann.LegendrePeriodMonodromy.zeroAffineTransform
          (generatedMonodromyBase token).ratio)).name
      ((generatedMonodromyData token).zeroPeriods 1).name :=
  (generatedProductiveMonodromyCertificate token).zeroTransport

/-- The generated prepared one transform is the ratio of the two actual
one-loop transported period coordinates. -/
def generatedOneProductiveTransport (token : Unit) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).onePeriods 0)
        (CCL.Riemann.LegendrePeriodMonodromy.oneTransform
          (generatedOnePreparation token))).name
      ((generatedMonodromyData token).onePeriods 1).name :=
  (generatedProductiveMonodromyCertificate token).oneTransport

/-- The generated prepared infinity transform is the ratio of the two actual
infinity-loop transported period coordinates. -/
def generatedInfinityProductiveTransport (token : Unit) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).infinityPeriods 0)
        (CCL.Riemann.LegendrePeriodMonodromy.infinityTransform
          (generatedInfinityPreparation token))).name
      ((generatedMonodromyData token).infinityPeriods 1).name :=
  (generatedProductiveMonodromyCertificate token).infinityTransport

/-! ## Closed end-to-end package -/

universe uFractionFree uOnePreparation uInfinityPreparation uReady uProductive
  uZeroTransport uOneTransport uInfinityTransport

/-- A small carrier keeps the final generated package inspectable without a
recursor which unfolds its large period-program indices. -/
structure GeneratedEndToEndMonodromyCertificatePayload
    (periodGeometryType basisProvenanceType normalizationType
      topologicalMonodromyType loopContinuationType : Prop)
    (fractionFreeType : Type uFractionFree)
    (onePreparationType : Type uOnePreparation)
    (infinityPreparationType : Type uInfinityPreparation)
    (readyType : Type uReady)
    (productiveType : Type uProductive)
    (zeroTransportType : Type uZeroTransport)
    (oneTransportType : Type uOneTransport)
    (infinityTransportType : Type uInfinityTransport) where
  periodGeometry : periodGeometryType
  basisProvenance : basisProvenanceType
  normalization : normalizationType
  topologicalMonodromy : topologicalMonodromyType
  loopContinuation : loopContinuationType
  fractionFree : fractionFreeType
  onePreparation : onePreparationType
  infinityPreparation : infinityPreparationType
  ready : readyType
  productive : productiveType
  zeroTransport : zeroTransportType
  oneTransport : oneTransportType
  infinityTransport : infinityTransportType

/-- Type of the single closed certificate joining generated row and canonical
symplectic-basis provenance, topological and dual-period monodromy, finite
period normalization, derived denominator preparations, and the three final
transported-coordinate statements. -/
def GeneratedEndToEndMonodromyCertificate (token : Unit) :=
  GeneratedEndToEndMonodromyCertificatePayload
    (GeneratedPeriodGeometryCertificate token)
    (GeneratedSymplecticBasisProvenance token)
    (GeneratedNormalizationCertificate token)
    (CCL.Riemann.LegendreMonodromy.StandardLoops.Certificate
      CCL.Riemann.ExplicitLegendreOneLoop.standardLoops)
    (GeneratedLoopContinuationCertificate token)
    (CCL.Riemann.LegendrePeriodMonodromy.FractionFreeCertificate
      (generatedMonodromyData token))
    (CCL.Riemann.LegendrePeriodMonodromy.OnePreparation
      (generatedMonodromyBase token).ratio)
    (CCL.Riemann.LegendrePeriodMonodromy.InfinityPreparation
      (generatedMonodromyBase token).ratio)
    (CCL.Riemann.LegendrePeriodMonodromy.StandardReady
      (generatedMonodromyBase token).ratio)
    (CCL.Riemann.LegendrePeriodMonodromy.ProductiveCertificate
      (generatedMonodromyData token) (generatedOnePreparation token)
        (generatedInfinityPreparation token))
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).zeroPeriods 0)
        (CCL.Riemann.LegendrePeriodMonodromy.zeroAffineTransform
          (generatedMonodromyBase token).ratio)).name
      ((generatedMonodromyData token).zeroPeriods 1).name)
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).onePeriods 0)
        (CCL.Riemann.LegendrePeriodMonodromy.oneTransform
          (generatedOnePreparation token))).name
      ((generatedMonodromyData token).onePeriods 1).name)
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        ((generatedMonodromyData token).infinityPeriods 0)
        (CCL.Riemann.LegendrePeriodMonodromy.infinityTransform
          (generatedInfinityPreparation token))).name
      ((generatedMonodromyData token).infinityPeriods 1).name)

/-- The headline executable client: every field is constructed from the
displayed rational paths and generated finite certificate data; the only
argument is the evaluation token used to retain large data lazily. -/
def generatedEndToEndMonodromyCertificate (token : Unit) :
    GeneratedEndToEndMonodromyCertificate token where
  periodGeometry := generatedPeriodGeometryCertificate token
  basisProvenance := generatedSymplecticBasisProvenance token
  normalization := generatedNormalizationCertificate token
  topologicalMonodromy := generatedTopologicalMonodromyCertificate
  loopContinuation := generatedLoopContinuationCertificate token
  fractionFree := generatedFractionFreeMonodromyCertificate token
  onePreparation := generatedOnePreparation token
  infinityPreparation := generatedInfinityPreparation token
  ready := generatedStandardReady token
  productive := generatedProductiveMonodromyCertificate token
  zeroTransport := generatedZeroProductiveTransport token
  oneTransport := generatedOneProductiveTransport token
  infinityTransport := generatedInfinityProductiveTransport token

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
