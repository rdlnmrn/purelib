import CCL.Riemann.LegendreGaussManin
import CCL.Riemann.FinitePeriodTheorem

/-!
# Finite normalized modular operations for the Legendre family

In genus one the finite Riemann-period package supplies the normalized
productive name `tau = A⁻¹B`.  This module develops the finite homogeneous
matrix algebra and apartness-certified fractional-linear operations used by
the dual period-monodromy interface.  It does not assert equality between
periods on different fibres.

No completed period, analytic quotient, or global upper-half-plane point is
introduced.
-/

namespace CCL.Riemann.LegendreModularMonodromy

open CCL.Riemann.LegendreGaussManin
open CCL.Riemann.PeriodMatrix
open CCL.Riemann.PeriodMatrix.ScaledInverseCertificate

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev IntegralMatrix := CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev RawPeriodVector := CCL.Riemann.LegendreGaussManin.RawPeriodVector
abbrev VectorEquivalent := CCL.Riemann.LegendreGaussManin.VectorEquivalent
abbrev Apart := CCL.ProgressiveTransducer.Named.Apart
abbrev OneByOneLower :=
  CCL.Riemann.PeriodMatrix.OneByOneEntryCandidateLowerCertificate

private theorem finTwo_cases (coordinate : Fin 2) :
    coordinate = 0 ∨ coordinate = 1 := by
  rcases coordinate with ⟨value, bound⟩
  omega0

/-! ## Small finite operational algebra -/

/-- A one-entry recursive named sum is its sole entry. -/
private def sumNamed_one (values : Fin 1 -> CoherentNamed) :
    NamedEquivalent (CCL.Riemann.PeriodMatrix.sumNamed values).name
      (values 0).name := by
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let geometricZero := CCL.Riemann.PeriodMatrix.geometricNamed
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0)
  have removeTail : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add (values 0)
        geometricZero).name
      (CCL.ProgressiveCoherence.CoherentNamed.add (values 0) zero).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      (values 0) (values 0) geometricZero zero
      (CCL.OperationalEquivalence.NamedEquivalent.refl (values 0).name)
      CCL.Riemann.FiniteBilinear.geometricZero_equivalent_exact
  change NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.add (values 0)
      geometricZero).name (values 0).name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans removeTail
    (CCL.OperationalFieldLaws.coherentAdd_zero_right (values 0))

/-- A two-entry recursive named sum is the actual sum of its entries. -/
private def sumNamed_two (values : Fin 2 -> CoherentNamed) :
    NamedEquivalent (CCL.Riemann.PeriodMatrix.sumNamed values).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (values 0) (values 1)).name := by
  let tail := fun coordinate : Fin 1 => values coordinate.succ
  have tailEquivalent := sumNamed_one tail
  change NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.add (values 0)
      (CCL.Riemann.PeriodMatrix.sumNamed tail)).name
    (CCL.ProgressiveCoherence.CoherentNamed.add (values 0) (values 1)).name
  exact CCL.TranscendentalCoherence.coherentAdd_respects
    (values 0) (values 0)
    (CCL.Riemann.PeriodMatrix.sumNamed tail) (values 1)
    (CCL.OperationalEquivalence.NamedEquivalent.refl (values 0).name)
    tailEquivalent

/-- A one-by-one named matrix product is the actual product of its two
entries. -/
private def matrixMul_one (left right : NamedMatrix 1) :
    NamedEquivalent (matrixMul left right 0 0).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (left 0 0) (right 0 0)).name := by
  rw [matrixMul_apply]
  simpa only using sumNamed_one (fun middle : Fin 1 =>
    CCL.ProgressiveCoherence.CoherentNamed.mul
      (left 0 middle) (right middle 0))

/-! ## Genus-one normalized fibres -/

/-- A normalized finite genus-one fibre tied definitionally to the raw fibre
used by Gauss--Manin transport.  The direct `A`-entry lower certificate is the
finite inverse-separation evidence accepted by the genus-one period theorem. -/
structure NormalizedFibreData {parameter : Gaussian}
    (frame : CCL.Riemann.LegendrePaths.Frame parameter) where
  normalized : NormalizedPeriodData
    (CCL.Riemann.LegendreGaussManin.frameCurve frame)
  aPeriodLower : OneByOneLower normalized.toPeriodData.aMatrix

namespace NormalizedFibreData

def toFibreData {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) : FibreData frame where
  periods := data.normalized.toPeriodData

def aPeriod {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) : CoherentNamed :=
  data.normalized.toPeriodData.aMatrix 0 0

def bPeriod {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) : CoherentNamed :=
  data.normalized.toPeriodData.bMatrix 0 0

def ratio {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) : CoherentNamed :=
  data.normalized.omega 0 0

@[simp] theorem rawPeriods_zero {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) :
    data.toFibreData.rawPeriods 0 = data.aPeriod := rfl

@[simp] theorem rawPeriods_one {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) :
    data.toFibreData.rawPeriods 1 = data.bPeriod := by
  unfold toFibreData FibreData.rawPeriods FibreData.rawRefinement bPeriod
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rfl

/-- The fraction-free defining identity `A * tau = B` uses only the
constructive scaled inverse stored by normalized period data.  No separate
uniform lower bound for the original A-entry sampler is needed. -/
def normalized_a_mul_ratio {curve :
    CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1}
    (normalized : NormalizedPeriodData curve) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (normalized.toPeriodData.aMatrix 0 0)
        (normalized.omega 0 0)).name
      (normalized.toPeriodData.bMatrix 0 0).name := by
  let periods := normalized.toPeriodData
  let inverse := normalized.aInverse
  let a := periods.aMatrix 0 0
  let b := periods.bMatrix 0 0
  let adjugate := inverse.adjugate 0 0
  let scalar := inverse.scalar
  let reciprocal := CCL.Riemann.PeriodMatrix.inverseScalar inverse
  let numerator := matrixMul inverse.adjugate periods.bMatrix 0 0
  have numeratorProduct : NamedEquivalent numerator.name
      (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate b).name := by
    change NamedEquivalent
      (matrixMul inverse.adjugate periods.bMatrix 0 0).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (inverse.adjugate 0 0) (periods.bMatrix 0 0)).name
    exact matrixMul_one inverse.adjugate periods.bMatrix
  have aAdjugate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate).name scalar.name := by
    have direct := matrixMul_one periods.aMatrix inverse.adjugate
    have identity := inverse.right_identity 0 0
    have matrixToScalar : NamedEquivalent
        (matrixMul periods.aMatrix inverse.adjugate 0 0).name scalar.name := by
      rw [scaleIdentity_apply, if_pos rfl] at identity
      exact identity
    exact CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm (by
        change NamedEquivalent
          (matrixMul periods.aMatrix inverse.adjugate 0 0).name
          (CCL.ProgressiveCoherence.CoherentNamed.mul
            (periods.aMatrix 0 0) (inverse.adjugate 0 0)).name at direct
        exact direct)) matrixToScalar
  have exposeNumerator : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul a
        (CCL.ProgressiveCoherence.CoherentNamed.mul numerator reciprocal)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul a
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate b)
          reciprocal)).name :=
    CCL.TranscendentalCoherence.coherentMul_respects a a
      (CCL.ProgressiveCoherence.CoherentNamed.mul numerator reciprocal)
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate b) reciprocal)
      (CCL.OperationalEquivalence.NamedEquivalent.refl a.name)
      (CCL.TranscendentalCoherence.coherentMul_respects numerator
        (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate b)
        reciprocal reciprocal numeratorProduct
        (CCL.OperationalEquivalence.NamedEquivalent.refl reciprocal.name))
  have rearrange : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul a
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate b)
          reciprocal)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate)
        (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal b)).name := by
    let adjugateB := CCL.ProgressiveCoherence.CoherentNamed.mul adjugate b
    let bReciprocal := CCL.ProgressiveCoherence.CoherentNamed.mul b reciprocal
    let reciprocalB := CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal b
    have innerAssociate : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.mul adjugateB reciprocal).name
        (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate
          bReciprocal).name := by
      simpa only [adjugateB, bReciprocal,
        CCL.ProgressiveCoherence.CoherentNamed.mul] using
        CCL.TranscendentalCoherence.coherentMul_assoc adjugate b reciprocal
    have exposeInner : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.mul a
          (CCL.ProgressiveCoherence.CoherentNamed.mul adjugateB
            reciprocal)).name
        (CCL.ProgressiveCoherence.CoherentNamed.mul a
          (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate
            bReciprocal)).name :=
      CCL.TranscendentalCoherence.coherentMul_respects a a
        (CCL.ProgressiveCoherence.CoherentNamed.mul adjugateB reciprocal)
        (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate bReciprocal)
        (CCL.OperationalEquivalence.NamedEquivalent.refl a.name)
        innerAssociate
    have exposeAAdjugate : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.mul a
          (CCL.ProgressiveCoherence.CoherentNamed.mul adjugate
            bReciprocal)).name
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate)
          bReciprocal).name := by
      exact CCL.OperationalEquivalence.NamedEquivalent.symm (by
        simpa only [bReciprocal,
          CCL.ProgressiveCoherence.CoherentNamed.mul] using
          CCL.TranscendentalCoherence.coherentMul_assoc
            a adjugate bReciprocal)
    have swapTail : NamedEquivalent bReciprocal.name reciprocalB.name := by
      simpa only [bReciprocal, reciprocalB,
        CCL.ProgressiveCoherence.CoherentNamed.mul] using
        CCL.TranscendentalCoherence.coherentMul_comm b reciprocal
    have replaceTail : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate)
          bReciprocal).name
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate)
          reciprocalB).name :=
      CCL.TranscendentalCoherence.coherentMul_respects
        (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate)
        (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate)
        bReciprocal reciprocalB
        (CCL.OperationalEquivalence.NamedEquivalent.refl _) swapTail
    exact CCL.OperationalEquivalence.NamedEquivalent.trans exposeInner
      (CCL.OperationalEquivalence.NamedEquivalent.trans exposeAAdjugate
        replaceTail)
  have replaceAdjugate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate)
        (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal b)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
        (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal b)).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      (CCL.ProgressiveCoherence.CoherentNamed.mul a adjugate) scalar
      (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal b)
      (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal b)
      aAdjugate (CCL.OperationalEquivalence.NamedEquivalent.refl _)
  have cancelScalar : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
        (CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal b)).name
      b.name := by
    apply CCL.OperationalEquivalence.NamedEquivalent.trans
    · exact CCL.OperationalEquivalence.NamedEquivalent.symm
        (CCL.TranscendentalCoherence.coherentMul_assoc scalar reciprocal b)
    · let scalarReciprocal :=
        CCL.ProgressiveCoherence.CoherentNamed.mul scalar reciprocal
      have scalarReciprocalOne : NamedEquivalent scalarReciprocal.name
          (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name :=
        CCL.OperationalEquivalence.NamedEquivalent.trans
          (by simpa only [scalarReciprocal,
              CCL.ProgressiveCoherence.CoherentNamed.mul] using
            CCL.TranscendentalCoherence.coherentMul_comm scalar reciprocal)
          (by
            have cancel :=
              CCL.Riemann.OperationalQuotients.reciprocal_mul_cancel
                scalar inverse.scalarApart
            simpa only [reciprocal, scalar,
              CCL.Riemann.PeriodMatrix.inverseScalar,
              CCL.ProgressiveCoherence.CoherentNamed.mul] using cancel)
      change NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalarReciprocal b).name
        b.name
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.TranscendentalCoherence.coherentMul_respects scalarReciprocal
          (CCL.ProgressiveCoherence.CoherentNamed.exact 1) b b
          scalarReciprocalOne
          (CCL.OperationalEquivalence.NamedEquivalent.refl b.name))
        (CCL.OperationalFieldLaws.coherentMul_one_left b)
  change NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.mul a
      (CCL.ProgressiveCoherence.CoherentNamed.mul numerator reciprocal)).name
    b.name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans exposeNumerator
    (CCL.OperationalEquivalence.NamedEquivalent.trans rearrange
      (CCL.OperationalEquivalence.NamedEquivalent.trans replaceAdjugate
        cancelScalar))

/-- Fibre-indexed form of the normalized period identity. -/
def a_mul_ratio {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul data.aPeriod data.ratio).name
      data.bPeriod.name :=
  normalized_a_mul_ratio data.normalized

/-! The direct finite lower certificate prepares a cancellable synchronized
view of the raw `A` period. -/

def sampledAPeriod {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    (CCL.ProgressiveSampling.approximation data.aPeriod.name)

def sampledAPossibleApart {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) :
    CCL.ProgressiveCharts.PossibleApart data.sampledAPeriod.name.process where
  lowerSq := data.aPeriodLower.lowerSq
  positive := data.aPeriodLower.positive
  lower := by
    intro state value possible
    change (CCL.ProgressiveSampling.approximation data.aPeriod.name).Possible
      state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    exact data.aPeriodLower.sample_lower later

def preparedAPeriod {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify data.sampledAPeriod
    data.sampledAPossibleApart

def preparedAPeriodApart {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) : Apart data.preparedAPeriod.name where
  certificate := CCL.ProgressiveCharts.apartifyApart data.sampledAPossibleApart

def aPeriod_equivalent_prepared {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) :
    NamedEquivalent data.aPeriod.name data.preparedAPeriod.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.named_toSamplingNamed data.aPeriod.name)
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
      data.sampledAPeriod data.sampledAPossibleApart)

/-- The normalized fibre extracted directly from a finite Riemann-period
result, retaining the direct genus-one `A`-entry separation used to construct
that result. -/
def ofFinitePeriodResult {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (result : CCL.Riemann.FinitePeriodTheorem.Result
      (CCL.Riemann.LegendreGaussManin.frameCurve frame))
    (aPeriodLower : OneByOneLower result.periodData.aMatrix) :
    NormalizedFibreData frame where
  normalized := result.analytic.normalized
  aPeriodLower := aPeriodLower

end NormalizedFibreData

/-! ## Matrix action on a normalized column -/

def scaleVector (scalar : CoherentNamed) (values : RawPeriodVector) :
    RawPeriodVector := fun coordinate =>
  CCL.ProgressiveCoherence.CoherentNamed.mul scalar (values coordinate)

/-- A finite recursive named sum commutes with multiplication by one coherent
scalar. -/
private def sumNamed_scale_left : {count : Nat} ->
    (scalar : CoherentNamed) -> (values : Fin count -> CoherentNamed) ->
      NamedEquivalent
        (CCL.Riemann.PeriodMatrix.sumNamed fun coordinate =>
          CCL.ProgressiveCoherence.CoherentNamed.mul scalar
            (values coordinate)).name
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
          (CCL.Riemann.PeriodMatrix.sumNamed values)).name
  | 0, scalar, values => by
      let geometricZero := CCL.Riemann.PeriodMatrix.geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0)
      let exactZero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
      have rightZero : NamedEquivalent
          (CCL.ProgressiveCoherence.CoherentNamed.mul scalar geometricZero).name
          exactZero.name :=
        CCL.OperationalEquivalence.NamedEquivalent.trans
          (CCL.TranscendentalCoherence.coherentMul_respects scalar scalar
            geometricZero exactZero
            (CCL.OperationalEquivalence.NamedEquivalent.refl scalar.name)
            CCL.Riemann.FiniteBilinear.geometricZero_equivalent_exact)
          (CCL.OperationalFieldLaws.coherentMul_zero_right scalar)
      change NamedEquivalent geometricZero.name
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar geometricZero).name
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        CCL.Riemann.FiniteBilinear.geometricZero_equivalent_exact
        (CCL.OperationalEquivalence.NamedEquivalent.symm rightZero)
  | count + 1, scalar, values => by
      let tail := fun coordinate : Fin count => values coordinate.succ
      let tailSum := CCL.Riemann.PeriodMatrix.sumNamed tail
      let scaledTail := fun coordinate : Fin count =>
        CCL.ProgressiveCoherence.CoherentNamed.mul scalar (tail coordinate)
      have tailEquivalent := sumNamed_scale_left scalar tail
      have replaceTail : NamedEquivalent
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (CCL.ProgressiveCoherence.CoherentNamed.mul scalar (values 0))
            (CCL.Riemann.PeriodMatrix.sumNamed scaledTail)).name
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (CCL.ProgressiveCoherence.CoherentNamed.mul scalar (values 0))
            (CCL.ProgressiveCoherence.CoherentNamed.mul scalar tailSum)).name :=
        CCL.TranscendentalCoherence.coherentAdd_respects
          (CCL.ProgressiveCoherence.CoherentNamed.mul scalar (values 0))
          (CCL.ProgressiveCoherence.CoherentNamed.mul scalar (values 0))
          (CCL.Riemann.PeriodMatrix.sumNamed scaledTail)
          (CCL.ProgressiveCoherence.CoherentNamed.mul scalar tailSum)
          (CCL.OperationalEquivalence.NamedEquivalent.refl _) tailEquivalent
      change NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add
          (CCL.ProgressiveCoherence.CoherentNamed.mul scalar (values 0))
          (CCL.Riemann.PeriodMatrix.sumNamed scaledTail)).name
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (values 0) tailSum)).name
      exact CCL.OperationalEquivalence.NamedEquivalent.trans replaceTail
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (CCL.OperationalFieldLaws.coherentMul_add_left
            scalar (values 0) tailSum))

/-- Move a common left scalar through one matrix-action summand. -/
private def coefficient_mul_scaled
    (coefficient scalar value : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul coefficient
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar value)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
        (CCL.ProgressiveCoherence.CoherentNamed.mul coefficient value)).name := by
  let coefficientScalar :=
    CCL.ProgressiveCoherence.CoherentNamed.mul coefficient scalar
  let scalarCoefficient :=
    CCL.ProgressiveCoherence.CoherentNamed.mul scalar coefficient
  apply CCL.OperationalEquivalence.NamedEquivalent.trans
  · exact CCL.OperationalEquivalence.NamedEquivalent.symm (by
      simpa only [coefficientScalar,
        CCL.ProgressiveCoherence.CoherentNamed.mul] using
        CCL.TranscendentalCoherence.coherentMul_assoc
          coefficient scalar value)
  · apply CCL.OperationalEquivalence.NamedEquivalent.trans
    · exact CCL.TranscendentalCoherence.coherentMul_respects
        coefficientScalar scalarCoefficient value value
        (by simpa only [coefficientScalar, scalarCoefficient,
            CCL.ProgressiveCoherence.CoherentNamed.mul] using
          CCL.TranscendentalCoherence.coherentMul_comm coefficient scalar)
        (CCL.OperationalEquivalence.NamedEquivalent.refl value.name)
    · exact (by
        simpa only [scalarCoefficient,
          CCL.ProgressiveCoherence.CoherentNamed.mul] using
          CCL.TranscendentalCoherence.coherentMul_assoc
            scalar coefficient value)

/-- Integral matrix action commutes operationally with a common coherent
scalar on the input vector. -/
def matrixAction_scale (matrix : IntegralMatrix) (scalar : CoherentNamed)
    (values : RawPeriodVector) :
    VectorEquivalent (matrixAction matrix (scaleVector scalar values))
      (scaleVector scalar (matrixAction matrix values)) := by
  intro row
  let terms := fun column : Fin 2 =>
    CCL.ProgressiveCoherence.CoherentNamed.mul
      (integralNamedMatrix matrix row column) (values column)
  have moveScalar : NamedEquivalent
      (CCL.Riemann.PeriodMatrix.sumNamed fun column : Fin 2 =>
        CCL.ProgressiveCoherence.CoherentNamed.mul
          (integralNamedMatrix matrix row column)
          (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
            (values column))).name
      (CCL.Riemann.PeriodMatrix.sumNamed fun column : Fin 2 =>
        CCL.ProgressiveCoherence.CoherentNamed.mul scalar
          (terms column)).name :=
    CCL.Riemann.PeriodMatrix.sumNamed_respects _ _ fun column =>
      coefficient_mul_scaled (integralNamedMatrix matrix row column)
        scalar (values column)
  change NamedEquivalent
    (matrixAction matrix (scaleVector scalar values) row).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
      (matrixAction matrix values row)).name
  rw [matrixAction, CCL.Riemann.PeriodMatrix.matrixMul_apply]
  change NamedEquivalent
    (CCL.Riemann.PeriodMatrix.sumNamed fun column : Fin 2 =>
      CCL.ProgressiveCoherence.CoherentNamed.mul
        (integralNamedMatrix matrix row column)
        (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
          (values column))).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul scalar
      (matrixAction matrix values row)).name
  rw [matrixAction, CCL.Riemann.PeriodMatrix.matrixMul_apply]
  exact CCL.OperationalEquivalence.NamedEquivalent.trans moveScalar
    (sumNamed_scale_left scalar terms)

/-- The homogeneous column `(1,tau)` associated with a normalized
genus-one period ratio. -/
def fractionalVector (tau : CoherentNamed) : RawPeriodVector :=
  fun coordinate => if coordinate = 0 then
    CCL.ProgressiveCoherence.CoherentNamed.exact 1
  else tau

/-- The raw genus-one period column is the source `A` period times its
homogeneous normalized column `(1,tau)`.  This statement belongs to one fibre
and therefore does not assume any open-path endpoint equality. -/
def NormalizedFibreData.raw_normalized {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedFibreData frame) :
    VectorEquivalent data.toFibreData.rawPeriods
      (scaleVector data.aPeriod (fractionalVector data.ratio)) := by
  intro coordinate
  refine Fin.cases ?_ (fun tail => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) tail) coordinate
  · exact CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentMul_one_right data.aPeriod)
  · exact CCL.OperationalEquivalence.NamedEquivalent.symm data.a_mul_ratio

@[simp] theorem fractionalVector_zero (tau : CoherentNamed) :
    fractionalVector tau 0 =
      CCL.ProgressiveCoherence.CoherentNamed.exact 1 := rfl

@[simp] theorem fractionalVector_one (tau : CoherentNamed) :
    fractionalVector tau 1 = tau := by
  unfold fractionalVector
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- One row of an integral matrix acting on `(1,tau)`. -/
def fractionalRow (matrix : IntegralMatrix) (tau : CoherentNamed)
    (row : Fin 2) : CoherentNamed :=
  matrixAction matrix (fractionalVector tau) row

def fractionalDenominator (matrix : IntegralMatrix) (tau : CoherentNamed) :
    CoherentNamed := fractionalRow matrix tau 0

def fractionalNumerator (matrix : IntegralMatrix) (tau : CoherentNamed) :
    CoherentNamed := fractionalRow matrix tau 1

/-- Expand one row of the finite two-by-two integral action into its two
ordinary coherent products.  This is the shared exact calculation behind the
standard affine row formulas and later composition checks. -/
def matrixAction_row_two (matrix : IntegralMatrix) (values : RawPeriodVector)
    (row : Fin 2) :
    NamedEquivalent (matrixAction matrix values row).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.exact
            (integralGaussian (matrix row 0))) (values 0))
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.exact
            (integralGaussian (matrix row 1))) (values 1))).name := by
  let terms := fun column : Fin 2 =>
    CCL.ProgressiveCoherence.CoherentNamed.mul
      (integralNamedMatrix matrix row column) (values column)
  have exposeSum : NamedEquivalent
      (CCL.Riemann.PeriodMatrix.sumNamed terms).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (terms 0) (terms 1)).name := sumNamed_two terms
  have coefficientEquivalent : forall column : Fin 2,
      NamedEquivalent (integralNamedMatrix matrix row column).name
        (CCL.ProgressiveCoherence.CoherentNamed.exact
          (integralGaussian (matrix row column))).name := by
    intro column
    rw [integralNamedMatrix_apply]
    exact CCL.Riemann.FiniteBilinear.geometricExact_equivalent_exact _
  have replaceTerms : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (terms 0) (terms 1)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.exact
            (integralGaussian (matrix row 0))) (values 0))
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          (CCL.ProgressiveCoherence.CoherentNamed.exact
            (integralGaussian (matrix row 1))) (values 1))).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      (terms 0)
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.exact
          (integralGaussian (matrix row 0))) (values 0))
      (terms 1)
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.exact
          (integralGaussian (matrix row 1))) (values 1))
      (CCL.TranscendentalCoherence.coherentMul_respects
        (integralNamedMatrix matrix row 0)
        (CCL.ProgressiveCoherence.CoherentNamed.exact
          (integralGaussian (matrix row 0)))
        (values 0) (values 0) (coefficientEquivalent 0)
        (CCL.OperationalEquivalence.NamedEquivalent.refl (values 0).name))
      (CCL.TranscendentalCoherence.coherentMul_respects
        (integralNamedMatrix matrix row 1)
        (CCL.ProgressiveCoherence.CoherentNamed.exact
          (integralGaussian (matrix row 1)))
        (values 1) (values 1) (coefficientEquivalent 1)
        (CCL.OperationalEquivalence.NamedEquivalent.refl (values 1).name))
  rw [matrixAction, CCL.Riemann.PeriodMatrix.matrixMul_apply]
  change NamedEquivalent
    (CCL.Riemann.PeriodMatrix.sumNamed terms).name _
  exact CCL.OperationalEquivalence.NamedEquivalent.trans exposeSum replaceTerms

/-- For the standard loop around one, row zero is exactly the constant unit:
the transformed `A` coordinate has no `tau` contribution. -/
def one_denominator_one (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator CCL.Riemann.LegendreMonodromy.oneMatrix tau).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.oneMatrix (fractionalVector tau) 0
  change NamedEquivalent
    (fractionalDenominator CCL.Riemann.LegendreMonodromy.oneMatrix tau).name
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul one one)
      (CCL.ProgressiveCoherence.CoherentNamed.mul zero tau)).name at expanded
  have simplifyTerms : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.mul one one)
        (CCL.ProgressiveCoherence.CoherentNamed.mul zero tau)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add one zero).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      (CCL.ProgressiveCoherence.CoherentNamed.mul one one) one
      (CCL.ProgressiveCoherence.CoherentNamed.mul zero tau) zero
      (CCL.OperationalFieldLaws.coherentMul_one_right one)
      (CCL.OperationalFieldLaws.coherentMul_zero_left tau)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (CCL.OperationalEquivalence.NamedEquivalent.trans simplifyTerms
      (CCL.OperationalFieldLaws.coherentAdd_zero_right one))

/-- For the standard loop around one, row one is the direct affine expression
`2 + tau`; no reciprocal is involved. -/
def one_numerator_two_add (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator CCL.Riemann.LegendreMonodromy.oneMatrix tau).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.exact 2) tau).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let two := CCL.ProgressiveCoherence.CoherentNamed.exact 2
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.oneMatrix (fractionalVector tau) 1
  change NamedEquivalent
    (fractionalNumerator CCL.Riemann.LegendreMonodromy.oneMatrix tau).name
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul two one)
      (CCL.ProgressiveCoherence.CoherentNamed.mul one tau)).name at expanded
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (CCL.TranscendentalCoherence.coherentAdd_respects
      (CCL.ProgressiveCoherence.CoherentNamed.mul two one) two
      (CCL.ProgressiveCoherence.CoherentNamed.mul one tau) tau
      (CCL.OperationalFieldLaws.coherentMul_one_right two)
      (CCL.OperationalFieldLaws.coherentMul_one_left tau))

/-- Canonical productive affine action of the standard loop around one. -/
def oneAffineTransform (tau : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.exact 2) tau

/-! ## Apartness-certified fractional-linear output -/

/-- Exact typed preparation needed before dividing by the transformed
`A`-coordinate.  The prepared denominator may be a certified based refinement
of the original process; operational equivalence records that provenance
without requiring whole-process apartness at the original state. -/
structure DenominatorPreparation (denominator : CoherentNamed) where
  prepared : CoherentNamed
  apart : Apart prepared.name
  equivalent : NamedEquivalent denominator.name prepared.name

namespace DenominatorPreparation

/-- The former whole-process preparation is the special case obtained by
apartifying the original denominator directly. -/
def ofPossibleApart (denominator : CoherentNamed)
    (possibleApart : CCL.ProgressiveCharts.PossibleApart
      denominator.name.process) : DenominatorPreparation denominator where
  prepared := CCL.ProgressiveCoherence.CoherentNamed.apartify
    denominator possibleApart
  apart := { certificate := CCL.ProgressiveCharts.apartifyApart possibleApart }
  equivalent :=
    CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent denominator
      possibleApart

end DenominatorPreparation

/-- Productive fractional-linear action, formed only after the exact
denominator has been constructively apartified. -/
def fractionalLinear (matrix : IntegralMatrix) (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator matrix tau)) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul
    (fractionalNumerator matrix tau)
    (CCL.ProgressiveCoherence.CoherentNamed.div
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1)
      preparation.prepared preparation.apart)

/-- Multiplying the fractional-linear output by its prepared denominator
recovers the exact numerator operationally. -/
def prepared_denominator_mul_fractionalLinear
    (matrix : IntegralMatrix) (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        preparation.prepared
        (fractionalLinear matrix tau preparation)).name
      (fractionalNumerator matrix tau).name := by
  let denominator := preparation.prepared
  let numerator := fractionalNumerator matrix tau
  let reciprocal := CCL.ProgressiveCoherence.CoherentNamed.div
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1) denominator
      preparation.apart
  let reciprocalDenominator :=
    CCL.ProgressiveCoherence.CoherentNamed.mul reciprocal denominator
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  have rearrange : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul denominator
        (CCL.ProgressiveCoherence.CoherentNamed.mul numerator reciprocal)).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul numerator
        reciprocalDenominator).name := by
    let numeratorReciprocal :=
      CCL.ProgressiveCoherence.CoherentNamed.mul numerator reciprocal
    apply CCL.OperationalEquivalence.NamedEquivalent.trans
    · simpa only [numeratorReciprocal,
        CCL.ProgressiveCoherence.CoherentNamed.mul] using
        CCL.TranscendentalCoherence.coherentMul_comm
          denominator numeratorReciprocal
    · simpa only [numeratorReciprocal, reciprocalDenominator,
        CCL.ProgressiveCoherence.CoherentNamed.mul] using
        CCL.TranscendentalCoherence.coherentMul_assoc
          numerator reciprocal denominator
  have cancel : NamedEquivalent reciprocalDenominator.name
      one.name := by
    simpa only [reciprocalDenominator, reciprocal, one,
      CCL.ProgressiveCoherence.CoherentNamed.mul] using
      CCL.Riemann.OperationalQuotients.reciprocal_mul_cancel denominator
        preparation.apart
  change NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.mul denominator
      (CCL.ProgressiveCoherence.CoherentNamed.mul numerator reciprocal)).name
    numerator.name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans rearrange
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects numerator numerator
        reciprocalDenominator one
        (CCL.OperationalEquivalence.NamedEquivalent.refl numerator.name) cancel)
      (CCL.OperationalFieldLaws.coherentMul_one_right numerator))

/-- Multiplying by the original, unprepared denominator also recovers the
fractional numerator operationally. -/
def denominator_mul_fractionalLinear
    (matrix : IntegralMatrix) (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (fractionalDenominator matrix tau)
        (fractionalLinear matrix tau preparation)).name
      (fractionalNumerator matrix tau).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.coherentMul_respects
      (fractionalDenominator matrix tau) preparation.prepared
      (fractionalLinear matrix tau preparation)
      (fractionalLinear matrix tau preparation) preparation.equivalent
      (CCL.OperationalEquivalence.NamedEquivalent.refl _))
    (prepared_denominator_mul_fractionalLinear matrix tau preparation)

/-! ## Standard productive transformations -/

def standardZeroDenominator (tau : CoherentNamed) : CoherentNamed :=
  fractionalDenominator CCL.Riemann.LegendreMonodromy.zeroMatrix
    tau

/-- The one-loop transformed `A` coordinate. -/
def standardOneDenominator (tau : CoherentNamed) : CoherentNamed :=
  fractionalDenominator CCL.Riemann.LegendreMonodromy.oneMatrix
    tau

/-- The infinity-loop transformed `A` coordinate. -/
def standardInfinityDenominator (tau : CoherentNamed) : CoherentNamed :=
  fractionalDenominator CCL.Riemann.LegendreMonodromy.infinityMatrix
    tau

/-- Type boundary for retryable zero-loop denominator evidence. -/
def StandardZeroPreparation (tau : CoherentNamed) : Type 1 :=
  DenominatorPreparation (standardZeroDenominator tau)

/-- Type boundary for retryable one-loop denominator evidence. -/
def StandardOnePreparation (tau : CoherentNamed) : Type 1 :=
  DenominatorPreparation (standardOneDenominator tau)

/-- Type boundary for retryable infinity-loop denominator evidence. -/
def StandardInfinityPreparation (tau : CoherentNamed) : Type 1 :=
  DenominatorPreparation (standardInfinityDenominator tau)

/-- Productive zero-loop transform `tau / (1 - 2*tau)`. -/
def zeroTransform {tau : CoherentNamed}
    (preparation : StandardZeroPreparation tau) : CoherentNamed := by
  change DenominatorPreparation
    (fractionalDenominator CCL.Riemann.LegendreMonodromy.zeroMatrix tau)
      at preparation
  exact fractionalLinear CCL.Riemann.LegendreMonodromy.zeroMatrix
    tau preparation

/-- Productive one-loop transform `2 + tau`. -/
def oneTransform {tau : CoherentNamed}
    (preparation : StandardOnePreparation tau) : CoherentNamed := by
  change DenominatorPreparation
    (fractionalDenominator CCL.Riemann.LegendreMonodromy.oneMatrix tau)
      at preparation
  exact fractionalLinear CCL.Riemann.LegendreMonodromy.oneMatrix
    tau preparation

/-- The legacy division-shaped one-loop transform is operationally the direct
affine transform.  This compatibility theorem isolates callers which already
carry the now-redundant preparation. -/
def oneTransform_equivalent_affine {tau : CoherentNamed}
    (preparation : StandardOnePreparation tau) :
    NamedEquivalent (oneTransform preparation).name
      (oneAffineTransform tau).name := by
  change DenominatorPreparation
    (fractionalDenominator CCL.Riemann.LegendreMonodromy.oneMatrix tau)
      at preparation
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let transformed := fractionalLinear
    CCL.Riemann.LegendreMonodromy.oneMatrix tau preparation
  let numerator := fractionalNumerator
    CCL.Riemann.LegendreMonodromy.oneMatrix tau
  have onePrepared : NamedEquivalent one.name preparation.prepared.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (one_denominator_one tau)) preparation.equivalent
  have scaled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul one transformed).name
      numerator.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects
        one preparation.prepared transformed transformed onePrepared
        (CCL.OperationalEquivalence.NamedEquivalent.refl transformed.name))
      (by simpa only [transformed, numerator,
          CCL.ProgressiveCoherence.CoherentNamed.mul] using
        (prepared_denominator_mul_fractionalLinear
          CCL.Riemann.LegendreMonodromy.oneMatrix tau preparation))
  change NamedEquivalent transformed.name (oneAffineTransform tau).name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentMul_one_left transformed))
    (CCL.OperationalEquivalence.NamedEquivalent.trans scaled
      (by simpa only [numerator, oneAffineTransform] using
        one_numerator_two_add tau))

/-- Productive infinity-loop transform `(-2 + tau) / (-3 + 2*tau)`. -/
def infinityTransform {tau : CoherentNamed}
    (preparation : StandardInfinityPreparation tau) : CoherentNamed := by
  change DenominatorPreparation
    (fractionalDenominator CCL.Riemann.LegendreMonodromy.infinityMatrix tau)
      at preparation
  exact fractionalLinear CCL.Riemann.LegendreMonodromy.infinityMatrix
    tau preparation

/-- The infinity loop is matrix-inverse to the zero-then-one loop in both
multiplication orders.  Its normalized formula above is therefore the
inverse modular transformation supplied by certified path reversal. -/
theorem infinity_inverse_combined :
    RFAP.ConstructiveFiniteMatrix.mul
        CCL.Riemann.LegendreMonodromy.infinityMatrix
        (RFAP.ConstructiveFiniteMatrix.mul
          CCL.Riemann.LegendreMonodromy.oneMatrix
          CCL.Riemann.LegendreMonodromy.zeroMatrix) =
      RFAP.ConstructiveFiniteMatrix.identity ∧
    RFAP.ConstructiveFiniteMatrix.mul
        (RFAP.ConstructiveFiniteMatrix.mul
          CCL.Riemann.LegendreMonodromy.oneMatrix
          CCL.Riemann.LegendreMonodromy.zeroMatrix)
        CCL.Riemann.LegendreMonodromy.infinityMatrix =
      RFAP.ConstructiveFiniteMatrix.identity :=
  ⟨CCL.Riemann.LegendreMonodromy.explicit_loop_product_left,
    CCL.Riemann.LegendreMonodromy.explicit_loop_product_right⟩

/-- The corresponding path matrices are inverse because the infinity path
is definitionally the certified reversal of the combined path. -/
theorem reversal_path_matrices {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame) :
    RFAP.ConstructiveFiniteMatrix.mul
        (CCL.Riemann.LegendrePicardLefschetz.wordMatrix
          loops.infinityPath.word)
        (CCL.Riemann.LegendrePicardLefschetz.wordMatrix
          loops.combinedPath.word) = RFAP.ConstructiveFiniteMatrix.identity ∧
    RFAP.ConstructiveFiniteMatrix.mul
        (CCL.Riemann.LegendrePicardLefschetz.wordMatrix
          loops.combinedPath.word)
        (CCL.Riemann.LegendrePicardLefschetz.wordMatrix
          loops.infinityPath.word) = RFAP.ConstructiveFiniteMatrix.identity :=
  CCL.Riemann.LegendreMonodromy.StandardLoops.reversePath_matrix_identities
    loops.combinedPath

end CCL.Riemann.LegendreModularMonodromy
