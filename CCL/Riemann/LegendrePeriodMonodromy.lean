import CCL.Riemann.LegendreDenominatorAcquisition

/-!
# Dual finite period monodromy for the Legendre family

`wordMatrix` acts on homology-coordinate columns.  Periods evaluated on the
transported basis therefore carry `periodMatrix = transpose wordMatrix`.
This module gives that dual action its own normalized public interface.  It
does not identify periods on distinct endpoint curves.

The unconditional layer retains homogeneous period columns.  Productive
division is added only for the two standard dual actions whose first row is
not the constant unit.
-/

namespace CCL.Riemann.LegendrePeriodMonodromy

open CCL.Riemann.LegendreGaussManin
open CCL.Riemann.LegendreModularMonodromy
open CCL.Riemann.LegendreFractionalAction
open CCL.Riemann.LegendreFractionalWords

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev RawPeriodVector := CCL.Riemann.LegendreGaussManin.RawPeriodVector
abbrev VectorEquivalent := CCL.Riemann.LegendreGaussManin.VectorEquivalent
abbrev DenominatorPreparation :=
  CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation

/-! ## One normalized fibre and its transported period columns -/

/-- Normalized period data needed by dual closed-loop transport.  Unlike the
legacy cancellation interface, this structure does not demand a uniform
lower bound for every coarse A-period sampler.  A tail-separated scaled
inverse already contains exactly the apartness needed to define `tau`. -/
structure NormalizedData {parameter : Gaussian}
    (frame : CCL.Riemann.LegendrePaths.Frame parameter) where
  normalized : CCL.Riemann.PeriodMatrix.NormalizedPeriodData
    (CCL.Riemann.LegendreGaussManin.frameCurve frame)

namespace NormalizedData

def toFibreData {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame) :
    CCL.Riemann.LegendreGaussManin.FibreData frame where
  periods := data.normalized.toPeriodData

def aPeriod {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame) : CoherentNamed :=
  data.normalized.toPeriodData.aMatrix 0 0

def bPeriod {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame) : CoherentNamed :=
  data.normalized.toPeriodData.bMatrix 0 0

def ratio {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame) : CoherentNamed :=
  data.normalized.omega 0 0

/-- The normalized raw column identity requires only the scaled inverse
already stored by `NormalizedPeriodData`. -/
def raw_normalized {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame) :
    VectorEquivalent data.toFibreData.rawPeriods
      (scaleVector data.aPeriod (fractionalVector data.ratio)) := by
  intro coordinate
  refine Fin.cases ?_ (fun tail => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) tail) coordinate
  · exact CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentMul_one_right data.aPeriod)
  · exact CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.Riemann.LegendreModularMonodromy.NormalizedFibreData.normalized_a_mul_ratio
        data.normalized)

/-- The finite endpoint-continuation object for any certified closed path on
this normalized fibre. -/
def continuation {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame)
    (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    EndpointContinuation path where
  source := data.toFibreData
  target := data.toFibreData

/-- Actual periods on the base fibre evaluated on the homology basis
transported around an arbitrary certified finite loop. -/
def periods {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame)
    (path : CCL.Riemann.LegendrePaths.Path frame frame) : RawPeriodVector :=
  (data.continuation path).periods

/-- The arbitrary-loop period column is the original `A` scale times the
exact dual matrix acting on `(1,tau)`. -/
def periods_normalized {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame)
    (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.aPeriod
        (matrixAction
          (CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word)
          (fractionalVector data.ratio))) :=
  VectorEquivalent.trans
    (matrixAction_respects _ data.raw_normalized)
    (matrixAction_scale _ data.aPeriod (fractionalVector data.ratio))

/-- Every legacy normalized fibre forgets to the smaller dual-transport
interface without changing its period programs or ratio. -/
def ofLegacy {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : CCL.Riemann.LegendreModularMonodromy.NormalizedFibreData frame) :
    NormalizedData frame where
  normalized := data.normalized

end NormalizedData

/-- The normalized base fibre used by all standard closed-loop transports. -/
structure Data {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame) where
  base : NormalizedData frame

namespace Data

/-- The generic finite endpoint-continuation object for a closed path on the
normalized base fibre. -/
def continuation {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    EndpointContinuation path :=
  data.base.continuation path

/-- Actual base-fibre periods evaluated on the basis transported around a
certified closed path. -/
def periods {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    RawPeriodVector :=
  data.base.periods path

/-- Transporting a normalized raw column is homogeneous matrix action on
`(1,tau)`, with the original `A` period retained as common scale. -/
def periods_normalized {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.base.aPeriod
        (matrixAction
          (CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word)
          (fractionalVector data.base.ratio))) :=
  data.base.periods_normalized path

def zeroPeriods {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.zeroPath

def onePeriods {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.onePath

def infinityPeriods {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.infinityPath

def productPeriods {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) : RawPeriodVector := data.periods loops.productPath

def zero_homogeneous {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.zeroPeriods
      (scaleVector data.base.aPeriod
        (matrixAction CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
          (fractionalVector data.base.ratio))) := by
  simpa only [zeroPeriods] using data.periods_normalized loops.zeroPath
    |>.trans (fun coordinate => by
      rw [loops.zeroPath_periodMatrix]
      exact CCL.OperationalEquivalence.NamedEquivalent.refl _)

def one_homogeneous {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.onePeriods
      (scaleVector data.base.aPeriod
        (matrixAction CCL.Riemann.LegendreMonodromy.onePeriodMatrix
          (fractionalVector data.base.ratio))) := by
  simpa only [onePeriods] using data.periods_normalized loops.onePath
    |>.trans (fun coordinate => by
      rw [loops.onePath_periodMatrix]
      exact CCL.OperationalEquivalence.NamedEquivalent.refl _)

def infinity_homogeneous {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.infinityPeriods
      (scaleVector data.base.aPeriod
        (matrixAction CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
          (fractionalVector data.base.ratio))) := by
  simpa only [infinityPeriods] using data.periods_normalized loops.infinityPath
    |>.trans (fun coordinate => by
      rw [loops.infinityPath_periodMatrix]
      exact CCL.OperationalEquivalence.NamedEquivalent.refl _)

def product_identity {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.productPeriods data.base.toFibreData.rawPeriods := by
  unfold productPeriods Data.periods NormalizedData.periods
    NormalizedData.continuation EndpointContinuation.periods
  rw [loops.productPath_periodMatrix]
  exact matrixAction_identity data.base.toFibreData.rawPeriods

end Data

/-! ## Exact standard dual rows -/

def zeroAffineTransform (tau : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.exact (-2)) tau

def oneDenominator (tau : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1)
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact 2) tau)

def infinityDenominator (tau : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.exact (-3))
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact (-2)) tau)

def infinityNumerator (tau : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.exact 2) tau

/-- Around zero the transformed `A` coordinate is exactly the original `A`:
the dual denominator is the constant unit. -/
def zero_denominator_one (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator
        CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix tau).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
    (fractionalVector tau) 0
  rw [CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalDenominator
      CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix tau).name
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
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      simplifyTerms
      (CCL.OperationalFieldLaws.coherentAdd_zero_right one))

def zero_numerator_affine (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator
        CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix tau).name
      (zeroAffineTransform tau).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let minusTwo := CCL.ProgressiveCoherence.CoherentNamed.exact (-2)
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
    (fractionalVector tau) 1
  rw [CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalNumerator
      CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix tau).name
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul minusTwo one)
      (CCL.ProgressiveCoherence.CoherentNamed.mul one tau)).name at expanded
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (by
      simpa only [zeroAffineTransform,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.TranscendentalCoherence.coherentAdd_respects _ _ _ _
          (CCL.OperationalFieldLaws.coherentMul_one_right minusTwo)
          (CCL.OperationalFieldLaws.coherentMul_one_left tau))

def one_denominator_explicit (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator
        CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau).name
      (oneDenominator tau).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let two := CCL.ProgressiveCoherence.CoherentNamed.exact 2
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.onePeriodMatrix
    (fractionalVector tau) 0
  rw [CCL.Riemann.LegendreMonodromy.onePeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalDenominator
      CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau).name
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul one one)
      (CCL.ProgressiveCoherence.CoherentNamed.mul two tau)).name at expanded
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (by
      simpa only [oneDenominator,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.TranscendentalCoherence.coherentAdd_respects _ _ _ _
          (CCL.OperationalFieldLaws.coherentMul_one_right one)
          (CCL.OperationalEquivalence.NamedEquivalent.refl _))

def one_numerator_tau (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator
        CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau).name tau.name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.onePeriodMatrix
    (fractionalVector tau) 1
  rw [CCL.Riemann.LegendreMonodromy.onePeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalNumerator
      CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau).name
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul zero one)
      (CCL.ProgressiveCoherence.CoherentNamed.mul one tau)).name at expanded
  have simplifyTerms : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.mul zero one)
        (CCL.ProgressiveCoherence.CoherentNamed.mul one tau)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add zero tau).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      (CCL.ProgressiveCoherence.CoherentNamed.mul zero one) zero
      (CCL.ProgressiveCoherence.CoherentNamed.mul one tau) tau
      (CCL.OperationalFieldLaws.coherentMul_zero_left one)
      (CCL.OperationalFieldLaws.coherentMul_one_left tau)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      simplifyTerms
      (CCL.OperationalFieldLaws.coherentAdd_zero_left tau))

def infinity_denominator_explicit (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalDenominator
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau).name
      (infinityDenominator tau).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let minusThree := CCL.ProgressiveCoherence.CoherentNamed.exact (-3)
  let minusTwo := CCL.ProgressiveCoherence.CoherentNamed.exact (-2)
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
    (fractionalVector tau) 0
  rw [CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalDenominator
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau).name
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul minusThree one)
      (CCL.ProgressiveCoherence.CoherentNamed.mul minusTwo tau)).name at expanded
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (by
      simpa only [infinityDenominator,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.TranscendentalCoherence.coherentAdd_respects _ _ _ _
          (CCL.OperationalFieldLaws.coherentMul_one_right minusThree)
          (CCL.OperationalEquivalence.NamedEquivalent.refl _))

def infinity_numerator_explicit (tau : CoherentNamed) :
    NamedEquivalent
      (fractionalNumerator
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau).name
      (infinityNumerator tau).name := by
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let two := CCL.ProgressiveCoherence.CoherentNamed.exact 2
  have expanded := matrixAction_row_two
    CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
    (fractionalVector tau) 1
  rw [CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix_explicit] at expanded
  change NamedEquivalent
    (fractionalNumerator
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau).name
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul two one)
      (CCL.ProgressiveCoherence.CoherentNamed.mul one tau)).name at expanded
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (by
      simpa only [infinityNumerator,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.TranscendentalCoherence.coherentAdd_respects _ _ _ _
          (CCL.OperationalFieldLaws.coherentMul_one_right two)
          (CCL.OperationalFieldLaws.coherentMul_one_left tau))

/-! ## Unconditional and productive headline packages -/

def scaleVector_respects (scalar : CoherentNamed)
    {left right : RawPeriodVector} (equivalent : VectorEquivalent left right) :
    VectorEquivalent (scaleVector scalar left) (scaleVector scalar right) :=
  fun coordinate => CCL.TranscendentalCoherence.coherentMul_respects
    scalar scalar (left coordinate) (right coordinate)
    (CCL.OperationalEquivalence.NamedEquivalent.refl scalar.name)
    (equivalent coordinate)

/-- Arbitrary finite-word dual period transport.  The actual periods from
`EndpointContinuation` are the original `A` scale times the stepwise action
of the reversed transposed generator matrices on `(1,tau)`. -/
def NormalizedData.periodWord_homogeneous {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame)
    (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.aPeriod
        (blockAction (periodBraidMatrices path.word)
          (fractionalVector data.ratio))) :=
  VectorEquivalent.trans (data.periods_normalized path)
    (scaleVector_respects data.aPeriod
      (periodBraidRows_word path.word data.ratio))

/-- Standard-loop data inherits the arbitrary-word homogeneous theorem
without adding any premise. -/
def Data.periodWord_homogeneous {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    VectorEquivalent (data.periods path)
      (scaleVector data.base.aPeriod
        (blockAction (periodBraidMatrices path.word)
          (fractionalVector data.base.ratio))) :=
  data.base.periodWord_homogeneous path

def zero_rows_affine (tau : CoherentNamed) :
    VectorEquivalent
      (matrixAction CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
        (fractionalVector tau))
      (fractionalVector (zeroAffineTransform tau)) := by
  intro coordinate
  refine Fin.cases ?_ (fun tail => Fin.cases ?_
    (fun impossible => Fin.elim0 impossible) tail) coordinate
  · exact zero_denominator_one tau
  · exact zero_numerator_affine tau

def Data.zero_affine {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) :
    VectorEquivalent data.zeroPeriods
      (scaleVector data.base.aPeriod
        (fractionalVector (zeroAffineTransform data.base.ratio))) :=
  VectorEquivalent.trans data.zero_homogeneous
    (scaleVector_respects data.base.aPeriod
      (zero_rows_affine data.base.ratio))

/-- Small carrier whose generated recursor never unfolds the large period
programs appearing in the public statement types. -/
structure FractionFreeCertificatePayload
    (zeroType oneType infinityType productType : Type)
    (inverseType : Prop) where
  zero : zeroType
  one : oneType
  infinity : infinityType
  product : productType
  inverseMatrices : inverseType

/-- Unconditional certificate for the correct dual period action.  Its
zero-loop formula is already productive because that dual denominator is
exactly one. -/
def FractionFreeCertificate {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) : Type :=
  FractionFreeCertificatePayload
    (VectorEquivalent data.zeroPeriods
      (scaleVector data.base.aPeriod
        (fractionalVector (zeroAffineTransform data.base.ratio))))
    (VectorEquivalent data.onePeriods
      (scaleVector data.base.aPeriod
        (matrixAction CCL.Riemann.LegendreMonodromy.onePeriodMatrix
          (fractionalVector data.base.ratio))))
    (VectorEquivalent data.infinityPeriods
      (scaleVector data.base.aPeriod
        (matrixAction CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
          (fractionalVector data.base.ratio))))
    (VectorEquivalent data.productPeriods data.base.toFibreData.rawPeriods)
    (RFAP.ConstructiveFiniteMatrix.mul
          (RFAP.ConstructiveFiniteMatrix.mul
            CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
            CCL.Riemann.LegendreMonodromy.onePeriodMatrix)
          CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix =
        RFAP.ConstructiveFiniteMatrix.identity ∧
      RFAP.ConstructiveFiniteMatrix.mul
          CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
          (RFAP.ConstructiveFiniteMatrix.mul
            CCL.Riemann.LegendreMonodromy.zeroPeriodMatrix
            CCL.Riemann.LegendreMonodromy.onePeriodMatrix) =
        RFAP.ConstructiveFiniteMatrix.identity)

def certificate {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) : FractionFreeCertificate data := by
  unfold FractionFreeCertificate
  exact
    { zero := data.zero_affine
      one := data.one_homogeneous
      infinity := data.infinity_homogeneous
      product := data.product_identity
      inverseMatrices :=
        ⟨CCL.Riemann.LegendreMonodromy.explicit_period_product_left,
          CCL.Riemann.LegendreMonodromy.explicit_period_product_right⟩ }

abbrev OnePreparation (tau : CoherentNamed) :=
  DenominatorPreparation
    (fractionalDenominator CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau)

abbrev InfinityPreparation (tau : CoherentNamed) :=
  DenominatorPreparation
    (fractionalDenominator
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau)

def oneTransform {tau : CoherentNamed}
    (preparation : OnePreparation tau) : CoherentNamed :=
  fractionalLinear CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau
    preparation

def infinityTransform {tau : CoherentNamed}
    (preparation : InfinityPreparation tau) : CoherentNamed :=
  fractionalLinear CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau
    preparation

/-- Convert a homogeneous transported period column and a fraction-free
quotient equation into the directly useful statement that the productive
quotient is the ratio of the two actual transported coordinates. -/
def productiveRatio_ofHomogeneous
    (periods : RawPeriodVector)
    (scale denominator numerator transform : CoherentNamed)
    (denominatorTransport : NamedEquivalent (periods 0).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul scale denominator).name)
    (numeratorTransport : NamedEquivalent (periods 1).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul scale numerator).name)
    (quotientEquation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul denominator transform).name
      numerator.name) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (periods 0) transform).name
      (periods 1).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.coherentMul_respects
      (periods 0)
      (CCL.ProgressiveCoherence.CoherentNamed.mul scale denominator)
      transform transform denominatorTransport
      (CCL.OperationalEquivalence.NamedEquivalent.refl transform.name))
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_assoc
        scale denominator transform)
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.TranscendentalCoherence.coherentMul_respects
          scale scale
          (CCL.ProgressiveCoherence.CoherentNamed.mul denominator transform)
          numerator
          (CCL.OperationalEquivalence.NamedEquivalent.refl scale.name)
          quotientEquation)
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          numeratorTransport)))

/-- Arbitrary finite-word productive dual period theorem.  Given exactly the
per-generator and combined denominator preparations for the reversed
transposed generator list, the resulting stepwise value is operationally the
ratio of the two actual period coordinates returned by endpoint
continuation. -/
def NormalizedData.periodWord_productive_transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : NormalizedData frame)
    (path : CCL.Riemann.LegendrePaths.Path frame frame)
    (preparations : PeriodFoldPreparations path.word data.ratio) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.periods path 0)
        (foldAction data.ratio (periodBraidMatrices path.word)
          preparations)).name
      (data.periods path 1).name := by
  let matrix := CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word
  let denominator := fractionalDenominator matrix data.ratio
  let numerator := fractionalNumerator matrix data.ratio
  let transform := foldAction data.ratio
    (periodBraidMatrices path.word) preparations
  have homogeneous := data.periods_normalized path
  have denominatorTransport := homogeneous 0
  change NamedEquivalent (data.periods path 0).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.aPeriod
      denominator).name at denominatorTransport
  have numeratorTransport := homogeneous 1
  change NamedEquivalent (data.periods path 1).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.aPeriod
      numerator).name at numeratorTransport
  exact productiveRatio_ofHomogeneous (data.periods path) data.aPeriod
    denominator numerator transform denominatorTransport numeratorTransport
    (by
      simpa only [matrix, denominator, numerator, transform] using
        periodFold_denominator_mul path.word data.ratio preparations)

/-- Standard-loop data inherits the arbitrary finite-word productive theorem
for every additional certified closed path on its base frame. -/
def Data.periodWord_productive_transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) (path : CCL.Riemann.LegendrePaths.Path frame frame)
    (preparations : PeriodFoldPreparations path.word data.base.ratio) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.periods path 0)
        (foldAction data.base.ratio (periodBraidMatrices path.word)
          preparations)).name
      (data.periods path 1).name :=
  data.base.periodWord_productive_transport path preparations

/-- The unconditional affine zero output is the ratio of the two period
coordinates transported around the actual zero loop. -/
def Data.zero_productive_transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.zeroPeriods 0) (zeroAffineTransform data.base.ratio)).name
      (data.zeroPeriods 1).name := by
  have denominatorTransport := data.zero_affine 0
  change NamedEquivalent (data.zeroPeriods 0).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.base.aPeriod
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1)).name
      at denominatorTransport
  have numeratorTransport := data.zero_affine 1
  change NamedEquivalent (data.zeroPeriods 1).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.base.aPeriod
      (zeroAffineTransform data.base.ratio)).name at numeratorTransport
  exact productiveRatio_ofHomogeneous data.zeroPeriods data.base.aPeriod
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1)
    (zeroAffineTransform data.base.ratio)
    (zeroAffineTransform data.base.ratio) denominatorTransport
    numeratorTransport
    (CCL.OperationalFieldLaws.coherentMul_one_left
      (zeroAffineTransform data.base.ratio))

/-- The prepared one-loop output is the ratio of the two period coordinates
transported around the actual one loop. -/
def Data.one_productive_transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) (preparation : OnePreparation data.base.ratio) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.onePeriods 0) (oneTransform preparation)).name
      (data.onePeriods 1).name := by
  have denominatorTransport := data.one_homogeneous 0
  change NamedEquivalent (data.onePeriods 0).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.base.aPeriod
      (fractionalDenominator CCL.Riemann.LegendreMonodromy.onePeriodMatrix
        data.base.ratio)).name at denominatorTransport
  have numeratorTransport := data.one_homogeneous 1
  change NamedEquivalent (data.onePeriods 1).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.base.aPeriod
      (fractionalNumerator CCL.Riemann.LegendreMonodromy.onePeriodMatrix
        data.base.ratio)).name at numeratorTransport
  exact productiveRatio_ofHomogeneous data.onePeriods data.base.aPeriod
    (fractionalDenominator CCL.Riemann.LegendreMonodromy.onePeriodMatrix
      data.base.ratio)
    (fractionalNumerator CCL.Riemann.LegendreMonodromy.onePeriodMatrix
      data.base.ratio)
    (oneTransform preparation) denominatorTransport numeratorTransport
    (by
      simpa only [oneTransform] using
        (denominator_mul_fractionalLinear
          CCL.Riemann.LegendreMonodromy.onePeriodMatrix data.base.ratio
          preparation))

/-- The prepared infinity-loop output is the ratio of the two period
coordinates transported around the actual infinity loop. -/
def Data.infinity_productive_transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops)
    (preparation : InfinityPreparation data.base.ratio) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.infinityPeriods 0) (infinityTransform preparation)).name
      (data.infinityPeriods 1).name := by
  have denominatorTransport := data.infinity_homogeneous 0
  change NamedEquivalent (data.infinityPeriods 0).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.base.aPeriod
      (fractionalDenominator
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
        data.base.ratio)).name at denominatorTransport
  have numeratorTransport := data.infinity_homogeneous 1
  change NamedEquivalent (data.infinityPeriods 1).name
    (CCL.ProgressiveCoherence.CoherentNamed.mul data.base.aPeriod
      (fractionalNumerator
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix
        data.base.ratio)).name at numeratorTransport
  exact productiveRatio_ofHomogeneous data.infinityPeriods data.base.aPeriod
    (fractionalDenominator
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix data.base.ratio)
    (fractionalNumerator
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix data.base.ratio)
    (infinityTransform preparation) denominatorTransport numeratorTransport
    (by
      simpa only [infinityTransform] using
        (denominator_mul_fractionalLinear
          CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix data.base.ratio
          preparation))

/-- Small productive carrier, again separated from expanded process indices.
The transport fields close the final algebraic step for the supplied data;
clients need not reconstruct it from the homogeneous and quotient fields. -/
structure ProductiveCertificatePayload
    (fractionFreeType oneType infinityType zeroTransportType
      oneTransportType infinityTransportType : Type) where
  fractionFree : fractionFreeType
  oneEquation : oneType
  infinityEquation : infinityType
  zeroTransport : zeroTransportType
  oneTransport : oneTransportType
  infinityTransport : infinityTransportType

/-- Productive standard dual outputs.  Only the one and infinity
denominators require typed apartness; zero remains the direct affine name. -/
def ProductiveCertificate {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops)
    (onePreparation : OnePreparation data.base.ratio)
    (infinityPreparation : InfinityPreparation data.base.ratio) : Type :=
  ProductiveCertificatePayload
    (FractionFreeCertificate data)
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (fractionalDenominator
          CCL.Riemann.LegendreMonodromy.onePeriodMatrix data.base.ratio)
        (oneTransform onePreparation)).name
      (fractionalNumerator
        CCL.Riemann.LegendreMonodromy.onePeriodMatrix data.base.ratio).name)
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (fractionalDenominator
          CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix data.base.ratio)
        (infinityTransform infinityPreparation)).name
      (fractionalNumerator
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix data.base.ratio).name)
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.zeroPeriods 0) (zeroAffineTransform data.base.ratio)).name
      (data.zeroPeriods 1).name)
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.onePeriods 0) (oneTransform onePreparation)).name
      (data.onePeriods 1).name)
    (NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.infinityPeriods 0)
        (infinityTransform infinityPreparation)).name
      (data.infinityPeriods 1).name)

def productiveCertificate {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops)
    (onePreparation : OnePreparation data.base.ratio)
    (infinityPreparation : InfinityPreparation data.base.ratio) :
    ProductiveCertificate data onePreparation infinityPreparation := by
  unfold ProductiveCertificate
  exact
    { fractionFree := certificate data
      oneEquation := denominator_mul_fractionalLinear _ _ onePreparation
      infinityEquation :=
        denominator_mul_fractionalLinear _ _ infinityPreparation
      zeroTransport := data.zero_productive_transport
      oneTransport := data.one_productive_transport onePreparation
      infinityTransport :=
        data.infinity_productive_transport infinityPreparation }

/-- Precisely indexed readiness for both nonconstant dual standard-loop
denominators. -/
structure StandardReadyPayload (oneType infinityType : Type 1) where
  one : oneType
  infinity : infinityType

def StandardReady (tau : CoherentNamed) : Type 1 :=
  StandardReadyPayload (OnePreparation tau) (InfinityPreparation tau)

/-- A ready pair feeds the productive dual headline certificate directly. -/
def productiveCertificateOfReady {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {loops : CCL.Riemann.LegendreMonodromy.StandardLoops frame}
    (data : Data loops) (ready : StandardReady data.base.ratio) :
    ProductiveCertificate data ready.one ready.infinity :=
  productiveCertificate data ready.one ready.infinity

/-! ## Retryable standard denominator acquisition -/

def attemptStandardOne (tau : CoherentNamed) (fuel : Nat) :
    CCL.Riemann.LegendreDenominatorAcquisition.RunResult
      CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau
      (CCL.Riemann.LegendreDenominatorAcquisition.initial
        CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau) fuel :=
  CCL.Riemann.LegendreDenominatorAcquisition.attempt
    CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau
    (CCL.Riemann.LegendreDenominatorAcquisition.initial
      CCL.Riemann.LegendreMonodromy.onePeriodMatrix tau) fuel

def attemptStandardInfinity (tau : CoherentNamed) (fuel : Nat) :
    CCL.Riemann.LegendreDenominatorAcquisition.RunResult
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau
      (CCL.Riemann.LegendreDenominatorAcquisition.initial
        CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau) fuel :=
  CCL.Riemann.LegendreDenominatorAcquisition.attempt
    CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau
    (CCL.Riemann.LegendreDenominatorAcquisition.initial
      CCL.Riemann.LegendreMonodromy.infinityPeriodMatrix tau) fuel

end CCL.Riemann.LegendrePeriodMonodromy
