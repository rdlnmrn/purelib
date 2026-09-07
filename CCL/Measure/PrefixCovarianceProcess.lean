import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixCenteredVarianceProcess
import CCL.Measure.PrefixCovariance

/-!
# Progressive covariance from finite CCL prefixes

Three progressive witness-centred variance enclosures, for two rational
probes and their sum, combine by the exact finite polarization identity.
The resulting process retains only finite prefix states and computes a finite
request for every positive rational covariance tolerance.
-/

namespace CCL.FiniteMeasure

/-- Positive sensitivity data needed by the finite-request centred-variance
process for one rational probe. -/
structure ProbeCenteredVarianceProcessData {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) where
  meanFactor : Coordinate
  meanFactorPositive : 0 < meanFactor
  meanSensitive : ∀ left right,
    _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
      meanFactor * CCL.Chordal.chordalSq left right
  deviationFactor : Coordinate
  deviationFactorPositive : 0 < deviationFactor
  deviationSensitive : ∀ left right,
    _root_.FiniteMeasure.rationalSeparation
        (poweredDeviationProbe probe
          (process.witnessProbeExpectation distribution probe) 2 left)
        (poweredDeviationProbe probe
          (process.witnessProbeExpectation distribution probe) 2 right) ≤
      deviationFactor * CCL.Chordal.chordalSq left right

namespace ProbeCenteredVarianceProcessData

/-- Package one probe's progressive centred-variance enclosure. -/
def toBoundProcess {ι : Type} {process : PrefixFamilyProcess ι}
    {distribution : _root_.FiniteMeasure.Distribution ι}
    {probe : Proj → Coordinate}
    (data : ProbeCenteredVarianceProcessData process distribution probe) :
    _root_.FiniteMeasure.BoundProcess :=
  process.toProbeCenteredVarianceProcess distribution probe data.meanFactor
    data.meanFactorPositive data.meanSensitive data.deviationFactor
    data.deviationFactorPositive data.deviationSensitive

end ProbeCenteredVarianceProcessData

namespace PrefixFamilyProcess

/-- Covariance process obtained by finite rational polarization of three
progressive variance processes. -/
def toProbeCovarianceProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (left right : Proj → Coordinate)
    (leftData : ProbeCenteredVarianceProcessData process distribution left)
    (rightData : ProbeCenteredVarianceProcessData process distribution right)
    (sumData : ProbeCenteredVarianceProcessData process distribution
      (addProbe left right)) :
    _root_.FiniteMeasure.BoundProcess :=
  _root_.FiniteMeasure.BoundProcess.scalePositive
    ((sumData.toBoundProcess.sub leftData.toBoundProcess).sub
      rightData.toBoundProcess)
    (1 / 2) (by decide)

/-- One realization family is admitted simultaneously by the sum, left, and
right variance states making up a progressive covariance state. -/
structure ProbeCovarianceRealizesAt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (left right : Proj → Coordinate)
    (leftData : ProbeCenteredVarianceProcessData process distribution left)
    (rightData : ProbeCenteredVarianceProcessData process distribution right)
    (sumData : ProbeCenteredVarianceProcessData process distribution
      (addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (points : ι → Proj) where
  sumRealizes : ∀ atom, atom ∈ distribution.atoms →
    CCL.Cylinder.Realizes (process.blocks state.1.1 atom.item)
      (points atom.item)
  leftRealizes : ∀ atom, atom ∈ distribution.atoms →
    CCL.Cylinder.Realizes (process.blocks state.1.2 atom.item)
      (points atom.item)
  rightRealizes : ∀ atom, atom ∈ distribution.atoms →
    CCL.Cylinder.Realizes (process.blocks state.2 atom.item)
      (points atom.item)

/-- If one realization family is admitted by each of the three displayed
prefix states, its exact covariance lies in their combined rational
enclosure. -/
theorem probeCovarianceProcess_bound_contains {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (left right : Proj → Coordinate)
    (leftData : ProbeCenteredVarianceProcessData process distribution left)
    (rightData : ProbeCenteredVarianceProcessData process distribution right)
    (sumData : ProbeCenteredVarianceProcessData process distribution
      (addProbe left right))
    (sumState leftState rightState : process.State)
    (points : ι → Proj)
    (sumRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks sumState atom.item)
        (points atom.item))
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks leftState atom.item)
        (points atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks rightState atom.item)
        (points atom.item)) :
    ((process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).bound ⟨⟨sumState, leftState⟩, rightState⟩).Contains
        (distribution.covariance
          (fun item => left (points item))
          (fun item => right (points item))) := by
  have sumInside :=
    process.variance_mem_toProbeCenteredVarianceProcess_bound distribution
      (addProbe left right) sumData.meanFactor sumData.meanFactorPositive
      sumData.meanSensitive sumData.deviationFactor
      sumData.deviationFactorPositive sumData.deviationSensitive sumState
      points sumRealize
  have leftInside :=
    process.variance_mem_toProbeCenteredVarianceProcess_bound distribution
      left leftData.meanFactor leftData.meanFactorPositive
      leftData.meanSensitive leftData.deviationFactor
      leftData.deviationFactorPositive leftData.deviationSensitive leftState
      points leftRealize
  have rightInside :=
    process.variance_mem_toProbeCenteredVarianceProcess_bound distribution
      right rightData.meanFactor rightData.meanFactorPositive
      rightData.meanSensitive rightData.deviationFactor
      rightData.deviationFactorPositive rightData.deviationSensitive rightState
      points rightRealize
  have differenceInside := _root_.FiniteMeasure.Bound.sub_contains
    (_root_.FiniteMeasure.Bound.sub_contains sumInside leftInside) rightInside
  have scaled := _root_.FiniteMeasure.Bound.scale_contains
    (by decide : (0 : Coordinate) ≤ 1 / 2) differenceInside
  have polarization :=
    distribution.two_mul_covariance_eq_variance_add_sub
      (fun item => left (points item))
      (fun item => right (points item))
  have covarianceIdentity :
      (1 / 2 : Coordinate) *
          (distribution.variance
              (fun item => addProbe left right (points item)) -
            distribution.variance (fun item => left (points item)) -
            distribution.variance (fun item => right (points item))) =
        distribution.covariance
          (fun item => left (points item))
          (fun item => right (points item)) := by
    unfold addProbe
    rw [← polarization]
    calc
      (1 / 2 : Coordinate) *
          (2 * distribution.covariance
            (fun item => left (points item))
            (fun item => right (points item))) =
        ((1 / 2 : Coordinate) * 2) *
          distribution.covariance
            (fun item => left (points item))
            (fun item => right (points item)) := by ring1
      _ = distribution.covariance
          (fun item => left (points item))
          (fun item => right (points item)) := by
        rw [show (1 / 2 : Coordinate) * 2 = 1 by decide]
        ring1
  rw [covarianceIdentity] at scaled
  exact scaled

/-- Packaged covariance containment for one composite process state. -/
theorem covariance_mem_toProbeCovarianceProcess_bound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (left right : Proj → Coordinate)
    (leftData : ProbeCenteredVarianceProcessData process distribution left)
    (rightData : ProbeCenteredVarianceProcessData process distribution right)
    (sumData : ProbeCenteredVarianceProcessData process distribution
      (addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (points : ι → Proj)
    (realizes : process.ProbeCovarianceRealizesAt distribution left right
      leftData rightData sumData state points) :
    ((process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).bound state).Contains
        (distribution.covariance
          (fun item => left (points item))
          (fun item => right (points item))) := by
  exact process.probeCovarianceProcess_bound_contains distribution left right
    leftData rightData sumData state.1.1 state.1.2 state.2 points
    realizes.sumRealizes realizes.leftRealizes realizes.rightRealizes

/-- One finite composite request makes the progressive covariance enclosure
narrower than the supplied positive rational tolerance. -/
theorem request_probeCovariance_width_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (left right : Proj → Coordinate)
    (leftData : ProbeCenteredVarianceProcessData process distribution left)
    (rightData : ProbeCenteredVarianceProcessData process distribution right)
    (sumData : ProbeCenteredVarianceProcessData process distribution
      (addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).bound
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive)).width < epsilon :=
  (process.toProbeCovarianceProcess distribution left right leftData rightData
    sumData).accurate state epsilon positive

/-- After one finite composite request, the covariances of every two
realization families admitted by all three returned prefix states are within
the requested rational separation. -/
theorem request_probeCovariances_pairwise_separation_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (left right : Proj → Coordinate)
    (leftData : ProbeCenteredVarianceProcessData process distribution left)
    (rightData : ProbeCenteredVarianceProcessData process distribution right)
    (sumData : ProbeCenteredVarianceProcessData process distribution
      (addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Proj)
    (leftRealizes : process.ProbeCovarianceRealizesAt distribution left right
      leftData rightData sumData
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive) leftPoints)
    (rightRealizes : process.ProbeCovarianceRealizesAt distribution left right
      leftData rightData sumData
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive) rightPoints) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.covariance
          (fun item => left (leftPoints item))
          (fun item => right (leftPoints item)))
        (distribution.covariance
          (fun item => left (rightPoints item))
          (fun item => right (rightPoints item))) < epsilon := by
  let covarianceProcess := process.toProbeCovarianceProcess distribution left
    right leftData rightData sumData
  let requested := covarianceProcess.request state epsilon positive
  apply covarianceProcess.request_rationalSeparation_lt state epsilon positive
  · exact process.covariance_mem_toProbeCovarianceProcess_bound distribution
      left right leftData rightData sumData requested leftPoints leftRealizes
  · exact process.covariance_mem_toProbeCovarianceProcess_bound distribution
      left right leftData rightData sumData requested rightPoints rightRealizes

end PrefixFamilyProcess

end CCL.FiniteMeasure
