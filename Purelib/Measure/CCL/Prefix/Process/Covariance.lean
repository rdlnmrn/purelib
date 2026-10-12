module

import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.Approximation.Bound.Observation
import Purelib.Approximation.Bound.Process
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
public import Purelib.Data.Function.Rat.Algebra
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.CCL.Prefix.Process.Variance.Data
public import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Approximation.OneSided.BoundProcess
import Purelib.Measure.CCL.Prefix.Process.Variance.Centered
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
public section

/-!
# Progressive covariance from finite CCL prefixes

Three progressive witness-centred variance enclosures, for two rational
probes and their sum, combine by the exact finite polarization identity.
The resulting process retains only finite prefix states and computes a finite
request for every positive rational covariance tolerance.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder
namespace ProbeCenteredVarianceProcessData
end ProbeCenteredVarianceProcessData

namespace PrefixFamilyProcess

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Combine three retained centered-variance processes using covariance polarization.

The sum, left and right probes keep separate states and certificates; half the sum variance minus both individual
variances gives the covariance enclosure. -/
@[expose] def toProbeCovarianceProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution left)
    (rightData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution right)
    (sumData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution
      (Function.Rat.addProbe left right)) :
    Approximation.BoundProcess :=
  Approximation.BoundProcess.scalePositive
    ((sumData.toBoundProcess.sub leftData.toBoundProcess).sub
      rightData.toBoundProcess)
    (1 / 2) (by decide)

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
set_option genInjectivity false in
/-- A point family realizing all three states of a retained covariance enclosure.

The exact nested state contains separate sum-probe, left-probe and right-probe prefix states, and the same points must
realize each on every original atom. -/
structure ProbeCovarianceRealizesAt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution left)
    (rightData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution right)
    (sumData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution
      (Function.Rat.addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (points : ι → Line.GaussianLine) where
  /-- The points realize the sum-probe state's original blocks on every retained atom. -/ sumRealizes : ∀ atom, atom ∈
    distribution.atoms →
    Realizes (process.blocks state.1.1 atom.item)
      (points atom.item)
  /-- The same points realize the left-probe state's original blocks on every retained atom. -/ leftRealizes : ∀ atom,
    atom ∈ distribution.atoms →
    Realizes (process.blocks state.1.2 atom.item)
      (points atom.item)
  /-- The same points realize the right-probe state's original blocks on every retained atom. -/ rightRealizes : ∀ atom,
    atom ∈ distribution.atoms →
    Realizes (process.blocks state.2 atom.item)
      (points atom.item)

constructive_injectivity ProbeCovarianceRealizesAt

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The polarization enclosure contains covariance when the same points realize the supplied sum, left and right states.
-/
theorem probeCovarianceProcess_bound_contains {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution left)
    (rightData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution right)
    (sumData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution
      (Function.Rat.addProbe left right))
    (sumState leftState rightState : process.State)
    (points : ι → Line.GaussianLine)
    (sumRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks sumState atom.item)
        (points atom.item))
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks leftState atom.item)
        (points atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks rightState atom.item)
        (points atom.item)) :
    ((process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).bound ⟨⟨sumState, leftState⟩, rightState⟩).Contains
        (distribution.covariance
          (fun item => left (points item))
          (fun item => right (points item))) := by
  have sumInside :=
    (CCL.Prefix.PrefixFamilyProcess.variance_mem_toProbeCenteredVarianceProcess_bound process) distribution
      (Function.Rat.addProbe left right) sumData.meanFactor sumData.meanFactorPositive
      sumData.meanSensitive sumData.deviationFactor
      sumData.deviationFactorPositive sumData.deviationSensitive sumState
      points sumRealize
  have leftInside :=
    (CCL.Prefix.PrefixFamilyProcess.variance_mem_toProbeCenteredVarianceProcess_bound process) distribution
      left leftData.meanFactor leftData.meanFactorPositive
      leftData.meanSensitive leftData.deviationFactor
      leftData.deviationFactorPositive leftData.deviationSensitive leftState
      points leftRealize
  have rightInside :=
    (CCL.Prefix.PrefixFamilyProcess.variance_mem_toProbeCenteredVarianceProcess_bound process) distribution
      right rightData.meanFactor rightData.meanFactorPositive
      rightData.meanSensitive rightData.deviationFactor
      rightData.deviationFactorPositive rightData.deviationSensitive rightState
      points rightRealize
  have differenceInside := Interval.sub_contains
    (Interval.sub_contains sumInside leftInside) rightInside
  have scaled := Interval.scale_contains
    (by decide : (0 : Fraction.Rational) ≤ 1 / 2) differenceInside
  have polarization :=
    distribution.two_mul_covariance_eq_variance_add_sub
      (fun item => left (points item))
      (fun item => right (points item))
  have covarianceIdentity :
      (1 / 2 : Fraction.Rational) *
          (distribution.variance
              (fun item => Function.Rat.addProbe left right (points item)) -
            distribution.variance (fun item => left (points item)) -
            distribution.variance (fun item => right (points item))) =
        distribution.covariance
          (fun item => left (points item))
          (fun item => right (points item)) := by
    unfold Function.Rat.addProbe
    rw [← polarization]
    calc
      (1 / 2 : Fraction.Rational) *
          (2 * distribution.covariance
            (fun item => left (points item))
            (fun item => right (points item))) =
        ((1 / 2 : Fraction.Rational) * 2) *
          distribution.covariance
            (fun item => left (points item))
            (fun item => right (points item)) := by ring1
      _ = distribution.covariance
          (fun item => left (points item))
          (fun item => right (points item)) := by
        rw [show (1 / 2 : Fraction.Rational) * 2 = 1 by decide]
        ring1
  rw [covarianceIdentity] at scaled
  exact scaled

/-- A retained three-state realization certificate places covariance inside its exact process enclosure. -/
theorem covariance_mem_toProbeCovarianceProcess_bound {ι :
  Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution left)
    (rightData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution right)
    (sumData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution
      (Function.Rat.addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (points : ι → Line.GaussianLine)
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

/-- The requested covariance enclosure is narrower than the positive epsilon. -/
theorem request_probeCovariance_width_lt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution left)
    (rightData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution right)
    (sumData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution
      (Function.Rat.addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).bound
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive)).width < epsilon :=
  (process.toProbeCovarianceProcess distribution left right leftData rightData
    sumData).accurate state epsilon positive

/-- Two families realizing all three requested states have covariance separation strictly below epsilon. -/
theorem request_probeCovariances_pairwise_separation_lt {ι
  : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (left right : Line.GaussianLine → Fraction.Rational)
    (leftData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution left)
    (rightData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution right)
    (sumData : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution
      (Function.Rat.addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Line.GaussianLine)
    (leftRealizes : process.ProbeCovarianceRealizesAt distribution left right
      leftData rightData sumData
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive) leftPoints)
    (rightRealizes : process.ProbeCovarianceRealizesAt distribution left right
      leftData rightData sumData
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive) rightPoints) :
    Distance.rationalSeparation
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

end

end PrefixFamilyProcess

end Purelib.Data.CCL.Encoding.Cylinder

end
