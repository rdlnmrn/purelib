module

import Purelib.Approximation.Gaussian.Table.Request
import Purelib.Curves.Hyperelliptic.Periods.PreparedNormalization
import Purelib.Examples.Riemann.ExplicitLegendreNormalizedAcquisition
import Purelib.Riemann.Periods.PeriodMatrix

/-! The same retained ball supplies both numerical reads and accuracy. The
symbolic owner checks preserve arbitrary supplied inverse presentations; the
Legendre client accepts a completed theorem result without rerunning it. -/

namespace Test.Riemann.PreparedNormalizedEntry

open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PeriodMatrix

/-- A concrete shared request preserves an exact channel's center and zero radius in its retained ball. -/
example :
    let channel := Name.Coherent.CoherentNamed.Coherence.exact 3
    let prepared := Table.Request.prepareEntry [channel] channel 1 (by decide)
    prepared.center = 3 ∧ prepared.radiusSq = 0 := by
  decide

/-- A prepared table request retains its actual name, selected ball and strict accuracy together. -/
example (channels : List Name.Coherent.CoherentNamed) (channel : Name.Coherent.CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) :
    let prepared := Table.Request.prepareEntry channels channel target positive
    prepared.name = Table.Request.sharedName channels channel target positive ∧
      prepared.ball = prepared.name.process.ball prepared.name.state ∧
      (prepared.center, prepared.radiusSq) = (prepared.ball.center, prepared.ball.radiusSq) ∧
      0 ≤ prepared.radiusSq ∧ prepared.radiusSq < target := by
  let prepared := Table.Request.prepareEntry channels channel target positive
  exact ⟨prepared.name_eq, prepared.ball_eq, prepared.readings_readback,
    prepared.radiusSq_nonneg, prepared.radiusSq_lt_target⟩

/-- Arbitrary normalization owners preserve their original data, inverse and requested scalar readbacks. -/
example {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {raw : PeriodData curve} {inverse : ScaledInverseCertificate raw.aMatrix}
    (owner : Periods.PreparedNormalization.Normalization raw inverse)
    (target : Fraction.Rational) (positive : 0 < target) (row column : Fin genus) :
    let prepared := owner.prepareEntry target positive row column
    owner.normalized.toPeriodData = raw ∧ HEq owner.normalized.aInverse inverse ∧
      prepared.center = owner.normalized.omegaCenter target positive row column ∧
      prepared.radiusSq = owner.normalized.omegaRadiusSq target positive row column ∧
      prepared.radiusSq < target := by
  let prepared := owner.prepareEntry target positive row column
  exact ⟨owner.raw_readback, owner.inverse_readback,
    owner.prepareEntry_center_readback target positive row column,
    owner.prepareEntry_radiusSq_readback target positive row column, prepared.radiusSq_lt_target⟩

/-- The production genus-one client obtains both numbers and accuracy from a retained theorem and one request. -/
example (result : PeriodTheorem.Result
      Curves.Legendre.LoopBaseBranches.baseCurve)
    (target : Fraction.Rational) (positive : 0 < target) :
    let prepared := Riemann.ExplicitLegendreNormalizedAcquisition.prepareRatio result target positive
    prepared.name = result.normalization.refinedEntry target positive 0 0 ∧
      (prepared.center, prepared.radiusSq) = (prepared.ball.center, prepared.ball.radiusSq) ∧
      prepared.radiusSq < target := by
  let prepared := Riemann.ExplicitLegendreNormalizedAcquisition.prepareRatio result target positive
  exact ⟨result.normalization.prepareEntry_name target positive 0 0,
    prepared.readings_readback, prepared.radiusSq_lt_target⟩

end Test.Riemann.PreparedNormalizedEntry
