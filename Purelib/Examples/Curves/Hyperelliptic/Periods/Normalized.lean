module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Periods.PreparedNormalization
import Purelib.Riemann.Periods.PeriodTheorem
import Purelib.Examples.Riemann.ExplicitLegendreNormalizedAcquisition
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

namespace Purelib.Examples.Curves.Hyperelliptic.Periods.Normalized

open Purelib.Examples.Riemann

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

open Purelib.Riemann.Periods.PeriodMatrix (PeriodData ScaledInverseCertificate NormalizedPeriodData)
open Purelib.Curves.Hyperelliptic.Periods.PreparedNormalization (Normalization)
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Riemann.Periods.PeriodTheorem (Result)

/-! Supplied finite period data and its actual scaled inverse first construct
one retained normalization. A bounded entry request then provides both scalar
readings from one cached ball. The production Legendre example also consumes
an already retained theorem result, without reacquiring its period data.
A certified-tail inverse remains its own presentation; operational equivalence
does not identify its name with the canonical inverse name. -/
/-- The realized normalized period owner retains the exact raw parent and scaled-inverse omega readback. -/
example {genus : Nat} {curve : HyperellipticCurve genus}
    (raw : PeriodData curve) (inverse : ScaledInverseCertificate raw.aMatrix)
    (row column : Fin genus) :
    let retained := Normalization.realize raw inverse
    retained.normalized.toPeriodData = raw ∧
      retained.omega row column =
        (NormalizedPeriodData.ofScaledInverse raw inverse).omega row column := by
  let retained := Normalization.realize raw inverse
  exact ⟨retained.raw_readback, retained.omega_readback row column⟩

/-- One supplied-data normalization and one prepared entry supply the paired reading and strict target certificate. -/
example {genus : Nat} {curve : HyperellipticCurve genus}
    (raw : PeriodData curve) (inverse : ScaledInverseCertificate raw.aMatrix)
    (target : Fraction.Rational) (positive : 0 < target) (row column : Fin genus) :
    let retained := Normalization.realize raw inverse
    let prepared := retained.prepareEntry target positive row column
    prepared.name = retained.normalized.refinedOmegaEntry target positive row column ∧
      (prepared.center, prepared.radiusSq) = (prepared.ball.center, prepared.ball.radiusSq) ∧
      prepared.radiusSq < target := by
  let retained := Normalization.realize raw inverse
  let prepared := retained.prepareEntry target positive row column
  exact ⟨retained.prepareEntry_name_readback target positive row column,
    prepared.readings_readback, prepared.radiusSq_lt_target⟩

/-- An already retained Legendre theorem result supplies one ratio request without another curve acquisition. -/
example (result : Result
      Curves.Legendre.LoopBaseBranches.baseCurve)
    (target : Fraction.Rational) (positive : 0 < target) :
    let prepared := ExplicitLegendreNormalizedAcquisition.prepareRatio result target positive
    (prepared.center, prepared.radiusSq) = (prepared.ball.center, prepared.ball.radiusSq) ∧
      prepared.radiusSq < target := by
  let prepared := ExplicitLegendreNormalizedAcquisition.prepareRatio result target positive
  exact ⟨prepared.readings_readback, prepared.radiusSq_lt_target⟩

end Purelib.Examples.Curves.Hyperelliptic.Periods.Normalized
