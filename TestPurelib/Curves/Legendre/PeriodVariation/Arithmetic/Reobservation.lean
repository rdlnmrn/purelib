module

import TestPurelib.Curves.Legendre.PeriodVariation.Arithmetic
import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservation
import Purelib.Approximation.AccuracyRequest.Scaling

/-! # Independent new evaluator payments on the retained nonsquare-root fixture

The original arithmetic fixture and both full-root scalar observations stay
unchanged. A genuinely new bank requests the common spatial/parameter
accuracy on each old evaluator. Both Taylor rows consume the actual new
readings; the old complete observations and operational comparisons remain.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation.Arithmetic.Reobservation

open Purelib
open Purelib.Approximation
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open TestPurelib.Curves.Legendre.PeriodVariation

/-- The independent free evaluator request is one quarter of the original parameter-fourth request. -/
def spatial : AccuracyRequest := Sampling.jet.accuracy.quarter

/-- Materialize the genuinely new arithmetic bank on the actual old evaluator caches and scalar root data. -/
def paid : Variation.Arithmetic.Reobservations Arithmetic.observations spatial :=
  Variation.Arithmetic.Reobservations.build Arithmetic.observations spatial

attribute [local irreducible] spatial paid

/-- The complete old source observation and its original starts remain retained verbatim. -/
theorem old_source_cache (coordinate : Fin 2) :
    (paid.sourceValue.get coordinate).original = Arithmetic.observations.sourceValue coordinate :=
  (paid.sourceValue.get coordinate).original_eq

/-- The new source observation uses the identical old complete evaluator cache rather than another scalar name. -/
theorem source_evaluator (coordinate : Fin 2) :
    (paid.sourceValue.get coordinate).requested.original.coefficient =
      (Arithmetic.observations.sourceValue coordinate).original.coefficient := by
  have same := (paid.sourceValue.get coordinate).requested.coefficient_eq
  exact same.trans (congrArg (fun original => original.original.coefficient)
    (paid.sourceValue.get coordinate).original_eq)

/-- The independent target observation retains its own original target evaluator cache. -/
theorem target_evaluator (coordinate : Fin 2) :
    (paid.targetFirst.get coordinate).requested.original.coefficient =
      (Arithmetic.observations.targetFirst coordinate).original.coefficient := by
  have same := (paid.targetFirst.get coordinate).requested.coefficient_eq
  exact same.trans (congrArg (fun original => original.original.coefficient)
    (paid.targetFirst.get coordinate).original_eq)

/-- The new value certificate keeps the original numerical factor while its actual new readings remain distinct. -/
theorem value_factor (coordinate : Fin 2) :
    (paid.valueCertificate coordinate).factor = (Arithmetic.observations.valueCertificate coordinate).factor :=
  paid.valueCertificate_factor_eq coordinate

/-- The independently observed second slope keeps the first-derivative certificate's original numerical factor. -/
theorem first_factor (coordinate : Fin 2) :
    (paid.firstCertificate coordinate).factor = (Arithmetic.observations.firstCertificate coordinate).factor :=
  paid.firstCertificate_factor_eq coordinate

/-- The actual newly requested value readings satisfy their direct finite parameter Taylor estimate. -/
theorem value_remainder (coordinate : Fin 2) : Canonical.normSq
    ((paid.targetValue.get coordinate).requested.reading - (paid.sourceValue.get coordinate).requested.reading -
      Sampling.increment * (paid.sourceFirst.get coordinate).requested.reading) ≤
    (paid.valueCertificate coordinate).factor * Canonical.normSq Sampling.increment ^ 2 :=
  paid.value_remainder_le coordinate

/-- The new first readings satisfy the second row estimate with the actual independently requested second slope. -/
theorem first_remainder (coordinate : Fin 2) : Canonical.normSq
    ((paid.targetFirst.get coordinate).requested.reading - (paid.sourceFirst.get coordinate).requested.reading -
      Sampling.increment * (paid.sourceSecond.get coordinate).requested.reading) ≤
    (paid.firstCertificate coordinate).factor * Canonical.normSq Sampling.increment ^ 2 :=
  paid.first_remainder_le coordinate

end TestPurelib.Curves.Legendre.PeriodVariation.Arithmetic.Reobservation
