module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Interpretation
public import Purelib.Approximation.Gaussian.Name.Coherent.Transport

/-! # Exact request-index transport of the same original arithmetic Reading

Equality of whole positive AccuracyRequest objects changes only their nominal
index. The complete original evaluator, two selected states, both observations,
comparison, stage floors and displayed witness remain unchanged. No weaker
payment is upgraded and no root or arithmetic observation is requested.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Reading

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {radicand : Coefficients} {differential : OddPowerDifferential radicand}
    {point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
    {state : sheet.name.process.State} {rootObservation : RootObservation} {first last : AccuracyRequest}

/-- Transport the SAME whole arithmetic Reading through equality of its complete original accuracy request. -/
@[expose] def castAccuracy (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    Reading differential point sheet apart state rootObservation last := by
  cases equal
  exact retained

/-- Exact request transport preserves the complete original Reading, including all proof and data fields. -/
theorem castAccuracy_heq (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    HEq (retained.castAccuracy equal) retained := by
  cases equal
  rfl

/-- The actual retained evaluator and complete coherent process are unchanged by the exact request transport. -/
theorem castAccuracy_coefficient (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    (retained.castAccuracy equal).coefficient = retained.coefficient := by
  cases equal
  rfl

/-- The independently selected original-start state is retained on its identical complete evaluator. -/
theorem castAccuracy_originalState (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    CoherentNamed.castState (retained.castAccuracy_coefficient equal)
      (retained.castAccuracy equal).originalState = retained.originalState := by
  cases equal
  rfl

/-- The original paid-start state remains unchanged under the same complete evaluator equality. -/
theorem castAccuracy_paidStart (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    CoherentNamed.castState (retained.castAccuracy_coefficient equal)
      (retained.castAccuracy equal).paidStart = retained.paidStart := by
  cases equal
  rfl

/-- The separately selected paid state survives the exact request transport without a new refinement. -/
theorem castAccuracy_paidState (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    CoherentNamed.castState (retained.castAccuracy_coefficient equal)
      (retained.castAccuracy equal).paidState = retained.paidState := by
  cases equal
  rfl

/-- The original displayed arithmetic observation remains the identical complete cache. -/
theorem castAccuracy_original (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    (retained.castAccuracy equal).original = retained.original := by
  cases equal
  rfl

/-- The independent paid-start observation remains the identical complete original cache. -/
theorem castAccuracy_paid (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    (retained.castAccuracy equal).paid = retained.paid := by
  cases equal
  rfl

/-- The complete actual two-start comparison retains its original selected indices and samples heterogeneously. -/
theorem castAccuracy_comparison (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    HEq (retained.castAccuracy equal).comparison retained.comparison := by
  cases equal
  rfl

/-- The original selected comparison index remains unchanged. -/
theorem castAccuracy_leftIndex (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    (retained.castAccuracy equal).comparison.leftIndex = retained.comparison.leftIndex := by
  cases equal
  rfl

/-- The independently selected paid comparison index remains unchanged. -/
theorem castAccuracy_rightIndex (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    (retained.castAccuracy equal).comparison.rightIndex = retained.comparison.rightIndex := by
  cases equal
  rfl

/-- The same displayed numerical witness is read after exact request-index transport. -/
theorem castAccuracy_reading (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    (retained.castAccuracy equal).reading = retained.reading := by
  cases equal
  rfl

/-- The generic observation view preserves its SAME original evaluator, state, witness and possibility certificate. -/
theorem castAccuracy_asObservation (equal : first = last)
    (retained : Reading differential point sheet apart state rootObservation first) :
    HEq (retained.castAccuracy equal).asObservation retained.asObservation := by
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Reading

end
