module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Reobservation
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Bounds
public import Purelib.Geometry.Rational.Box.Square.Centered.Norm
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Original-box ceilings for the same jointly paid arithmetic Taylor banks

All three candidate margins come from the ONE original continued source box.
Its fixed physical box bounds the original coefficient tables. Its positive
root floor constructs an explicit reciprocal box internally. The actual new
independently paid readings and the old scalar inverse/cubic cache retain the
same finite Taylor factors, independently of query time or request stages.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter increment point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} {step : Step source increment} {nonzero : increment ≠ 0}
    {sourceAdditional targetAdditional spatial : AccuracyRequest}

/-- The same original source box gives one positive fourfold paired-root margin. -/
private theorem sumFloor_positive (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) :
    0 < 4 * patch.rootLower :=
  Order.Arithmetic.mul_pos_direct (by decide +kernel) patch.rootLower_positive

/-- The original seed floor computes one explicit box for all possible source and target reciprocal readings. -/
@[expose] def inverseBox (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) : Box :=
  Box.Square.Centered.normBox patch.rootLower⁻¹ (Order.Field.inv_pos_direct patch.rootLower_positive).le

/-- The reciprocal of every candidate of the SAME retained source observation lies in the original computed box. -/
theorem sourceInverse_contains (retained : Joint step nonzero sourceAdditional targetAdditional)
    {candidate : Canonical} (possible : retained.core.sourceSample.observation.Possible candidate) :
    (inverseBox patch).Contains candidate⁻¹ := by
  have lower := retained.core.clearance.sourceLower possible
  rewrite [retained.core_sourceFloor] at lower
  exact Box.Square.Centered.normBox_contains (Order.Field.inv_pos_direct patch.rootLower_positive).le
    (Norm.Reciprocal.normSq_le patch.rootLower_positive lower)

/-- The independently selected target candidates obey the SAME original source-box reciprocal enclosure. -/
theorem targetInverse_contains (retained : Joint step nonzero sourceAdditional targetAdditional)
    {candidate : Canonical} (possible : retained.core.targetSample.observation.Possible candidate) :
    (inverseBox patch).Contains candidate⁻¹ := by
  have lower := retained.core.clearance.targetLower possible
  rewrite [retained.core_targetFloor] at lower
  exact Box.Square.Centered.normBox_contains (Order.Field.inv_pos_direct patch.rootLower_positive).le
    (Norm.Reciprocal.normSq_le patch.rootLower_positive lower)

/-- The actual source anchor's reciprocal belongs to that same internally computed box. -/
theorem sourceInverse_reading (retained : Joint step nonzero sourceAdditional targetAdditional) :
    (inverseBox patch).Contains retained.core.sourceSample.reading⁻¹ :=
  retained.sourceInverse_contains retained.core.sourceSample.observation.witness_possible

/-- The distinct target anchor's reciprocal belongs to the identical internally computed box. -/
theorem targetInverse_reading (retained : Joint step nonzero sourceAdditional targetAdditional) :
    (inverseBox patch).Contains retained.core.targetSample.reading⁻¹ :=
  retained.targetInverse_contains retained.core.targetSample.observation.witness_possible

/-- Compute the value-row factor ceiling from the SAME original physical box and its three root margins. -/
@[expose] def valueCeiling (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (increment : Canonical) (coordinate : Fin 2) : Rational :=
  Arithmetic.valueCeiling parameter increment coordinate patch.box patch.rootLower patch.rootLower (4 * patch.rootLower)

/-- Compute the first-row factor ceiling with the original physical box and internally constructed reciprocal box. -/
@[expose] def firstCeiling (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (increment : Canonical) (coordinate : Fin 2) : Rational :=
  Arithmetic.firstCeiling parameter increment coordinate patch.box (inverseBox patch)
    patch.rootLower patch.rootLower (4 * patch.rootLower)

/-- The computed value-row factor ceiling is nonnegative on the original continued neighborhood. -/
theorem valueCeiling_nonnegative (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (increment : Canonical) (coordinate : Fin 2) : 0 ≤ valueCeiling patch increment coordinate :=
  Arithmetic.valueCeiling_nonnegative parameter increment coordinate patch.box
    patch.rootLower_positive patch.rootLower_positive (sumFloor_positive patch)

/-- The computed first-row ceiling is nonnegative, with no externally supplied inverse enclosure. -/
theorem firstCeiling_nonnegative (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (increment : Canonical) (coordinate : Fin 2) : 0 ≤ firstCeiling patch increment coordinate :=
  Arithmetic.firstCeiling_nonnegative parameter increment coordinate patch.box (inverseBox patch)
    patch.rootLower_positive patch.rootLower_positive (sumFloor_positive patch)

/-- Every actual independently reobserved value certificate obeys the fixed original-box ceiling.

The factor equality concerns the same scalar core and actual candidate
floors. Both old and new arithmetic observations, their original evaluator
caches and operational comparisons remain distinct retained data.
-/
theorem value_factor_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    (paid.valueCertificate coordinate).factor ≤ valueCeiling patch increment coordinate := by
  have bound := retained.arithmetic.value_factor_le coordinate inside
  rewrite [retained.core_sourceFloor, retained.core_targetFloor, retained.core_sumFloor] at bound
  rewrite [paid.valueCertificate_factor_eq coordinate]
  exact bound

/-- Every actual new first-row certificate retains its old inverse/cubic caches and obeys the same fixed-box ceiling. -/
theorem first_factor_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    (paid.firstCertificate coordinate).factor ≤ firstCeiling patch increment coordinate := by
  have bound := retained.arithmetic.first_factor_le coordinate inside
    retained.sourceInverse_reading retained.targetInverse_reading
  rewrite [retained.core_sourceFloor, retained.core_targetFloor, retained.core_sumFloor] at bound
  rewrite [paid.firstCertificate_factor_eq coordinate]
  exact bound

/-- The SAME new value readings have an explicit parameter-fourth remainder with no time- or stage-dependent factor. -/
theorem value_remainder_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    Canonical.normSq ((paid.targetValue.get coordinate).requested.reading -
      (paid.sourceValue.get coordinate).requested.reading -
      increment * (paid.sourceFirst.get coordinate).requested.reading) ≤
      valueCeiling patch increment coordinate * Canonical.normSq increment ^ 2 :=
  (paid.value_remainder_le coordinate).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (retained.value_factor_le paid coordinate inside)
      (Order.Arithmetic.sq_nonneg_direct (Canonical.normSq increment)))

/-- The SAME new first readings retain their independent second slope and the computed uniform parameter remainder. -/
theorem first_remainder_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    Canonical.normSq ((paid.targetFirst.get coordinate).requested.reading -
      (paid.sourceFirst.get coordinate).requested.reading -
      increment * (paid.sourceSecond.get coordinate).requested.reading) ≤
      firstCeiling patch increment coordinate * Canonical.normSq increment ^ 2 :=
  (paid.first_remainder_le coordinate).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (retained.first_factor_le paid coordinate inside)
      (Order.Arithmetic.sq_nonneg_direct (Canonical.normSq increment)))

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

end
