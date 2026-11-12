module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Bounds
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservation.Rows
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Transport
import Purelib.Data.Fin.Two
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # One common request and fixed-box bounds for all four actual arithmetic rows

The same actual Joint and independently paid bank supply both derivative
orders at both coordinates. Exact whole-request equality transports the
original Reading records. Original value/first ceilings provide numerical
bounds without a new query, caller inverse box or desired remainder input.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter increment point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} {step : Step source increment} {nonzero : increment ≠ 0}
    {sourceAdditional targetAdditional spatial : AccuracyRequest}

/-- Read the SAME three complete original Readings at their exactly equal whole common request index.

The original selected states, observations, displayed witnesses, coefficient
processes and arithmetic comparisons are transported unchanged. Equality
of the entire AccuracyRequest is required; no smaller tolerance is assigned
to an old observation by this operation.
-/
@[expose] def rowNumericsAtCommon (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (order coordinate : Fin 2) :=
  let equal := retained.minimum_accuracy spatial
  let numerics := paid.rowNumerics order coordinate
  (numerics.1.castAccuracy equal, numerics.2.1.castAccuracy equal, numerics.2.2.castAccuracy equal)

/-- The selected numerical base is the identical actual source witness under the exact common-request transport. -/
theorem rowCommon_base (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).base =
      (retained.rowNumericsAtCommon paid order coordinate).1.reading :=
  (paid.rowCertificate_base order coordinate).trans
    ((paid.rowNumerics order coordinate).1.castAccuracy_reading (retained.minimum_accuracy spatial)).symm

/-- The selected output is the same independent target witness after the exact whole-request index transport. -/
theorem rowCommon_output (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).output =
      (retained.rowNumericsAtCommon paid order coordinate).2.1.reading :=
  (paid.rowCertificate_output order coordinate).trans
    ((paid.rowNumerics order coordinate).2.1.castAccuracy_reading (retained.minimum_accuracy spatial)).symm

/-- The selected slope remains the actual independent derivative witness at that SAME common request. -/
theorem rowCommon_slope (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).slope =
      (retained.rowNumericsAtCommon paid order coordinate).2.2.reading :=
  (paid.rowCertificate_slope order coordinate).trans
    ((paid.rowNumerics order coordinate).2.2.castAccuracy_reading (retained.minimum_accuracy spatial)).symm

/-- Select the original fixed physical-box value or first ceiling for the original adjacent-derivative row. -/
@[expose] def rowCeiling (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (increment : Canonical) (order coordinate : Fin 2) : Rational :=
  Fin.cases (valueCeiling patch increment coordinate)
    (Fin.cases (firstCeiling patch increment coordinate) (fun index => Fin.elim0 index)) order

/-- Every selected original fixed-box row ceiling is nonnegative without a selected node or stage. -/
theorem rowCeiling_nonnegative (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (increment : Canonical) (order coordinate : Fin 2) : 0 ≤ rowCeiling patch increment order coordinate := by
  rcases Data.Fin.Two.finTwo_cases order with equal | equal
  · subst order
    exact valueCeiling_nonnegative patch increment coordinate
  · subst order
    exact firstCeiling_nonnegative patch increment coordinate

/-- The numerical row ceiling is independent of increment indices while its original source patch remains fixed. -/
theorem rowCeiling_increments (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (firstIncrement lastIncrement : Canonical) (order coordinate : Fin 2) :
    rowCeiling patch firstIncrement order coordinate = rowCeiling patch lastIncrement order coordinate := by
  rcases Data.Fin.Two.finTwo_cases order with equal | equal
  · subst order
    exact Arithmetic.valueCeiling_parameters parameter firstIncrement parameter lastIncrement coordinate
      patch.box patch.rootLower patch.rootLower (4 * patch.rootLower)
  · subst order
    exact Arithmetic.firstCeiling_parameters parameter firstIncrement parameter lastIncrement coordinate
      patch.box (inverseBox patch) patch.rootLower patch.rootLower (4 * patch.rootLower)

/-- Each actual selected certificate has the original fixed-box ceiling on the SAME retained scalar and paid bank. -/
theorem row_factor_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (order coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    (paid.rowCertificate order coordinate).factor ≤ rowCeiling patch increment order coordinate := by
  rcases Data.Fin.Two.finTwo_cases order with equal | equal
  · subst order
    exact retained.value_factor_le paid coordinate inside
  · subst order
    exact retained.first_factor_le paid coordinate inside

/-- The same original common-request readings satisfy the computed fixed-box parameter-fourth remainder. -/
theorem rowCommon_remainder_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (order coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    Canonical.normSq ((retained.rowNumericsAtCommon paid order coordinate).2.1.reading -
      (retained.rowNumericsAtCommon paid order coordinate).1.reading -
      increment * (retained.rowNumericsAtCommon paid order coordinate).2.2.reading) ≤
      rowCeiling patch increment order coordinate * Canonical.normSq increment ^ 2 := by
  have bound := (paid.rowCertificate order coordinate).remainder_le
  rewrite [← (paid.rowCertificate order coordinate).expansion, retained.rowCommon_base paid order coordinate,
    retained.rowCommon_output paid order coordinate, retained.rowCommon_slope paid order coordinate] at bound
  exact bound.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (retained.row_factor_le paid order coordinate inside)
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct (Canonical.normSq increment)))

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

end
