module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaReplacement
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Integration.Path.HomogeneousTraceConnection
public import Purelib.Integration.Path.HomogeneousIncrementRestoration
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Restore a certified homogeneous trace through retained source endpoints.
Only endpoint detours and the incoming potential comparison add new loss. -/
namespace Purelib.Integration.Path.HomogeneousTraceRestoration

open Purelib.Integration.Path.IncrementArea (Gaussian Coordinate Summary traceArea)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Integration.Path.HomogeneousTraceConnection (HomogeneousTrace)

open Purelib.Integration.Path in
/-- Insert the exact incoming, chart and outgoing connectors around the original increment list. -/
def sourceRestoredPath (path : List IncrementArea.Gaussian) (first last firstSource lastSource lastOld previous :
  IncrementArea.Gaussian) : List Gaussian :=
  (firstSource - previous) :: (((first - firstSource) :: (path ++ [lastSource - last])) ++ [lastOld - lastSource])

namespace HomogeneousTrace

variable {genus : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {path : List Purelib.Integration.Path.IncrementArea.Gaussian} {first last firstPotential lastPotential :
    Purelib.Integration.Path.IncrementArea.Gaussian} {loss : Purelib.Integration.Path.IncrementArea.Coordinate}

open Purelib.Integration.Path in
/-- The corrected trace is the negative summary area and endpoint area plus the original potential difference. -/
public theorem corrected_summary (connection : HomogeneousTraceConnection.HomogeneousTrace coefficients path first last
  firstPotential lastPotential loss) :
    connection.corrected = -connection.summary.area - BoundaryRibbon.area first last + lastPotential - firstPotential :=
      by
  rw [connection.corrected_eq, connection.trace_eq, IncrementArea.traceArea_eq,
    ← connection.summary.area_eq, ← connection.summary.total_eq, connection.total_eq,
    BoundaryRibbon.area_sub_self_right]
  ring1

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.Topology in
/-- Restore a retained homogeneous trace to its original source and old-point endpoints with a paid additional loss.

The construction reuses the exact original summary, connector geometry and coefficient vector. Separate target, joining
and incoming-potential estimates certify the restored trace and its original allowance payment. -/
def restore (connection : HomogeneousTraceConnection.HomogeneousTrace coefficients path first last firstPotential
  lastPotential loss)
    (firstSource lastSource firstOld lastOld previous previousPotential : IncrementArea.Gaussian)
    {target joining : IncrementArea.Coordinate}
    (targetNonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1)
    (firstSourceBound : Data.Gaussian.Norm.Basic.normSq (firstSource - firstOld) ≤ joining *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (lastSourceBound : Data.Gaussian.Norm.Basic.normSq (lastOld - lastSource) ≤ joining *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (firstChartBound : Data.Gaussian.Norm.Basic.normSq (first - firstSource) ≤ 4 * target *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (lastChartBound : Data.Gaussian.Norm.Basic.normSq (lastSource - last) ≤ 4 * target *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (gap : Data.Gaussian.Norm.Basic.normSq (firstOld - previous) ≤ joining *
      PreparedObservationCoercivity.coefficientNormSq
      coefficients)
    (joined : Data.Gaussian.Norm.Basic.normSq (IncrementRestoration.potential firstPotential first firstOld -
      previousPotential - BoundaryRibbon.area previous firstOld) ≤
      (80 * target + 2 * joining) * (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2)
    (allowance : IncrementArea.Coordinate) (nonnegative : 0 ≤ allowance)
    (paid : 416 * target + 20 * joining ≤ (4 * allowance) ^ 2) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients (HomogeneousTraceRestoration.sourceRestoredPath path first
      last firstSource lastSource lastOld previous)
      previous lastOld previousPotential (IncrementRestoration.potential lastPotential last lastOld) (loss + allowance)
        := by
  let core := IncrementAreaReplacement.bracket connection.summary (first - firstSource) (lastSource - last)
  let summary := IncrementAreaReplacement.bracket core (firstSource - previous) (lastOld - lastSource)
  have total : summary.total = lastOld - previous := by
    dsimp only [summary, core]
    rw [IncrementAreaReplacement.bracket_total, IncrementAreaReplacement.bracket_total, connection.total_eq]
    ring1
  let trace := summary.area + BoundaryRibbon.area previous summary.total
  have traceEq : trace = IncrementArea.traceArea previous (HomogeneousTraceRestoration.sourceRestoredPath path first
    last firstSource lastSource lastOld previous) := by
    rw [HomogeneousTraceRestoration.sourceRestoredPath, IncrementArea.traceArea_eq, ← summary.area_eq, ←
      summary.total_eq]
  let lastRestoredPotential := IncrementRestoration.potential lastPotential last lastOld
  let corrected := -trace + lastRestoredPotential - previousPotential
  have discrepancy : connection.corrected - corrected =
      IncrementRestoration.detour first last firstSource lastSource firstOld lastOld previous -
        (IncrementRestoration.potential firstPotential first firstOld - previousPotential - BoundaryRibbon.area previous
          firstOld) := by
    have identity := IncrementRestoration.restored_discrepancy connection.summary first last firstSource lastSource
      firstOld lastOld previous
      firstPotential lastPotential previousPotential connection.corrected connection.total_eq
    change connection.corrected - (-IncrementArea.traceArea previous (HomogeneousTraceRestoration.sourceRestoredPath
      path first last firstSource lastSource lastOld previous) +
      lastRestoredPotential - previousPotential) = _ at identity
    rw [← traceEq] at identity
    have zero : connection.corrected - (-connection.summary.area - BoundaryRibbon.area first last + lastPotential -
      firstPotential) = 0 := by
      rw [corrected_summary connection]
      ring1
    rw [zero, _root_.zero_add] at identity
    exact identity
  have detourBound := HomogeneousIncrementRestoration.detour_bound_homogeneous targetNonnegative joinNonnegative
    joinSmall
    firstSourceBound lastSourceBound firstChartBound lastChartBound gap
  have error := (Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct detourBound
      joined) (by decide : (0 : IncrementArea.Coordinate) ≤ 2))
  have bounded : Data.Gaussian.Norm.Basic.normSq (connection.corrected - corrected) ≤ (4 * (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    rw [discrepancy]
    exact (error.trans_eq (show 2 * ((128 * target + 8 * joining) * (PreparedObservationCoercivity.coefficientNormSq
      coefficients) ^ 2 +
      (80 * target + 2 * joining) * (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2) =
      (416 * target + 20 * joining) * (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 by
        ring1)).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid (Fraction.Order.Arithmetic.sq_nonneg_direct
        _)).trans_eq (by ring1))
  have coefficientNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : IncrementArea.Coordinate)) _ (fun row =>
      Basic.Canonical.normSq_nonneg (coefficients row)))
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le connection.corrected corrected
    (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative) bounded
  have lower := (Fraction.Order.Arithmetic.sub_le_sub_right_direct connection.lower (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison
  exact ⟨summary, total, trace, traceEq, corrected, rfl,
    (show -((loss + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients) =
      -(loss * PreparedObservationCoercivity.coefficientNormSq coefficients) - allowance *
        PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le lower⟩

end HomogeneousTrace
end Purelib.Integration.Path.HomogeneousTraceRestoration
