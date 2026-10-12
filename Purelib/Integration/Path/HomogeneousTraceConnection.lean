module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Compose paid homogeneous trace bounds on their literal increment paths.
Shared endpoint potentials telescope; the polygon area remains in the trace. -/
namespace Purelib.Integration.Path.HomogeneousTraceConnection

open Purelib.Integration.Path.IncrementArea (Gaussian Coordinate Summary traceArea)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Integration.Path in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
set_option genInjectivity false in
/-- A retained increment summary and corrected trace with a coefficient-homogeneous lower energy bound.

The exact path, endpoint potentials and coefficient vector remain indexed; the retained total equals the endpoint
displacement and the corrected value keeps its defining trace equation. -/
structure HomogeneousTrace {genus : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (path : List IncrementArea.Gaussian) (first last firstPotential lastPotential : IncrementArea.Gaussian) (loss :
      IncrementArea.Coordinate) where
  /-- The retained summary of the exact original increment list. -/ summary : IncrementArea.Summary path
  /-- The retained total equals the original last-minus-first displacement. -/ total_eq : summary.total = last - first
  /-- The cached original path trace. -/ trace : IncrementArea.Gaussian
  /-- The cached trace equals the trace area of the original path at its original first point. -/ trace_eq : trace =
    IncrementArea.traceArea first path
  /-- The cached trace corrected by the original endpoint potentials. -/ corrected : IncrementArea.Gaussian
  /-- The correction is the negative trace plus last potential minus first potential. -/ corrected_eq : corrected =
    -trace + lastPotential - firstPotential
  /-- One quarter of the corrected imaginary part is bounded below by the negative retained coefficient-weighted loss.
  -/ lower : -(loss * PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ corrected.im / 4

constructive_injectivity HomogeneousTrace

namespace HomogeneousTrace

variable {genus : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {first middle last firstPotential middlePotential lastPotential : Purelib.Integration.Path.IncrementArea.Gaussian}
  {firstPath lastPath : List Purelib.Integration.Path.IncrementArea.Gaussian} {firstLoss lastLoss :
    Purelib.Integration.Path.IncrementArea.Coordinate}

open Purelib.Integration.Path in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- Construct the zero-loss empty trace at the exact original endpoint and potential. -/
def empty (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (first firstPotential :
  IncrementArea.Gaussian) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients [] first first firstPotential firstPotential 0 := by
  refine ⟨Summary.build [], ?_, 0, rfl, 0, ?_, ?_⟩
  · change (0 : IncrementArea.Gaussian) = first - first; ring1
  · ring1
  · change -((0 : IncrementArea.Coordinate) * PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ 0 / 4
    rw [show -((0 : IncrementArea.Coordinate) * PreparedObservationCoercivity.coefficientNormSq coefficients) = 0 by
      ring1]
    decide

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- Concatenate two retained traces at their shared endpoint and potential, adding their exact losses.

The original ordered paths, summaries and coefficient vector are reused, and the corrected trace adds without replacing
either input owner. -/
def append (left : HomogeneousTraceConnection.HomogeneousTrace coefficients firstPath first middle firstPotential
  middlePotential firstLoss)
    (right : HomogeneousTraceConnection.HomogeneousTrace coefficients lastPath middle last middlePotential lastPotential
      lastLoss) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients (firstPath ++ lastPath) first last firstPotential
      lastPotential (firstLoss + lastLoss) := by
  let summary := left.summary.append right.summary
  have totalEq : summary.total = last - first := by
    change left.summary.total + right.summary.total = _
    rw [left.total_eq, right.total_eq]
    ring1
  have traceEq : left.trace + right.trace = IncrementArea.traceArea first (firstPath ++ lastPath) := by
    rw [IncrementArea.traceArea_append, ← left.summary.total_eq, left.total_eq,
      show first + (middle - first) = middle by ring1, ← left.trace_eq, ← right.trace_eq]
  have correctedEq : left.corrected + right.corrected = -(left.trace + right.trace) + lastPotential - firstPotential :=
    by
    rw [left.corrected_eq, right.corrected_eq]
    ring1
  have lower := Fraction.Order.Arithmetic.add_le_add_direct left.lower right.lower
  have leftEq : -(firstLoss * PreparedObservationCoercivity.coefficientNormSq coefficients) + -(lastLoss *
    PreparedObservationCoercivity.coefficientNormSq coefficients) =
      -((firstLoss + lastLoss) * PreparedObservationCoercivity.coefficientNormSq coefficients) := by ring1
  have rightEq : left.corrected.im / 4 + right.corrected.im / 4 = (left.corrected + right.corrected).im / 4 := by
    rw [Basic.add_im]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  exact ⟨summary, totalEq, left.trace + right.trace, traceEq, left.corrected + right.corrected, correctedEq,
    leftEq.symm.trans_le (lower.trans_eq rightEq)⟩

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.Topology in
/-- A bounded potential return transfers the corrected lower bound to the negative original trace.

The extra nonnegative allowance is scaled by the original coefficient norm squared, and its squared return estimate
retains the exact factor four. -/
theorem trace_lower {path : List IncrementArea.Gaussian} {loss : IncrementArea.Coordinate}
    (connection : HomogeneousTraceConnection.HomogeneousTrace coefficients path first last firstPotential lastPotential
      loss)
    (allowance : IncrementArea.Coordinate) (nonnegative : 0 ≤ allowance)
    (returned : Data.Gaussian.Norm.Basic.normSq (lastPotential - firstPotential) ≤ (4 * allowance) ^ 2 *
      (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2) :
    -((loss + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ (-IncrementArea.traceArea
      first path).im / 4 := by
  have coefficientNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : IncrementArea.Coordinate)) _ (fun row => by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using (Norm.Basic.normSq_nonneg (coefficients row))))
  have error : Data.Gaussian.Norm.Basic.normSq (connection.corrected - (-connection.trace)) ≤ (4 * (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    rw [connection.corrected_eq, show (-connection.trace + lastPotential - firstPotential) - (-connection.trace) =
      lastPotential - firstPotential by ring1]
    exact returned.trans_eq (by ring1)
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le connection.corrected (-connection.trace)
    (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative) error
  have bound := (Fraction.Order.Arithmetic.sub_le_sub_right_direct connection.lower (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)).trans comparison
  rw [connection.trace_eq] at bound
  exact (show -((loss + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -(loss * PreparedObservationCoercivity.coefficientNormSq coefficients) - allowance *
      PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le bound

end HomogeneousTrace
end Purelib.Integration.Path.HomogeneousTraceConnection
