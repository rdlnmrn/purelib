module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
public import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Riemann

public section

/-! Every basis primitive is compared on one retained root coordinate.
The reading request is independent of the eventual coefficient vector. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus index : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {point : Normalization.InverseRootPolynomial.Gaussian} {owner : Topology.SquareRootContinuationChain.Owner
    ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
  {overlap : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner} {box :
    Rational.Box}

set_option genInjectivity false in
/-- One original basis polynomial's endpoint and chart request on the exact retained root overlap.

Both entries retain the same root overlap, original basis sample and positive chart-reading target. -/
structure BasisChartEntry (overlap : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (target :
      Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original basis endpoint on the same retained root overlap. -/ endpoint :
    Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint overlap sample
  /-- The actual chart request for that exact retained endpoint. -/ request :
    Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.ChartRequest endpoint target floor

constructive_injectivity BasisChartEntry

/-- The actual retained chart requests for every original basis polynomial on one shared root overlap. -/
@[expose] def BasisChartEntries (overlap : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) :=
  Data.Vector.DependentVector (fun row : Fin genus =>
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartEntry overlap (polynomials.get row) target floor)

set_option genInjectivity false in
/-- A coefficient-independent chart comparison request retaining all original basis endpoints and one sufficient common
stage.

The individual original endpoint requests share the retained per-term allowance and a common maximum stage above the
supplied floor. -/
structure BasisChartRequest (overlap : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original coefficient-independent target is positive. -/ positive : 0 < target
  /-- The retained local allowance for each original basis polynomial. -/ tolerance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The local tolerance is the original aggregate allocation over the genus. -/ tolerance_eq : tolerance =
    Rational.Budget.Aggregate.perTerm target genus
  /-- The actual chart requests on the same retained overlap and original basis polynomials. -/ entries :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartEntries overlap polynomials tolerance floor
  /-- The common sufficient endpoint-reading stage. -/ stage : Nat
  /-- The stage is the maximum of the supplied floor and original retained entry stages. -/ stage_eq : stage = max floor
    (entries.maximum fun _ entry => entry.request.stage)

constructive_injectivity BasisChartRequest

namespace BasisChartRequest

variable {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box} {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Prepare every original basis endpoint on the same root overlap and cache their maximum sufficient stage. -/
@[expose] def build (overlap : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner) (polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest overlap polynomials target floor :=
  let tolerance := Rational.Budget.Aggregate.perTerm target genus
  let entries : Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartEntries overlap polynomials tolerance
    floor := Data.Vector.DependentVector.ofFn fun row =>
    let endpoint := Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint.build overlap (polynomials.get
      row)
    ⟨endpoint, Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.ChartRequest.build endpoint tolerance
      (Rational.Budget.Aggregate.perTerm_positive positive genus) floor⟩
  ⟨positive, tolerance, rfl, entries, max floor (entries.maximum fun _ entry => entry.request.stage), rfl⟩

/-- The common retained chart-reading stage meets the supplied floor.

The retained common stage is the original maximum of the supplied floor and the stages of its stored entry requests. -/
theorem floor_le (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest overlap
  polynomials target floor) : floor ≤ request.stage := by
  rw [request.stage_eq]
  exact Data.Nat.Order.le_max_left _ _

set_option genInjectivity false in
/-- The direct endpoint values and chart values share exactly the supplied
root reading; their discrepancy budget is cached for all coefficient vectors.

Direct values, chart values and their discrepancies are cached at the same retained coordinate and stage, with a
coefficient-independent paid weighted budget. -/
structure Evaluation (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest overlap
  polynomials target floor)
    (coordinate : Normalization.InverseRootPolynomial.Gaussian) (stage : Nat) where
  /-- The cached direct endpoint values on the shared original root coordinate. -/ direct : Data.Vector
    Normalization.InverseRootPolynomial.Gaussian genus
  /-- Each direct value is the original endpoint approximation at the retained stage. -/ direct_eq : ∀ row, direct row =
    ((request.entries.get row).endpoint.approximation).sample stage
  /-- The cached original basis polynomial values at the same root coordinate. -/ chart : Data.Vector
    Normalization.InverseRootPolynomial.Gaussian genus
  /-- Each chart value is the corresponding original polynomial evaluation. -/ chart_eq : ∀ row, chart row =
    (polynomials.get row).primitive.value.eval coordinate
  /-- The cached direct-minus-chart discrepancies for the original basis entries. -/ discrepancies :
    Data.Vector Normalization.InverseRootPolynomial.Gaussian genus
  /-- Each cached discrepancy is exactly the original direct value minus its chart value. -/ discrepancies_eq : ∀ row,
    discrepancies row = direct row - chart row
  /-- The coefficient-independent weighted-norm budget on the actual retained discrepancies. -/ budget :
    Readings.AffineBasisEnergy.WeightedNormBudget discrepancies
  /-- The original discrepancy budget scale fits the supplied target. -/ paid : budget.scale ≤ target

constructive_injectivity Evaluation

/-- Consume a retained coordinate from any differential on this exact owner.
No root is sampled a second time, and no equality of different owners is used.

Every row consumes the supplied original coordinate once; the original endpoint and chart readings provide the same
cached discrepancy budget. -/
@[expose] def evaluate (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest overlap
  polynomials target floor)
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {sample :
      Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
    {endpoint : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint overlap sample} {stage : Nat} (reading
      : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading endpoint stage)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (later : request.stage ≤
      stage) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest.Evaluation request reading.coordinate
      stage := open Purelib.Data.Rat in by
  let rows := Data.Vector.DependentVector.ofFn fun row : Fin genus =>
    let entry := request.entries.get row
    let root : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading entry.endpoint stage :=
      ⟨reading.coordinate, reading.coordinate_eq, reading.coordinate * entry.endpoint.coefficient, rfl⟩
    let after := (request.entries.get_le_maximum (fun _ entry => entry.request.stage) row).trans
      ((Data.Nat.Order.le_max_right _ _).trans (request.stage_eq.symm.trans_le later))
    (⟨root, entry.request.evaluate root after⟩ : (root :
      Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading entry.endpoint stage) ×
      entry.request.Evaluation root)
  let direct := Data.Vector.Basic.vectorOfFn fun row => (rows.get row).1.value
  let chart := Data.Vector.Basic.vectorOfFn fun row => (rows.get row).2.value
  let discrepancies := Data.Vector.Basic.vectorOfFn fun row => direct row - chart row
  let budget := Readings.AffineBasisEnergy.WeightedNormBudget.build discrepancies
  have directEq (row : Fin genus) : direct row = (request.entries.get row).endpoint.approximation.sample stage := by
    rw [Data.Vector.Basic.vectorOfFn_apply]
    exact (rows.get row).1.sample_eq
  have chartEq (row : Fin genus) : chart row = (polynomials.get row).primitive.value.eval reading.coordinate := by
    rw [Data.Vector.Basic.vectorOfFn_apply, (rows.get row).2.value_eq, branch, if_neg (show (1 : Nat) ≠ 0 by decide)]
    rw [(rows.get row).1.coordinate_eq, reading.coordinate_eq]
  have each (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq (discrepancies row) ≤ request.tolerance := by
    rw [Data.Vector.Basic.vectorOfFn_apply]
    dsimp only [direct, chart]
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
    exact (rows.get row).2.accurate.le
  have paid : budget.scale ≤ target := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [FiniteSum.Fin.Rational.sum_constant, request.tolerance_eq] at bound
    exact bound.trans (Rational.Budget.Aggregate.count_mul_perTerm_lt request.positive genus).le
  exact ⟨direct, directEq, chart, chartEq, discrepancies, Data.Vector.Basic.vectorOfFn_apply _, budget, paid⟩

/-- Homogeneous endpoint comparison, including the zero coefficient vector. -/
theorem Evaluation.accurate {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest
  overlap polynomials target floor}
    {coordinate : Normalization.InverseRootPolynomial.Gaussian} {stage : Nat} (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest.Evaluation request coordinate stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.direct row) -
      polynomials.value coefficients coordinate) ≤ target * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients := open Purelib.Data.Rat in by
  have readback : FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.direct row) -
      polynomials.value coefficients coordinate = FiniteSum.Fin.sumFin (fun row => coefficients row *
        evaluated.discrepancies row) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials.value
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    rw [evaluated.discrepancies_eq, evaluated.chart_eq]
    ring1
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  rw [readback]
  exact (evaluated.budget.bound coefficients).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct evaluated.paid nonnegative).trans_eq (by ring1))

/-- Owner transport alone controls the retained direct endpoint values. -/
theorem Evaluation.source_direct_accurate {request :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest overlap polynomials target floor}
    {coordinate : Normalization.InverseRootPolynomial.Gaussian} {stage : Nat} (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest.Evaluation request coordinate stage)
    (source : Data.Vector Normalization.InverseRootPolynomial.Gaussian genus)
    (bounded : ∀ row, Data.Gaussian.Norm.Basic.normSq (source row - evaluated.direct row) ≤ 4 * request.tolerance)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun row => coefficients row * source row) -
      FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.direct row)) ≤ 4 * target *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Data.Rat in by
  let errors := fun row => source row - evaluated.direct row
  let budget := Readings.AffineBasisEnergy.WeightedNormBudget.build errors
  have scale : budget.scale ≤ 4 * target := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ bounded)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [FiniteSum.Fin.Rational.sum_constant] at bound
    have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rational.Budget.Aggregate.count_mul_perTerm_lt request.positive genus).le (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
    rw [← request.tolerance_eq] at paid
    exact bound.trans ((show (genus : Normalization.InverseRootPolynomial.Coordinate) * ((genus :
      Normalization.InverseRootPolynomial.Coordinate) * (4 * request.tolerance)) =
      4 * ((genus : Normalization.InverseRootPolynomial.Coordinate) * ((genus :
        Normalization.InverseRootPolynomial.Coordinate) * request.tolerance)) by ring1).trans_le paid)
  have readback : FiniteSum.Fin.sumFin (fun row => coefficients row * source row) -
      FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.direct row) = FiniteSum.Fin.sumFin (fun row =>
        coefficients row * errors row) := by
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun row => by dsimp only [errors]; ring1)
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  rw [readback]
  exact (budget.bound coefficients).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct scale nonnegative).trans_eq (by ring1))

/-- Combine owner-transport bounds for the actual source pullback values
with the cached chart comparison. The tolerance is fixed before coefficients. -/
theorem Evaluation.source_accurate {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest
  overlap polynomials target floor}
    {coordinate : Normalization.InverseRootPolynomial.Gaussian} {stage : Nat} (evaluated :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest.Evaluation request coordinate stage)
    (source : Data.Vector Normalization.InverseRootPolynomial.Gaussian genus)
    (bounded : ∀ row, Data.Gaussian.Norm.Basic.normSq (source row - evaluated.direct row) ≤ 4 * request.tolerance)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun row => coefficients row * source row) -
      polynomials.value coefficients coordinate) ≤
      10 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Data.Rat in by
  have sourceClose := evaluated.source_direct_accurate source bounded coefficients
  exact (Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      sourceClose (evaluated.accurate coefficients))
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1))

end BasisChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings
