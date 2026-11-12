module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints
public import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order

/-! # Both original endpoint samples of one retained checked Head

The two endpoint requests keep their original Points, denotations and global
numerator. The same physical cell supplies its retained inverse, power cache
and potential polynomial. A sufficient common floor pays the actual Head
stage, without casting a request or rebuilding any model or Point.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.Head

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive (regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveEndpoint)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedCell)
open Purelib.Data.Gaussian

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The two complete original endpoint samples on the same Head's physical inverse, powers and polynomial.

The exact pair preserves both original request owners and compilation
proofs. Its numerator equality is scalar; neither request nor cell is cast.
-/
abbrev EndpointSamples
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (globalCoefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points)
    (endpointTarget : Coordinate) {remaining : Type 3}
    (endpoints : EndpointRequests.Entry (floor := floor) data planned.2.1 globalCoefficient.val points
      endpointTarget remaining) :=
  PrimitiveEndpoint.Sample (depth := head.paid.2.2.2.2.val) endpoints.2.2.1
    head.attached.physical.cell.inverse head.attached.physical.cell.inverse_eq
    head.attached.physical.cell.powers head.attached.physical.cell.value
    (Cell.endpoint_compiled_of_numerator_eq (point := planned.2.1.point 0)
      head.attached.physical.cell (head.attached.physical.1.property.trans globalCoefficient.property.symm)) ×
  PrimitiveEndpoint.Sample (depth := head.paid.2.2.2.2.val) endpoints.2.2.2.1
    head.attached.physical.cell.inverse head.attached.physical.cell.inverse_eq
    head.attached.physical.cell.powers head.attached.physical.cell.value
    (Cell.endpoint_compiled_of_numerator_eq (point := planned.2.1.point 1)
      head.attached.physical.cell (head.attached.physical.1.property.trans globalCoefficient.property.symm))

/-- Sample both retained original endpoint requests at this Head's sufficient actual cell stage.

Each generic sampler selects one new root witness and same-model reading.
It reuses the supplied original Point, denotation, observation request,
numerator factor, model, powers and potential; no Point or model is rebuilt.
-/
def sampleEndpoints
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (globalCoefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points)
    (endpointTarget : Coordinate) {remaining : Type 3}
    (endpoints : EndpointRequests.Entry (floor := floor) data planned.2.1 globalCoefficient.val points
      endpointTarget remaining)
    (payment : Nat.max endpoints.2.2.1.source.stage endpoints.2.2.2.1.source.stage ≤ common)
    (positive : 0 < endpointTarget) :
    EndpointSamples data rest values planned regular globalCoefficient bounds accuracy physicalPaid common
      lifted points head endpointTarget endpoints :=
  have firstLater : endpoints.2.2.1.source.stage ≤ head.paid.2.2.2.2.val :=
    ((Data.Nat.Order.le_max_left _ _).trans payment).trans head.paid.floor_le
  have lastLater : endpoints.2.2.2.1.source.stage ≤ head.paid.2.2.2.2.val :=
    ((Data.Nat.Order.le_max_right _ _).trans payment).trans head.paid.floor_le
  let first := PrimitiveEndpoint.Sample.build
    (patch := data.terminal.neighborhood.patch) (count := count) (point := planned.2.1.point 0)
    (sample := endpoints.1.val) (pairs := (0 : Fin 3)) (numerator := globalCoefficient.val)
    (floor := floor) (target := endpointTarget) (depth := head.paid.2.2.2.2.val)
    endpoints.2.2.1
    head.attached.physical.cell.inverse head.attached.physical.cell.inverse_eq
    head.attached.physical.cell.powers head.attached.physical.cell.value
    (Cell.endpoint_compiled_of_numerator_eq (point := planned.2.1.point 0)
      head.attached.physical.cell (head.attached.physical.1.property.trans globalCoefficient.property.symm))
    (planned.2.1.point_inside data.segment.firstInside data.segment.lastInside
      (by decide +kernel : (0 : Coordinate) ≤ 0) (by decide +kernel : (0 : Coordinate) ≤ 1))
    firstLater positive
  let last := PrimitiveEndpoint.Sample.build
    (patch := data.terminal.neighborhood.patch) (count := count) (point := planned.2.1.point 1)
    (sample := endpoints.2.1.val) (pairs := (0 : Fin 3)) (numerator := globalCoefficient.val)
    (floor := floor) (target := endpointTarget) (depth := head.paid.2.2.2.2.val)
    endpoints.2.2.2.1
    head.attached.physical.cell.inverse head.attached.physical.cell.inverse_eq
    head.attached.physical.cell.powers head.attached.physical.cell.value
    (Cell.endpoint_compiled_of_numerator_eq (point := planned.2.1.point 1)
      head.attached.physical.cell (head.attached.physical.1.property.trans globalCoefficient.property.symm))
    (planned.2.1.point_inside data.segment.firstInside data.segment.lastInside
      (by decide +kernel : (0 : Coordinate) ≤ 1) (by decide +kernel : (1 : Coordinate) ≤ 1))
    lastLater positive
  ⟨first, last⟩

/-- Both actual physical polynomial endpoint values obey their original requested observation budgets. -/
theorem endpoint_errors_le
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (globalCoefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points)
    (endpointTarget : Coordinate) {remaining : Type 3}
    (endpoints : EndpointRequests.Entry (floor := floor) data planned.2.1 globalCoefficient.val points
      endpointTarget remaining)
    (observed : EndpointSamples data rest values planned regular globalCoefficient bounds accuracy physicalPaid common
      lifted points head endpointTarget endpoints) :
    Norm.Basic.normSq (head.attached.physical.cell.value.eval (planned.2.1.point 0) -
      endpoints.2.2.1.observation.reading.value) ≤ endpointTarget ∧
    Norm.Basic.normSq (head.attached.physical.cell.value.eval (planned.2.1.point 1) -
      endpoints.2.2.2.1.observation.reading.value) ≤ endpointTarget :=
  ⟨PrimitiveEndpoint.Sample.error_le endpoints.2.2.1 observed.1,
    PrimitiveEndpoint.Sample.error_le endpoints.2.2.2.1 observed.2⟩

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.Head

end
