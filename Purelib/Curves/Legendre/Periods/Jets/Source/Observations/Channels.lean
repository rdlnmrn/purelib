module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation

/-! # Original six-channel query views with exact physical point and root readbacks

The selector reads the six fields of one existing observation bundle. The
root theorem consumes its complete original factory identity, preserving
the actual shared point and all six original query observations.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Normalization.ContinuedInverseRoot
open ContinuedNeighborhood (UniformBounds)

variable {parameter : Canonical} {count : Nat}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
variable {cache : Cache patch} {floor : Nat} {target allowance : Rational}
variable {request : Request cache floor target} {uniformBounds : UniformBounds patch} {uniformFloor : Nat}
variable {frame : Paths.Frame parameter} {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
variable {models : CellModels request start.coordinate finish.coordinate allowance}
variable {requests : IntegrandRequests uniformBounds uniformFloor (allowance / 4)} {input : Rational}

namespace CellModels.Observations

/-- Select the actual original observation on the corresponding original differential and spatial-model owners. -/
@[expose] def channel (observed : Observations frame lifted models requests input) :
    (index : Fin 6) → Jets.UniformObservation (Fibre.frameCurve frame) (Specification.Table.forms parameter index)
      lifted (models.cell index) input :=
  Fin.cases observed.valueZero (Fin.cases observed.valueOne
    (Fin.cases observed.firstZero (Fin.cases observed.firstOne
      (Fin.cases observed.secondZero (Fin.cases observed.secondOne (fun index => Fin.elim0 index))))))

/-- Any retained uniform pullback observation is at its original coordinate's SAME rational parameter. -/
private theorem pullback_point
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {polynomial : Algebra.Quadratic.Pair.Polynomial.Coefficients}
    (pullback : Spatial.Pullback coordinate polynomial allowance)
    {differential : Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Paths.polynomial parameter)}
    (observed : Jets.UniformObservation (Fibre.frameCurve frame) differential lifted pullback.model input) :
    observed.algebraic.point = coordinate.point input :=
  observed.algebraic.point_eq.trans
    ((pullback.observationPoint_eq observed.observation).trans (congrArg coordinate.point observed.parameter_eq))

/-- Every selected actual observation uses the SAME shared physical coordinate and original queried parameter. -/
theorem channel_point (observed : Observations frame lifted models requests input) (index : Fin 6) :
    (observed.channel index).algebraic.point = models.coordinate.point input := by
  refine Fin.cases (pullback_point models.valueZero observed.valueZero) ?_ index
  intro index
  refine Fin.cases (pullback_point models.valueOne observed.valueOne) ?_ index
  intro index
  refine Fin.cases (pullback_point models.firstZero observed.firstZero) ?_ index
  intro index
  refine Fin.cases (pullback_point models.firstOne observed.firstOne) ?_ index
  intro index
  refine Fin.cases (pullback_point models.secondZero observed.secondZero) ?_ index
  intro index
  exact Fin.cases (pullback_point models.secondOne observed.secondOne) (fun index => Fin.elim0 index) index

end CellModels.Observations

namespace Cell.Query

variable {cell : Cell (parameter := parameter) lifted}
variable (query : Query cell) (frame : Paths.Frame parameter) (input : Rational)
variable (lower : 0 ≤ input) (upper : input ≤ 1)

/-- Each selected root of the actual six-channel factory is its one original shared retained point certificate. -/
private theorem factory_channel_root (index : Fin 6) :
    ((query.observe frame input lower upper).channel index).algebraic.sheetValue.value.name =
      (query.observe frame input lower upper).retained.sample.certificate.value.name := by
  have sample := congrArg (fun retained : ContinuedNeighborhood.Point cell.patch
    (cell.models.coordinate.point input) => retained.certificate.value.name)
    (query.observe_sample frame input lower upper)
  refine Fin.cases ((query.observe_valueZero_root_name frame input lower upper).trans sample.symm) ?_ index
  intro index
  refine Fin.cases ((query.observe_valueOne_root_name frame input lower upper).trans sample.symm) ?_ index
  intro index
  refine Fin.cases ((query.observe_firstZero_root_name frame input lower upper).trans sample.symm) ?_ index
  intro index
  refine Fin.cases ((query.observe_firstOne_root_name frame input lower upper).trans sample.symm) ?_ index
  intro index
  refine Fin.cases ((query.observe_secondZero_root_name frame input lower upper).trans sample.symm) ?_ index
  intro index
  exact Fin.cases ((query.observe_secondOne_root_name frame input lower upper).trans sample.symm)
    (fun index => Fin.elim0 index) index

/-- Read the original common root from an already retained six-channel bundle and its whole raw-factory identity.

The input is the old bundle, with its actual point, states and readings.
Its equality to the original query factory transports only this named
readback; the observer is not run again.
-/
theorem channel_root_name
    (observed : CellModels.Observations frame lifted cell.models query.requests input)
    (factory_eq : observed = query.observe frame input lower upper) (index : Fin 6) :
    (observed.channel index).algebraic.sheetValue.value.name = observed.retained.sample.certificate.value.name := by
  cases factory_eq
  exact factory_channel_root query frame input lower upper index

end Cell.Query

end Purelib.Curves.Legendre.Periods.Jets.Source

end
