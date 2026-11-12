module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Uniform
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order
import Purelib.Data.Except

/-! # Requested preparation of the same physical primitive cell

The original integral selection and uniform odd-reading request are retained
once for the actual new numerator. Checking their two finite stages either
certifies the supplied old cell using genuine original continued Points, or
returns the exact unpaid floor. Neither branch refines an old model or
changes its stage, and the finite regular-model residual remains separate.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve (reciprocalCurve)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box half)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point UniformRequest)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Data.Gaussian

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {count : Nat} {center : Gaussian}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {sourceDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {comparison : TerminalComparison.Data terminal sourceDifferential}
    {preparation : PotentialComparison.Preparation comparison}
    {numerator : Polynomial} {index : Nat} {regularBox : Box}
    {first last : LiftedPoint 2} {coordinate : Spatial.Coordinate first.coordinate last.coordinate}
    {stage : Nat} {allowance : Coordinate} {positive : 0 < allowance}
    {sample : PolynomialSample cap numerator index regularBox}
    {retained : Cell preparation.2.1 coordinate stage allowance positive.le}

/-- The two original paid requests for the actual physical primitive numerator and original retained source box. -/
@[expose] def Requests (data : PhysicalPrimitive sample retained) (floor : Nat) (target : Coordinate) : Type _ :=
  Selection (2 * Norm.Basic.normSq coordinate.displacement * data.2.2.1.scale) floor target ×
    UniformRequest preparation.2.2 1 (data.2.2.1.coefficient.scale half) floor (allowance / 4)

/-- Select the integral and uniform-reading floors once without constructing another inverse, cube or preparation.

The supplied cell and P sample remain unchanged. These requests can ask for
stages later than that fixed cell; the checked preparation below retains
such a request as an unpaid finite floor rather than silently refining it.
-/
def requests (data : PhysicalPrimitive sample retained) (floor : Nat) (target : Coordinate)
    (targetPositive : 0 < target) : Requests (positive := positive) data floor target :=
  let integral := Cell.choose data.2.2.1 coordinate floor target targetPositive
  let quarterPositive := Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let uniform := preparation.2.2.request 1 (data.2.2.1.coefficient.scale half) floor (allowance / 4) quarterPositive
  ⟨integral, uniform⟩

/-- The whole request factory contains the two exact original selections and no cell-model factory. -/
private theorem packaged_requests_factory (data : PhysicalPrimitive sample retained) (floor : Nat)
    (target : Coordinate) (targetPositive : 0 < target) :
    requests (positive := positive) data floor target targetPositive =
      (let integral := Cell.choose data.2.2.1 coordinate floor target targetPositive
       let quarterPositive := Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       let uniform := preparation.2.2.request 1 (data.2.2.1.coefficient.scale half) floor
         (allowance / 4) quarterPositive
       ⟨integral, uniform⟩ : Requests (positive := positive) data floor target) := by rfl

/-- The whole request factory contains the two exact original selections and no cell-model factory. -/
theorem requests_factory (data : PhysicalPrimitive sample retained) (floor : Nat)
    (target : Coordinate) (targetPositive : 0 < target) :
    requests (positive := positive) data floor target targetPositive =
      (let integral := Cell.choose data.2.2.1 coordinate floor target targetPositive
       let quarterPositive := Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       let uniform := preparation.2.2.request 1 (data.2.2.1.coefficient.scale half) floor
         (allowance / 4) quarterPositive
       ⟨integral, uniform⟩ : Requests (positive := positive) data floor target) :=
  packaged_requests_factory (positive := positive) data floor target targetPositive

variable {floor : Nat} {target : Coordinate}

/-- The original successful physical check certificate, both actual stage payments and its finite integral accuracy. -/
@[expose] def Accepted (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := positive) data floor target) (lifted : LiftedCell first last) : Type _ :=
  { _certificate : Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame))
        data.2.2.1.differential lifted data.cell.pullback.model //
    paid.1.stage ≤ stage ∧ paid.2.selection.stage ≤ stage ∧
      Norm.Basic.normSq (data.cell.value.eval last.coordinate - data.cell.value.eval first.coordinate -
        data.cell.pullback.model.integralSample) < target }

/-- A checked preparation retains its original query certificate and both actual paid stage inequalities.

The failure value is the actual maximum of the two retained request stages.
The error bound refers only to the finite primitive increment versus this same
cell's computed integral. It does not discard the independent P-model
residual in the comparison with the regular remainder.
-/
@[expose] def Preparation (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := positive) data floor target)
    (lifted : LiftedCell first last) : Type _ :=
  Except
    { future : Nat // future = Nat.max paid.1.stage paid.2.selection.stage ∧ stage < future }
    (Accepted (positive := positive) data paid lifted)

/-- Check the same supplied cell against both retained requests and construct its original source certificate if paid.

Failure retains the exact computed common floor and proves that it lies
strictly beyond the actual supplied stage. Success uses the supplied Point
family directly; only the original certificate's query operation requests new root readings.
No Point, preparation, inverse or power bank is reacquired here.
-/
def check (data : PhysicalPrimitive sample retained) (paid : Requests (positive := positive) data floor target)
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    Preparation (positive := positive) data paid lifted :=
  let required := Nat.max paid.1.stage paid.2.selection.stage
  if stagePaid : required ≤ stage then
    have integralPaid := (Data.Nat.Order.le_max_left _ _).trans stagePaid
    have uniformPaid := (Data.Nat.Order.le_max_right _ _).trans stagePaid
    let certificate := Cell.certificate (curve := reciprocalCurve (Fibre.frameCurve frame))
      (patch := terminal.neighborhood.patch) (root := comparison.rootBounds)
      (residual := terminal.preparation.reciprocal) (primitive := data.2.1)
      (bounds := data.2.2.1) (uniform := preparation.2.2) (coordinate := coordinate)
      (first := first) (last := last) (depth := stage) (floor := floor) (allowance := allowance)
      (positive := positive) (request := paid.2) data.cell lifted firstInside lastInside points uniformPaid
    have accurate := Cell.accurate (root := comparison.rootBounds)
      (residual := terminal.preparation.reciprocal) (primitive := data.2.1)
      (bounds := data.2.2.1) (coordinate := coordinate) (stage := stage) (allowance := allowance)
      (nonnegative := positive.le) data.cell paid.1 integralPaid
        (terminal.neighborhood.patch.box_refines.contains firstInside)
        (terminal.neighborhood.patch.box_refines.contains lastInside)
    .ok ⟨certificate, integralPaid, uniformPaid, accurate⟩
  else .error ⟨required, rfl, Nat.lt_of_not_ge stagePaid⟩

/-- The complete check factory preserves the actual common-floor comparison and one same-Point certificate call. -/
private theorem packaged_check_factory (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := positive) data floor target)
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    check (positive := positive) data paid lifted firstInside lastInside points =
      (let required := Nat.max paid.1.stage paid.2.selection.stage
       if stagePaid : required ≤ stage then
         have integralPaid := (Data.Nat.Order.le_max_left _ _).trans stagePaid
         have uniformPaid := (Data.Nat.Order.le_max_right _ _).trans stagePaid
         let certificate := Cell.certificate (curve := reciprocalCurve (Fibre.frameCurve frame))
           (patch := terminal.neighborhood.patch) (root := comparison.rootBounds)
           (residual := terminal.preparation.reciprocal) (primitive := data.2.1)
           (bounds := data.2.2.1) (uniform := preparation.2.2) (coordinate := coordinate)
           (first := first) (last := last) (depth := stage) (floor := floor) (allowance := allowance)
           (positive := positive) (request := paid.2) data.cell lifted firstInside lastInside points uniformPaid
         have accurate := Cell.accurate (root := comparison.rootBounds)
           (residual := terminal.preparation.reciprocal) (primitive := data.2.1)
           (bounds := data.2.2.1) (coordinate := coordinate) (stage := stage) (allowance := allowance)
           (nonnegative := positive.le) data.cell paid.1 integralPaid
             (terminal.neighborhood.patch.box_refines.contains firstInside)
             (terminal.neighborhood.patch.box_refines.contains lastInside)
         .ok ⟨certificate, integralPaid, uniformPaid, accurate⟩
       else .error ⟨required, rfl, Nat.lt_of_not_ge stagePaid⟩ :
        Preparation (positive := positive) data paid lifted) := by rfl

/-- The complete check factory preserves the actual common-floor comparison and one same-Point certificate call. -/
theorem check_factory (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := positive) data floor target)
    (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    check (positive := positive) data paid lifted firstInside lastInside points =
      (let required := Nat.max paid.1.stage paid.2.selection.stage
       if stagePaid : required ≤ stage then
         have integralPaid := (Data.Nat.Order.le_max_left _ _).trans stagePaid
         have uniformPaid := (Data.Nat.Order.le_max_right _ _).trans stagePaid
         let certificate := Cell.certificate (curve := reciprocalCurve (Fibre.frameCurve frame))
           (patch := terminal.neighborhood.patch) (root := comparison.rootBounds)
           (residual := terminal.preparation.reciprocal) (primitive := data.2.1)
           (bounds := data.2.2.1) (uniform := preparation.2.2) (coordinate := coordinate)
           (first := first) (last := last) (depth := stage) (floor := floor) (allowance := allowance)
           (positive := positive) (request := paid.2) data.cell lifted firstInside lastInside points uniformPaid
         have accurate := Cell.accurate (root := comparison.rootBounds)
           (residual := terminal.preparation.reciprocal) (primitive := data.2.1)
           (bounds := data.2.2.1) (coordinate := coordinate) (stage := stage) (allowance := allowance)
           (nonnegative := positive.le) data.cell paid.1 integralPaid
             (terminal.neighborhood.patch.box_refines.contains firstInside)
             (terminal.neighborhood.patch.box_refines.contains lastInside)
         .ok ⟨certificate, integralPaid, uniformPaid, accurate⟩
       else .error ⟨required, rfl, Nat.lt_of_not_ge stagePaid⟩ : Preparation (positive := positive) data paid lifted) :=
  packaged_check_factory (positive := positive) data paid lifted firstInside lastInside points

/-- The original successful physical check value and its equation on the same supplied cell and Points. -/
@[expose] def Checked (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := positive) data floor target) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) : Type _ :=
  { accepted : Accepted (positive := positive) data paid lifted //
    check (positive := positive) data paid lifted firstInside lastInside points = .ok accepted }

/-- Check a sufficient actual cell once and retain its original successful certificate and accuracy.

The supplied maximum-stage payment rules out the original typed unpaid
branch. The cell, inverse, power bank, request pair and Point family keep
their actual owners and stages; no model or Point is acquired here.
-/
def checkPaid (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := positive) data floor target) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (stagePaid : Nat.max paid.1.stage paid.2.selection.stage ≤ stage) :
    Checked (positive := positive) data paid lifted firstInside lastInside points :=
  let checked := check (positive := positive) data paid lifted firstInside lastInside points
  Except.requireSuccess checked (fun future => by
    have futurePaid : future.val ≤ stage := future.property.1.symm ▸ stagePaid
    exact Nat.lt_irrefl _ (future.property.2.trans_le futurePaid))

/-- The retained successful value belongs to the original check on those same supplied owners. -/
theorem checkPaid_eq (data : PhysicalPrimitive sample retained)
    (paid : Requests (positive := positive) data floor target) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (stagePaid : Nat.max paid.1.stage paid.2.selection.stage ≤ stage) :
    check (positive := positive) data paid lifted firstInside lastInside points =
      .ok (checkPaid (positive := positive) data paid lifted firstInside lastInside points stagePaid).val :=
  (checkPaid (positive := positive) data paid lifted firstInside lastInside points stagePaid).property

/-- Select once and retain the checked outcome on the same original cell, including every unpaid floor. -/
def prepare (data : PhysicalPrimitive sample retained) (floor : Nat) (target : Coordinate)
    (targetPositive : 0 < target) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    (paid : Requests (positive := positive) data floor target) × Preparation (positive := positive) data paid lifted :=
  let paid := requests (positive := positive) data floor target targetPositive
  let checked := check (positive := positive) data paid lifted firstInside lastInside points
  ⟨paid, checked⟩

/-- The complete planner retains its two selected requests and its one check result on the unchanged original data. -/
private theorem packaged_prepare_factory (data : PhysicalPrimitive sample retained) (floor : Nat)
    (target : Coordinate) (targetPositive : 0 < target) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    prepare (positive := positive) data floor target targetPositive lifted firstInside lastInside points =
      (let paid := requests (positive := positive) data floor target targetPositive
       let checked := check (positive := positive) data paid lifted firstInside lastInside points
       ⟨paid, checked⟩ :
        (paid : Requests (positive := positive) data floor target) ×
          Preparation (positive := positive) data paid lifted) := by rfl

/-- The complete planner retains its two selected requests and its one check result on the unchanged original data. -/
theorem prepare_factory (data : PhysicalPrimitive sample retained) (floor : Nat)
    (target : Coordinate) (targetPositive : 0 < target) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    prepare (positive := positive) data floor target targetPositive lifted firstInside lastInside points =
      (let paid := requests (positive := positive) data floor target targetPositive
       let checked := check (positive := positive) data paid lifted firstInside lastInside points
       ⟨paid, checked⟩ :
        (paid : Requests (positive := positive) data floor target) ×
          Preparation (positive := positive) data paid lifted) :=
  packaged_prepare_factory (positive := positive) data floor target targetPositive lifted firstInside lastInside points

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive

end
