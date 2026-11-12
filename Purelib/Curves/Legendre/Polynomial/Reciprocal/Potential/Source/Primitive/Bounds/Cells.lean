module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive.Bounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Except

/-! # Checked physical cells at their retained request maximum

The supplied numerator budgets and both requests precede the one reciprocal
cell. Its actual maximum stage pays both requests. The old check consumes
the same request pair and supplied Point family, and its impossible unpaid
branch is eliminated using that original stage certificate.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive.Bounds

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve (reciprocalCurve)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
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
    {sample : PolynomialSample cap numerator index regularBox}
    {first last : LiftedPoint 2} {coordinate : Spatial.Coordinate first.coordinate last.coordinate}
    {floor : Nat} {target allowance : Coordinate} {positive : 0 < allowance}

namespace Prepared

/-- The original successful check payload on the same physical cell and two retained requests. -/
@[expose] def Accepted {data : Bounds comparison sample}
    (paid : Requests data preparation coordinate floor target allowance)
    {retained : Cell preparation.2.1 coordinate (Nat.max paid.1.stage paid.2.selection.stage)
      allowance positive.le}
    (lifted : LiftedCell first last) (actual : PhysicalPrimitive sample retained)
    (original : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (first := first) (last := last) (coordinate := coordinate)
      (positive := positive) actual floor target) : Type _ :=
  PhysicalPrimitive.Accepted (comparison := comparison) (preparation := preparation)
    (sample := sample) (retained := retained) (first := first) (last := last)
    (coordinate := coordinate) (stage := Nat.max paid.1.stage paid.2.selection.stage)
    (positive := positive) actual original lifted

end Prepared

/-- One original reciprocal cell, its cached attachment, the same request pair and the old check's successful value.

The reciprocal stage is exactly the actual maximum of the two supplied
requests. The typed request view preserves their complete values across
the stored attachment's dependent owner. No new selection, preparation,
Point acquisition or supplied final accuracy certificate occurs here.
-/
@[expose] def Prepared (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) : Type _ :=
  (retained : { value : Cell preparation.2.1 coordinate
        (Nat.max paid.1.stage paid.2.selection.stage) allowance positive.le //
      value = Cell.build preparation.2.1 coordinate (Nat.max paid.1.stage paid.2.selection.stage)
        allowance positive.le }) ×
  (actual : { value : PhysicalPrimitive sample retained.val //
      value = data.attach (preparation := preparation) (coordinate := coordinate) retained.val }) ×
  (original : { value : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
        (sample := sample) (first := first) (last := last)
        (coordinate := coordinate) (positive := positive) actual.val floor target // HEq value paid }) ×
  { accepted : Prepared.Accepted (data := data) (positive := positive) paid lifted actual.val original.val //
    PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained.val) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) actual.val original.val lifted firstInside lastInside points =
        .ok accepted }

namespace Prepared

/-- Retain abstract original caches and the successful value of their same checked preparation.

Keeping the supplied cell and attachment abstract avoids conversion through
computed inverse models while packaging the dependent certificate. The
original complete values and every factory equation remain in the result.
-/
def ofChecked (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (retained : Cell preparation.2.1 coordinate (Nat.max paid.1.stage paid.2.selection.stage)
      allowance positive.le)
    (retainedEq : retained = Cell.build preparation.2.1 coordinate
      (Nat.max paid.1.stage paid.2.selection.stage) allowance positive.le)
    (actual : PhysicalPrimitive sample retained)
    (actualEq : actual = data.attach (preparation := preparation) (coordinate := coordinate) retained)
    (original : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (first := first) (last := last) (coordinate := coordinate)
      (positive := positive) actual floor target)
    (originalEq : HEq original paid)
    (accepted : Accepted (data := data) (positive := positive) paid lifted actual original)
    (equation : PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) actual original lifted firstInside lastInside points =
        .ok accepted) : Prepared (positive := positive) data paid lifted firstInside lastInside points :=
  ⟨⟨retained, retainedEq⟩, ⟨actual, actualEq⟩, ⟨original, originalEq⟩, ⟨accepted, equation⟩⟩

/-- Retain the actual outcome on abstract caches and eliminate its impossible unpaid-stage branch. -/
def ofOutcome (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (retained : Cell preparation.2.1 coordinate (Nat.max paid.1.stage paid.2.selection.stage)
      allowance positive.le)
    (retainedEq : retained = Cell.build preparation.2.1 coordinate
      (Nat.max paid.1.stage paid.2.selection.stage) allowance positive.le)
    (actual : PhysicalPrimitive sample retained)
    (actualEq : actual = data.attach (preparation := preparation) (coordinate := coordinate) retained)
    (original : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (first := first) (last := last) (coordinate := coordinate)
      (positive := positive) actual floor target)
    (originalEq : HEq original paid)
    (stagePaid : Nat.max original.1.stage original.2.selection.stage ≤
      Nat.max paid.1.stage paid.2.selection.stage)
    (checked : PhysicalPrimitive.Preparation (positive := positive) actual original lifted)
    (checkedEq : checked = PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) actual original lifted firstInside lastInside points) :
    Prepared (positive := positive) data paid lifted firstInside lastInside points :=
  let accepted := Except.requireSuccess checked (fun future => by
      have futurePaid : future.val ≤ Nat.max paid.1.stage paid.2.selection.stage :=
        future.property.1.symm ▸ stagePaid
      exact Nat.lt_irrefl _ (future.property.2.trans_le futurePaid))
  ofChecked (comparison := comparison) (preparation := preparation) (sample := sample)
    (coordinate := coordinate) (positive := positive) data paid lifted firstInside lastInside points
    retained retainedEq actual actualEq original originalEq accepted.val (checkedEq.symm.trans accepted.property)

end Prepared

/-- Construct one sufficient reciprocal cell and retain the old check's internally derived successful certificate. -/
def prepare (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) :
    Prepared (positive := positive) data paid lifted firstInside lastInside points :=
  let stage := Nat.max paid.1.stage paid.2.selection.stage
  let retained := Cell.build preparation.2.1 coordinate stage allowance positive.le
  let actual := data.attach (preparation := preparation) (coordinate := coordinate) retained
  let original : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) actual floor target := paid
  let checked := PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
    (sample := sample) (retained := retained) (first := first) (last := last)
    (coordinate := coordinate) (positive := positive) actual original lifted firstInside lastInside points
  Prepared.ofOutcome (comparison := comparison) (preparation := preparation) (sample := sample)
    (coordinate := coordinate) (positive := positive) data paid lifted firstInside lastInside points
    retained rfl actual rfl original HEq.rfl (Nat.le_refl _) checked rfl

namespace Prepared

variable {data : Bounds comparison sample}
    {paid : Requests data preparation coordinate floor target allowance} {lifted : LiftedCell first last}
    {firstInside : terminal.neighborhood.patch.box.Contains first.coordinate}
    {lastInside : terminal.neighborhood.patch.box.Contains last.coordinate}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)}

/-- Read the whole original reciprocal cell at the actual retained request maximum. -/
def reciprocalCell (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    Cell preparation.2.1 coordinate (Nat.max paid.1.stage paid.2.selection.stage) allowance positive.le :=
  prepared.1.val

/-- Read the whole physical primitive attachment using the same retained budgets and reciprocal cell. -/
def physical (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    PhysicalPrimitive sample prepared.reciprocalCell := prepared.2.1.val

/-- Read the same request pair as a typed view on the stored physical attachment, without another selection. -/
def requests (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := prepared.reciprocalCell) (first := first) (last := last)
      (coordinate := coordinate)
      (positive := positive) prepared.physical floor target := prepared.2.2.1.val

/-- Read the old check's original certificate and its two payments and integral bound. -/
def accepted (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    Accepted (data := data) (positive := positive) paid lifted prepared.physical prepared.requests := prepared.2.2.2.val

/-- Read the same whole successful physical check value and its original outcome equation without checking again. -/
def checked (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    PhysicalPrimitive.Checked (positive := positive) prepared.physical prepared.requests
      lifted firstInside lastInside points := prepared.2.2.2

/-- The checked view retains exactly the existing original successful certificate and payments. -/
private theorem packaged_checked_value
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    prepared.checked.val = prepared.accepted := by rfl

/-- The checked view retains exactly the existing original successful certificate and payments. -/
theorem checked_value
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    prepared.checked.val = prepared.accepted := packaged_checked_value prepared

/-- The complete reciprocal cell is the one original factory at the actual request maximum. -/
private theorem packaged_reciprocalCell_eq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    prepared.reciprocalCell = Cell.build preparation.2.1 coordinate
      (Nat.max paid.1.stage paid.2.selection.stage) allowance positive.le := prepared.1.property

/-- The complete reciprocal cell is the one original factory at the actual request maximum. -/
theorem reciprocalCell_eq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    prepared.reciprocalCell = Cell.build preparation.2.1 coordinate
      (Nat.max paid.1.stage paid.2.selection.stage) allowance positive.le := packaged_reciprocalCell_eq prepared

/-- The whole physical data is the cached original attachment to that same reciprocal cell. -/
private theorem packaged_physical_eq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    prepared.physical = data.attach (preparation := preparation) (coordinate := coordinate)
      prepared.reciprocalCell := prepared.2.1.property

/-- The whole physical data is the cached original attachment to that same reciprocal cell. -/
theorem physical_eq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    prepared.physical = data.attach (preparation := preparation) (coordinate := coordinate)
      prepared.reciprocalCell := packaged_physical_eq prepared

/-- The complete stored request view is the originally supplied pair, including both selections and owners. -/
private theorem packaged_requests_heq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    HEq prepared.requests paid := prepared.2.2.1.property

/-- The complete stored request view is the originally supplied pair, including both selections and owners. -/
theorem requests_heq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    HEq prepared.requests paid := packaged_requests_heq prepared

/-- The old check actually returns the retained successful certificate and bound on these same caches and Points. -/
private theorem packaged_check_eq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := prepared.reciprocalCell) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) prepared.physical prepared.requests lifted firstInside
      lastInside points = .ok prepared.accepted :=
  prepared.2.2.2.property

/-- The old check actually returns the retained successful certificate and bound on these same caches and Points. -/
theorem check_eq
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := prepared.reciprocalCell) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) prepared.physical prepared.requests lifted firstInside
      lastInside points = .ok prepared.accepted :=
  packaged_check_eq prepared

/-- The computed physical integral has the old primitive's internally derived strict target bound. -/
theorem integral_lt
    (prepared : Prepared (positive := positive) data paid lifted firstInside lastInside points) :
    Norm.Basic.normSq (prepared.physical.cell.value.eval last.coordinate -
      prepared.physical.cell.value.eval first.coordinate - prepared.physical.cell.pullback.model.integralSample) <
      target := prepared.accepted.property.2.2

end Prepared

/-- The actual continued-Point callback and the whole checked physical cell constructed from that same callback.

The callback records the original Point.acquire factory at every supplied
unit parameter. This retains an executable function, not a bank of all
query results: each invocation performs its original seed-owner transport.
-/
@[expose] def Continued (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate) : Type _ :=
  (points : { value : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
        Point terminal.neighborhood.patch (coordinate.point input) //
      value = fun input lower upper => Point.acquire terminal.neighborhood.patch (coordinate.point input)
        (coordinate.point_inside firstInside lastInside lower upper) }) ×
  { actual : Prepared (positive := positive) data paid lifted firstInside lastInside points.val //
    actual = prepare (positive := positive) data paid lifted firstInside lastInside points.val }

/-- Retain one actual acquisition callback and pass it once to the same-request checked-cell constructor.

The two supplied endpoint containments derive every query containment.
The original patch then derives its own nonvanishing and movement budgets;
no root-equivalence, extra clearance or final accuracy premise is supplied.
-/
def prepareContinued (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate) :
    Continued (positive := positive) data paid lifted firstInside lastInside :=
  let points := fun (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) =>
    Point.acquire terminal.neighborhood.patch (coordinate.point input)
      (coordinate.point_inside firstInside lastInside lower upper)
  let actual := prepare (positive := positive) data paid lifted firstInside lastInside points
  ⟨⟨points, rfl⟩, ⟨actual, rfl⟩⟩

/-- The complete factory retains exactly the callback value and one whole checked-cell result using it. -/
private theorem packaged_prepareContinued_factory (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate) :
    prepareContinued (positive := positive) data paid lifted firstInside lastInside =
      (let points := fun (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) =>
         Point.acquire terminal.neighborhood.patch (coordinate.point input)
           (coordinate.point_inside firstInside lastInside lower upper)
       let actual := prepare (positive := positive) data paid lifted firstInside lastInside points
       ⟨⟨points, rfl⟩, ⟨actual, rfl⟩⟩ :
        Continued (positive := positive) data paid lifted firstInside lastInside) := by rfl

/-- The complete factory retains exactly the callback value and one whole checked-cell result using it. -/
theorem prepareContinued_factory (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate) :
    prepareContinued (positive := positive) data paid lifted firstInside lastInside =
      (let points := fun (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) =>
         Point.acquire terminal.neighborhood.patch (coordinate.point input)
           (coordinate.point_inside firstInside lastInside lower upper)
       let actual := prepare (positive := positive) data paid lifted firstInside lastInside points
       ⟨⟨points, rfl⟩, ⟨actual, rfl⟩⟩ :
        Continued (positive := positive) data paid lifted firstInside lastInside) :=
  packaged_prepareContinued_factory (positive := positive) data paid lifted firstInside lastInside

namespace Continued

variable {data : Bounds comparison sample}
    {paid : Requests data preparation coordinate floor target allowance} {lifted : LiftedCell first last}
    {firstInside : terminal.neighborhood.patch.box.Contains first.coordinate}
    {lastInside : terminal.neighborhood.patch.box.Contains last.coordinate}

/-- Read the same retained executable callback, without invoking it or acquiring a Point. -/
def points (continued : Continued (positive := positive) data paid lifted firstInside lastInside) :
    ∀ input : Coordinate, 0 ≤ input → input ≤ 1 → Point terminal.neighborhood.patch (coordinate.point input) :=
  continued.1.val

/-- Read the entire checked-cell value that consumed this same retained callback. -/
def prepared (continued : Continued (positive := positive) data paid lifted firstInside lastInside) :
    Prepared (positive := positive) data paid lifted firstInside lastInside continued.points := continued.2.val

/-- The callback is the complete original acquisition function on the actual retained physical segment. -/
private theorem packaged_points_eq
    (continued : Continued (positive := positive) data paid lifted firstInside lastInside) :
    continued.points = fun input lower upper => Point.acquire terminal.neighborhood.patch (coordinate.point input)
      (coordinate.point_inside firstInside lastInside lower upper) := continued.1.property

/-- The callback is the complete original acquisition function on the actual retained physical segment. -/
theorem points_eq
    (continued : Continued (positive := positive) data paid lifted firstInside lastInside) :
    continued.points = fun input lower upper => Point.acquire terminal.neighborhood.patch (coordinate.point input)
      (coordinate.point_inside firstInside lastInside lower upper) := packaged_points_eq continued

/-- The retained successful value is the whole original same-request constructor on this exact callback. -/
private theorem packaged_prepared_eq
    (continued : Continued (positive := positive) data paid lifted firstInside lastInside) :
    continued.prepared = prepare (positive := positive) data paid lifted firstInside lastInside continued.points :=
  continued.2.property

/-- The retained successful value is the whole original same-request constructor on this exact callback. -/
theorem prepared_eq
    (continued : Continued (positive := positive) data paid lifted firstInside lastInside) :
    continued.prepared = prepare (positive := positive) data paid lifted firstInside lastInside continued.points :=
  packaged_prepared_eq continued

/-- One actual query returns the whole original seed-transported Point at that exact unit parameter. -/
theorem point_eq
    (continued : Continued (positive := positive) data paid lifted firstInside lastInside)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    continued.points input lower upper = Point.acquire terminal.neighborhood.patch (coordinate.point input)
      (coordinate.point_inside firstInside lastInside lower upper) :=
  congrFun (congrFun (congrFun continued.points_eq input) lower) upper

/-- The queried Point's certified root name is the actual acquisition factory's name at that same physical point. -/
theorem point_name
    (continued : Continued (positive := positive) data paid lifted firstInside lastInside)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    (continued.points input lower upper).certificate.value.name =
      (Point.acquire terminal.neighborhood.patch (coordinate.point input)
        (coordinate.point_inside firstInside lastInside lower upper)).certificate.value.name :=
  congrArg (fun actual : Point terminal.neighborhood.patch (coordinate.point input) =>
    actual.certificate.value.name) (continued.point_eq input lower upper)

end Continued

variable {stage : Nat}

/-- One same-cell numerator attachment, the original request view and the successful original check.

The reciprocal cell is supplied at its actual stage and remains an index
of the whole cache. Only its new numerator attachment is constructed. The
stored check retains the original certificate, both stage payments and its
derived finite accuracy, without a cell-factory equation at another stage.
-/
@[expose] def Attached (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance)
    (retained : Cell preparation.2.1 coordinate stage allowance positive.le) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)) : Type _ :=
  (actual : { value : PhysicalPrimitive sample retained //
    value = data.attach (preparation := preparation) (coordinate := coordinate) retained }) ×
  (original : { value : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) actual.val floor target // HEq value paid }) ×
  PhysicalPrimitive.Checked (positive := positive) actual.val original.val lifted firstInside lastInside points

namespace Attached

/-- Package an abstract same-cell attachment, its exact request view and the original successful check value. -/
private def ofChecked (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance)
    (retained : Cell preparation.2.1 coordinate stage allowance positive.le) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (actual : PhysicalPrimitive sample retained)
    (actualEq : actual = data.attach (preparation := preparation) (coordinate := coordinate) retained)
    (original : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) actual floor target)
    (originalEq : HEq original paid)
    (checked : PhysicalPrimitive.Checked (positive := positive) actual original
      lifted firstInside lastInside points) :
    Attached (positive := positive) data paid retained lifted firstInside lastInside points :=
  ⟨⟨actual, actualEq⟩, ⟨original, originalEq⟩, checked⟩

end Attached

/-- Attach the cached numerator to the supplied sufficient cell once and run its original physical check once.

The input payment concerns the supplied cell's actual stage. All requests
and genuine continued Points are reused. Only the numerator-dependent
cell data are new; the reciprocal inverse and power bank are unchanged.
-/
def attachPaid (data : Bounds comparison sample)
    (paid : Requests data preparation coordinate floor target allowance)
    (retained : Cell preparation.2.1 coordinate stage allowance positive.le) (lifted : LiftedCell first last)
    (firstInside : terminal.neighborhood.patch.box.Contains first.coordinate)
    (lastInside : terminal.neighborhood.patch.box.Contains last.coordinate)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input))
    (stagePaid : Nat.max paid.1.stage paid.2.selection.stage ≤ stage) :
    Attached (positive := positive) data paid retained lifted firstInside lastInside points :=
  let actual := data.attach (preparation := preparation) (coordinate := coordinate) retained
  let original : PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) actual floor target := paid
  let checked := PhysicalPrimitive.checkPaid (comparison := comparison) (preparation := preparation)
    (sample := sample) (retained := retained) (first := first) (last := last)
    (coordinate := coordinate) (positive := positive) actual original
    lifted firstInside lastInside points stagePaid
  Attached.ofChecked (comparison := comparison) (preparation := preparation) (sample := sample)
    (coordinate := coordinate) (positive := positive) data paid retained lifted firstInside lastInside points
    actual rfl original HEq.rfl checked

namespace Attached

variable {data : Bounds comparison sample}
    {paid : Requests data preparation coordinate floor target allowance}
    {retained : Cell preparation.2.1 coordinate stage allowance positive.le} {lifted : LiftedCell first last}
    {firstInside : terminal.neighborhood.patch.box.Contains first.coordinate}
    {lastInside : terminal.neighborhood.patch.box.Contains last.coordinate}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point terminal.neighborhood.patch (coordinate.point input)}

/-- Read the complete cached attachment on the unchanged supplied reciprocal cell. -/
def physical (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    PhysicalPrimitive sample retained := attached.1.val

/-- Read the original paid pair as its same typed view on the stored attachment. -/
def requests (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    PhysicalPrimitive.Requests (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) attached.physical floor target := attached.2.1.val

/-- Read the original successful check certificate and its derived payments and accuracy. -/
def accepted (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    PhysicalPrimitive.Accepted (positive := positive) attached.physical attached.requests lifted := attached.2.2.val

/-- Read the same whole successful physical check value and its original outcome equation without checking again. -/
def checked (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    PhysicalPrimitive.Checked (positive := positive) attached.physical attached.requests
      lifted firstInside lastInside points := attached.2.2

/-- The checked view retains exactly the existing original successful certificate and payments. -/
private theorem packaged_checked_value
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    attached.checked.val = attached.accepted := by rfl

/-- The checked view retains exactly the existing original successful certificate and payments. -/
theorem checked_value
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    attached.checked.val = attached.accepted := packaged_checked_value attached

/-- The complete physical attachment is the one same-cell factory on the retained numerator budgets. -/
private theorem packaged_physical_eq
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    attached.physical = data.attach (preparation := preparation) (coordinate := coordinate) retained :=
  attached.1.property

/-- The complete physical attachment is the one same-cell factory on the retained numerator budgets. -/
theorem physical_eq
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    attached.physical = data.attach (preparation := preparation) (coordinate := coordinate) retained :=
  packaged_physical_eq attached

/-- The complete stored request view preserves both originally supplied selections and their owners. -/
private theorem packaged_requests_heq
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    HEq attached.requests paid := attached.2.1.property

/-- The complete stored request view preserves both originally supplied selections and their owners. -/
theorem requests_heq
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    HEq attached.requests paid := packaged_requests_heq attached

/-- The old check returns that same retained successful value on the unchanged cell and supplied Points. -/
private theorem packaged_check_eq
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) attached.physical attached.requests
      lifted firstInside lastInside points = .ok attached.accepted := attached.2.2.property

/-- The old check returns that same retained successful value on the unchanged cell and supplied Points. -/
theorem check_eq
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    PhysicalPrimitive.check (comparison := comparison) (preparation := preparation)
      (sample := sample) (retained := retained) (first := first) (last := last)
      (coordinate := coordinate) (positive := positive) attached.physical attached.requests
      lifted firstInside lastInside points = .ok attached.accepted := packaged_check_eq attached

/-- The successful same-cell check internally pays its actual primitive endpoint difference and integral. -/
theorem integral_lt
    (attached : Attached (positive := positive) data paid retained lifted firstInside lastInside points) :
    Norm.Basic.normSq (attached.physical.cell.value.eval last.coordinate -
      attached.physical.cell.value.eval first.coordinate - attached.physical.cell.pullback.model.integralSample) <
      target := attached.accepted.property.2.2

end Attached

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive.Bounds

end
