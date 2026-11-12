module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive.Bounds.Cells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Continued
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order

/-! # One checked primitive attachment on the original bank head

The original head continuation constructs its Request, Sample, Tables and
Pullbacks once. The same Sample cell receives the shared regular sample's
cached numerator and original request pair. The retained successful check
and original regular Selection then pay their actual local integral.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison (Request Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve (reciprocalCurve)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive
  (RemainderBounds regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Box)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedCell)
open Purelib.Data.Gaussian
open Purelib.Approximation.Rational.Geometric.Search (Selection)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The original four complete head caches and one successful numerator attachment on that same Sample cell.

The preparation and coordinate are the supplied planning values. Both
physical requests precede this head construction, and its attachment
retains the same reciprocal inverse and cube at the actual selected stage.
-/
@[expose] def Head {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)) : Type _ :=
  (original : Request planned.1 data.data values.1 values.2.1 planned.2.1 error errorPositive common) ×
  (sample : Sample original) × (tables : Tables sample.1) × (_cells : Pullbacks sample.1 tables) ×
  PhysicalPrimitive.Bounds.Attached (comparison := data.comparison) (preparation := planned.1)
    (sample := regular) (index := index) (regularBox := box)
    (first := ⟨data.segment.comparison.first, firstSheet⟩)
    (last := ⟨data.segment.comparison.last, lastSheet⟩)
    (coordinate := planned.2.1) (stage := original.2.2.2.2.val)
    (floor := floor) (target := accuracy) (allowance := error) (positive := errorPositive)
    bounds physicalPaid sample.1 lifted data.segment.firstInside data.segment.lastInside points

namespace Head

/-- Package abstract original caches and their same-cell successful attachment without rebuilding any owner. -/
private def ofParts {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (original : Request planned.1 data.data values.1 values.2.1 planned.2.1 error errorPositive common)
    (sample : Sample original) (tables : Tables sample.1) (cells : Pullbacks sample.1 tables)
    (attached : PhysicalPrimitive.Bounds.Attached (comparison := data.comparison) (preparation := planned.1)
      (sample := regular) (index := index) (regularBox := box)
      (first := ⟨data.segment.comparison.first, firstSheet⟩)
      (last := ⟨data.segment.comparison.last, lastSheet⟩)
      (coordinate := planned.2.1) (stage := original.2.2.2.2.val)
      (floor := floor) (target := accuracy) (allowance := error) (positive := errorPositive)
      bounds physicalPaid sample.1 lifted data.segment.firstInside data.segment.lastInside points) :
    Head data rest values planned regular bounds accuracy physicalPaid common lifted points :=
  ⟨original, sample, tables, cells, attached⟩

/-- Read the original complete potential request stored in this head. -/
abbrev paid {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {data : ParentData cap sourceDifferential count parent} {rest : Bank cap sourceDifferential count parents}
    {values : Potentials (.cons data rest)} {planned : Plan error errorPositive floor (.cons data rest)}
    {index : Nat} {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {bounds : PhysicalPrimitive.Bounds data.comparison regular} {accuracy : Coordinate}
    {physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error}
    {common : Nat} {firstSheet lastSheet : Fin 2}
    {lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)}
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points) :
    Request planned.1 data.data values.1 values.2.1 planned.2.1 error errorPositive common := head.1

/-- Read the same complete original Sample on the retained request. -/
abbrev sample {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {data : ParentData cap sourceDifferential count parent} {rest : Bank cap sourceDifferential count parents}
    {values : Potentials (.cons data rest)} {planned : Plan error errorPositive floor (.cons data rest)}
    {index : Nat} {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {bounds : PhysicalPrimitive.Bounds data.comparison regular} {accuracy : Coordinate}
    {physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error}
    {common : Nat} {firstSheet lastSheet : Fin 2}
    {lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)}
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points) :
    Sample head.paid := head.2.1

/-- Read the retained weighted and regular tables on that same Sample cell. -/
abbrev tables {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {data : ParentData cap sourceDifferential count parent} {rest : Bank cap sourceDifferential count parents}
    {values : Potentials (.cons data rest)} {planned : Plan error errorPositive floor (.cons data rest)}
    {index : Nat} {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {bounds : PhysicalPrimitive.Bounds data.comparison regular} {accuracy : Coordinate}
    {physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error}
    {common : Nat} {firstSheet lastSheet : Fin 2}
    {lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)}
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points) :
    Tables head.sample.1 := head.2.2.1

/-- Read the same actual two physical pullbacks on the retained tables. -/
abbrev pullbacks {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {data : ParentData cap sourceDifferential count parent} {rest : Bank cap sourceDifferential count parents}
    {values : Potentials (.cons data rest)} {planned : Plan error errorPositive floor (.cons data rest)}
    {index : Nat} {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {bounds : PhysicalPrimitive.Bounds data.comparison regular} {accuracy : Coordinate}
    {physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error}
    {common : Nat} {firstSheet lastSheet : Fin 2}
    {lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)}
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points) :
    Pullbacks head.sample.1 head.tables := head.2.2.2.1

/-- Read the original successful numerator attachment on the same unchanged Sample cell. -/
abbrev attached {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {data : ParentData cap sourceDifferential count parent} {rest : Bank cap sourceDifferential count parents}
    {values : Potentials (.cons data rest)} {planned : Plan error errorPositive floor (.cons data rest)}
    {index : Nat} {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {bounds : PhysicalPrimitive.Bounds data.comparison regular} {accuracy : Coordinate}
    {physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error}
    {common : Nat} {firstSheet lastSheet : Fin 2}
    {lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩}
    {points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)}
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points) :
    PhysicalPrimitive.Bounds.Attached (comparison := data.comparison) (preparation := planned.1)
      (sample := regular) (index := index) (regularBox := box)
      (first := ⟨data.segment.comparison.first, firstSheet⟩)
      (last := ⟨data.segment.comparison.last, lastSheet⟩)
      (coordinate := planned.2.1) (stage := head.paid.2.2.2.2.val)
      (floor := floor) (target := accuracy) (allowance := error) (positive := errorPositive)
      bounds physicalPaid head.sample.1 lifted data.segment.firstInside data.segment.lastInside points := head.2.2.2.2

/-- Construct one checked original head from actual cached budgets and a paid common reciprocal floor.

The regular sample and physical request pair are supplied unchanged.
The original continuation constructs its four caches once, and its actual
request stage pays the same-cell attachment without a sample stage cast.
-/
def build {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) (payment : Nat.max physicalPaid.1.stage physicalPaid.2.selection.stage ≤ common)
    {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)) :
    Head data rest values planned regular bounds accuracy physicalPaid common lifted points :=
  Plan.withHead (parameter := parameter) (frame := frame) (cap := cap)
    (error := error) (positive := errorPositive) (floor := floor) data rest values planned common
    (fun original sample tables cells =>
      have stagePaid := payment.trans original.floor_le
      let attached := PhysicalPrimitive.Bounds.attachPaid
        (comparison := data.comparison) (preparation := planned.1) (sample := regular)
        (coordinate := planned.2.1) (positive := errorPositive)
        (first := ⟨data.segment.comparison.first, firstSheet⟩)
        (last := ⟨data.segment.comparison.last, lastSheet⟩)
        (index := index) (regularBox := box) (stage := original.2.2.2.2.val)
        (floor := floor) (target := accuracy) (allowance := error)
        bounds physicalPaid sample.1 lifted data.segment.firstInside data.segment.lastInside points stagePaid
      ofParts (parameter := parameter) (frame := frame) (cap := cap)
        data rest values planned regular bounds accuracy physicalPaid common
        lifted points original sample tables cells attached)

/-- The original planned uniform floors are paid at this unchanged Head's actual reciprocal stage. -/
theorem extra_floor_le
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common) :
    planned.2.2.1.2.2.val ≤ head.paid.2.2.2.2.val := by
  have bound : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
    Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
  exact ((Data.Nat.Order.le_max_left _ _).trans bound).trans head.paid.floor_le

/-- Certify both original physical models on the same supplied lifted cell and continued Point callback.

Only the original uniform-query closures are constructed. The inverse,
cube, weighted/remainder tables, pullbacks and actual model stage are the
supplied Head's existing caches, and its two genuine floors are paid
internally from the retained common-stage proof.
-/
def certificates
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common) :
    Uniform.Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame))
      (Integration.differential (-cap.polynomial)) lifted head.pullbacks.1.val.model ×
    Uniform.Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame))
      (Integration.differential ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) lifted head.pullbacks.2.val.model :=
  Integration.certificates (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
    (count := count) (center := parent.edge.segment.pointAt parent.edge.left.parameter)
    (centerOwner := parent.edge.cached.preparedOwner) (terminal := data.terminal)
    (sourceDifferential := sourceDifferential) (comparison := data.comparison) (preparation := planned.1)
    (first := ⟨data.segment.comparison.first, firstSheet⟩) (last := ⟨data.segment.comparison.last, lastSheet⟩)
    (coordinate := planned.2.1) (allowance := error) (positive := errorPositive) (floor := floor)
    (stage := head.paid.2.2.2.2.val)
    head.sample.1 head.tables head.pullbacks planned.2.2.1
    (extra_floor_le data rest values planned regular bounds accuracy physicalPaid common
      lifted points head originalPaid)
    lifted data.segment.firstInside data.segment.lastInside points

/-- The two actual Head certificate queries keep the same supplied Point generator at every bounded fraction. -/
private theorem packaged_certificates_root_names
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((certificates data rest values planned regular bounds accuracy physicalPaid common
      lifted points head originalPaid).1.query input lower upper).algebraic.sheetValue.value.name =
      (points input lower upper).certificate.value.name ∧
    ((certificates data rest values planned regular bounds accuracy physicalPaid common
      lifted points head originalPaid).2.query input lower upper).algebraic.sheetValue.value.name =
      (points input lower upper).certificate.value.name := by
  unfold certificates
  exact Integration.certificates_root_names (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
    (count := count) (center := parent.edge.segment.pointAt parent.edge.left.parameter)
    (centerOwner := parent.edge.cached.preparedOwner) (terminal := data.terminal)
    (sourceDifferential := sourceDifferential) (comparison := data.comparison) (preparation := planned.1)
    (first := ⟨data.segment.comparison.first, firstSheet⟩) (last := ⟨data.segment.comparison.last, lastSheet⟩)
    (coordinate := planned.2.1) (allowance := error) (positive := errorPositive) (floor := floor)
    (stage := head.paid.2.2.2.2.val)
    head.sample.1 head.tables head.pullbacks planned.2.2.1
    (extra_floor_le data rest values planned regular bounds accuracy physicalPaid common
      lifted points head originalPaid)
    lifted data.segment.firstInside data.segment.lastInside points input lower upper

/-- The two actual Head certificate queries keep the same supplied Point generator at every bounded fraction.

The Point callback is reused as an operation; its fresh per-query
continuation and both independent observation chains are preserved. No
memoized Point family or root equality from coordinate labels is claimed.
-/
theorem certificates_root_names
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular) (accuracy : Coordinate)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor accuracy error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds accuracy physicalPaid common lifted points)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((certificates data rest values planned regular bounds accuracy physicalPaid common
      lifted points head originalPaid).1.query input lower upper).algebraic.sheetValue.value.name =
      (points input lower upper).certificate.value.name ∧
    ((certificates data rest values planned regular bounds accuracy physicalPaid common
      lifted points head originalPaid).2.query input lower upper).algebraic.sheetValue.value.name =
      (points input lower upper).certificate.value.name :=
  packaged_certificates_root_names data rest values planned regular bounds accuracy physicalPaid common
    lifted points head originalPaid input lower upper

/-- A retained Selection and successful same-cell check pay the actual local regular-integral discrepancy.

The actual regular index may exceed this Selection's own stage. All
original sample, coordinate, inverse/cube, Point and pullback owners remain
unchanged; the two original quarter-payments derive the final estimate.
-/
theorem integral_lt {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box} {target : Coordinate} {pFloor : Nat}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (bounds : PhysicalPrimitive.Bounds data.comparison regular)
    (physicalPaid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor (target / 4) error)
    (common : Nat) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned regular bounds (target / 4) physicalPaid common lifted points)
    (residuals : RemainderBounds data.comparison planned.2.1)
    (selection : Selection residuals.scale pFloor (target / 4)) (regularPaid : selection.stage ≤ index) :
    Norm.Basic.normSq (head.attached.physical.cell.value.eval data.segment.comparison.last -
      head.attached.physical.cell.value.eval data.segment.comparison.first -
      head.pullbacks.2.val.model.integralSample) < target :=
  RemainderBounds.primitive_integral_difference_lt
    (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
    (count := count) (center := parent.edge.segment.pointAt parent.edge.left.parameter)
    (centerOwner := parent.edge.cached.preparedOwner) (terminal := data.terminal)
    (sourceDifferential := sourceDifferential) (comparison := data.comparison) (preparation := planned.1)
    (first := ⟨data.segment.comparison.first, firstSheet⟩) (last := ⟨data.segment.comparison.last, lastSheet⟩)
    (coordinate := planned.2.1) (regularBox := box) (pFloor := pFloor) (qFloor := floor)
    (index := index) (stage := head.paid.2.2.2.2.val) (target := target)
    (allowance := error) (allowancePositive := errorPositive) (retained := head.sample.1)
    (lifted := lifted) (firstInside := data.segment.firstInside) (lastInside := data.segment.lastInside)
    (points := points) residuals regular selection regularPaid
    head.attached.physical head.attached.requests head.attached.checked
    data.segment.comparison.firstCap data.segment.comparison.lastCap head.tables head.pullbacks

end Head

/-- Construct one original head and attach the shared coefficient to its actual sufficiently late Sample cell.

The finite common-floor proof comes from the original companion cache.
The continuation retains its four original values together with the
original successful check. No preparation or original sample is rebuilt;
the genuine Point family is passed unchanged to that original checker.
-/
def buildHead {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {target : Coordinate} {quarterPositive : 0 < target / 4} {pFloor : Nat} {box : Box}
    (cached : Primitive target quarterPositive pFloor box (.cons data rest) planned)
    (common : { value : Nat // value = Nat.max (Plan.commonFloor (.cons data rest) planned)
      (Requests.maximum (.cons data rest) planned cached.2.2.2.2) })
    {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input)) :
    Head data rest values planned cached.2.2.1.val cached.2.2.2.2.1.val (target / 4)
      cached.2.2.2.2.2.1.val common.val lifted points := by
  have head : cached.2.2.2.2.2.2.1.val ≤ Requests.maximum (.cons data rest) planned cached.2.2.2.2 :=
    Eq.mp (congrArg (fun value : Nat => cached.2.2.2.2.2.2.1.val ≤ value)
      (Requests.maximum_cons data rest planned cached.2.2.2.2).symm) (Data.Nat.Order.le_max_left _ _)
  have retained := head.trans (requests_le cached common)
  have payment : Nat.max cached.2.2.2.2.2.1.val.1.stage cached.2.2.2.2.2.1.val.2.selection.stage ≤ common.val :=
    Eq.mp (congrArg (fun value : Nat => value ≤ common.val) cached.2.2.2.2.2.2.1.property) retained
  exact Head.build (parameter := parameter) (frame := frame) (cap := cap)
    data rest values planned cached.2.2.1.val cached.2.2.2.2.1.val (target / 4)
    cached.2.2.2.2.2.1.val common.val payment lifted points

/-- The retained original check and first paid Selection derive the actual local regular-integral discrepancy.

Both actual sample stages, the physical coordinate, inverse/cube and
original pullbacks are unchanged. This local estimate supplies neither
primitive endpoint normalization nor a closed-cycle root relation.
-/
theorem integral_lt {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {target : Coordinate} {quarterPositive : 0 < target / 4} {pFloor : Nat} {box : Box}
    (cached : Primitive target quarterPositive pFloor box (.cons data rest) planned) (common : Nat)
    {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (planned.2.1.point input))
    (head : Head data rest values planned cached.2.2.1.val cached.2.2.2.2.1.val (target / 4)
      cached.2.2.2.2.2.1.val common lifted points) :
    Norm.Basic.normSq (head.attached.physical.cell.value.eval data.segment.comparison.last -
      head.attached.physical.cell.value.eval data.segment.comparison.first -
      head.pullbacks.2.val.model.integralSample) < target :=
  Head.integral_lt (parameter := parameter) (frame := frame) (cap := cap)
    data rest values planned cached.2.2.1.val cached.2.2.2.2.1.val cached.2.2.2.2.2.1.val common
    lifted points head cached.1.1.val cached.1.2.1.val (head_pStage data rest planned cached)

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
