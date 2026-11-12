module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison.Bank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingCoordinates
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Continued
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Weighted physical cells on the original paid potential bank

Each parent preparation and both extra cubic-reading requests are retained
before the common starting floor is chosen. The original potential request
and sample then consume those same preparations at that floor. Both new
pullbacks use the original sample's one inverse and cube. The original
junction and root-return payments bound the ordered weighted-minus-remainder
sum; they do not assert that the regular remainder has zero integral.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison (Request Sample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve (reciprocalCurve)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedCell)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}

namespace Plan

/-- The original preparation, physical coordinate and two extra requests, followed by an abstract retained tail. -/
@[expose] def Entry {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent)
    (error : Coordinate) (positive : 0 < error) (floor : Nat) (remaining : Type 3) : Type 3 :=
  (preparation : PotentialComparison.Preparation data.comparison) ×
  (_coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last) ×
  Floors preparation error positive floor × remaining

end Plan

/-- An ordered planning bank retains each actual preparation before any request or model refinement consumes it. -/
@[expose] def Plan (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3
  | [], .nil => PUnit
  | _ :: _, .cons data rest => Plan.Entry data error positive floor (Plan error positive floor rest)

namespace Plan

variable {error : Coordinate} {positive : 0 < error} {floor : Nat}

/-- Construct one original planning head before evaluating the retained tail continuation. -/
private def buildStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (error : Coordinate) (positive : 0 < error) (floor : Nat)
    (finishTail : Unit → Plan error positive floor rest) : Plan error positive floor (.cons data rest) :=
  let preparation := PotentialComparison.Preparation.build data.comparison
  let coordinate := Spatial.Coordinate.build data.segment.comparison.first data.segment.comparison.last
  let extra := Floors.build preparation error positive floor
  let remaining := finishTail ()
  ⟨preparation, coordinate, extra, remaining⟩

/-- Build each original preparation and coordinate once, retaining both independent uniform selections before models. -/
def build (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → Plan error positive floor bank
  | [], .nil => ⟨⟩
  | _ :: _, .cons data rest =>
      buildStep (parameter := parameter) (frame := frame) (cap := cap)
        data rest error positive floor (fun _ => build error positive floor rest)

/-- The whole planning branch retains precisely the four original computations in their displayed order. -/
private theorem packaged_build_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    build error positive floor (.cons data rest) =
      (let preparation := PotentialComparison.Preparation.build data.comparison
       let coordinate := Spatial.Coordinate.build data.segment.comparison.first data.segment.comparison.last
       let extra := Floors.build preparation error positive floor
       let remaining := build error positive floor rest
       ⟨preparation, coordinate, extra, remaining⟩ : Plan error positive floor (.cons data rest)) := by rfl

/-- The whole planning branch retains precisely the four original computations in their displayed order. -/
theorem build_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (error : Coordinate) (positive : 0 < error) (floor : Nat) :
    build error positive floor (.cons data rest) =
      (let preparation := PotentialComparison.Preparation.build data.comparison
       let coordinate := Spatial.Coordinate.build data.segment.comparison.first data.segment.comparison.last
       let extra := Floors.build preparation error positive floor
       let remaining := build error positive floor rest
       ⟨preparation, coordinate, extra, remaining⟩ : Plan error positive floor (.cons data rest)) :=
  packaged_build_cons data rest error positive floor

/-- Compute the finite maximum of the already retained actual floors, using the supplied floor for the empty bank. -/
def commonFloor : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → Plan error positive floor bank → Nat
  | [], .nil, _ => floor
  | _ :: _, .cons _ rest, planned => max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2)

/-- The nonempty common-floor scan uses the retained head maximum and the same original tail. -/
private theorem packaged_commonFloor_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error positive floor (.cons data rest)) :
    commonFloor (.cons data rest) planned = max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2) := by rfl

/-- The nonempty common-floor scan uses the retained head maximum and the same original tail. -/
theorem commonFloor_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error positive floor (.cons data rest)) :
    commonFloor (.cons data rest) planned = max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2) :=
  packaged_commonFloor_cons data rest planned

/-- The retained common floor preserves the original requested starting floor. -/
theorem floor_le {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (planned : Plan error positive floor bank) :
    floor ≤ commonFloor bank planned := by
  cases bank with
  | nil => exact Nat.le_refl _
  | cons data rest =>
      have bounded : floor ≤ max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2) :=
        planned.2.2.1.floor_le.trans (Data.Nat.Order.le_max_left _ _)
      exact Eq.mp (congrArg (fun bound : Nat => floor ≤ bound) (commonFloor_cons data rest planned).symm) bounded

end Plan

namespace ExtraCells

/-- Two new products and pullbacks on the same complete original head and an abstract retained tail.

The original four head caches are passed together with their dependent
indices. Only the tail type is abstract; the stored weighted and regular
pullbacks and the actual extra stage certificate are unchanged.
-/
@[expose] def Entry {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent)
    (first : data.data.first.coordinates.Potential) (last : data.data.last.coordinates.Potential)
    (error : Coordinate) (positive : 0 < error) (floor common : Nat) {originalTail : Type 3}
    (work : PotentialCells.Entry data first last error positive common originalTail) (remaining : Type 3) : Type 3 :=
  (_extra : { actual : Floors work.1 error positive floor // actual.2.2.val ≤ work.2.2.1.2.2.2.2.val }) ×
  (tables : Tables work.2.2.2.1.1) × Pullbacks work.2.2.2.1.1 tables × remaining

namespace Entry

/-- Certify both retained head models with actual Points on the unchanged physical segment.

The complete original head supplies its preparation, coordinate, paid
request and sample together. Both uniform certificates consume the actual
extra requests and their stored sufficient-stage proof on that same sample.
-/
def certificates {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent)
    {first : data.data.first.coordinates.Potential} {last : data.data.last.coordinates.Potential}
    {error : Coordinate} {positive : 0 < error} {floor common : Nat} {originalTail : Type 3}
    (work : PotentialCells.Entry data first last error positive common originalTail) {remaining : Type 3}
    (extra : Entry data first last error positive floor common work remaining)
    {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      Point data.terminal.neighborhood.patch (work.2.1.point input)) :
    Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame)) (differential (-cap.polynomial))
      lifted extra.2.2.1.1.val.model ×
    Jets.UniformCellCertificate (reciprocalCurve (Fibre.frameCurve frame))
      (differential ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) lifted extra.2.2.1.2.val.model :=
  Integration.certificates (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
    (count := count) (center := parent.edge.segment.pointAt parent.edge.left.parameter)
    (centerOwner := parent.edge.cached.preparedOwner) (terminal := data.terminal)
    (sourceDifferential := sourceDifferential) (comparison := data.comparison) (preparation := work.1)
    (first := ⟨data.segment.comparison.first, firstSheet⟩) (last := ⟨data.segment.comparison.last, lastSheet⟩)
    (coordinate := work.2.1) (allowance := error) (positive := positive) (floor := floor)
    (stage := work.2.2.1.2.2.2.2.val) work.2.2.2.1.1 extra.2.1 extra.2.2.1 extra.1.val extra.1.property
    lifted data.segment.firstInside data.segment.lastInside points

end Entry

end ExtraCells

/-- The weighted and regular cells are indexed by the same complete original potential-cell bank. -/
@[expose] def ExtraCells (error : Coordinate) (positive : 0 < error) (floor common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → {values : Potentials bank} →
        PotentialCells error positive common bank values → Type 3
  | [], .nil, _, _ => PUnit
  | _ :: _, .cons data rest, values, work =>
      ExtraCells.Entry (parameter := parameter) (frame := frame) (cap := cap)
        data values.1 values.2.1 error positive floor common work
        (ExtraCells error positive floor common rest work.2.2.2.2)

namespace Plan

variable {error : Coordinate} {positive : 0 < error} {floor : Nat}

/-- The same original sample bank paired with its two retained dependent physical-cell consumers. -/
@[expose] def Materialized {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank) (common : Nat) : Type 3 :=
  (work : PotentialCells error positive common bank values) × ExtraCells error positive floor common bank work

/-- Construct one original request, sample and both physical pullbacks before consuming their exact cached values.

The supplied planning head fixes the original preparation and coordinate.
The continuation receives all four dependent caches together, before any
result packing can hide those original owners. No source preparation,
Point acquisition or existing sample construction is replayed.
-/
def withHead {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error positive floor (.cons data rest))
    (common : Nat) {Result : Type u}
    (consume : (paid : Request planned.1 data.data values.1 values.2.1 planned.2.1 error positive common) →
      (sample : Sample paid) → (tables : Tables sample.1) → Pullbacks sample.1 tables → Result) : Result :=
  let paid := Request.build planned.1 data.data values.1 values.2.1 planned.2.1 error positive common
  let sample := Sample.build paid
  let tables := Tables.build sample.1
  let pulled := pullbacks sample.1 tables
  consume paid sample tables pulled

/-- Construct one original sample and its two consumers before evaluating the same retained materialized tail. -/
private def materializeStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error positive floor (.cons data rest))
    (common : Nat) (later : commonFloor (.cons data rest) planned ≤ common)
    (finishTail : Unit → Materialized (error := error) (positive := positive) (floor := floor)
      rest values.2.2 common) : Materialized (error := error) (positive := positive) (floor := floor)
        (.cons data rest) values common :=
  withHead (parameter := parameter) (frame := frame) (cap := cap)
    (error := error) (positive := positive) (floor := floor) data rest values planned common
    (fun paid sample tables pulled =>
      have laterMax : max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2) ≤ common :=
        Eq.mp (congrArg (fun stage : Nat => stage ≤ common) (commonFloor_cons data rest planned)) later
      let remaining := finishTail ()
      have extraLater : planned.2.2.1.2.2.val ≤ paid.2.2.2.2.val :=
        ((Data.Nat.Order.le_max_left _ _).trans laterMax).trans paid.floor_le
      let work : PotentialCells error positive common (.cons data rest) values :=
        ⟨planned.1, planned.2.1, paid, sample, remaining.1⟩
      ⟨work, ⟨⟨planned.2.2.1, extraLater⟩, tables, pulled, remaining.2⟩⟩)

/-- Materialize original requests and samples from the retained planning bank at one sufficient common floor.

The original preparation and coordinate are consumed directly. One original
Sample supplies the inverse and cube for its endpoints and both extra cells;
no preparation, Point, quotient or existing acquisition is replayed.
-/
def materialize : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
      (planned : Plan error positive floor bank) → (common : Nat) → commonFloor bank planned ≤ common →
        Materialized (error := error) (positive := positive) (floor := floor) bank values common
  | [], .nil, _, _, _, _ => ⟨⟨⟩, ⟨⟩⟩
  | _ :: _, .cons data rest, values, planned, common, later =>
      materializeStep (parameter := parameter) (frame := frame) (cap := cap)
        (error := error) (positive := positive) (floor := floor) data rest values planned common later (fun _ =>
        have laterMax : max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2) ≤ common :=
          Eq.mp (congrArg (fun stage : Nat => stage ≤ common) (commonFloor_cons data rest planned)) later
        have tailLater : commonFloor rest planned.2.2.2 ≤ common :=
          (Data.Nat.Order.le_max_right _ _).trans laterMax
        materialize rest values.2.2 planned.2.2.2 common tailLater)

/-- The complete branch consumes the same planned preparation and builds exactly one original sample. -/
private theorem packaged_materialize_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error positive floor (.cons data rest))
    (common : Nat) (later : commonFloor (.cons data rest) planned ≤ common) :
    materialize (.cons data rest) values planned common later =
      (let paid := Request.build planned.1 data.data values.1 values.2.1 planned.2.1 error positive common
       let sample := Sample.build paid
       let tables := Tables.build sample.1
       let pulled := pullbacks sample.1 tables
       have laterMax : max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2) ≤ common :=
         Eq.mp (congrArg (fun stage : Nat => stage ≤ common) (commonFloor_cons data rest planned)) later
       have tailLater : commonFloor rest planned.2.2.2 ≤ common :=
         (Data.Nat.Order.le_max_right _ _).trans laterMax
       let remaining := materialize rest values.2.2 planned.2.2.2 common tailLater
       have extraLater : planned.2.2.1.2.2.val ≤ paid.2.2.2.2.val :=
         ((Data.Nat.Order.le_max_left _ _).trans laterMax).trans paid.floor_le
       let work : PotentialCells error positive common (.cons data rest) values :=
         ⟨planned.1, planned.2.1, paid, sample, remaining.1⟩
       ⟨work, ⟨⟨planned.2.2.1, extraLater⟩, tables, pulled, remaining.2⟩⟩ :
        (work : PotentialCells error positive common (.cons data rest) values) ×
          ExtraCells error positive floor common (.cons data rest) work) := by rfl

/-- The complete branch consumes the same planned preparation and builds exactly one original sample. -/
theorem materialize_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error positive floor (.cons data rest))
    (common : Nat) (later : commonFloor (.cons data rest) planned ≤ common) :
    materialize (.cons data rest) values planned common later =
      (let paid := Request.build planned.1 data.data values.1 values.2.1 planned.2.1 error positive common
       let sample := Sample.build paid
       let tables := Tables.build sample.1
       let pulled := pullbacks sample.1 tables
       have laterMax : max planned.2.2.1.2.2.val (commonFloor rest planned.2.2.2) ≤ common :=
         Eq.mp (congrArg (fun stage : Nat => stage ≤ common) (commonFloor_cons data rest planned)) later
       have tailLater : commonFloor rest planned.2.2.2 ≤ common :=
         (Data.Nat.Order.le_max_right _ _).trans laterMax
       let remaining := materialize rest values.2.2 planned.2.2.2 common tailLater
       have extraLater : planned.2.2.1.2.2.val ≤ paid.2.2.2.2.val :=
         ((Data.Nat.Order.le_max_left _ _).trans laterMax).trans paid.floor_le
       let work : PotentialCells error positive common (.cons data rest) values :=
         ⟨planned.1, planned.2.1, paid, sample, remaining.1⟩
       ⟨work, ⟨⟨planned.2.2.1, extraLater⟩, tables, pulled, remaining.2⟩⟩ :
        (work : PotentialCells error positive common (.cons data rest) values) ×
          ExtraCells error positive floor common (.cons data rest) work) :=
  packaged_materialize_cons data rest values planned common later

end Plan

namespace Plan.Materialized

variable {error : Coordinate} {positive : 0 < error} {floor common : Nat}

/-- View the original materialized tail with its same dependent work and extra-cell cache values. -/
private def tail {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest))
    (packed : Plan.Materialized (error := error) (positive := positive) (floor := floor)
      (.cons data rest) values common) :
    Plan.Materialized (error := error) (positive := positive) (floor := floor) rest values.2.2 common :=
  ⟨packed.1.2.2.2.2, packed.2.2.2.2⟩

/-- Read the original weighted head integral from the same materialized cache without a model operation. -/
private def firstWeighted {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest))
    (packed : Plan.Materialized (error := error) (positive := positive) (floor := floor)
      (.cons data rest) values common) : Gaussian :=
  packed.2.2.2.1.1.val.model.integralSample

/-- Read the original regular-remainder head integral from that same materialized cache. -/
private def firstRegular {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest))
    (packed : Plan.Materialized (error := error) (positive := positive) (floor := floor)
      (.cons data rest) values common) : Gaussian :=
  packed.2.2.2.1.2.val.model.integralSample

/-- Traverse the same retained weighted models, reading each head before its original ordered tail.

The one materialized argument keeps each original work value together with
its dependent extra cache. The tail view pairs only the two existing tail
values; no preparation, request, inverse, power or model is reconstructed.
-/
private def weighted : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
      Plan.Materialized (error := error) (positive := positive) (floor := floor) bank values common → List Gaussian
  | [], .nil, _, _ => []
  | _ :: _, .cons data rest, values, packed =>
      let value := firstWeighted (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (positive := positive) (floor := floor) (common := common) data rest values packed
      let remaining := weighted rest values.2.2
        (tail (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (positive := positive) (floor := floor) (common := common) data rest values packed)
      value :: remaining

/-- Traverse the same retained regular-remainder models in their original order and multiplicity.

The physical model and its displacement are read directly from each packed
head. The recursive call consumes the exact original dependent tail pair,
including repeated or zero-width parent occurrences.
-/
private def regular : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
      Plan.Materialized (error := error) (positive := positive) (floor := floor) bank values common → List Gaussian
  | [], .nil, _, _ => []
  | _ :: _, .cons data rest, values, packed =>
      let value := firstRegular (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (positive := positive) (floor := floor) (common := common) data rest values packed
      let remaining := regular rest values.2.2
        (tail (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (positive := positive) (floor := floor) (common := common) data rest values packed)
      value :: remaining

end Plan.Materialized

namespace ExtraCells

variable {error : Coordinate} {positive : 0 < error} {floor common : Nat}

/-- Read the weighted integral in each unchanged parent position, retaining repeats and orientation. -/
def weighted : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → {values : Potentials bank} →
      (work : PotentialCells error positive common bank values) →
        ExtraCells error positive floor common bank work → List Gaussian
  | _, bank, values, work, extra =>
      Plan.Materialized.weighted (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (positive := positive) (floor := floor) (common := common) bank values ⟨work, extra⟩

/-- Read the regular-remainder integral in the same original parent order and on the same sample cubes. -/
def regular : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → {values : Potentials bank} →
      (work : PotentialCells error positive common bank values) →
        ExtraCells error positive floor common bank work → List Gaussian
  | _, bank, values, work, extra =>
      Plan.Materialized.regular (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (positive := positive) (floor := floor) (common := common) bank values ⟨work, extra⟩

/-- The original weighted reader returns the empty list on every supplied original empty cache. -/
private theorem packaged_weighted_nil
    {values : Potentials (.nil : Bank cap sourceDifferential count [])}
    (work : PotentialCells error positive common (.nil : Bank cap sourceDifferential count []) values)
    (extra : ExtraCells error positive floor common (.nil : Bank cap sourceDifferential count []) work) :
    weighted (.nil : Bank cap sourceDifferential count []) work extra = [] := by rfl

/-- The original weighted reader returns the empty list on every supplied original empty cache. -/
theorem weighted_nil
    {values : Potentials (.nil : Bank cap sourceDifferential count [])}
    (work : PotentialCells error positive common (.nil : Bank cap sourceDifferential count []) values)
    (extra : ExtraCells error positive floor common (.nil : Bank cap sourceDifferential count []) work) :
    weighted (.nil : Bank cap sourceDifferential count []) work extra = [] :=
  packaged_weighted_nil work extra

/-- The original weighted reader retains its actual head integral and exact ordered tails. -/
private theorem packaged_weighted_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    {values : Potentials (.cons data rest)} (work : PotentialCells error positive common (.cons data rest) values)
    (extra : ExtraCells error positive floor common (.cons data rest) work) :
    weighted (.cons data rest) work extra = extra.2.2.1.1.val.model.integralSample ::
      weighted rest work.2.2.2.2 extra.2.2.2 := by rfl

/-- The original weighted reader retains its actual head integral and exact ordered tails. -/
theorem weighted_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    {values : Potentials (.cons data rest)} (work : PotentialCells error positive common (.cons data rest) values)
    (extra : ExtraCells error positive floor common (.cons data rest) work) :
    weighted (.cons data rest) work extra = extra.2.2.1.1.val.model.integralSample ::
      weighted rest work.2.2.2.2 extra.2.2.2 := packaged_weighted_cons data rest work extra

/-- The original regular reader returns the empty list on every supplied original empty cache. -/
private theorem packaged_regular_nil
    {values : Potentials (.nil : Bank cap sourceDifferential count [])}
    (work : PotentialCells error positive common (.nil : Bank cap sourceDifferential count []) values)
    (extra : ExtraCells error positive floor common (.nil : Bank cap sourceDifferential count []) work) :
    regular (.nil : Bank cap sourceDifferential count []) work extra = [] := by rfl

/-- The original regular reader returns the empty list on every supplied original empty cache. -/
theorem regular_nil
    {values : Potentials (.nil : Bank cap sourceDifferential count [])}
    (work : PotentialCells error positive common (.nil : Bank cap sourceDifferential count []) values)
    (extra : ExtraCells error positive floor common (.nil : Bank cap sourceDifferential count []) work) :
    regular (.nil : Bank cap sourceDifferential count []) work extra = [] :=
  packaged_regular_nil work extra

/-- The original regular reader retains its actual head integral and exact ordered work/extra tails. -/
private theorem packaged_regular_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    {values : Potentials (.cons data rest)} (work : PotentialCells error positive common (.cons data rest) values)
    (extra : ExtraCells error positive floor common (.cons data rest) work) :
    regular (.cons data rest) work extra = extra.2.2.1.2.val.model.integralSample ::
      regular rest work.2.2.2.2 extra.2.2.2 := by rfl

/-- The original regular reader retains its actual head integral and exact ordered work/extra tails. -/
theorem regular_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    {values : Potentials (.cons data rest)} (work : PotentialCells error positive common (.cons data rest) values)
    (extra : ExtraCells error positive floor common (.cons data rest) work) :
    regular (.cons data rest) work extra = extra.2.2.1.2.val.model.integralSample ::
      regular rest work.2.2.2.2 extra.2.2.2 := packaged_regular_cons data rest work extra

/-- Both ordered lists retain precisely one physical cell for every original parent occurrence. -/
theorem weighted_length {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) {values : Potentials bank}
    (work : PotentialCells error positive common bank values)
    (extra : ExtraCells error positive floor common bank work) :
    (weighted bank work extra).length = parents.length := by
  induction bank with
  | nil => rfl
  | cons data rest ih => exact congrArg Nat.succ (ih work.2.2.2.2 extra.2.2.2)

/-- The regular list retains the same finite multiplicity, including zero-width and repeated occurrences. -/
theorem regular_length {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) {values : Potentials bank}
    (work : PotentialCells error positive common bank values)
    (extra : ExtraCells error positive floor common bank work) :
    (regular bank work extra).length = parents.length := by
  induction bank with
  | nil => rfl
  | cons data rest ih => exact congrArg Nat.succ (ih work.2.2.2.2 extra.2.2.2)

/-- The exact local split sums in literal parent order on the original retained sample bank. -/
theorem sum_split {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) {values : Potentials bank}
    (work : PotentialCells error positive common bank values)
    (extra : ExtraCells error positive floor common bank work) :
    gaussianSum (weighted bank work extra) =
      2 * gaussianSum (PotentialCells.integrals bank work) + gaussianSum (regular bank work extra) := by
  induction bank with
  | nil =>
      rewrite [PotentialCells.integrals_nil work]
      change (0 : Gaussian) = 2 * 0 + 0
      ring1
  | cons data rest ih =>
      have original := integral_split work.2.2.2.1.1 extra.2.1 extra.2.2.1
      have model := congrArg (fun cell : CellModel => cell.integralSample)
        (Sample.model_eq work.2.2.1 work.2.2.2.1)
      have head := original.trans (congrArg (fun value : Gaussian =>
        2 * value + extra.2.2.1.2.val.model.integralSample) model.symm)
      have tail := ih work.2.2.2.2 extra.2.2.2
      rewrite [PotentialCells.integrals_cons data rest work]
      change extra.2.2.1.1.val.model.integralSample + gaussianSum (weighted rest work.2.2.2.2 extra.2.2.2) =
        2 * ((Sample.model work.2.2.1 work.2.2.2.1).integralSample +
          gaussianSum (PotentialCells.integrals rest work.2.2.2.2)) +
          (extra.2.2.1.2.val.model.integralSample + gaussianSum (regular rest work.2.2.2.2 extra.2.2.2))
      exact (congrArg₂ (· + ·) head tail).trans (by ring1)

end ExtraCells

/-- The actual whole-bank weighted payment retains its plan, original sample bank and genuine endpoint comparisons.

The local target is chosen internally from one quarter of the final target
and the actual parent count. The new cell bank retains both weighted and
regular-remainder integrals separately; only their difference is paid here.
-/
@[expose] def Payment
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (data : Boundary.Data cap owner sourceDifferential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) : Type 3 :=
  let quarterPositive := Field.div_pos_direct positive (by decide +kernel : (0 : Coordinate) < 4)
  let error := PotentialCells.localError data.covered.parentCount (target / 4)
  let errorPositive := PotentialCells.localError_positive data.covered.parentCount (target / 4) quarterPositive
  (planned : Plan error errorPositive floor data.covered.bank) ×
  (materialized : (work : PotentialCells error errorPositive
    (Plan.commonFloor data.covered.bank planned) data.covered.bank values) ×
    ExtraCells error errorPositive floor (Plan.commonFloor data.covered.bank planned) data.covered.bank work) ×
  PotentialCells.Junctions data.covered.bank materialized.1 ×
    PotentialCells.ClosingComparison data.covered.bank materialized.1

namespace Payment

variable {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    {data : Boundary.Data cap owner sourceDifferential} {values : Potentials data.covered.bank}
    {target : Coordinate} {positive : 0 < target} {floor : Nat}

/-- Construct the finite weighted payment from the same original closed boundary and supplied potential caches.

The common floor is computed once from the retained plan before any sample
is materialized. Original junction and closing constructors consume that
same complete sample bank. No potential, preparation or old acquisition is
reconstructed in a later stage callback.
-/
def build (data : Boundary.Data cap owner sourceDifferential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) : Payment data values target positive floor :=
  let quarterPositive := Field.div_pos_direct positive (by decide +kernel : (0 : Coordinate) < 4)
  let error := PotentialCells.localError data.covered.parentCount (target / 4)
  let errorPositive := PotentialCells.localError_positive data.covered.parentCount (target / 4) quarterPositive
  let planned := Plan.build error errorPositive floor data.covered.bank
  let common := Plan.commonFloor data.covered.bank planned
  let materialized := Plan.materialize data.covered.bank values planned common (Nat.le_refl _)
  let joints := PotentialCells.junctions data.covered.bank values materialized.1 data.covered.coordinates
  let returned := Boundary.closingCoordinates data
  let closing := PotentialCells.closingComparison data.covered.bank values materialized.1 returned
  ⟨planned, materialized, joints, closing⟩

/-- The whole payment factory retains the original plan, one materialization and the two actual comparison families. -/
private theorem packaged_build_factory (data : Boundary.Data cap owner sourceDifferential)
    (values : Potentials data.covered.bank) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build data values target positive floor =
      (let quarterPositive := Field.div_pos_direct positive (by decide +kernel : (0 : Coordinate) < 4)
       let error := PotentialCells.localError data.covered.parentCount (target / 4)
       let errorPositive := PotentialCells.localError_positive data.covered.parentCount (target / 4) quarterPositive
       let planned := Plan.build error errorPositive floor data.covered.bank
       let common := Plan.commonFloor data.covered.bank planned
       let materialized := Plan.materialize data.covered.bank values planned common (Nat.le_refl _)
       let joints := PotentialCells.junctions data.covered.bank values materialized.1 data.covered.coordinates
       let returned := Boundary.closingCoordinates data
       let closing := PotentialCells.closingComparison data.covered.bank values materialized.1 returned
       ⟨planned, materialized, joints, closing⟩ : Payment data values target positive floor) := by rfl

/-- The whole payment factory retains the original plan, one materialization and the two actual comparison families. -/
theorem build_factory (data : Boundary.Data cap owner sourceDifferential) (values : Potentials data.covered.bank)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build data values target positive floor =
      (let quarterPositive := Field.div_pos_direct positive (by decide +kernel : (0 : Coordinate) < 4)
       let error := PotentialCells.localError data.covered.parentCount (target / 4)
       let errorPositive := PotentialCells.localError_positive data.covered.parentCount (target / 4) quarterPositive
       let planned := Plan.build error errorPositive floor data.covered.bank
       let common := Plan.commonFloor data.covered.bank planned
       let materialized := Plan.materialize data.covered.bank values planned common (Nat.le_refl _)
       let joints := PotentialCells.junctions data.covered.bank values materialized.1 data.covered.coordinates
       let returned := Boundary.closingCoordinates data
       let closing := PotentialCells.closingComparison data.covered.bank values materialized.1 returned
       ⟨planned, materialized, joints, closing⟩ : Payment data values target positive floor) :=
  packaged_build_factory data values target positive floor

/-- The same retained endpoint and root-return comparisons pay the original physical potential-density sum. -/
theorem potential_lt (paid : Payment data values target positive floor) :
    Norm.Basic.normSq (gaussianSum (PotentialCells.integrals data.covered.bank paid.2.1.1)) < target / 4 := by
  have bound := PotentialCells.integral_le data.covered.bank paid.2.1.1 paid.2.2.1 paid.2.2.2
  have size := congrArg (fun size : Nat => ((2 * size : Nat) : Coordinate) *
    (((2 * size : Nat) : Coordinate) * PotentialCells.localError data.covered.parentCount (target / 4)))
    data.covered.parents_length
  have localBound := PotentialCells.localError_paid data.covered.parentCount (target / 4)
    (Field.div_pos_direct positive (by decide +kernel))
  exact bound.trans_lt (size.trans_lt localBound)

/-- The ordered weighted and remainder sums obey the same exact split on the already retained original sample bank. -/
theorem integral_split (paid : Payment data values target positive floor) :
    gaussianSum (ExtraCells.weighted data.covered.bank paid.2.1.1 paid.2.1.2) =
      2 * gaussianSum (PotentialCells.integrals data.covered.bank paid.2.1.1) +
        gaussianSum (ExtraCells.regular data.covered.bank paid.2.1.1 paid.2.1.2) :=
  ExtraCells.sum_split data.covered.bank paid.2.1.1 paid.2.1.2

/-- Internally selected local and endpoint payments bound the actual ordered weighted-minus-remainder integral sum.

The regular remainder is not set to zero. Both independent lists are the
physical pullbacks on the same original cells and retained inverse cubes;
canonical period attachment and a physical regular primitive remain separate.
-/
theorem accurate (paid : Payment data values target positive floor) :
    Norm.Basic.normSq
      (gaussianSum (ExtraCells.weighted data.covered.bank paid.2.1.1 paid.2.1.2) -
        gaussianSum (ExtraCells.regular data.covered.bank paid.2.1.1 paid.2.1.2)) < target := by
  have split := paid.integral_split
  have difference := congrArg (fun value : Gaussian =>
    value - gaussianSum (ExtraCells.regular data.covered.bank paid.2.1.1 paid.2.1.2)) split
  have twice : gaussianSum (ExtraCells.weighted data.covered.bank paid.2.1.1 paid.2.1.2) -
      gaussianSum (ExtraCells.regular data.covered.bank paid.2.1.1 paid.2.1.2) =
        2 * gaussianSum (PotentialCells.integrals data.covered.bank paid.2.1.1) :=
    difference.trans (by ring1)
  have scalar := (congrArg Norm.Basic.normSq twice).trans
    (Norm.Basic.normSq_mul 2 (gaussianSum (PotentialCells.integrals data.covered.bank paid.2.1.1)))
  have two : Norm.Basic.normSq (2 : Gaussian) = (4 : Coordinate) := by decide +kernel
  have squared := scalar.trans (congrArg (fun value : Coordinate =>
    value * Norm.Basic.normSq (gaussianSum (PotentialCells.integrals data.covered.bank paid.2.1.1))) two)
  have small := Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide +kernel : (0 : Coordinate) < 4) paid.potential_lt
  have cancellation : 4 * (target / 4) = target :=
    (Field.mul_comm 4 (target / 4)).trans (Field.div_mul_cancel_of_ne target 4 (by decide +kernel))
  exact squared.trans_lt (small.trans_eq cancellation)

end Payment

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration

end
