module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Cells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison.Bank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic

/-! # Checked cells on one globally retained regular sample

The recursive worker descends through the literal plan and request tails,
keeping the actual global regular sample and coefficient fixed. It stores
each original checked Head and one original-bank view assembled from those
same Head caches. The supplied common reciprocal floor may be enlarged.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive
  (regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedCell)
open Purelib.Data.Gaussian

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace LiftedCells

/-- The actual labelled lifted cell and continued Point family on one literal planned coordinate, then its tail. -/
@[expose] def Entry {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent)
    (coordinate : Spatial.Coordinate data.segment.comparison.first data.segment.comparison.last)
    (remaining : Type 3) : Type 3 :=
  (firstSheet : Fin 2) × (lastSheet : Fin 2) ×
  (_cell : LiftedCell ⟨data.segment.comparison.first, firstSheet⟩ ⟨data.segment.comparison.last, lastSheet⟩) ×
  (_points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
    Point data.terminal.neighborhood.patch (coordinate.point input)) × remaining

end LiftedCells

/-- Ordered genuine lifted cells and Point callbacks retain the exact original bank and planned coordinate owners. -/
@[expose] def LiftedCells : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → Plan error errorPositive floor bank → Type 3
  | [], .nil, _ => PUnit
  | _ :: _, .cons data rest, planned =>
      LiftedCells.Entry data planned.2.1 (LiftedCells rest planned.2.2.2)

namespace Heads

/-- One retained actual Head uses the same global regular sample and its original request entry, followed by a tail. -/
@[expose] def Entry {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) {requestTail pathTail : Type 3}
    (requests : Requests.Entry data planned regular coefficient accuracy positive requestTail)
    (paths : LiftedCells.Entry data planned.2.1 pathTail) (remaining : Type 3) : Type 3 :=
  Head (parameter := parameter) (frame := frame) (cap := cap)
    data rest values planned regular requests.1.val accuracy requests.2.1.val common
    (firstSheet := paths.1) (lastSheet := paths.2.1) paths.2.2.1 paths.2.2.2.1 × remaining

end Heads

/-- Every ordered original occurrence retains its one checked Head at the unchanged shared regular index. -/
@[expose] def Heads {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            LiftedCells bank planned → Type 3 := by
  intro parents bank
  induction bank with
  | nil => exact fun _ _ _ _ => PUnit
  | cons data rest ih =>
      intro values planned requests paths
      exact Heads.Entry (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor) (index := index) (box := box)
        (requestTail := Requests regular coefficient accuracy positive rest planned.2.2.2)
        (pathTail := LiftedCells rest planned.2.2.2)
        data rest values planned regular coefficient accuracy positive common requests paths
        (ih values.2.2 planned.2.2.2
          requests.2.2.2 paths.2.2.2.2)

namespace Heads

/-- Build the actual checked Head before evaluating its original delayed tail. -/
private def buildStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (physicalPaid : Requests.maximum (.cons data rest) planned requests ≤ common)
    (finishTail : Unit → Heads regular coefficient accuracy positive common rest values.2.2 planned.2.2.2
      requests.2.2.2 paths.2.2.2.2) :
    Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths :=
  have head : requests.2.2.1.val ≤ Requests.maximum (.cons data rest) planned requests :=
    Eq.mp (congrArg (fun value : Nat => requests.2.2.1.val ≤ value)
      (Requests.maximum_cons data rest planned requests).symm) (Data.Nat.Order.le_max_left _ _)
  have paid : Nat.max requests.2.1.val.1.stage requests.2.1.val.2.selection.stage ≤ common :=
    Eq.mp (congrArg (fun value : Nat => value ≤ common) requests.2.2.1.property) (head.trans physicalPaid)
  let actual := Head.build (parameter := parameter) (frame := frame) (cap := cap)
    data rest values planned regular requests.1.val accuracy requests.2.1.val common paid
    (firstSheet := paths.1) (lastSheet := paths.2.1) paths.2.2.1 paths.2.2.2.1
  let remaining := finishTail ()
  ⟨actual, remaining⟩

/-- Construct each checked Head once, propagating all three payments through the same literal cache tails.

The regular sample and certified coefficient remain fixed throughout.
The common reciprocal floor is any genuinely paid later floor; it is
not required to equal an earlier cache's smallest sufficient maximum.
-/
def build {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (pFloor common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (selections : Selections accuracy positive pFloor bank planned) →
            (requests : Requests regular coefficient accuracy positive bank planned) →
              (paths : LiftedCells bank planned) →
                Selections.maximum bank planned selections ≤ index →
                  Requests.maximum bank planned requests ≤ common → Plan.commonFloor bank planned ≤ common →
                    Heads regular coefficient accuracy positive common bank values planned requests paths
  := by
  intro parents bank
  refine Bank.fold (motive := fun {_parents} bank =>
    (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (selections : Selections accuracy positive pFloor bank planned) →
            (requests : Requests regular coefficient accuracy positive bank planned) →
              (paths : LiftedCells bank planned) →
                Selections.maximum bank planned selections ≤ index →
                  Requests.maximum bank planned requests ≤ common → Plan.commonFloor bank planned ≤ common →
                    Heads regular coefficient accuracy positive common bank values planned requests paths) ?_ ?_ bank
  · exact fun _ _ _ _ _ _ _ _ => ⟨⟩
  · intro parent parents data rest finishTail values planned selections requests paths
        regularPaid physicalPaid originalPaid
    exact buildStep (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (index := index) (box := box)
      data rest values planned regular coefficient accuracy positive common requests paths physicalPaid (fun _ =>
        have tailRegular := (Selections.tail_le data rest planned selections).trans regularPaid
        have tailPhysical := (Requests.tail_le data rest planned requests).trans physicalPaid
        have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
          Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
        have tailOriginal := (Data.Nat.Order.le_max_right _ _).trans originalMax
        let remaining := finishTail ()
        remaining values.2.2 planned.2.2.2 selections.2.2 requests.2.2.2 paths.2.2.2.2
          tailRegular tailPhysical tailOriginal)

/-- Assemble an original-bank head from its same actual Head caches and already retained original tail. -/
private def originalStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (head : Head data rest values planned regular requests.1.val accuracy requests.2.1.val common
      (firstSheet := paths.1) (lastSheet := paths.2.1) paths.2.2.1 paths.2.2.2.1)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common)
    (finishTail : Unit → Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
      rest values.2.2 common) :
    Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
      (.cons data rest) values common :=
  have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
    Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
  have extraPaid : planned.2.2.1.2.2.val ≤ head.paid.2.2.2.2.val :=
    ((Data.Nat.Order.le_max_left _ _).trans originalMax).trans head.paid.floor_le
  let remaining := finishTail ()
  let work : PotentialCells error errorPositive common (.cons data rest) values :=
    ⟨planned.1, planned.2.1, head.paid, head.sample, remaining.1⟩
  ⟨work, ⟨⟨planned.2.2.1, extraPaid⟩, head.tables, head.pullbacks, remaining.2⟩⟩

/-- The abstract original-view head worker retains the supplied Head's exact regular integral scalar. -/
private theorem originalStep_head_regular {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (head : Head data rest values planned regular requests.1.val accuracy requests.2.1.val common
      (firstSheet := paths.1) (lastSheet := paths.2.1) paths.2.2.1 paths.2.2.2.1)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common)
    (finishTail : Unit → Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
      rest values.2.2 common) :
    (originalStep (parameter := parameter) (frame := frame) (cap := cap)
      data rest values planned regular coefficient accuracy positive common requests paths head originalPaid
      finishTail).2.2.2.1.2.val.model.integralSample = head.pullbacks.2.val.model.integralSample := by rfl

/-- The abstract original-view worker retains both complete supplied Head models. -/
private theorem originalStep_head_models {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (head : Head data rest values planned regular requests.1.val accuracy requests.2.1.val common
      (firstSheet := paths.1) (lastSheet := paths.2.1) paths.2.2.1 paths.2.2.2.1)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common)
    (finishTail : Unit → Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
      rest values.2.2 common) :
    ((originalStep (parameter := parameter) (frame := frame) (cap := cap)
      data rest values planned regular coefficient accuracy positive common requests paths head originalPaid
      finishTail).2.2.2.1.1.val.model,
      (originalStep (parameter := parameter) (frame := frame) (cap := cap)
      data rest values planned regular coefficient accuracy positive common requests paths head originalPaid
      finishTail).2.2.2.1.2.val.model) =
      (head.pullbacks.1.val.model, head.pullbacks.2.val.model) := by rfl

/-- The original-view function retains all original cache arguments and their actual stage payment.

Its body is exposed so consumers can apply the function at the same values,
plan, requests, lifted cells and Heads. The result remains the original
PotentialCells/ExtraCells owner; this is an exact function-type alias.
-/
@[expose] def Original
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 := fun {_parents} bank =>
    (values : Potentials bank) →
      (planned : Plan error errorPositive floor bank) →
        (requests : Requests regular coefficient accuracy positive bank planned) →
          (paths : LiftedCells bank planned) →
            Heads regular coefficient accuracy positive common bank values planned requests paths →
              Plan.commonFloor bank planned ≤ common →
                Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
                  bank values common

/-- The original empty-view value at the exact original function family. -/
private def originalEmpty {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    Original (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common .nil :=
  fun _ _ _ _ _ _ => ⟨⟨⟩, ⟨⟩⟩

/-- The original view algebra consumes its head and delays the same literal checked cache tail.

The function family stays named in its signature. Both the executable fold
and its pointwise readbacks consume this same algebra and head worker.
-/
private def originalAlgebra {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (finishTail : Unit → Original (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common rest) :
    Original (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common (.cons data rest) :=
  fun values planned requests paths heads originalPaid =>
      originalStep (parameter := parameter) (frame := frame) (collar := collar) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor) (index := index) (box := box)
        data rest values planned regular coefficient accuracy positive common requests paths heads.1 originalPaid
        (fun _ =>
          have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
            Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned))
              originalPaid
          have tailOriginal := (Data.Nat.Order.le_max_right _ _).trans originalMax
          let remaining := finishTail ()
          remaining values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 tailOriginal)

/-- Form the original PotentialCells and ExtraCells tuple spines from the same retained Head values.

This is a linear view construction. It performs no request, sample,
model, numerator attachment, continued Point or original materializer call.
-/
def original {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        Original (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common bank
  := fun {_parents} bank =>
  Bank.fold (motive := Original (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common)
    (originalEmpty (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) regular coefficient accuracy positive common)
    (originalAlgebra (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common) bank

set_option linter.unusedVariables false in
/-- The retained first Selection pays the actual first Head's local primitive-versus-regular integral error.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition. The named `regularPaid` premise is retained for
callers and the proof, although it is absent from the conclusion.
-/
@[expose] def HeadIntegralLtLaw : Prop :=
  ∀
    {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {count : Nat}
    {error : Coordinate}
    {errorPositive : 0 < error}
    {floor : Nat}
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent)
    (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest))
    (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat}
    {box : Box}
    {target : Coordinate}
    {positive : 0 < target / 4}
    {pFloor : Nat}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (common : Nat)
    (selections : Selections (target / 4) positive pFloor (.cons data rest) planned)
    (requests : Requests regular coefficient (target / 4) positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient (target / 4) positive common (.cons data rest) values planned requests paths)
    (regularPaid : Selections.maximum (.cons data rest) planned selections ≤ index),
    Norm.Basic.normSq (heads.1.attached.physical.cell.value.eval data.segment.comparison.last -
      heads.1.attached.physical.cell.value.eval data.segment.comparison.first -
      heads.1.pullbacks.2.val.model.integralSample) < target

/-- The retained first Selection pays the actual first Head's local primitive-versus-regular integral error. -/
theorem head_integral_lt : HeadIntegralLtLaw := by
  unfold HeadIntegralLtLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor parent parents data rest
    values planned index box target positive pFloor regular coefficient common selections requests paths heads
    regularPaid
  exact Head.integral_lt (parameter := parameter) (frame := frame) (cap := cap)
      data rest values planned regular requests.1.val requests.2.1.val common
      (firstSheet := paths.1) (lastSheet := paths.2.1) paths.2.2.1 paths.2.2.2.1 heads.1
      selections.1.val selections.2.1.val ((Selections.head_le data rest planned selections).trans regularPaid)

section

attribute [local irreducible] Original

/-- One owned fold equation retains the complete original-view function on a cons bank.

The equality is the original dependent fold's equation before application
to any preparation, Head or view. It preserves the original delayed tail
and uses no equality between functions derived from pointwise premises.
-/
private theorem original_fold_cons
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents) :
    (original regular coefficient accuracy positive common (.cons data rest) :
      Original (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common (.cons data rest)) =
      originalAlgebra (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common data rest
        (fun _ => original regular coefficient accuracy positive common rest) :=
  Bank.fold_cons (motive := Original (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) regular coefficient accuracy positive common)
    (originalEmpty (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) regular coefficient accuracy positive common)
    (originalAlgebra (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common) data rest

end

/-- The original view retains exactly the same actual regular head integral as the supplied checked Head. -/
private theorem packaged_original_head_regular {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common) :
    (original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.1.2.val.model.integralSample =
      heads.1.pullbacks.2.val.model.integralSample := by
  have folded := original_fold_cons (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common data rest
  have applied := congrArg
    (fun next : Original (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common (.cons data rest) =>
      next values planned requests paths heads originalPaid) folded
  have observed := congrArg
    (fun value : Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
        (.cons data rest) values common => value.2.2.2.1.2.val.model.integralSample) applied
  have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
    Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
  have tailPaid := (Data.Nat.Order.le_max_right _ _).trans originalMax
  exact observed.trans (originalStep_head_regular (parameter := parameter) (frame := frame) (cap := cap)
    data rest values planned regular coefficient accuracy positive common requests paths heads.1 originalPaid
    (fun _ => original regular coefficient accuracy positive common rest values.2.2 planned.2.2.2
      requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid))

/-- The original view retains exactly the same actual regular head integral as the supplied checked Head.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def OriginalHeadRegularLaw : Prop :=
  ∀
    {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {count : Nat}
    {error : Coordinate}
    {errorPositive : 0 < error}
    {floor : Nat}
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent)
    (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest))
    (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat}
    {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common),
    (original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.1.2.val.model.integralSample =
      heads.1.pullbacks.2.val.model.integralSample

/-- The original view retains exactly the same actual regular head integral as the supplied checked Head. -/
theorem original_head_regular : OriginalHeadRegularLaw := by
  unfold OriginalHeadRegularLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor parent parents data rest
    values planned index box regular coefficient accuracy positive common requests paths heads originalPaid
  exact packaged_original_head_regular data rest values planned regular coefficient accuracy positive common
      requests paths heads originalPaid

/-- The original view keeps both complete weighted and regular models of the same supplied checked Head. -/
private theorem packaged_original_head_models {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common) :
    ((original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.1.1.val.model,
      (original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.1.2.val.model) =
      (heads.1.pullbacks.1.val.model, heads.1.pullbacks.2.val.model) := by
  have folded := original_fold_cons (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common data rest
  have applied := congrArg
    (fun next : Original (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common (.cons data rest) =>
      next values planned requests paths heads originalPaid) folded
  have observed := congrArg
    (fun value : Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
        (.cons data rest) values common =>
      (value.2.2.2.1.1.val.model, value.2.2.2.1.2.val.model)) applied
  have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
    Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
  have tailPaid := (Data.Nat.Order.le_max_right _ _).trans originalMax
  exact observed.trans (originalStep_head_models (parameter := parameter) (frame := frame) (cap := cap)
    data rest values planned regular coefficient accuracy positive common requests paths heads.1 originalPaid
    (fun _ => original regular coefficient accuracy positive common rest values.2.2 planned.2.2.2
      requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid))

/-- The original view keeps both complete weighted and regular models of the same supplied checked Head.

This is whole-model identity on the retained fields, rather than equality
of only their scalar integrals. The existing original-tail law preserves
the accompanying complete work and extra caches.
-/
theorem original_head_models {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common) :
    ((original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.1.1.val.model,
      (original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.1.2.val.model) =
      (heads.1.pullbacks.1.val.model, heads.1.pullbacks.2.val.model) :=
  packaged_original_head_models data rest values planned regular coefficient accuracy positive common
    requests paths heads originalPaid

/-- The whole original work/extra tail is the original view of the same literal checked Head tail. -/
private theorem packaged_original_tail {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common)
    (tailPaid : Plan.commonFloor rest planned.2.2.2 ≤ common) :
    (⟨(original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).1.2.2.2.2,
      (original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.2⟩ :
      Plan.Materialized (error := error) (positive := errorPositive) (floor := floor) rest values.2.2 common) =
      original regular coefficient accuracy positive common rest values.2.2 planned.2.2.2
        requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid := by
  have folded := original_fold_cons (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common data rest
  exact congrArg
    (fun next : Original (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common (.cons data rest) =>
      (⟨(next values planned requests paths heads originalPaid).1.2.2.2.2,
        (next values planned requests paths heads originalPaid).2.2.2.2⟩ :
        Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
          rest values.2.2 common)) folded

/-- The whole original work/extra tail is the original view of the same literal checked Head tail.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def OriginalTailLaw : Prop :=
  ∀
    {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {count : Nat}
    {error : Coordinate}
    {errorPositive : 0 < error}
    {floor : Nat}
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent)
    (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest))
    (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat}
    {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths)
    (originalPaid : Plan.commonFloor (.cons data rest) planned ≤ common)
    (tailPaid : Plan.commonFloor rest planned.2.2.2 ≤ common),
    (⟨(original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).1.2.2.2.2,
      (original regular coefficient accuracy positive common
      (.cons data rest) values planned requests paths heads originalPaid).2.2.2.2⟩ :
      Plan.Materialized (error := error) (positive := errorPositive) (floor := floor) rest values.2.2 common) =
      original regular coefficient accuracy positive common rest values.2.2 planned.2.2.2
        requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid

/-- The whole original work/extra tail is the original view of the same literal checked Head tail. -/
theorem original_tail : OriginalTailLaw := by
  unfold OriginalTailLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor parent parents data rest
    values planned index box regular coefficient accuracy positive common requests paths heads originalPaid
    tailPaid
  exact packaged_original_tail data rest values planned regular coefficient accuracy positive common
      requests paths heads originalPaid tailPaid

end Heads

/-- The checked Head bank and one retained exact original-bank view on those same complete caches.

The view is constructed once and stored for repeated original consumers.
The complete named view-factory identity is retained as a subtype field;
no original request, sample or acquisition is repeated to construct it.
-/
@[expose] def Materialized {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common) : Type 3 :=
  (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) ×
  { value : Plan.Materialized (error := error) (positive := errorPositive) (floor := floor) bank values common //
    value = Heads.original regular coefficient accuracy positive common bank values planned requests paths
      heads originalPaid }

namespace Materialized

/-- Cache one abstract original-bank view of the already retained checked Heads. -/
private def ofHeads {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) :
    Materialized regular coefficient accuracy positive common bank values planned requests paths originalPaid :=
  let original := Heads.original regular coefficient accuracy positive common
    bank values planned requests paths heads originalPaid
  ⟨heads, ⟨original, rfl⟩⟩

/-- Read the same stored ordered checked Head bank. -/
abbrev heads {index : Nat} {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {coefficient : { value : Polynomial // value = regular.physicalCoefficient }}
    {accuracy : Coordinate} {positive : 0 < accuracy} {common : Nat}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {values : Potentials bank}
    {planned : Plan error errorPositive floor bank}
    {requests : Requests regular coefficient accuracy positive bank planned} {paths : LiftedCells bank planned}
    {originalPaid : Plan.commonFloor bank planned ≤ common}
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid) :
    Heads regular coefficient accuracy positive common bank values planned requests paths := actual.1

/-- Read the retained original PotentialCells/ExtraCells view without reconstructing its tuple spines. -/
abbrev original {index : Nat} {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {coefficient : { value : Polynomial // value = regular.physicalCoefficient }}
    {accuracy : Coordinate} {positive : 0 < accuracy} {common : Nat}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {values : Potentials bank}
    {planned : Plan error errorPositive floor bank}
    {requests : Requests regular coefficient accuracy positive bank planned} {paths : LiftedCells bank planned}
    {originalPaid : Plan.commonFloor bank planned ≤ common}
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid) :
    Plan.Materialized (error := error) (positive := errorPositive) (floor := floor) bank values common := actual.2.val

/-- The whole cached original view is the original-owner tuple view of these same retained Heads.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def OriginalEqLaw : Prop :=
  ∀
    {parameter : Gaussian}
    {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}
    {count : Nat}
    {error : Coordinate}
    {errorPositive : 0 < error}
    {floor : Nat}
    {index : Nat}
    {box : Box}
    {regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {coefficient : { value : Polynomial // value = regular.physicalCoefficient }}
    {accuracy : Coordinate}
    {positive : 0 < accuracy}
    {common : Nat}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents}
    {values : Potentials bank}
    {planned : Plan error errorPositive floor bank}
    {requests : Requests regular coefficient accuracy positive bank planned}
    {paths : LiftedCells bank planned}
    {originalPaid : Plan.commonFloor bank planned ≤ common}
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid),
    actual.original = Heads.original regular coefficient accuracy positive common
      bank values planned requests paths actual.heads originalPaid

/-- The whole cached original view is the original-owner tuple view of these same retained Heads. -/
theorem original_eq : OriginalEqLaw := by
  unfold OriginalEqLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common parents bank values planned requests paths originalPaid actual
  exact actual.2.property

end Materialized

/-- Materialize checked Heads and cache their original-bank view at any common floor paying the retained requests.

The actual global regular sample/coefficient are passed unchanged through
all literal suffixes. Additional endpoint requests can enlarge common
without rebuilding or retagging either sample family.
-/
def materialize {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    {target : Coordinate} {positive : 0 < target / 4} {pFloor : Nat} {box : Box}
    (cached : Primitive target positive pFloor box bank planned) (common : Nat)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (physicalPaid : Requests.maximum bank planned cached.2.2.2.2 ≤ common)
    (paths : LiftedCells bank planned) :
    Materialized cached.2.2.1.val cached.2.2.2.1 (target / 4) positive common
      bank values planned cached.2.2.2.2 paths originalPaid :=
  have regularPaid : Selections.maximum bank planned cached.1 ≤ cached.2.1.val :=
    Eq.mp (congrArg (fun value : Nat => value ≤ cached.2.1.val) cached.2.1.property)
      (Nat.le_refl cached.2.1.val)
  let heads := Heads.build (parameter := parameter) (frame := frame) (cap := cap)
    cached.2.2.1.val cached.2.2.2.1 (target / 4) positive pFloor common bank values planned
    cached.1 cached.2.2.2.2 paths regularPaid physicalPaid originalPaid
  Materialized.ofHeads (parameter := parameter) (frame := frame) (cap := cap)
    cached.2.2.1.val cached.2.2.2.1 (target / 4) positive common bank values planned
    cached.2.2.2.2 paths originalPaid heads

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
