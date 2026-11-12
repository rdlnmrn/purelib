module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Materialized
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison.Bank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order

/-! # Ordered primitive and regular readings on retained checked cells

Each original occurrence contributes its actual primitive polynomial endpoint
difference and the regular integral of the same retained physical pullback.
A finite list caches those two scalar readings once. Its right column is the
unchanged original-bank regular list, and its paid discrepancy bound keeps
the actual occurrence count, including repeated and empty occurrences.
-/

public section

universe u

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
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace Heads

/-- The exact function result of reading scalar pairs from one supplied checked bank. -/
private def ReadingFamily
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {_parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells bank planned) →
          Heads regular coefficient accuracy positive common bank values planned requests paths →
            List (Gaussian × Gaussian)

/-- Read the scalar head before invoking its delayed literal cache tail. -/
private def readingStep
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (finishTail : Unit → ReadingFamily (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common rest) :
    ReadingFamily (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common (.cons data rest) :=
  fun values planned requests paths heads =>
    let primitive := heads.1.attached.physical.cell.value
    let pair : Gaussian × Gaussian :=
      ⟨primitive.eval data.segment.comparison.last - primitive.eval data.segment.comparison.first,
        heads.1.pullbacks.2.val.model.integralSample⟩
    let remaining := finishTail ()
    pair :: remaining values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2

/-- Read the two actual scalar values of every supplied Head in the original ordered bank.

The left scalar uses its attached primitive's same polynomial at the two
actual endpoints. The right scalar is the original regular pullback sample.
No request, sample, model, attachment or original-bank view is rebuilt.
-/
def readings
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              Heads regular coefficient accuracy positive common bank values planned requests paths →
                List (Gaussian × Gaussian) :=
  fun {_parents} bank =>
    Bank.fold (motive := ReadingFamily (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common)
      (fun _ _ _ _ _ => [])
      (readingStep (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common) bank

/-- The empty ordered bank has no scalar reading pairs. -/
private theorem packaged_readings_nil
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (values : Potentials (.nil : Bank cap sourceDifferential count []))
    (planned : Plan error errorPositive floor .nil)
    (requests : Requests regular coefficient accuracy positive .nil planned)
    (paths : LiftedCells .nil planned)
    (heads : Heads regular coefficient accuracy positive common .nil values planned requests paths) :
    readings regular coefficient accuracy positive common .nil values planned requests paths heads = [] := by
  have folded := Bank.fold_nil (motive := ReadingFamily (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common)
    (fun _ _ _ _ _ => [])
    (readingStep (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common)
  exact congrArg
    (fun next : ReadingFamily (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common .nil =>
      next values planned requests paths heads) folded

/-- The empty ordered bank has no scalar reading pairs.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ReadingsNilLaw : Prop :=
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
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    (values : Potentials (.nil : Bank cap sourceDifferential count []))
    (planned : Plan error errorPositive floor .nil)
    (requests : Requests regular coefficient accuracy positive .nil planned)
    (paths : LiftedCells .nil planned)
    (heads : Heads regular coefficient accuracy positive common .nil values planned requests paths),
    readings regular coefficient accuracy positive common .nil values planned requests paths heads = []

/-- The empty ordered bank has no scalar reading pairs. -/
theorem readings_nil : ReadingsNilLaw := by
  unfold ReadingsNilLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common values planned requests paths heads
  exact packaged_readings_nil regular coefficient accuracy positive common values planned requests paths heads

/-- The first scalar pair is followed by the same literal checked Head tail. -/
private theorem packaged_readings_cons
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths) :
    readings regular coefficient accuracy positive common (.cons data rest) values planned requests paths heads =
      (heads.1.attached.physical.cell.value.eval data.segment.comparison.last -
        heads.1.attached.physical.cell.value.eval data.segment.comparison.first,
      heads.1.pullbacks.2.val.model.integralSample) ::
        readings regular coefficient accuracy positive common
          rest values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 := by
  have folded := Bank.fold_cons (motive := ReadingFamily (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common)
    (fun _ _ _ _ _ => [])
    (readingStep (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common) data rest
  have observed := congrArg
    (fun next : ReadingFamily (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common (.cons data rest) =>
      next values planned requests paths heads) folded
  exact observed

/-- The first scalar pair is followed by the same literal checked Head tail.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ReadingsConsLaw : Prop :=
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
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths),
    readings regular coefficient accuracy positive common (.cons data rest) values planned requests paths heads =
      (heads.1.attached.physical.cell.value.eval data.segment.comparison.last -
        heads.1.attached.physical.cell.value.eval data.segment.comparison.first,
      heads.1.pullbacks.2.val.model.integralSample) ::
        readings regular coefficient accuracy positive common
          rest values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2

/-- The first scalar pair is followed by the same literal checked Head tail. -/
theorem readings_cons : ReadingsConsLaw := by
  unfold ReadingsConsLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor parent parents data rest
    values planned index box regular coefficient accuracy positive common requests paths heads
  exact packaged_readings_cons data rest values planned regular coefficient accuracy positive common
      requests paths heads

/-- Scalar reading pairs retain the exact original ordered occurrence count.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ReadingsLengthLaw : Prop :=
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
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat),
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (readings regular coefficient accuracy positive common
                  bank values planned requests paths heads).length = parents.length

/-- Scalar reading pairs retain the exact original ordered occurrence count. -/
theorem readings_length : ReadingsLengthLaw := by
  unfold ReadingsLengthLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common parents bank
  induction bank with
  | nil =>
      intro values planned requests paths heads
      exact congrArg List.length
        (readings_nil regular coefficient accuracy positive common values planned requests paths heads)
  | cons data rest ih =>
      intro values planned requests paths heads
      have step := congrArg List.length
        (readings_cons data rest values planned regular coefficient accuracy positive common requests paths heads)
      exact step.trans (congrArg Nat.succ
        (ih values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2))

/-- The right column is the regular list of the whole original-bank view of these same Heads.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ReadingsRegularLaw : Prop :=
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
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat),
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (originalPaid : Plan.commonFloor bank planned ≤ common) →
                  (readings regular coefficient accuracy positive common
                    bank values planned requests paths heads).map Prod.snd =
                    ExtraCells.regular bank
                      (original regular coefficient accuracy positive common
                        bank values planned requests paths heads originalPaid).1
                      (original regular coefficient accuracy positive common
                        bank values planned requests paths heads originalPaid).2

/-- The right column is the regular list of the whole original-bank view of these same Heads. -/
theorem readings_regular : ReadingsRegularLaw := by
  unfold ReadingsRegularLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common parents bank
  induction bank with
  | nil =>
      intro values planned requests paths heads originalPaid
      have empty := readings_nil regular coefficient accuracy positive common values planned requests paths heads
      have old := ExtraCells.regular_nil
        (original regular coefficient accuracy positive common .nil values planned requests paths heads originalPaid).1
        (original regular coefficient accuracy positive common .nil values planned requests paths heads originalPaid).2
      exact (congrArg (fun rows : List (Gaussian × Gaussian) => rows.map Prod.snd) empty).trans old.symm
  | cons data rest ih =>
      intro values planned requests paths heads originalPaid
      have originalMax : Nat.max planned.2.2.1.2.2.val (Plan.commonFloor rest planned.2.2.2) ≤ common :=
        Eq.mp (congrArg (fun value : Nat => value ≤ common) (Plan.commonFloor_cons data rest planned)) originalPaid
      have tailPaid := (Data.Nat.Order.le_max_right _ _).trans originalMax
      have headReadback := original_head_regular data rest values planned regular coefficient accuracy positive common
        requests paths heads originalPaid
      have tailReadback := congrArg
        (fun cached : Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
            rest values.2.2 common => ExtraCells.regular rest cached.1 cached.2)
        (original_tail data rest values planned regular coefficient accuracy positive common
          requests paths heads originalPaid tailPaid)
      have old := ExtraCells.regular_cons data rest
        (original regular coefficient accuracy positive common
          (.cons data rest) values planned requests paths heads originalPaid).1
        (original regular coefficient accuracy positive common
          (.cons data rest) values planned requests paths heads originalPaid).2
      have sameHead := congrArg
        (fun value : Gaussian => value :: ExtraCells.regular rest
          (original regular coefficient accuracy positive common
            (.cons data rest) values planned requests paths heads originalPaid).1.2.2.2.2
          (original regular coefficient accuracy positive common
            (.cons data rest) values planned requests paths heads originalPaid).2.2.2.2) headReadback
      have sameTail := congrArg (List.cons heads.1.pullbacks.2.val.model.integralSample) tailReadback
      have oldPair := old.trans (sameHead.trans sameTail)
      have newPair := congrArg (fun rows : List (Gaussian × Gaussian) => rows.map Prod.snd)
        (readings_cons data rest values planned regular coefficient accuracy positive common requests paths heads)
      have remaining := ih values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 tailPaid
      exact newPair.trans ((congrArg (List.cons heads.1.pullbacks.2.val.model.integralSample) remaining).trans
        oldPair.symm)

/-- Every retained scalar pair is paid by its actual first Selection at the unchanged global regular stage.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ReadingsBoundedLaw : Prop :=
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
    {entryTarget : Coordinate}
    {positive : 0 < entryTarget / 4}
    {pFloor : Nat}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (common : Nat),
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (selections : Selections (entryTarget / 4) positive pFloor bank planned) →
            (requests : Requests regular coefficient (entryTarget / 4) positive bank planned) →
              (paths : LiftedCells bank planned) →
                (heads : Heads regular coefficient (entryTarget / 4) positive common
                  bank values planned requests paths) →
                  Selections.maximum bank planned selections ≤ index →
                    ∀ pair ∈ readings regular coefficient (entryTarget / 4) positive common
                        bank values planned requests paths heads,
                      Norm.Basic.normSq (pair.1 - pair.2) < entryTarget

/-- Every retained scalar pair is paid by its actual first Selection at the unchanged global regular stage. -/
theorem readings_bounded : ReadingsBoundedLaw := by
  unfold ReadingsBoundedLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box entryTarget
    positive pFloor regular coefficient common parents bank
  induction bank with
  | nil =>
      intro values planned selections requests paths heads regularPaid pair member
      have empty := readings_nil regular coefficient (entryTarget / 4) positive common
        values planned requests paths heads
      have absent := Eq.mp (congrArg (fun rows : List (Gaussian × Gaussian) => pair ∈ rows) empty) member
      nomatch absent
  | cons data rest ih =>
      intro values planned selections requests paths heads regularPaid pair member
      have layout := readings_cons data rest values planned regular coefficient (entryTarget / 4) positive common
        requests paths heads
      have present := Eq.mp (congrArg (fun rows : List (Gaussian × Gaussian) => pair ∈ rows) layout) member
      cases Data.List.Membership.mem_cons.mp present with
      | inl same =>
          have head := head_integral_lt (index := index) (box := box)
            (target := entryTarget) (positive := positive) (pFloor := pFloor)
            data rest values planned regular coefficient common
            selections requests paths heads regularPaid
          exact (congrArg (fun row : Gaussian × Gaussian => Norm.Basic.normSq (row.1 - row.2)) same).trans_lt head
      | inr member =>
          exact ih values.2.2 planned.2.2.2 selections.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
            ((Selections.tail_le data rest planned selections).trans regularPaid) pair member

end Heads

namespace Materialized

/-- One scalar-pair list retains its whole reading-factory identity on the same stored checked bank.

This subtype caches the newly evaluated endpoint differences and original
regular sample scalars. It retains the supplied Materialized owner rather
than rebuilding any Head, original view or acquisition.
-/
@[expose] def Readings
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid) : Type :=
  { rows : List (Gaussian × Gaussian) //
    rows = Heads.readings regular coefficient accuracy positive common
      bank values planned requests paths actual.heads }

/-- Evaluate and retain the ordered scalar-pair list once on the existing stored checked bank. -/
def readings
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid) :
    Readings regular coefficient accuracy positive common bank values planned requests paths originalPaid actual :=
  let rows := Heads.readings regular coefficient accuracy positive common
    bank values planned requests paths actual.heads
  ⟨rows, rfl⟩

namespace Readings

/-- The retained scalar-pair list is exactly the original ordered reader on the same stored Heads.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def RowsEqLaw : Prop :=
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
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned)
    (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid)
    (readings : Readings regular coefficient accuracy positive common
      bank values planned requests paths originalPaid actual),
    readings.val = Heads.readings regular coefficient accuracy positive common
      bank values planned requests paths actual.heads

/-- The retained scalar-pair list is exactly the original ordered reader on the same stored Heads. -/
theorem rows_eq : RowsEqLaw := by
  unfold RowsEqLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common parents bank values planned requests paths originalPaid actual
    readings
  exact readings.property

/-- The scalar-pair cache retains every original occurrence, including repeated and empty cases.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def LengthLaw : Prop :=
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
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned)
    (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid)
    (readings : Readings regular coefficient accuracy positive common
      bank values planned requests paths originalPaid actual),
    readings.val.length = parents.length

/-- The scalar-pair cache retains every original occurrence, including repeated and empty cases. -/
theorem length : LengthLaw := by
  unfold LengthLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common parents bank values planned requests paths originalPaid actual
    readings
  exact (congrArg List.length readings.property).trans
      (Heads.readings_length regular coefficient accuracy positive common
        bank values planned requests paths actual.heads)

/-- The retained right column is the regular list of the same once-stored original-bank view.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def RegularEqLaw : Prop :=
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
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned)
    (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid)
    (readings : Readings regular coefficient accuracy positive common
      bank values planned requests paths originalPaid actual),
    readings.val.map Prod.snd = ExtraCells.regular bank actual.original.1 actual.original.2

/-- The retained right column is the regular list of the same once-stored original-bank view. -/
theorem regular_eq : RegularEqLaw := by
  unfold RegularEqLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common parents bank values planned requests paths originalPaid actual
    readings
  have sampled := congrArg (fun rows : List (Gaussian × Gaussian) => rows.map Prod.snd) readings.property
  have generated := Heads.readings_regular regular coefficient accuracy positive common
    bank values planned requests paths actual.heads originalPaid
  have retained := congrArg
    (fun cached : Plan.Materialized (error := error) (positive := errorPositive) (floor := floor)
        bank values common => ExtraCells.regular bank cached.1 cached.2) actual.original_eq
  exact (sampled.trans generated).trans retained.symm

set_option linter.unusedVariables false in
/-- A paid finite local request bounds the discrepancy from the same stored original regular integral sum.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition. The named `targetPositive` and `regularPaid` premises remain
required by callers and the proof, although absent from the conclusion.
-/
@[expose] def IntegralDifferenceLtLaw : Prop :=
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
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    {index : Nat}
    {box : Box}
    (target : Coordinate)
    (targetPositive : 0 < target)
    {positive : 0 < PotentialCells.localError parents.length target / 4}
    {pFloor : Nat}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (common : Nat)
    (selections : Selections (PotentialCells.localError parents.length target / 4) positive pFloor bank planned)
    (requests : Requests regular coefficient
      (PotentialCells.localError parents.length target / 4) positive bank planned)
    (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient
      (PotentialCells.localError parents.length target / 4) positive common
      bank values planned requests paths originalPaid)
    (readings : Readings regular coefficient
      (PotentialCells.localError parents.length target / 4) positive common
      bank values planned requests paths originalPaid actual)
    (regularPaid : Selections.maximum bank planned selections ≤ index),
    Norm.Basic.normSq (gaussianSum (readings.val.map Prod.fst) -
      gaussianSum (ExtraCells.regular bank actual.original.1 actual.original.2)) < target

/-- A paid finite local request bounds the discrepancy from the same stored original regular integral sum.

The actual local error is selected before constructing the common regular
sample and Head bank. Every occurrence then uses that unchanged request at
the same global regular stage. This estimate does not identify primitive
endpoints across occurrences or assert that either integral sum vanishes.
-/
theorem integral_difference_lt : IntegralDifferenceLtLaw := by
  unfold IntegralDifferenceLtLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor parents bank values
    planned index box target targetPositive positive pFloor regular coefficient common selections requests
    paths originalPaid actual readings regularPaid
  have each := Heads.readings_bounded (index := index) (box := box)
    (entryTarget := PotentialCells.localError parents.length target) (positive := positive) (pFloor := pFloor)
    regular coefficient common
    bank values planned selections requests paths actual.heads regularPaid
  have small : ∀ pair ∈ readings.val,
      Norm.Basic.normSq (pair.1 - pair.2) ≤ PotentialCells.localError parents.length target := by
    intro pair member
    have sameMember := Eq.mp
      (congrArg (fun rows : List (Gaussian × Gaussian) => pair ∈ rows) readings.property) member
    exact (each pair sameMember).le
  have estimate := Norm.Sum.Bounds.normSq_gaussianSum_map_sub_le readings.val Prod.fst Prod.snd small
  have count := length regular coefficient
    (PotentialCells.localError parents.length target / 4) positive common
    bank values planned requests paths originalPaid actual readings
  have counted := estimate.trans_eq
    (congrArg (fun count : Nat =>
      (count : Coordinate) * ((count : Coordinate) * PotentialCells.localError parents.length target)) count)
  have doubled : parents.length ≤ 2 * parents.length :=
    Eq.mp (congrArg (fun count : Nat => parents.length ≤ count) (Nat.two_mul parents.length).symm)
      (Nat.le_add_right parents.length parents.length)
  have countBound := Cast.Order.natCast_le_direct doubled
  have countNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le parents.length)
  have largerNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le (2 * parents.length))
  have entryPositive := PotentialCells.localError_positive parents.length target targetPositive
  have squared := Arithmetic.mul_le_mul_direct countBound
    (Arithmetic.mul_le_mul_of_nonneg_right_direct countBound entryPositive.le)
    (Arithmetic.mul_nonneg_direct countNonnegative entryPositive.le) largerNonnegative
  have paid := (counted.trans squared).trans_lt
    (PotentialCells.localError_paid parents.length target targetPositive)
  have retained := regular_eq regular coefficient
    (PotentialCells.localError parents.length target / 4) positive common
    bank values planned requests paths originalPaid actual readings
  have difference := congrArg
    (fun samples : List Gaussian => gaussianSum (readings.val.map Prod.fst) - gaussianSum samples) retained
  exact (congrArg Norm.Basic.normSq difference).symm.trans_lt paid

end Readings

end Materialized

/-- Select the finite local budget before the shared P sample, then retain its paid endpoint-aware reading bank.

The same actual Primitive cache supplies all endpoint requests and every
checked Head. The continuation receives that whole cache, its original
endpoint bank, the enlarged common reciprocal floor, the once-materialized
original view, one scalar reading cache and their internally derived bound.
No pre-existing sample, stage, accuracy or requested coefficient is retagged.
-/
def withReadings
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (target : Coordinate) (targetPositive : 0 < target) (pFloor : Nat) (box : Box)
    (endpointTarget : Coordinate) (endpointPositive : 0 < endpointTarget) (paths : LiftedCells bank planned)
    {Result : Type u}
    (consume : (quarterPositive : 0 < PotentialCells.localError parents.length target / 4) →
      (cached : Primitive (PotentialCells.localError parents.length target) quarterPositive pFloor box bank planned) →
      (endpoints : EndpointRequests cached.2.2.2.1.val endpointTarget bank planned paths) →
      (common : Nat) → (originalPaid : Plan.commonFloor bank planned ≤ common) →
      Requests.maximum bank planned cached.2.2.2.2 ≤ common →
      EndpointRequests.maximum cached.2.2.2.1.val endpointTarget bank planned paths endpoints ≤ common →
      (actual : Materialized cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError parents.length target / 4) quarterPositive common
        bank values planned cached.2.2.2.2 paths originalPaid) →
      (readings : Materialized.Readings cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError parents.length target / 4) quarterPositive common
        bank values planned cached.2.2.2.2 paths originalPaid actual) →
      Norm.Basic.normSq (gaussianSum (readings.val.map Prod.fst) -
        gaussianSum (ExtraCells.regular bank actual.original.1 actual.original.2)) < target → Result) : Result :=
  let entryTarget := PotentialCells.localError parents.length target
  have quarterPositive : 0 < entryTarget / 4 :=
    Field.div_pos_direct (PotentialCells.localError_positive parents.length target targetPositive)
      (Cast.Order.natCast_pos_direct (n := 4) (by decide +kernel))
  let cached := Primitive.build (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    bank planned entryTarget quarterPositive pFloor box
  Primitive.withEndpoints (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    (target := entryTarget) (positive := quarterPositive) (pFloor := pFloor) (box := box)
    bank values planned cached endpointTarget endpointPositive paths
    (fun endpoints common originalPaid physicalPaid endpointPaid actual =>
      let readings := Materialized.readings (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1 (entryTarget / 4) quarterPositive common
        bank values planned cached.2.2.2.2 paths originalPaid actual
      have regularPaid : Selections.maximum bank planned cached.1 ≤ cached.2.1.val :=
        Eq.mp (congrArg (fun value : Nat => value ≤ cached.2.1.val) cached.2.1.property)
          (Nat.le_refl cached.2.1.val)
      have bound := Materialized.Readings.integral_difference_lt
        (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        (index := cached.2.1.val) (box := box) (positive := quarterPositive) (pFloor := pFloor)
        bank values planned target targetPositive cached.2.2.1.val cached.2.2.2.1 common
        cached.1 cached.2.2.2.2 paths originalPaid actual readings regularPaid
      consume quarterPositive cached endpoints common originalPaid physicalPaid endpointPaid actual readings bound)

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
