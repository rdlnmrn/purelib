module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.Samples
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Readings
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Endpoints
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.List.Map

/-! # Cached endpoint scalars on the original sampled bank

The retained PrimitiveValue supplies each exact source scalar without
reevaluating its polynomial. The ordered pairs retain every original
occurrence, and their differences read the same stored primitive column
already used by the regular-integral payment.
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
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive (regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveEndpoint)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace EndpointRequests.Samples

/-- The exact scalar-reader function consumes the original sampled and checked cache spines. -/
private def ValueFamily
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 := fun {_parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths) →
              Samples regular coefficient accuracy positive common endpointTarget
                bank values planned requests paths heads endpoints → List (Gaussian × Gaussian)

/-- Read both cached scalars before traversing the original delayed literal tail. -/
private def valueStep
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (finishTail : Unit → ValueFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget rest) :
    ValueFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget (.cons data rest) :=
  fun original planned requests paths heads endpoints sampled =>
    let pair : Gaussian × Gaussian := ⟨PrimitiveEndpoint.Sample.value (paid := endpoints.2.2.1) sampled.1.1,
      PrimitiveEndpoint.Sample.value (paid := endpoints.2.2.2.1) sampled.1.2⟩
    let remaining := finishTail ()
    pair :: remaining original.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
      endpoints.2.2.2.2 sampled.2

/-- Read the ordered exact source endpoint pairs from the already retained original Samples.

Both scalar values were cached by retainPrimitiveValue on the same model.
The reader does no polynomial evaluation, sampling or acquisition.
-/
def values
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths) →
              Samples regular coefficient accuracy positive common endpointTarget
                bank values planned requests paths heads endpoints → List (Gaussian × Gaussian) :=
  fun {_parents} bank =>
    Bank.fold (motive := ValueFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget)
      (fun _ _ _ _ _ _ _ => [])
      (valueStep (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common endpointTarget) bank

/-- The empty bank has no cached endpoint scalar pairs. -/
private theorem packaged_values_nil
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate)
    (original : Potentials (.nil : Bank cap sourceDifferential count []))
    (planned : Plan error errorPositive floor .nil)
    (requests : Requests regular coefficient accuracy positive .nil planned) (paths : LiftedCells .nil planned)
    (heads : Heads regular coefficient accuracy positive common .nil original planned requests paths)
    (endpoints : EndpointRequests coefficient.val endpointTarget .nil planned paths)
    (sampled : Samples regular coefficient accuracy positive common endpointTarget
      .nil original planned requests paths heads endpoints) :
    values regular coefficient accuracy positive common endpointTarget
      .nil original planned requests paths heads endpoints sampled = [] := by
  have folded := Bank.fold_nil (motive := ValueFamily (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget)
    (fun _ _ _ _ _ _ _ => [])
    (valueStep (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget)
  exact congrArg (fun next : ValueFamily (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget .nil =>
    next original planned requests paths heads endpoints sampled) folded

/-- The empty bank has no cached endpoint scalar pairs.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ValuesNilLaw : Prop :=
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
    (endpointTarget : Coordinate)
    (original : Potentials (.nil : Bank cap sourceDifferential count []))
    (planned : Plan error errorPositive floor .nil)
    (requests : Requests regular coefficient accuracy positive .nil planned)
    (paths : LiftedCells .nil planned)
    (heads : Heads regular coefficient accuracy positive common .nil original planned requests paths)
    (endpoints : EndpointRequests coefficient.val endpointTarget .nil planned paths)
    (sampled : Samples regular coefficient accuracy positive common endpointTarget
      .nil original planned requests paths heads endpoints),
    values regular coefficient accuracy positive common endpointTarget
      .nil original planned requests paths heads endpoints sampled = []

/-- The empty bank has no cached endpoint scalar pairs. -/
theorem values_nil : ValuesNilLaw := by
  unfold ValuesNilLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common endpointTarget original planned requests paths heads endpoints
    sampled
  exact packaged_values_nil regular coefficient accuracy positive common endpointTarget
      original planned requests paths heads endpoints sampled

/-- The original cached head pair is followed by its literal remaining sampled bank. -/
private theorem packaged_values_cons
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (original : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) original planned requests paths)
    (endpoints : EndpointRequests coefficient.val endpointTarget (.cons data rest) planned paths)
    (sampled : Samples regular coefficient accuracy positive common endpointTarget
      (.cons data rest) original planned requests paths heads endpoints) :
    values regular coefficient accuracy positive common endpointTarget
      (.cons data rest) original planned requests paths heads endpoints sampled =
      (PrimitiveEndpoint.Sample.value (paid := endpoints.2.2.1) sampled.1.1,
        PrimitiveEndpoint.Sample.value (paid := endpoints.2.2.2.1) sampled.1.2) ::
        values regular coefficient accuracy positive common endpointTarget
          rest original.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 endpoints.2.2.2.2 sampled.2 := by
  have folded := Bank.fold_cons (motive := ValueFamily (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget)
    (fun _ _ _ _ _ _ _ => [])
    (valueStep (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget) data rest
  exact congrArg (fun next : ValueFamily (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget (.cons data rest) =>
    next original planned requests paths heads endpoints sampled) folded

/-- The original cached head pair is followed by its literal remaining sampled bank.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ValuesConsLaw : Prop :=
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
    (original : Potentials (.cons data rest))
    (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat}
    {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate)
    (positive : 0 < accuracy)
    (common : Nat)
    (endpointTarget : Coordinate)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) original planned requests paths)
    (endpoints : EndpointRequests coefficient.val endpointTarget (.cons data rest) planned paths)
    (sampled : Samples regular coefficient accuracy positive common endpointTarget
      (.cons data rest) original planned requests paths heads endpoints),
    values regular coefficient accuracy positive common endpointTarget
      (.cons data rest) original planned requests paths heads endpoints sampled =
      (PrimitiveEndpoint.Sample.value (paid := endpoints.2.2.1) sampled.1.1,
        PrimitiveEndpoint.Sample.value (paid := endpoints.2.2.2.1) sampled.1.2) ::
        values regular coefficient accuracy positive common endpointTarget
          rest original.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 endpoints.2.2.2.2 sampled.2

/-- The original cached head pair is followed by its literal remaining sampled bank. -/
theorem values_cons : ValuesConsLaw := by
  unfold ValuesConsLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor parent parents data rest
    original planned index box regular coefficient accuracy positive common endpointTarget requests paths
    heads endpoints sampled
  exact packaged_values_cons data rest original planned regular coefficient accuracy positive common endpointTarget
      requests paths heads endpoints sampled

/-- Cached endpoint pairs keep the exact original occurrence count, including the empty bank.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ValuesLengthLaw : Prop :=
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
    (endpointTarget : Coordinate),
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (original : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank original planned requests paths) →
                (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths) →
                  (sampled : Samples regular coefficient accuracy positive common endpointTarget
                    bank original planned requests paths heads endpoints) →
                    (values regular coefficient accuracy positive common endpointTarget
                      bank original planned requests paths heads endpoints sampled).length =
                      parents.length

/-- Cached endpoint pairs keep the exact original occurrence count, including the empty bank. -/
theorem values_length : ValuesLengthLaw := by
  unfold ValuesLengthLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common endpointTarget parents bank
  induction bank with
  | nil =>
      intro original planned requests paths heads endpoints sampled
      exact congrArg List.length (values_nil regular coefficient accuracy positive common endpointTarget
        original planned requests paths heads endpoints sampled)
  | cons data rest ih =>
      intro original planned requests paths heads endpoints sampled
      have step := congrArg List.length
        (values_cons data rest original planned regular coefficient accuracy positive common endpointTarget
          requests paths heads endpoints sampled)
      exact step.trans (congrArg Nat.succ
        (ih original.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 endpoints.2.2.2.2 sampled.2))

/-- Cached endpoint differences are the same ordered primitive column used by the integral reader.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def ValuesIncrementsLaw : Prop :=
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
    (endpointTarget : Coordinate),
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (original : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank original planned requests paths) →
                (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths) →
                  (sampled : Samples regular coefficient accuracy positive common endpointTarget
                    bank original planned requests paths heads endpoints) →
                    (values regular coefficient accuracy positive common endpointTarget
                      bank original planned requests paths heads endpoints sampled).map
                        (fun pair => pair.2 - pair.1) =
                      (Heads.readings regular coefficient accuracy positive common
                        bank original planned requests paths heads).map Prod.fst

/-- Cached endpoint differences are the same ordered primitive column used by the integral reader.

Each supplied Sample retains its actual source scalar. The original
coordinate endpoint laws identify that scalar with the same Head polynomial
endpoint, and literal tail readbacks preserve the ordered whole list.
No closing relation or zero primitive increment is assumed.
-/
theorem values_increments : ValuesIncrementsLaw := by
  unfold ValuesIncrementsLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common endpointTarget parents bank
  induction bank with
  | nil =>
      intro original planned requests paths heads endpoints sampled
      have left := congrArg (fun rows : List (Gaussian × Gaussian) => rows.map (fun pair => pair.2 - pair.1))
        (values_nil regular coefficient accuracy positive common endpointTarget
          original planned requests paths heads endpoints sampled)
      have right := congrArg (fun rows : List (Gaussian × Gaussian) => rows.map Prod.fst)
        (Heads.readings_nil regular coefficient accuracy positive common original planned requests paths heads)
      exact left.trans right.symm
  | cons data rest ih =>
      intro original planned requests paths heads endpoints sampled
      have firstValue := PrimitiveEndpoint.Sample.value_eq (paid := endpoints.2.2.1) sampled.1.1
      have lastValue := PrimitiveEndpoint.Sample.value_eq (paid := endpoints.2.2.2.1) sampled.1.2
      have first := firstValue.trans
        (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point) planned.2.1.point_zero)
      have last := lastValue.trans
        (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point) planned.2.1.point_one)
      have head := congrArg₂ (fun first last : Gaussian => last - first) first last
      have left := congrArg (fun rows : List (Gaussian × Gaussian) => rows.map (fun pair => pair.2 - pair.1))
        (values_cons data rest original planned regular coefficient accuracy positive common endpointTarget
          requests paths heads endpoints sampled)
      have right := congrArg (fun rows : List (Gaussian × Gaussian) => rows.map Prod.fst)
        (Heads.readings_cons data rest original planned regular coefficient accuracy positive common
          requests paths heads)
      have remaining := ih original.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
        endpoints.2.2.2.2 sampled.2
      have sameHead := congrArg (fun value : Gaussian => value ::
        (values regular coefficient accuracy positive common endpointTarget
          rest original.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
          endpoints.2.2.2.2 sampled.2).map (fun pair => pair.2 - pair.1)) head
      have sameTail := congrArg
        (List.cons (heads.1.attached.physical.cell.value.eval data.segment.comparison.last -
          heads.1.attached.physical.cell.value.eval data.segment.comparison.first)) remaining
      exact left.trans ((sameHead.trans sameTail).trans right.symm)

end EndpointRequests.Samples

namespace Materialized.Readings

/-- The endpoint-scalar increments agree with the same already stored primitive reading column.

All original inputs, ownership equations and finite bounds are quantified
in this exact proposition.
-/
@[expose] def EndpointIncrementsEqLaw : Prop :=
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
    (endpointTarget : Coordinate)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (original : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned)
    (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank original planned requests paths originalPaid)
    (readings : Materialized.Readings regular coefficient accuracy positive common
      bank original planned requests paths originalPaid actual)
    (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths)
    (sampled : EndpointRequests.Samples regular coefficient accuracy positive common endpointTarget
      bank original planned requests paths actual.heads endpoints),
    (EndpointRequests.Samples.values regular coefficient accuracy positive common endpointTarget
      bank original planned requests paths actual.heads endpoints sampled).map (fun pair => pair.2 - pair.1) =
      readings.val.map Prod.fst

/-- The endpoint-scalar increments agree with the same already stored primitive reading column. -/
theorem endpoint_increments_eq : EndpointIncrementsEqLaw := by
  unfold EndpointIncrementsEqLaw
  intro parameter frame collar cap sourceDifferential count error errorPositive floor index box regular
    coefficient accuracy positive common endpointTarget parents bank original planned requests paths
    originalPaid actual readings endpoints sampled
  exact (EndpointRequests.Samples.values_increments regular coefficient accuracy positive common endpointTarget
      bank original planned requests paths actual.heads endpoints sampled).trans
        (congrArg (fun rows : List (Gaussian × Gaussian) => rows.map Prod.fst) readings.property.symm)

end Materialized.Readings

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
