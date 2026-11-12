module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.Closing
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.Samples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Endpoints.Coordinates
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Power
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Norm.Basic

/-! # The actual closing primitive-polynomial comparison

The original first endpoint request and its existing sampled value stay
fixed while the worker descends through literal Head and endpoint tails.
The actual final sample and retained closing root/coordinate evidence pay
the original last-minus-first physical polynomial value internally.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.EndpointRequests

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive (regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box Model)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
  (PrimitiveEndpoint primitivePolynomial)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Gaussian

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}
    {targetPoint : Gaussian}
    {targetPatch : ContinuedNeighborhood (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) count}
    {targetPointOwner : Point targetPatch targetPoint}

namespace LastComparison

/-- The exact function space of final-comparison types on one original checked bank.

All cached input owners remain parameters of this function space. The
separate type algebra determines the original final comparison formula.
-/
@[expose] def Function
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (_targetRequest : PrimitiveEndpoint targetPointOwner 0 coefficient.val floor target)
    (_targetValue : Gaussian) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {_parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
            bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
                coefficient.val target bank planned paths → Type 1

/-- Form the same final-comparison type from one head and its literal following type function.

The singleton formula retains the actual final request and physical
polynomial. Longer banks preserve every supplied cache tail. The exposed
body supports the public relation's original client reduction.
-/
@[expose] def cons
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetRequest : PrimitiveEndpoint targetPointOwner 0 coefficient.val floor target)
    (targetValue : Gaussian)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (following : Unit → Function (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target targetRequest targetValue rest) :
    Function (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target targetRequest targetValue (.cons data rest) := by
  cases rest with
  | nil =>
      intro values planned requests paths heads endpoints
      exact { compared : Observation.Comparison endpoints.2.2.2.1.observation.reading
          targetRequest.observation.reading (target / 64) //
        Norm.Basic.normSq (heads.1.attached.physical.cell.value.eval data.segment.comparison.last -
          targetValue) < 8 * target }
  | cons next remaining =>
      intro values planned requests paths heads endpoints
      exact following () values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 endpoints.2.2.2.2

end LastComparison

/-- The final original requested observation is compared with one fixed original target request and scalar.

The relation keeps the actual observation comparison as its value. Its
bound concerns the literal final Head polynomial at the original segment
endpoint and the supplied target scalar. Nil contributes no endpoint.
-/
@[expose] def LastComparison
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetRequest : PrimitiveEndpoint targetPointOwner 0 coefficient.val floor target)
    (targetValue : Gaussian) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
            bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
                  (sourceDifferential := sourceDifferential) (count := count)
                  (error := error) (errorPositive := errorPositive) (floor := floor)
                  coefficient.val target bank planned paths → Type 1 := by
  intro parents bank
  exact Bank.rec (motive := fun parents bank =>
      LastComparison.Function (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common target targetRequest targetValue (parents := parents) bank)
    (fun _ _ _ _ _ _ => PUnit)
    (fun {_parent} {_parents} data rest following =>
      LastComparison.cons (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common target targetRequest targetValue data rest
        (fun _ => following)) bank

/-- The exact function type of the closing comparison on supplied literal bank caches. -/
private def CompareFamily
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetRequest : PrimitiveEndpoint targetPointOwner 0 coefficient.val floor target)
    (targetValue : Gaussian) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {_parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
            bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            (endpoints : EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
              (sourceDifferential := sourceDifferential) (count := count)
              (error := error) (errorPositive := errorPositive) (floor := floor)
              coefficient.val target bank planned paths) →
              Samples regular coefficient accuracy positive common target
                bank values planned requests paths heads endpoints →
                  LastRelation (parameter := parameter) (frame := frame) (cap := cap)
                    (sourceDifferential := sourceDifferential) (count := count)
                    (error := error) (errorPositive := errorPositive) (floor := floor)
                    coefficient.val target targetPoint targetPointOwner.certificate.value.name
                    bank planned paths endpoints →
                    LastComparison (parameter := parameter) (frame := frame) (cap := cap)
                      (sourceDifferential := sourceDifferential) (count := count)
                      (error := error) (errorPositive := errorPositive) (floor := floor)
                      regular coefficient accuracy positive common target targetRequest targetValue
                      bank values planned requests paths heads endpoints

/-- Consume the actual final sample against the same original target sample without replaying either sampler.

The target scalar is an existing PrimitiveValue cache with its exact
readback. Only the final finite observation comparison is newly constructed;
all preceding occurrences pass their literal tails without new sampling.
-/
private def compareLast
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (targetRequest : PrimitiveEndpoint targetPointOwner 0 coefficient.val floor target)
    {targetDepth : Nat}
    {targetModel : Model (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) targetPatch.base.box}
    {targetSameModel : targetModel = targetPatch.base.refine targetDepth}
    {targetPowers : OddPowers targetModel.value} {targetSource : Polynomial}
    {targetCompiled : targetSource.eval targetPoint =
      coefficient.val.eval targetPoint * (primitivePolynomial targetPowers 0).eval targetPoint}
    (targetObserved : targetRequest.Sample targetModel targetSameModel targetPowers targetSource targetCompiled)
    (targetValue : Gaussian) (targetValueEq : targetSource.eval targetPoint = targetValue)
    (targetPositive : 0 < target) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        CompareFamily (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
          regular coefficient accuracy positive common target targetRequest targetValue bank := by
  intro parents bank
  refine Bank.fold (motive := CompareFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target targetRequest targetValue) ?_ ?_ bank
  · exact fun _ _ _ _ _ _ _ _ => ⟨⟩
  · intro parent parents data rest finishTail
    cases rest with
    | nil =>
        intro values planned requests paths heads endpoints observed closing
        let compared := PrimitiveEndpoint.Sample.compareAt endpoints.2.2.2.1 targetRequest
          observed.1.2 targetObserved closing.property closing.val targetPositive
        have scalar := congrArg₂ (fun left right : Gaussian => left - right)
          (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point)
            planned.2.1.point_one) targetValueEq
        exact ⟨compared.val, (congrArg Norm.Basic.normSq scalar).symm.trans_lt compared.property⟩
    | cons next remaining =>
        intro values planned requests paths heads endpoints observed closing
        exact finishTail () values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
          endpoints.2.2.2.2 observed.2 closing

/-- Construct the actual closing observation comparison and its strict eight-budget polynomial bound.

The fixed target is the existing first endpoint request and Sample. Its
cached PrimitiveValue is reused during traversal and then read back to the
original first physical polynomial endpoint. Closing supplies root and
coordinate evidence; no final discrepancy bound is an input.
-/
def compareClosing
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data rest)) (planned : Plan error errorPositive floor (.cons data rest))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (requests : Requests regular coefficient accuracy positive (.cons data rest) planned)
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned)
    (heads : Heads regular coefficient accuracy positive common (.cons data rest) values planned requests paths)
    (endpoints : EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient.val target (.cons data rest) planned paths)
    (observed : Samples regular coefficient accuracy positive common target
      (.cons data rest) values planned requests paths heads endpoints)
    (closing : Closing (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient.val target (.cons data rest) planned paths endpoints)
    (targetPositive : 0 < target) :
    LastComparison (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target endpoints.2.2.1
        (heads.1.attached.physical.cell.value.eval data.segment.comparison.first)
        (.cons data rest) values planned requests paths heads endpoints := by
  let firstValue := PrimitiveEndpoint.Sample.value (paid := endpoints.2.2.1) observed.1.1
  have reading : firstValue = heads.1.attached.physical.cell.value.eval (planned.2.1.point 0) :=
    PrimitiveEndpoint.Sample.value_eq (paid := endpoints.2.2.1) observed.1.1
  let compared := compareLast (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common target endpoints.2.2.1 observed.1.1
    firstValue reading.symm targetPositive
    (.cons data rest) values planned requests paths heads endpoints observed closing
  have physical := reading.trans
    (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point) planned.2.1.point_zero)
  exact Eq.rec (motive := fun targetValue _ =>
    LastComparison (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common target endpoints.2.2.1 targetValue
        (.cons data rest) values planned requests paths heads endpoints) compared physical

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.EndpointRequests

end
