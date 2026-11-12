module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Head.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Nat.Order

/-! # Ordered endpoint samples on an existing checked bank

The global regular sample, coefficient and common reciprocal floor remain
fixed. Each literal occurrence consumes its two original endpoint requests
and its same checked Head. The finite request maximum pays both actual
sample depths; no Head, model, request, Point or original view is rebuilt.
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

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace EndpointRequests

/-- Every original occurrence retains its two actual endpoint Samples on the same checked Head.

The cache is indexed by the complete supplied request bank and Head bank.
The global P sample/coefficient and actual common q floor are unchanged in
every literal suffix, including repeated and stationary occurrences.
-/
@[expose] def Samples
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
            EndpointRequests coefficient.val endpointTarget bank planned paths → Type 3 := by
  intro parents bank
  induction bank with
  | nil => exact fun _ _ _ _ _ _ => PUnit
  | cons data rest ih =>
      intro values planned requests paths heads endpoints
      exact Head.EndpointSamples (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        data rest values planned regular coefficient requests.1.val accuracy requests.2.1.val common
        (firstSheet := paths.1) (lastSheet := paths.2.1)
        paths.2.2.1 paths.2.2.2.1 heads.1 endpointTarget endpoints ×
        ih values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2 endpoints.2.2.2.2

namespace Samples

/-- The exact runtime result function samples the supplied literal caches after their endpoint stage payment. -/
private def BuildFamily
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {_parents} bank =>
    (values : Potentials bank) → (planned : Plan error errorPositive floor bank) →
      (requests : Requests regular coefficient accuracy positive bank planned) →
        (paths : LiftedCells bank planned) →
          (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
            (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths) →
              EndpointRequests.maximum coefficient.val endpointTarget bank planned paths endpoints ≤ common →
                Samples (parameter := parameter) (frame := frame) (cap := cap)
                  (sourceDifferential := sourceDifferential) (count := count)
                  (error := error) (errorPositive := errorPositive) (floor := floor)
                  regular coefficient accuracy positive common endpointTarget
                    bank values planned requests paths heads endpoints

/-- Sample the same head before forcing the delayed literal endpoint-request and Head tails. -/
private def sampleStep
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate)
    (endpointPositive : 0 < endpointTarget)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (finishTail : Unit → BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common endpointTarget rest) :
    BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget (.cons data rest) :=
  fun values planned requests paths heads endpoints payment =>
    have headPaid := (EndpointRequests.head_le (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient.val endpointTarget data rest planned paths endpoints).trans payment
    let observed := Head.sampleEndpoints (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      data rest values planned regular coefficient requests.1.val accuracy requests.2.1.val common
      (firstSheet := paths.1) (lastSheet := paths.2.1)
      paths.2.2.1 paths.2.2.2.1 heads.1 endpointTarget endpoints headPaid endpointPositive
    have tailPaid := (EndpointRequests.tail_le (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient.val endpointTarget data rest planned paths endpoints).trans payment
    let remaining := finishTail ()
    ⟨observed, remaining values.2.2 planned.2.2.2 requests.2.2.2 paths.2.2.2.2 heads.2
      endpoints.2.2.2.2 tailPaid⟩

/-- Sample every supplied original endpoint request at its actual sufficient checked Head stage.

The original maximum pays the head and literal tail internally. The only
new endpoint work is the same Head sampler's two root/readModel/comparison
chains. No existing acquisition or materializer is replayed.
-/
def build
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate)
    (endpointPositive : 0 < endpointTarget) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (values : Potentials bank) →
        (planned : Plan error errorPositive floor bank) →
          (requests : Requests regular coefficient accuracy positive bank planned) →
            (paths : LiftedCells bank planned) →
              (heads : Heads regular coefficient accuracy positive common bank values planned requests paths) →
                (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths) →
                  EndpointRequests.maximum coefficient.val endpointTarget bank planned paths endpoints ≤ common →
                    Samples (parameter := parameter) (frame := frame) (cap := cap)
                      (sourceDifferential := sourceDifferential) (count := count)
                      (error := error) (errorPositive := errorPositive) (floor := floor)
                      regular coefficient accuracy positive common endpointTarget
                        bank values planned requests paths heads endpoints :=
  fun {_parents} bank =>
    Bank.fold (motive := BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget)
      (fun _ _ _ _ _ _ _ => ⟨⟩)
      (sampleStep (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        regular coefficient accuracy positive common endpointTarget endpointPositive) bank

end Samples

end EndpointRequests

namespace Materialized

/-- Retain the ordered endpoint Sample cache on this same already-materialized checked bank.

The result is indexed by the supplied actual.heads and endpoint request
bank. The original Materialized value and its cached old-bank view are
inputs and are never reconstructed or re-materialized.
-/
def sampleEndpoints
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (endpointTarget : Coordinate)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    (requests : Requests regular coefficient accuracy positive bank planned) (paths : LiftedCells bank planned)
    (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient accuracy positive common
      bank values planned requests paths originalPaid)
    (endpoints : EndpointRequests coefficient.val endpointTarget bank planned paths)
    (payment : EndpointRequests.maximum coefficient.val endpointTarget bank planned paths endpoints ≤ common)
    (endpointPositive : 0 < endpointTarget) :
    EndpointRequests.Samples (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      regular coefficient accuracy positive common endpointTarget
        bank values planned requests paths actual.heads endpoints :=
  EndpointRequests.Samples.build (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient accuracy positive common endpointTarget endpointPositive
    bank values planned requests paths actual.heads endpoints payment

end Materialized

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
