module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.Samples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Endpoints
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Endpoints.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Basic

/-! # Actual adjacent endpoint comparisons on the retained primitive bank

The original root-link spine supplies generator agreement. The independent
coordinate junction supplies exact point alignment. The two already sampled
endpoint requests then pay the actual neighbouring potential-polynomial jump.
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
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveEndpoint)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Gaussian

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}
    {parent next : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}

/-- The original root links compare the actual last and next first requested Point generators. -/
def adjacentRoots (coefficient : Polynomial) (target : Coordinate)
    (data : ParentData cap sourceDifferential count parent)
    (nextData : ParentData cap sourceDifferential count next) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data (.cons nextData rest)))
    (paths : LiftedCells (.cons data (.cons nextData rest)) planned)
    (endpoints : EndpointRequests coefficient target (.cons data (.cons nextData rest)) planned paths)
    {first last : Named} (roots : RootLinks (.cons data (.cons nextData rest)) first last) :
    NamedEquivalent endpoints.2.1.val.certificate.value.name endpoints.2.2.2.2.1.val.certificate.value.name :=
  (data.lastPoint_owner planned.2.1 endpoints.2.1.val).symm.trans
    (roots.adjacent.trans (nextData.firstPoint_owner planned.2.2.2.2.1 endpoints.2.2.2.2.1.val))

/-- The original coordinate junction identifies the same two endpoint evaluation coordinates exactly. -/
theorem adjacentCoordinates
    (data : ParentData cap sourceDifferential count parent)
    (nextData : ParentData cap sourceDifferential count next) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data (.cons nextData rest)))
    (junctions : Junctions (.cons data (.cons nextData rest))) :
    planned.2.1.point 1 = planned.2.2.2.2.1.point 0 :=
  planned.2.1.point_one.trans (junctions.1.trans planned.2.2.2.2.1.point_zero.symm)

/-- One actual adjacent observation comparison retains its original readings and physical-polynomial jump payment. -/
abbrev AdjacentComparison
    (data : ParentData cap sourceDifferential count parent)
    (nextData : ParentData cap sourceDifferential count next) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data (.cons nextData rest)))
    (planned : Plan error errorPositive floor (.cons data (.cons nextData rest)))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (requests : Requests regular coefficient accuracy positive (.cons data (.cons nextData rest)) planned)
    (paths : LiftedCells (.cons data (.cons nextData rest)) planned)
    (heads : Heads regular coefficient accuracy positive common
      (.cons data (.cons nextData rest)) values planned requests paths)
    (endpoints : EndpointRequests coefficient.val target (.cons data (.cons nextData rest)) planned paths) :=
    { _compared : Observation.Comparison endpoints.2.2.2.1.observation.reading
        endpoints.2.2.2.2.2.2.1.observation.reading (target / 64) //
      Norm.Basic.normSq (heads.1.attached.physical.cell.value.eval data.segment.comparison.last -
        heads.2.1.attached.physical.cell.value.eval nextData.segment.comparison.first) < 8 * target }

/-- Retain the original adjacent observation comparison and derive its actual polynomial jump bound internally.

Both endpoint samples use their original requests, physical cells and
possibly different actual reciprocal depths. The original root links and
coordinate junctions supply distinct necessary evidence; no jump bound or
endpoint observation equality is assumed.
-/
def compareAdjacent
    (data : ParentData cap sourceDifferential count parent)
    (nextData : ParentData cap sourceDifferential count next) (rest : Bank cap sourceDifferential count parents)
    (values : Potentials (.cons data (.cons nextData rest)))
    (planned : Plan error errorPositive floor (.cons data (.cons nextData rest)))
    {index : Nat} {box : Box}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient })
    (accuracy : Coordinate) (positive : 0 < accuracy) (common : Nat) (target : Coordinate)
    (requests : Requests regular coefficient accuracy positive (.cons data (.cons nextData rest)) planned)
    (paths : LiftedCells (.cons data (.cons nextData rest)) planned)
    (heads : Heads regular coefficient accuracy positive common
      (.cons data (.cons nextData rest)) values planned requests paths)
    (endpoints : EndpointRequests coefficient.val target (.cons data (.cons nextData rest)) planned paths)
    (observed : Samples regular coefficient accuracy positive common target
      (.cons data (.cons nextData rest)) values planned requests paths heads endpoints)
    {first last : Named} (roots : RootLinks (.cons data (.cons nextData rest)) first last)
    (junctions : Junctions (.cons data (.cons nextData rest))) (targetPositive : 0 < target) :
    AdjacentComparison data nextData rest values planned regular coefficient accuracy positive common target
      requests paths heads endpoints :=
  let compared := PrimitiveEndpoint.Sample.compareAt endpoints.2.2.2.1 endpoints.2.2.2.2.2.2.1
    observed.1.2 observed.2.1.1
    (adjacentCoordinates data nextData rest planned junctions)
    (adjacentRoots coefficient.val target data nextData rest planned paths endpoints roots) targetPositive
  have scalar := congrArg₂ (fun left right : Gaussian => left - right)
    (congrArg (fun point : Gaussian => heads.1.attached.physical.cell.value.eval point) planned.2.1.point_one)
    (congrArg (fun point : Gaussian => heads.2.1.attached.physical.cell.value.eval point)
      planned.2.2.2.2.1.point_zero)
  ⟨compared.val, (congrArg Norm.Basic.normSq scalar).symm.trans_lt compared.property⟩

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.EndpointRequests

end
