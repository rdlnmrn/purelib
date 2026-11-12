module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints.Payment
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.BoundaryReturn
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison.Bank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! # Requested finite regular integrals on the same returned cap bank

The endpoint budget is chosen from the literal parent count before any P
selection, endpoint request or q materialization. Actual root return and
coordinate joins construct the finite comparison cache. Its paid gaps and
the same retained reading error bound the original regular integral sum.
No primitive constant, exact endpoint cancellation or period identity is
assumed.
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
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive (regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Clearance.Box.Boundary.Basic

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The literal occurrence square pays its allocated eighth-budget endpoint comparisons. -/
private theorem endpointBudget_paid (size : Nat) (target : Coordinate) (positive : 0 < target) :
    (size : Coordinate) * ((size : Coordinate) * (8 * (PotentialCells.localError size target / 8))) <
      target := by
  have cancel : 8 * (PotentialCells.localError size target / 8) =
      PotentialCells.localError size target :=
    (Field.mul_comm _ _).trans
      (Field.div_mul_cancel_of_ne _ (8 : Coordinate) (by decide +kernel))
  have doubled : size ≤ 2 * size :=
    Eq.mp (congrArg (fun value : Nat => size ≤ value) (Nat.two_mul size).symm)
      (Nat.le_add_right size size)
  have lower := Cast.Order.natCast_le_direct doubled
  have firstNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le size)
  have secondNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le (2 * size))
  have entryPositive := PotentialCells.localError_positive size target positive
  have squared := Arithmetic.mul_le_mul_direct lower
    (Arithmetic.mul_le_mul_of_nonneg_right_direct lower entryPositive.le)
    (Arithmetic.mul_nonneg_direct firstNonnegative entryPositive.le) secondNonnegative
  have scalar := congrArg
    (fun value : Coordinate => (size : Coordinate) * ((size : Coordinate) * value)) cancel
  exact scalar.trans_lt (squared.trans_lt (PotentialCells.localError_paid size target positive))

namespace Materialized.Readings

/-- The same requested reading cache and actual endpoint comparisons pay the original regular integral sum.

The endpoint target is an eighth of the original literal-count budget.
The original Selection family pays the shared P stage, and all comparison
witnesses remain indexed by the same Heads, endpoint requests and Samples.
Both small-error estimates are derived internally before scalar addition.
-/
theorem closed_integral_lt
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (values : Potentials bank)
    (planned : Plan error errorPositive floor bank)
    {index : Nat} {box : Box} (target : Coordinate) (targetPositive : 0 < target)
    {positive : 0 < PotentialCells.localError parents.length (target / 4) / 4} {pFloor : Nat}
    (regular : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = regular.physicalCoefficient }) (common : Nat)
    (selections : Selections (PotentialCells.localError parents.length (target / 4) / 4)
      positive pFloor bank planned)
    (requests : Requests regular coefficient
      (PotentialCells.localError parents.length (target / 4) / 4) positive bank planned)
    (paths : LiftedCells bank planned) (originalPaid : Plan.commonFloor bank planned ≤ common)
    (actual : Materialized regular coefficient
      (PotentialCells.localError parents.length (target / 4) / 4) positive common
      bank values planned requests paths originalPaid)
    (readings : Readings regular coefficient
      (PotentialCells.localError parents.length (target / 4) / 4) positive common
      bank values planned requests paths originalPaid actual)
    (endpoints : EndpointRequests coefficient.val
      (PotentialCells.localError parents.length (target / 4) / 8) bank planned paths)
    (sampled : EndpointRequests.Samples regular coefficient
      (PotentialCells.localError parents.length (target / 4) / 4) positive common
      (PotentialCells.localError parents.length (target / 4) / 8)
      bank values planned requests paths actual.heads endpoints)
    (compared : EndpointRequests.Payment regular coefficient
      (PotentialCells.localError parents.length (target / 4) / 4) positive common
      (PotentialCells.localError parents.length (target / 4) / 8)
      bank values planned requests paths actual.heads endpoints)
    (regularPaid : Selections.maximum bank planned selections ≤ index) :
    Norm.Basic.normSq (gaussianSum (ExtraCells.regular bank actual.original.1 actual.original.2)) <
      target := by
  have quarterPositive : 0 < target / 4 :=
    Field.div_pos_direct targetPositive (by decide +kernel : (0 : Coordinate) < 4)
  have increments := EndpointRequests.Payment.increments_normSq_le
    (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    regular coefficient (PotentialCells.localError parents.length (target / 4) / 4) positive common
    (PotentialCells.localError parents.length (target / 4) / 8)
    bank values planned requests paths actual.heads endpoints sampled compared
  have same := endpoint_increments_eq regular coefficient
    (PotentialCells.localError parents.length (target / 4) / 4) positive common
    (PotentialCells.localError parents.length (target / 4) / 8)
    bank values planned requests paths originalPaid actual readings endpoints sampled
  have scalar := congrArg Norm.Basic.normSq (congrArg gaussianSum same)
  have primitiveSmall := (scalar.symm.trans_le increments).trans_lt
    (endpointBudget_paid parents.length (target / 4) quarterPositive)
  have discrepancy := integral_difference_lt (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    (index := index) (box := box) (positive := positive) (pFloor := pFloor)
    bank values planned (target / 4) quarterPositive regular coefficient common
    selections requests paths originalPaid actual readings regularPaid
  have reversed := (Norm.Bounds.normSq_sub_symm
    (gaussianSum (ExtraCells.regular bank actual.original.1 actual.original.2))
    (gaussianSum (readings.val.map Prod.fst))).trans_lt discrepancy
  have combined := BoundaryClearance.normSq_add_lt_of_quarters (target := target) reversed primitiveSmall.le
  have total :
      (gaussianSum (ExtraCells.regular bank actual.original.1 actual.original.2) -
        gaussianSum (readings.val.map Prod.fst)) + gaussianSum (readings.val.map Prod.fst) =
      gaussianSum (ExtraCells.regular bank actual.original.1 actual.original.2) := by ring1
  exact (congrArg Norm.Basic.normSq total).symm.trans_lt combined

end Materialized.Readings

/-- Construct and retain the requested closed-bank regular integral payment on one original boundary.

The actual bank supplies every lifted cell and continued Point callback.
The occurrence count fixes both budgets before P selection or endpoint/q
work. The continuation receives the same selected cache, sampled endpoints,
comparison data, once-retained readings and internally derived integral
bound. Actual comparison operations may perform their original finite
observation work; no earlier preparation or materialization is replayed.
-/
def withClosedReadings
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (closed : Boundary.Data cap owner sourceDifferential)
    (values : Potentials closed.covered.bank)
    (planned : Plan error errorPositive floor closed.covered.bank)
    (target : Coordinate) (targetPositive : 0 < target) (pFloor : Nat) (box : Box)
    {Result : Type u}
    (consume :
      (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := error) (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned) →
      paths = LiftedCells.build (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := error) (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned →
      (positive : 0 < PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 4) →
      (cached : Primitive (PotentialCells.localError closed.covered.cache.parents.length (target / 4))
        positive pFloor box closed.covered.bank planned) →
      (endpoints : EndpointRequests cached.2.2.2.1.val
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 8)
        closed.covered.bank planned paths) →
      (common : Nat) → (originalPaid : Plan.commonFloor closed.covered.bank planned ≤ common) →
      Requests.maximum closed.covered.bank planned cached.2.2.2.2 ≤ common →
      EndpointRequests.maximum cached.2.2.2.1.val
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 8)
        closed.covered.bank planned paths endpoints ≤ common →
      (actual : Materialized cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid) →
      (readings : Materialized.Readings cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual) →
      (sampled : EndpointRequests.Samples cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 4) positive common
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths actual.heads endpoints) →
      EndpointRequests.Payment cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 4) positive common
        (PotentialCells.localError closed.covered.cache.parents.length (target / 4) / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths actual.heads endpoints →
      Norm.Basic.normSq
        (gaussianSum (ExtraCells.regular closed.covered.bank actual.original.1 actual.original.2)) < target →
      Result) : Result :=
  let entryTarget := PotentialCells.localError closed.covered.cache.parents.length (target / 4)
  have quarterPositive : 0 < target / 4 :=
    Field.div_pos_direct targetPositive (by decide +kernel : (0 : Coordinate) < 4)
  have endpointPositive : 0 < entryTarget / 8 :=
    Field.div_pos_direct
      (PotentialCells.localError_positive closed.covered.cache.parents.length (target / 4) quarterPositive)
      (by decide +kernel : (0 : Coordinate) < 8)
  let paths := LiftedCells.build (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := 1)
    (error := error) (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned
  withReadings (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := 1)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    closed.covered.bank values planned (target / 4) quarterPositive pFloor box (entryTarget / 8) endpointPositive paths
    (fun positive cached endpoints common originalPaid physicalPaid endpointPaid actual readings _readingBound =>
      let sampled := Materialized.sampleEndpoints (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1 (entryTarget / 4) positive common (entryTarget / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual endpoints
        endpointPaid endpointPositive
      have junctions : Bank.Junctions closed.covered.bank := by
        obtain ⟨chain⟩ := closed.covered.cache.chain
        exact Bank.junctionsOfChain closed.covered.bank chain
      let closing := EndpointRequests.Closing.ofBoundary cached.2.2.2.1.val (entryTarget / 8)
        closed planned paths endpoints
      let compared := EndpointRequests.Payment.build (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1 (entryTarget / 4) positive common (entryTarget / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths actual.heads endpoints sampled
        closed.covered.roots junctions closing endpointPositive
      have regularPaid : Selections.maximum closed.covered.bank planned cached.1 ≤ cached.2.1.val :=
        Eq.mp (congrArg (fun value : Nat => value ≤ cached.2.1.val) cached.2.1.property)
          (Nat.le_refl cached.2.1.val)
      have bound := Materialized.Readings.closed_integral_lt
        (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := error) (errorPositive := errorPositive) (floor := floor)
        (index := cached.2.1.val) (box := box) (positive := positive) (pFloor := pFloor)
        closed.covered.bank values planned target targetPositive cached.2.2.1.val cached.2.2.2.1 common
        cached.1 cached.2.2.2.2 paths originalPaid actual readings endpoints sampled compared regularPaid
      consume paths (Eq.refl paths) positive cached endpoints common originalPaid physicalPaid endpointPaid
        actual readings sampled compared bound)

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
