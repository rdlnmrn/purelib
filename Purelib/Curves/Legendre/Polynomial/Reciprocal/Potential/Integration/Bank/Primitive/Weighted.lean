module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Closed
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells.Models
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison.Bank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingCoordinates
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Weighted finite payment on the same checked cap cells

The old physical potential density, weighted cube and cleared regular
remainder are the three original pullbacks of the same materialized Sample.
Their exact signed integral split and both actual endpoint-comparison banks
pay the weighted sum. The regular primitive requests enlarge the same q
floor; no older cell bank is constructed to obtain a different payment.
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
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPath)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial.Clearance.Box.Boundary.Basic

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1}

/-- The exact signed split combines separately paid potential-density and regular-remainder sums. -/
private theorem split_bounds (weighted potential regular : Gaussian) (target : Coordinate)
    (split : weighted = 2 * potential + regular)
    (potentialSmall : Norm.Basic.normSq potential < (target / 4) / 4)
    (regularSmall : Norm.Basic.normSq regular < target / 4) :
    Norm.Basic.normSq (weighted - regular) < target / 4 ∧ Norm.Basic.normSq weighted < target := by
  have squared := Norm.Basic.normSq_mul (2 : Gaussian) potential
  have two : Norm.Basic.normSq (2 : Gaussian) = (4 : Coordinate) := by decide +kernel
  have scalar := squared.trans (congrArg (fun value : Coordinate => value * Norm.Basic.normSq potential) two)
  have small := Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide +kernel : (0 : Coordinate) < 4) potentialSmall
  have cancel : 4 * ((target / 4) / 4) = target / 4 :=
    (Field.mul_comm _ _).trans (Field.div_mul_cancel_of_ne _ (4 : Coordinate) (by decide +kernel))
  have twiceSmall := scalar.trans_lt (small.trans_eq cancel)
  have difference := congrArg (fun value : Gaussian => value - regular) split
  have twice := difference.trans (show 2 * potential + regular - regular = 2 * potential by ring1)
  have bound := BoundaryClearance.normSq_add_lt_of_quarters (target := target) twiceSmall regularSmall.le
  exact ⟨(congrArg Norm.Basic.normSq twice).trans_lt twiceSmall,
    (congrArg Norm.Basic.normSq split).trans_lt bound⟩

/-- Construct finite weighted and regular payments on one and the same checked original sample bank.

The actual old density target is chosen before Plan.build. The shared
regular primitive selects its P sample and all enlarged q floors before
materialization. Actual old-potential joins then compare the original
stored endpoint observations, while the regular payment consumes the same
Readings, Samples and endpoint Payment produced by withClosedReadings.
The continuation retains both comparison families and their original
closing coordinate join. All three sums read the same materialized original cells.
-/
def withWeightedReadings
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (closed : Boundary.Data cap owner sourceDifferential) (values : Potentials closed.covered.bank)
    (target : Coordinate) (targetPositive : 0 < target) (floor pFloor : Nat) (box : Box)
    {Result : Type u}
    (consume :
      (errorPositive : 0 < PotentialCells.localError closed.covered.parentCount ((target / 4) / 4)) →
      (planned : Plan (PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        errorPositive floor closed.covered.bank) →
      (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned) →
      paths = LiftedCells.build (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned →
      (positive : 0 < PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) →
      (cached : Primitive (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4))
        positive pFloor box closed.covered.bank planned) →
      (endpoints : EndpointRequests cached.2.2.2.1.val
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank planned paths) →
      (common : Nat) → (originalPaid : Plan.commonFloor closed.covered.bank planned ≤ common) →
      Requests.maximum closed.covered.bank planned cached.2.2.2.2 ≤ common →
      EndpointRequests.maximum cached.2.2.2.1.val
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank planned paths endpoints ≤ common →
      (actual : Materialized cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid) →
      (readings : Materialized.Readings cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual) →
      (sampled : EndpointRequests.Samples cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths actual.heads endpoints) →
      EndpointRequests.Payment cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths actual.heads endpoints →
      PotentialCells.Junctions closed.covered.bank actual.original.1 →
      Bank.ClosingJoin closed.covered.bank →
      PotentialCells.ClosingComparison closed.covered.bank actual.original.1 →
      Norm.Basic.normSq
        (gaussianSum (ExtraCells.regular closed.covered.bank actual.original.1 actual.original.2)) < target / 4 →
      Norm.Basic.normSq
        (gaussianSum (ExtraCells.weighted closed.covered.bank actual.original.1 actual.original.2) -
          gaussianSum (ExtraCells.regular closed.covered.bank actual.original.1 actual.original.2)) < target / 4 →
      Norm.Basic.normSq
        (gaussianSum (ExtraCells.weighted closed.covered.bank actual.original.1 actual.original.2)) < target →
      Result) : Result :=
  have quarterPositive : 0 < target / 4 :=
    Field.div_pos_direct targetPositive (by decide +kernel : (0 : Coordinate) < 4)
  have potentialPositive : 0 < (target / 4) / 4 :=
    Field.div_pos_direct quarterPositive (by decide +kernel : (0 : Coordinate) < 4)
  let error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4)
  have errorPositive : 0 < error :=
    PotentialCells.localError_positive closed.covered.parentCount ((target / 4) / 4) potentialPositive
  let planned := Plan.build (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := 1) error errorPositive floor closed.covered.bank
  withClosedReadings (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential)
    (error := error) (errorPositive := errorPositive) (floor := floor)
    closed values planned (target / 4) quarterPositive pFloor box
    (fun paths pathsFactory positive cached endpoints common originalPaid physicalPaid endpointPaid
        actual readings sampled compared regularSmall =>
      let joints := PotentialCells.junctions closed.covered.bank values actual.original.1 closed.covered.coordinates
      let returned := Boundary.closingCoordinates closed
      let closing := PotentialCells.closingComparison closed.covered.bank values actual.original.1 returned
      have potentialSmall :
          Norm.Basic.normSq (gaussianSum (PotentialCells.integrals closed.covered.bank actual.original.1)) <
            (target / 4) / 4 := by
        let retained : Boundary.PotentialPayment closed values ((target / 4) / 4) potentialPositive common :=
          ⟨actual.original.1, joints, closing⟩
        exact Boundary.PotentialPayment.accurate closed values ((target / 4) / 4) potentialPositive common retained
      have split := ExtraCells.sum_split closed.covered.bank actual.original.1 actual.original.2
      have bounds := split_bounds _ _ _ target split potentialSmall regularSmall
      consume errorPositive planned paths pathsFactory positive cached endpoints common originalPaid physicalPaid
        endpointPaid actual readings sampled compared joints returned closing regularSmall bounds.1 bounds.2)

/-- Retain one cached lifted path, one certified model bank and all three paid integral-list bounds.

The original weighted constructor supplies the same Materialized, reading,
request, sample and comparison owners. This constructor binds the actual
path once and certifies that GIVEN path once. Its same retained model lists
are identified with the original weighted/regular lists by their whole
factory equality; only those scalar equalities transport the paid bounds.
No path, model, sample or observation factory is replayed for the proof.
-/
def withCertifiedWeightedReadings
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (closed : Boundary.Data cap owner sourceDifferential) (values : Potentials closed.covered.bank)
    (target : Coordinate) (targetPositive : 0 < target) (floor pFloor : Nat) (box : Box)
    {Result : Type u}
    (consume :
      (errorPositive : 0 < PotentialCells.localError closed.covered.parentCount ((target / 4) / 4)) →
      (planned : Plan (PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        errorPositive floor closed.covered.bank) →
      (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned) →
      (pathsFactory : paths = LiftedCells.build (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned) →
      (positive : 0 < PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) →
      (cached : Primitive (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4))
        positive pFloor box closed.covered.bank planned) →
      (endpoints : EndpointRequests cached.2.2.2.1.val
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank planned paths) →
      (common : Nat) → (originalPaid : Plan.commonFloor closed.covered.bank planned ≤ common) →
      Requests.maximum closed.covered.bank planned cached.2.2.2.2 ≤ common →
      EndpointRequests.maximum cached.2.2.2.1.val
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank planned paths endpoints ≤ common →
      (actual : Materialized cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid) →
      (readings : Materialized.Readings cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual) →
      (sampled : EndpointRequests.Samples cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths actual.heads endpoints) →
      EndpointRequests.Payment cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 8)
        closed.covered.bank values planned cached.2.2.2.2 paths actual.heads endpoints →
      PotentialCells.Junctions closed.covered.bank actual.original.1 →
      Bank.ClosingJoin closed.covered.bank →
      PotentialCells.ClosingComparison closed.covered.bank actual.original.1 →
      Norm.Basic.normSq
        (gaussianSum (ExtraCells.regular closed.covered.bank actual.original.1 actual.original.2)) < target / 4 →
      Norm.Basic.normSq
        (gaussianSum (ExtraCells.weighted closed.covered.bank actual.original.1 actual.original.2) -
          gaussianSum (ExtraCells.regular closed.covered.bank actual.original.1 actual.original.2)) < target / 4 →
      Norm.Basic.normSq
        (gaussianSum (ExtraCells.weighted closed.covered.bank actual.original.1 actual.original.2)) < target →
      (keptPath : LiftedPath 2 ⟨collar.box.anchor, 0⟩ ⟨collar.box.anchor, 0⟩) →
      (keptFactory : keptPath = LiftedCells.path (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        closed.covered.bank planned paths pathsFactory closed.covered.cache.chain) →
      (retained : LiftedCells.CertifiedModels (parameter := parameter) (frame := frame)
        (collar := collar) (cap := cap) keptPath) →
      retained = Materialized.certifyOnPath (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual pathsFactory
        closed.covered.cache.chain keptPath keptFactory →
      (retained.1.1.map CellModel.integralSample, retained.1.2.map CellModel.integralSample) =
        (ExtraCells.weighted closed.covered.bank actual.original.1 actual.original.2,
          ExtraCells.regular closed.covered.bank actual.original.1 actual.original.2) →
      Norm.Basic.normSq (gaussianSum (retained.1.2.map CellModel.integralSample)) < target / 4 →
      Norm.Basic.normSq (gaussianSum (retained.1.1.map CellModel.integralSample) -
        gaussianSum (retained.1.2.map CellModel.integralSample)) < target / 4 →
      Norm.Basic.normSq (gaussianSum (retained.1.1.map CellModel.integralSample)) < target →
      Result) : Result :=
  withWeightedReadings (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) closed values target targetPositive floor pFloor box
    (fun errorPositive planned paths pathsFactory positive cached endpoints common originalPaid physicalPaid
        endpointPaid actual readings sampled compared joints returned closing
        regularSmall differenceSmall weightedSmall =>
      let keptPath := LiftedCells.path (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        closed.covered.bank planned paths pathsFactory closed.covered.cache.chain
      have keptFactory : keptPath = LiftedCells.path (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := 1)
          (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
          (errorPositive := errorPositive) (floor := floor)
          closed.covered.bank planned paths pathsFactory closed.covered.cache.chain := Eq.refl keptPath
      let retained := Materialized.certifyOnPath (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual pathsFactory
        closed.covered.cache.chain keptPath keptFactory
      have retainedFactory : retained = Materialized.certifyOnPath
          (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := 1)
          (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
          (errorPositive := errorPositive) (floor := floor)
          cached.2.2.1.val cached.2.2.2.1
          (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
          closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual pathsFactory
          closed.covered.cache.chain keptPath keptFactory := Eq.refl retained
      have lists := Materialized.integral_lists_eq (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := 1)
        (error := PotentialCells.localError closed.covered.parentCount ((target / 4) / 4))
        (errorPositive := errorPositive) (floor := floor)
        cached.2.2.1.val cached.2.2.2.1
        (PotentialCells.localError closed.covered.cache.parents.length ((target / 4) / 4) / 4) positive common
        closed.covered.bank values planned cached.2.2.2.2 paths originalPaid actual pathsFactory
        closed.covered.cache.chain keptPath keptFactory retained retainedFactory
      have regularEq := congrArg (fun rows : List Gaussian × List Gaussian => gaussianSum rows.2) lists
      have differenceEq := congrArg (fun rows : List Gaussian × List Gaussian =>
        gaussianSum rows.1 - gaussianSum rows.2) lists
      have weightedEq := congrArg (fun rows : List Gaussian × List Gaussian => gaussianSum rows.1) lists
      have regularBound := (congrArg Norm.Basic.normSq regularEq).trans_lt regularSmall
      have differenceBound := (congrArg Norm.Basic.normSq differenceEq).trans_lt differenceSmall
      have weightedBound := (congrArg Norm.Basic.normSq weightedEq).trans_lt weightedSmall
      consume errorPositive planned paths pathsFactory positive cached endpoints common originalPaid physicalPaid
        endpointPaid actual readings sampled compared joints returned closing regularSmall differenceSmall weightedSmall
        keptPath keptFactory retained retainedFactory lists regularBound differenceBound weightedBound)

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive

end
