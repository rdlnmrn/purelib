module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Combination
import Purelib.Polynomial.Winding.Circle.Operations
import Purelib.System.IO

/-!
# Actual common-window readings of selected repeated and zero-root combinations

Each original source constructs its complete inventory, recurrence ledger,
coefficient vector, synchronized request and automatic common model. Native
checks inspect the actual original formal sum at every common coordinate;
zero transients and a nonmonic repeated inside root retain the same owners.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Combination

open Purelib
open Data.Vector.Basic
open Data.Rat.Fraction (Rational)
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian
open Polynomial.Clearance.Circle (Certificate)
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots
open Polynomial.Recurrence.Mode.Reading (Selected)

/-- The original double zero retains both startup transients. -/
private def zeroSource : CoefficientPolynomial := ⟨[1, 0, 0]⟩

/-- A nonmonic double interior root retains a coupled nonzero-row boundary. -/
private def repeatedSource : CoefficientPolynomial := ⟨[2, -2, 1/2]⟩

/-- Check the complete same-ledger automatic common-window construction and its actual formal sums. -/
private def check {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0) : IO Unit := do
  let argument := PositiveArgument.prepare inventory
  let ledger := Roots.Recurrence.prepare argument rows nonzero
  let coefficients := vectorOfFn (fun column : Fin ledger.owners.selection.word.length =>
    Multiplicity.Roots.Stages.Images.coefficientMap ledger.prepared.separation.prepared.stages
      ((column.val + 1 : Nat) : Canonical))
  let request := Roots.Recurrence.Combination.Request.prepare ledger coefficients (1/16) (by decide +kernel) 4
  let observation := Roots.Recurrence.Combination.Observation.prepare request
  have _ := request.restore
  have _ := observation.restore
  have _ := request.schedule.tolerance_positive
  unless decide (0 < request.schedule.tolerance) && decide (0 < request.schedule.modeTarget) &&
      observation.reading.gain == ledger.parameters.finalGain &&
      decide (observation.reading.error < request.schedule.tolerance) do
    throw (IO.userError "the synchronized original request lost its positive common payment")
  for column in List.ofFn (fun column : Fin ledger.owners.selection.word.length => column) do
    have _ := request.schedule.threshold_le_start column
    unless (request.schedule.thresholds.get column).index ≤ request.schedule.start do
      throw (IO.userError "the retained common start failed to synchronize an original threshold")
  for offset in List.ofFn (fun offset : Fin 4 => offset) do
    have _ := observation.window_lt offset
    have _ := request.association_window_lt observation.association observation.error_le offset
    let actual := observation.reading.read (request.schedule.value offset)
    unless decide (actual.normSq < (1/16 : Rational)) do
      throw (IO.userError "a paid common-window original formal combination exceeded its requested bound")
    let independent := Purelib.Algebra.FiniteSum.Fin.sumFin (fun column =>
      coefficients column * Polynomial.Recurrence.Mode.entry
        (ledger.prepared.bank.block (Selected.original ledger.owners.selection column)).point
        (request.orders.orders column) (request.schedule.start + offset.val))
    unless decide (observation.reading.read independent = actual) do
      throw (IO.userError "the actual weighted combination changed an original root, order, coefficient or index")
  System.IO.println s!"Synchronized original combination: rows{rows}, columns{ledger.owners.selection.word.length}, \
    common-start{request.schedule.start}, window4; paid actual same-model formal sums."

/-- Dispatch the same complete original source inventory without supplying selected roots or final inequalities. -/
private def positive {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) (rows : Nat) (nonzero : 0 < rows → source.eval 0 ≠ 0) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "a positive combination source became constant")
  | .positive _ _, locations => check locations rows nonzero

/-- Execute both original zero-transient and nonmonic repeated-root automatic combination chains. -/
public def run : IO Unit := do
  let zeroClearance : Certificate zeroSource :=
    have same : Power.polynomialPower (LinearFactor.linearFactor 0) 2 = zeroSource := by decide +kernel
    same ▸ (Certificate.linearInside 0 (by decide +kernel)).power 2
  let repeatedClearance : Certificate repeatedSource :=
    have same : Purelib.Polynomial.Dense.Basic.DensePolynomial.scale (2 : Canonical)
        (Power.polynomialPower (LinearFactor.linearFactor (⟨1/2, 0⟩ : Canonical)) 2) = repeatedSource :=
      by decide +kernel
    same ▸ ((Certificate.linearInside (⟨1/2, 0⟩ : Canonical) (by decide +kernel)).power 2).scale
      (2 : Canonical) (by decide +kernel)
  positive (Inventory.prepare zeroClearance (by decide +kernel)) 0
    (fun impossible => False.elim (Nat.not_lt_zero _ impossible))
  positive (Inventory.prepare repeatedClearance (by decide +kernel)) 1 (fun _ => by decide +kernel)

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Combination
