module

import Purelib.Polynomial.Laurent.Toeplitz
import Purelib.Polynomial.Clearance.Circle.LinearFactor
import Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Bounds.Outside
import Purelib.System.IO

/-!
# An actual near-circle Laurent ledger and its paid mode request

The original linear factor has root 15/16. Its exact whole-circle certificate
feeds the public automatic comparison. The same resulting ledger computes
and pays its own finite mode schedule from the retained physical ceiling.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz.SmallMargin

open Purelib
open Polynomial.Laurent
open Basic (LaurentPolynomial)
open Data.Gaussian.Basic (Canonical)
open Data.Rat.Fraction (Rational)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Clearance.Circle (Certificate)
open RootIsolation.Multiplicity.Side.Basic (SideResult)
open RootIsolation.Multiplicity.Circle
open RationalFunctions.Curve.Canonical.Circle

/-- The actual rational root lies close to the unit circle. -/
private def root : Canonical := ⟨15 / 16, 0⟩

/-- Observe the same positive branch retained by the public Laurent comparison. -/
private def paid {source opposite : CoefficientPolynomial} {clearance : Certificate source}
    (rows : Nat) :
    (side : SideResult source opposite) → (locations : SideLocations clearance side) →
      (argument : SideArgument side locations) → Recurrence.Side rows side locations argument → IO Unit
  | .constant _ _ _, _, _, _ => throw (IO.userError "the near-circle source unexpectedly became constant")
  | .positive _ _, _, _, ledger => do
      let outside := Roots.Reading.Bounds.Outside.prepare ledger.bounds ledger.owners
      have _ := outside.restore
      have _ := outside.commonFloorAboveOne
      unless outside.commonFloor == 2 do
        throw (IO.userError "the empty outside selection lost its positive default floor")
      for original in List.ofFn (fun index : Fin ledger.prepared.bank.blocks.length => index) do
        unless outside.selected original == false && outside.floors original == (225 / 256 : Rational) do
          throw (IO.userError "the outside floor cache changed an inside label or its original physical bound")
      let request := Roots.Recurrence.Request.prepare ledger (1 / 16) (by decide +kernel) 2
      let observation := Roots.Recurrence.Observation.prepare request
      let reading := observation.reading
      unless ledger.owners.selection.count == 1 && ledger.recurrence.fullWord.length == 1 &&
          reading.error == 0 && decide (reading.error < request.modes.tolerance) do
        throw (IO.userError "the actual near-circle ledger lost its original root or common payment")
      for column in List.ofFn (fun column : Fin ledger.owners.selection.word.length => column) do
        let entry := request.modes.schedule.entryAt column
        let original := Polynomial.Recurrence.Mode.Reading.Selected.original ledger.owners.selection column
        let point := (ledger.prepared.bank.block original).point
        let ceiling := request.modes.ceilings original
        unless reading.read point == root && decide (ceiling = (225 / 256 : Rational)) &&
            entry.inside.index > 0 do
          throw (IO.userError "the near-circle schedule lost its actual retained root ceiling or computed threshold")
        for offset in List.ofFn (fun offset : Fin 2 => offset) do
          have _ := observation.window_lt column offset
          let value := reading.read (Polynomial.Recurrence.Mode.window point (request.modes.orders.orders column)
            (entry.inside.index + 2) (entry.index offset))
          unless decide (value.normSq < (1 / 16 : Rational)) do
            throw (IO.userError "the actual near-circle formal mode exceeded its paid finite-window request")
        System.IO.println s!"Toeplitz small margin: original ceiling225/256; computed threshold{entry.inside.index}; \
          actual common reading paid both formal mode observations."
      let coefficients : Roots.Recurrence.Combination.Coefficients ledger :=
        Data.Vector.Basic.vectorOfFn fun _ =>
          Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images.coefficientMap
            ledger.prepared.separation.prepared.stages (2 : Canonical)
      let combinedRequest := Roots.Recurrence.Combination.Request.prepare ledger coefficients
        (1 / 16) (by decide +kernel) 2
      let combinedObservation := Roots.Recurrence.Combination.Observation.prepare combinedRequest
      have _ := combinedRequest.restore
      have _ := combinedObservation.restore
      unless combinedObservation.reading.error == 0 &&
          decide (combinedObservation.reading.error < combinedRequest.schedule.tolerance) do
        throw (IO.userError "the same near-circle ledger failed its weighted common-window payment")
      for offset in List.ofFn (fun offset : Fin 2 => offset) do
        have _ := combinedObservation.window_lt offset
        let value := combinedObservation.reading.read (combinedRequest.schedule.value offset)
        unless decide (value.normSq < (1 / 16 : Rational)) do
          throw (IO.userError "the actual near-circle weighted formal sum exceeded its paid common-window bound")
      System.IO.println s!"Toeplitz small margin: coefficient2; computed common start{combinedRequest.schedule.start}; \
        actual original weighted sum paid at both common-window coordinates."

/-- Run the actual public automatic constructor and pay its same retained near-circle mode schedule. -/
public def run : IO Unit := do
  let source : LaurentPolynomial := ⟨[⟨1, .nonnegative 1⟩, ⟨-root, .nonnegative 0⟩]⟩
  match source.prepare with
  | .zero _ => throw (IO.userError "the near-circle source returned a zero-symbol obstruction")
  | .normalized normalized =>
      if same : normalized.polynomial = Polynomial.Dense.Gaussian.LinearFactor.linearFactor root then
        let margin : Certificate normalized.polynomial :=
          same.symm ▸ Certificate.linearInside root (by decide +kernel)
        let paths := Boundary.Substitutions.prepare normalized.polynomial
        let clearance := margin.onBoundary paths
        let comparison := Toeplitz.Comparison.prepare normalized paths clearance
        unless normalized.poleOrder == 0 && comparison.index == -1 && comparison.circle.reading.winding == 1 do
          throw (IO.userError "the actual near-circle public comparison lost its index or independent winding")
        paid normalized.poleOrder comparison.circle.polynomial.inventory.side
          comparison.circle.polynomial.inventory.locations comparison.circle.polynomial.argument comparison.recurrence
      else
        throw (IO.userError "the near-circle normalization did not retain the actual original linear factor")

end TestPurelib.Polynomial.Laurent.Toeplitz.SmallMargin
