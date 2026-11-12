module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Observation
import Purelib.Polynomial.Clearance.Circle
import Purelib.Data.Vector.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.GetD
import Purelib.System.IO

/-!
# Complete original recurrence ledgers and paid mode observations

Mixed zero and exterior factors test the inverse-free zero-row branch. A
nonmonic repeated interior factor tests an actual startup constraint, full
source coordinates and a nontrivial constant reciprocal. Every finite mode
request is paid through the same original automatic common reading.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence

open Purelib
open Data renaming Vector → Vec
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data.List (getD)
open Data.Vector.Basic
open Data.Vector
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian
open Data.Rat.Fraction (Rational)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian
open Polynomial.Clearance.Circle (Certificate Margin)
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots
open Polynomial.Recurrence.Mode (Hermite)
open Polynomial.Recurrence.Mode.Reading (Selected)
open LinearAlgebra.Matrix

/-- A genuine double zero and triple exterior root supply five complete source modes but two selected transients. -/
private def mixedSource : CoefficientPolynomial := ⟨[1, -6, 12, -8, 0, 0]⟩

/-- A nonmonic double interior root supplies one coupled startup equation. -/
private def repeatedSource : CoefficientPolynomial := ⟨[2, -2, 1 / 2]⟩

/-- Check the actual ledger, automatic common payment and formal mode windows at the same original owners. -/
private def check {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0) (degree inside rank kernel : Nat) (defect : Int) : IO Unit := do
  let argument := PositiveArgument.prepare inventory
  let ledger := Roots.Recurrence.prepare argument rows nonzero
  let request := Roots.Recurrence.Request.prepare ledger (1 / 16) (by decide +kernel) 3
  let observation := Roots.Recurrence.Observation.prepare request
  let reading := observation.reading
  have _ := ledger.defect_eq
  have _ := ledger.restore
  have _ := request.restore
  have _ := observation.restore
  have _ := observation.selected_equations
  unless ledger.recurrence.fullWord.length == degree && ledger.owners.selection.count == inside &&
      inventory.insideCount == inside && ledger.boundary.selected.result.normal.rank == rank &&
      ledger.boundary.selected.result.normal.kernelDimension == kernel && ledger.defect == defect &&
      reading.gain == ledger.parameters.finalGain && reading.error == 0 &&
      decide (reading.error < request.modes.tolerance) do
    throw (IO.userError "the actual recurrence ledger lost its full basis, computed boundary or paid common endpoint")
  for column in List.ofFn (fun column : Fin ledger.owners.selection.word.length => column) do
    let entry := request.modes.schedule.entryAt column
    let point := (ledger.prepared.bank.block (Selected.original ledger.owners.selection column)).point
    for offset in List.ofFn (fun offset : Fin 3 => offset) do
      have _ := observation.window_lt column offset
      let value := reading.read (Polynomial.Recurrence.Mode.window point (request.modes.orders.orders column)
        (entry.inside.index + 3) (entry.index offset))
      unless decide (value.normSq < (1 / 16 : Rational)) do
        throw (IO.userError "a paid original formal generalized mode exceeded its retained finite-window request")
  let columns := ledger.boundary.selected.result.readings.values
  for column in List.ofFn (fun column : Fin ledger.boundary.selected.selection.word.length => column) do
    let values := columns column
    have _ := observation.row_eq values 0
    have _ := observation.boundary_eq values
    let observed := Polynomial.Recurrence.Reading.values reading values
    unless decide (reading.read (Polynomial.Recurrence.row ledger.prepared.mapped rows values 0) =
        Polynomial.Recurrence.row source rows observed 0) do
      throw (IO.userError "the actual original mode lost an exact Gaussian recurrence reading")
    let originalBoundary := Polynomial.Recurrence.Reading.values reading
      (Polynomial.Recurrence.boundary ledger.prepared.mapped rows values)
    let observedBoundary := Polynomial.Recurrence.boundary source rows observed
    for index in List.ofFn (fun index : Fin rows => index) do
      unless decide (originalBoundary index = observedBoundary index) do
        throw (IO.userError "the actual original mode lost an exact Gaussian startup reading")
  let actual := ledger.boundary.selected.result
  let normal := actual.normal
  let free := vectorOfFn (fun index : Fin (ledger.boundary.selected.selection.word.length - normal.rank) =>
    Multiplicity.Roots.Stages.Images.coefficientMap ledger.prepared.separation.prepared.stages
      ((index.val + 1 : Nat) : Canonical))
  let kernelCoefficients := normal.kernelVector free
  let selectedMatrix := Rectangular.transpose actual.readings.values
  let selectedValues := Rectangular.apply selectedMatrix kernelCoefficients
  have solution := actual.kernel_solution ledger.recurrence.companion
    ledger.boundary.selected.selection.admissible free
  have _ := actual.kernel_coordinates kernelCoefficients solution.1
  have _ := (actual.kernel_iff kernelCoefficients).mp solution.1
  let coefficientRecovery := normal.kernelVector (normal.kernelCoordinates kernelCoefficients)
  for index in List.ofFn (fun index : Fin ledger.boundary.selected.selection.word.length => index) do
    unless decide (coefficientRecovery index = kernelCoefficients index) do
      throw (IO.userError "the actual one-sided solution lost its original free-coordinate reconstruction")
  let startup := Polynomial.Recurrence.boundary ledger.prepared.mapped rows selectedValues
  let scalarStartup := Polynomial.Recurrence.boundary source rows
    (Polynomial.Recurrence.Reading.values reading selectedValues)
  for index in List.ofFn (fun index : Fin rows => index) do
    unless decide (startup index = 0) && decide (scalarStartup index = 0) do
      throw (IO.userError "the actual boundary kernel failed an original formal or Gaussian startup row")
  for start in List.range (Roots.Boundary.horizon ledger.prepared rows) do
    if complete : start + ledger.prepared.mapped.natDegree < Roots.Boundary.horizon ledger.prepared rows then
      have _ := solution.2 start complete
      let lower := sumFin (fun column : Fin ledger.prepared.mapped.natDegree =>
        getD ledger.recurrence.companion.coefficients column.val 0 *
          selectedValues ⟨start + column.val, Nat.lt_trans (Nat.add_lt_add_left column.isLt start) complete⟩)
      let tail := lower + ledger.prepared.mapped.leadingCoeff *
        selectedValues ⟨start + ledger.prepared.mapped.natDegree, complete⟩
      unless decide (tail = 0) do
        throw (IO.userError "the actual one-sided kernel failed a fully contained original source row")
  if rows == 1 && degree == 2 then
    let far := reading.read (Polynomial.Recurrence.row ledger.prepared.mapped rows selectedValues
      (rows + Roots.Boundary.horizon ledger.prepared rows - 1))
    unless far == (1 / 4 : Canonical) do
      throw (IO.userError "the finite recurrence fixture accidentally imposed an extra zero right boundary")
  let count := ledger.recurrence.fullWord.length + 2
  let coefficients := vectorOfFn (fun index : Fin ledger.recurrence.fullWord.length =>
    Multiplicity.Roots.Stages.Images.coefficientMap ledger.prepared.separation.prepared.stages
      ((index.val + 1 : Nat) : Canonical))
  for start in [0, 1, 5] do
    let lateRows := ledger.recurrence.basis.horizonFrom start ledger.recurrence.fullWord.length
    let lateValues := Rectangular.apply lateRows coefficients
    let recovered := ledger.recurrence.basis.coordinates lateValues
    let transition := Hermite.Shift.transition (Hermite.point ledger.prepared.bank.blocks) ledger.recurrence.fullWord
      ledger.recurrence.basis.occurrences
    let shifted := Rectangular.apply (Arithmetic.power transition start) coefficients
    have _ := ledger.recurrence.basis.coordinates_horizonFrom start coefficients
    for index in List.ofFn (fun index : Fin ledger.recurrence.fullWord.length => index) do
      unless decide (recovered index = shifted index) do
        throw (IO.userError "the same original inverse failed to recover the canonical late-window coordinates")
  let fullValues := Rectangular.apply (ledger.recurrence.basis.horizon count) coefficients
  have equations := ledger.recurrence.horizon_satisfies count coefficients
  have enough := Nat.le_add_right ledger.recurrence.fullWord.length 2
  have _ := ledger.reconstruct fullValues enough equations
  let extracted := ledger.recurrence.basis.coordinates (Split.take enough fullValues)
  let anyCoordinates := ledger.recurrence.basis.coordinatesOfHorizon fullValues
  have _ := ledger.reconstruct_any fullValues equations
  have _ := ledger.recurrence.basis.coordinatesOfHorizon_of_le fullValues enough
  for index in List.ofFn (fun index : Fin ledger.recurrence.fullWord.length => index) do
    unless decide (extracted index = anyCoordinates index) do
      throw (IO.userError "complete-horizon coordinates changed the original retained prefix/inverse operation")
  let restored := Rectangular.apply (ledger.recurrence.basis.horizon count) extracted
  for index in List.ofFn (fun index : Fin count => index) do
    unless decide (restored index = fullValues index) do
      throw (IO.userError "the complete original source basis failed to reconstruct its actual finite \
        recurrence solution")
  for shortCount in [0, 1] do
    if short : shortCount < ledger.prepared.mapped.natDegree then
      let prefixValues := vectorOfFn (fun index : Fin shortCount =>
        Multiplicity.Roots.Stages.Images.coefficientMap ledger.prepared.separation.prepared.stages
          ((index.val + 7 : Nat) : Canonical))
      have prefixEquations : ledger.recurrence.companion.Satisfies prefixValues := by
        intro start complete
        have degreeBelow := Nat.lt_of_le_of_lt
          (Nat.le_add_left ledger.prepared.mapped.natDegree start) complete
        exact False.elim (Nat.lt_asymm short degreeBelow)
      have _ := ledger.reconstruct_any prefixValues prefixEquations
      let prefixCoordinates := ledger.recurrence.basis.coordinatesOfHorizon prefixValues
      let prefixRestored := Rectangular.apply (ledger.recurrence.basis.horizon shortCount) prefixCoordinates
      for index in List.ofFn (fun index : Fin shortCount => index) do
        unless decide (prefixRestored index = prefixValues index) do
          throw (IO.userError "the actual shorter finite source prefix failed to reconstruct")
      let initial := Rectangular.apply ledger.recurrence.basis.matrix prefixCoordinates
      for index in List.ofFn (fun index : Fin ledger.recurrence.fullWord.length => index) do
        let expected := if before : index.val < shortCount then prefixValues ⟨index.val, before⟩ else 0
        unless decide (initial index = expected) do
          throw (IO.userError "the actual shorter prefix did not use the same zero-padded initial inverse")
    else
      throw (IO.userError "the original shorter-prefix fixture no longer has a shorter horizon")
  System.IO.println s!"Original recurrence ledger: rows{rows}, full{degree}, inside{inside}, \
    rank{rank}, kernel{kernel}, \
    defect{defect}; paid actual generalized-mode windows and exact source/startup readings."

/-- Dispatch the same original positive inventory without rebuilding preprocessing or its geometric owners. -/
private def positive {source : CoefficientPolynomial} {clearance : Certificate source}
    (rows : Nat) (nonzero : 0 < rows → source.eval 0 ≠ 0)
    (degree inside rank kernel : Nat) (defect : Int) (inventory : Inventory clearance) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "a positive original recurrence fixture became constant")
  | .positive _ _, locations => check locations rows nonzero degree inside rank kernel defect

/-- Prepare the original whole-circle clearance and feed the same automatic inventory to its recurrence ledger. -/
private def exercise (source : CoefficientPolynomial) (normalized : source.normalize = source)
    (rows : Nat) (nonzero : 0 < rows → source.eval 0 ≠ 0)
    (degree inside rank kernel : Nat) (defect : Int) : IO Unit := do
  let attempt := RationalFunctions.Curve.Canonical.Circle.Boundary.prepare source 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "an original recurrence fixture met the unit circle")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "an original recurrence fixture lacked whole-circle clearance")
  | .clear boundary =>
      let margin := Margin.prepare attempt.1.paths boundary
      positive rows nonzero degree inside rank kernel defect (Inventory.prepare margin.toCertificate normalized)

/-- Run the mixed zero/exterior and nonmonic repeated-interior original construction chains. -/
public def run : IO Unit := do
  exercise mixedSource (by decide +kernel) 0
    (fun impossible => False.elim (Nat.not_lt_zero 0 impossible)) 5 2 0 2 (-2)
  exercise repeatedSource (by decide +kernel) 1 (fun _ => by decide +kernel) 2 2 1 1 (-1)

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence
