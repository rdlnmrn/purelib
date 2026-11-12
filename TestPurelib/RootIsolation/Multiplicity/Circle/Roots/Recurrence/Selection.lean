module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Selection
import Purelib.Polynomial.Clearance.Circle
import Purelib.System.IO

/-!
# Selected startup kernels inside the complete original source basis

The same automatic ledger retains its full and selected words. Their
coordinate transport preserves repeated and zero roots, excludes exterior
blocks, and reads the actual startup kernel through the complete basis.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Selection

open Purelib
open Data renaming Vector → Vec
open Data.Vector.Basic
open Data.Vector
open Data.Gaussian.Basic (Canonical)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian
open Polynomial.Clearance.Circle (Certificate Margin)
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots
open LinearAlgebra.Matrix

/-- A double zero and triple exterior root retain both transient coordinates and reject the exterior block. -/
private def mixedSource : CoefficientPolynomial := ⟨[1, -6, 12, -8, 0, 0]⟩

/-- A nonmonic double interior root has a genuine one-row startup kernel. -/
private def repeatedSource : CoefficientPolynomial := ⟨[2, -2, 1/2]⟩

/-- A single exterior root gives a genuinely empty original selected word. -/
private def exteriorSource : CoefficientPolynomial := ⟨[1, -2]⟩

/-- Check one original automatic ledger's cached inclusion, exact full action and actual startup/free coordinates. -/
private def check {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0) : IO Unit := do
  let argument := PositiveArgument.prepare inventory
  let ledger := Roots.Recurrence.prepare argument rows nonzero
  let bridge := Roots.Recurrence.Selection.prepare ledger
  let actual := ledger.boundary.selected.result
  let selection := ledger.boundary.selected.selection
  let coordinates := bridge.coordinates
  let fullBasis := bridge.basis
  let free := vectorOfFn fun index : Fin (selection.word.length - actual.normal.rank) =>
    Multiplicity.Roots.Stages.Images.coefficientMap ledger.prepared.separation.prepared.stages
      ((index.val + 1 : Nat) : Canonical)
  let selected := actual.normal.kernelVector free
  let extended := coordinates.extend selected
  let restricted := coordinates.restrict extended
  let fullValues := Rectangular.apply (fullBasis.horizon (Roots.Boundary.horizon ledger.prepared rows)) extended
  let selectedValues := Rectangular.apply (Rectangular.transpose actual.readings.values) selected
  let recovered := fullBasis.coordinates (Split.take bridge.room selectedValues)
  have _ := bridge.restore
  have _ := coordinates.restore
  have _ := coordinates.restrict_extend selected
  have _ := bridge.horizon_extend selected
  have _ := bridge.selected_coordinates selected
  have _ := bridge.horizon_satisfies 11 extended
  have _ := bridge.horizon_restrict extended (fun index rejected =>
    coordinates.extend_rejected selected index rejected)
  have solution := bridge.kernel_extend free
  have _ := (bridge.kernel_extend_iff selected).mp solution.1
  for index in List.ofFn (fun index : Fin selection.word.length => index) do
    unless decide (restricted index = selected index) do
      throw (IO.userError "the original selected coefficient did not survive full-word inclusion and restriction")
  for index in List.ofFn (fun index : Fin selection.fullWord.length => index) do
    unless decide (recovered index = extended index) do
      throw (IO.userError "the same complete source inverse did not recover the actual selected zero extension")
    if rejected : selection.labels (selection.fullWord[index.val]'index.isLt) = false then
      have _ := coordinates.extend_rejected selected index rejected
      unless decide (extended index = 0) do
        throw (IO.userError "the actual selected inclusion retained a rejected original exterior coordinate")
  for index in List.ofFn (fun index : Fin (Roots.Boundary.horizon ledger.prepared rows) => index) do
    unless decide (fullValues index = selectedValues index) do
      throw (IO.userError "the full original source basis changed a selected repeated/transient mode trajectory")
  let startup := Polynomial.Recurrence.boundary ledger.prepared.mapped rows fullValues
  for index in List.ofFn (fun index : Fin rows => index) do
    unless decide (startup index = 0) do
      throw (IO.userError "the complete source trajectory lost the actual selected free startup coordinates")
  System.IO.println s!"Original selected/full coordinate transport: full{selection.fullWord.length}, \
    selected{selection.word.length}, startup{rows}; same exact source trajectory and kernel."

/-- Dispatch the original positive inventory without supplying roots, labels, ranks or coordinate matrices. -/
private def positive {source : CoefficientPolynomial} {clearance : Certificate source}
    (inventory : Inventory clearance) (rows : Nat) (nonzero : 0 < rows → source.eval 0 ≠ 0) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "the original positive selection fixture became constant")
  | .positive _ _, locations => check locations rows nonzero

/-- The original finite boundary attempt supplies each actual source ledger's complete clearance. -/
private def exercise (source : CoefficientPolynomial) (normalized : source.normalize = source) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0) : IO Unit := do
  let attempt := RationalFunctions.Curve.Canonical.Circle.Boundary.prepare source 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "the original selected/full fixture has actual boundary contact")
  | .inconclusive _ _ _ _ _ =>
      throw (IO.userError "the bounded original selected/full clearance attempt is inconclusive")
  | .clear boundary =>
      let margin := Margin.prepare attempt.1.paths boundary
      positive (Inventory.prepare margin.toCertificate normalized) rows nonzero

/-- Execute both original mixed-transient/exterior and nonmonic repeated-interior transport chains. -/
public def run : IO Unit := do
  exercise mixedSource (by decide +kernel) 0 (fun impossible => False.elim (Nat.not_lt_zero _ impossible))
  exercise repeatedSource (by decide +kernel) 1 (fun _ => by decide +kernel)
  exercise exteriorSource (by decide +kernel) 1 (fun _ => by decide +kernel)

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Recurrence.Selection
