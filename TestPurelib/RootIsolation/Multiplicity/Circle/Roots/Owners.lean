module

import Purelib.RootIsolation.Multiplicity.Circle.Roots.Owners
import Purelib.Polynomial.Clearance.Circle
import Purelib.System.IO

/-!
# Original radial labels of automatic formal root occurrences

The mixed source has a double zero and a triple exterior linear root. Its
original geometric inventory and automatic formal Bank share one positive
input. The aligned original occurrences retain both context coordinates,
their original multiplicities and the independently counted selected word.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Owners

open Purelib
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Clearance.Circle (Certificate Margin)
open RationalFunctions.Curve.Canonical.Circle
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Polynomial.Dense.Gaussian.Multiplicity.Roots
open RootIsolation.Multiplicity.Circle
open RootIsolation.Multiplicity.Circle.Roots

/-- The normalized degree-five mixed source `z²(z-2)³` with distinct original multiplicities. -/
private def source : CoefficientPolynomial := ⟨[1, -6, 12, -8, 0, 0]⟩

/-- The source retains its original nonzero leading coefficient. -/
private theorem normalized : source.normalize = source := by decide +kernel

/-- Check both original context occurrences in the same retained geometric and formal parents. -/
private def check {opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {clearance : Certificate source} {family : PositiveFamily input}
    (inventory : PositiveInventory clearance input family) : IO Unit := do
  let prepared := Polynomial.Dense.Gaussian.Multiplicity.Roots.prepare input
  let owners := Owners.prepare prepared inventory
  let rows := List.ofFn (fun index : Fin prepared.bank.blocks.length =>
    let occurrence := owners.occurrences index
    (occurrence.context.val, occurrence.localRoot.val, occurrence.multiplicity, occurrence.inside inventory))
  System.IO.println s!"Original owner rows {reprStr rows}; inside/outside \
    {inventory.insideCount}/{inventory.outsideCount}; selected {owners.selection.count}."
  unless input.contexts.length == 2 && prepared.bank.blocks.length == 2 &&
      inventory.insideCount == 2 && inventory.outsideCount == 3 &&
      owners.selection.count == 2 && owners.selection.word.length == 2 &&
      rows == [(0, 0, 3, false), (1, 0, 2, true)] do
    throw (IO.userError "original formal/geometric occurrence labels or multiplicities changed")
  for index in List.ofFn (fun index : Fin prepared.bank.blocks.length => index) do
    unless (owners.occurrences index).context.val == (prepared.contextIndex index).val &&
        (owners.occurrences index).localRoot.val == (prepared.origin index).root.val &&
        owners.selection.labels index == (owners.occurrences index).inside inventory do
      throw (IO.userError "an aligned occurrence lost its original context, local root or retained radial state")
  System.IO.println "Original owner alignment: two contexts/blocks, inside2/outside3; selected length2."

/-- Read the positive branch of the same already constructed original radial inventory. -/
private def positive {clearance : Certificate source} (inventory : Inventory clearance) : IO Unit :=
  match inventory.side, inventory.locations with
  | .constant _ _ _, _ => throw (IO.userError "the mixed ownership source became constant")
  | .positive _ _, locations => check locations

/-- Construct the mixed zero/linear original inventory and align its actual original formal Bank once. -/
public def run : IO Unit := do
  let attempt := Boundary.prepare source 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "the ownership fixture met the unit boundary")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "the ownership fixture lacked whole-circle clearance")
  | .clear boundary =>
      let margin := Margin.prepare attempt.1.paths boundary
      positive (Inventory.prepare margin.toCertificate normalized)

end TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Owners
